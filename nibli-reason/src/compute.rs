use super::*;

// ─── Injectable compute dispatch (per-KB; see `KnowledgeBase::set_compute_dispatch`) ───

/// Single-predicate external compute dispatch function (stored on `KnowledgeBaseInner`).
pub(crate) type EvalFn = fn(&str, &[LogicalTerm]) -> Result<bool, String>;
/// Batch external compute dispatch function (stored on `KnowledgeBaseInner`).
pub(crate) type BatchEvalFn = fn(&[ComputeRequest]) -> Vec<Result<bool, String>>;

/// One external compute call, keyed by the exact typed public arguments sent to
/// the backend. Numeric keys use their IEEE-754 bits so `-0.0`, `0.0`, and NaN
/// payloads cannot alias accidentally.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ComputeCallKey {
    relation: String,
    args: Vec<ComputeArgKey>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ComputeArgKey {
    Variable(String),
    Constant(String),
    Description(String),
    Unspecified,
    Number(u64),
}

impl ComputeCallKey {
    fn new(relation: &str, args: &[LogicalTerm]) -> Self {
        Self {
            relation: relation.to_string(),
            args: args
                .iter()
                .map(|arg| match arg {
                    LogicalTerm::Variable(v) => ComputeArgKey::Variable(v.clone()),
                    LogicalTerm::Constant(c) => ComputeArgKey::Constant(c.clone()),
                    LogicalTerm::Description(d) => ComputeArgKey::Description(d.clone()),
                    LogicalTerm::Unspecified => ComputeArgKey::Unspecified,
                    LogicalTerm::Number(n) => ComputeArgKey::Number(n.to_bits()),
                })
                .collect(),
        }
    }
}

/// The evidence returned for one proof-local compute call.
#[derive(Clone)]
pub(super) struct ComputeEvaluation {
    pub method: &'static str,
    pub verdict: QueryResult,
}

/// Fresh per top-level query. This is deliberately not a KB field: it makes a
/// backend reply stable across iterative-deepening probes, proof reconstruction,
/// quantifier probe/re-walk, and duplicate roots, while retaining nothing for a
/// later query.
#[derive(Default)]
pub(super) struct QueryComputeMemo {
    entries: HashMap<ComputeCallKey, ComputeEvaluation>,
}

pub(super) fn extract_num_value(
    term: &LogicalTerm,
    subs: &HashMap<String, GroundTerm>,
) -> Option<f64> {
    match term {
        LogicalTerm::Number(n) => Some(*n),
        LogicalTerm::Variable(v) => {
            let gt = subs.get(v.as_str())?;
            gt.as_f64()
        }
        _ => None,
    }
}

/// Flat-path numeric comparison. Returns `None` when this is not a numeric
/// comparison at all (non-numeric args or an unknown relation — the caller
/// falls through to normal predicate lookup), and a VERDICT otherwise: finite
/// operands decide `True`/`False`; a NON-FINITE operand is
/// `Unknown(NonFinite)` — mirroring the event-decomposed path's guard below.
/// A comparison over ±inf/NaN is meaningless, and returning `None` for it
/// would degrade to `PredicateNotFound` → a confident FALSE.
pub(super) fn try_numeric_comparison(
    rel: &str,
    args: &[LogicalTerm],
    subs: &HashMap<String, GroundTerm>,
) -> Option<QueryResult> {
    let a = extract_num_value(args.first()?, subs)?;
    let b = extract_num_value(args.get(1)?, subs)?;
    let holds = match rel {
        "greater" => a > b,
        "less" => a < b,
        "num_equal" => a == b,
        _ => return None,
    };
    if !a.is_finite() || !b.is_finite() {
        return Some(QueryResult::Unknown(UnknownReason::NonFinite));
    }
    Some(if holds {
        QueryResult::True
    } else {
        QueryResult::False
    })
}

pub(super) fn try_arithmetic_evaluation(
    rel: &str,
    args: &[LogicalTerm],
    subs: &HashMap<String, GroundTerm>,
) -> Option<bool> {
    let x1 = extract_num_value(args.first()?, subs)?;
    let x2 = extract_num_value(args.get(1)?, subs)?;
    let x3 = extract_num_value(args.get(2)?, subs)?;
    // The relation match + tolerant-equality comparison is shared with the nibli-host
    // host fast path (and the Python reference backend) so the three agree.
    nibli_types::eval_arithmetic(rel, &[x1, x2, x3])
}

/// Project a ground term onto the public `LogicalTerm` surface.
///
/// Compute dispatch calls this only after its structural guard has rejected
/// internal `Skolem`/`SkolemFn`/`DepPair` terms. The generated-term arms are a
/// presentation fallback for non-dispatch consumers; they do not authorize
/// sending a display name to the backend.
pub(super) fn ground_term_to_logical_term(gt: &GroundTerm) -> LogicalTerm {
    match gt {
        GroundTerm::Constant(c) => LogicalTerm::Constant(c.clone()),
        GroundTerm::Skolem(symbol) => LogicalTerm::Constant(symbol.display_name()),
        GroundTerm::Number(bits) => LogicalTerm::Number(f64::from_bits(*bits)),
        GroundTerm::Description(d) => LogicalTerm::Description(d.clone()),
        GroundTerm::Unspecified => LogicalTerm::Unspecified,
        GroundTerm::PatternVar(v) => LogicalTerm::Variable(v.clone()),
        GroundTerm::SkolemFn(symbol, _) => LogicalTerm::Constant(symbol.display_name()),
        GroundTerm::DepPair(_, _) => LogicalTerm::Unspecified,
        GroundTerm::SkolemPlaceholder(symbol) => LogicalTerm::Variable(symbol.display_name()),
    }
}

/// Witness-surface conversion. Dependent Skolem terms keep their functional
/// display form — SkolemFn("sk_1", adam) renders as `sk_1(adam)` — so
/// distinct dependent witnesses stay distinguishable in `[Find]` results and
/// proof steps. Identity and origin are carried separately and never recovered
/// from this presentation string.
pub(super) fn witness_term_to_logical_term(gt: &GroundTerm) -> LogicalTerm {
    match gt {
        GroundTerm::Skolem(..) | GroundTerm::SkolemFn(..) | GroundTerm::DepPair(..) => {
            LogicalTerm::Constant(gt.to_display_string())
        }
        other => ground_term_to_logical_term(other),
    }
}

// ─── Decomposed numeric-group evaluation ────────────────────────────────────
//
// Neo-Davidsonian event decomposition compiles a surface numeric proposition to
// `∃ev. head(ev) ∧ rel_x1(ev, a) ∧ rel_x2(ev, b) ∧ ...` — the head
// (ComputeNode for registered compute predicates, a plain Predicate for the
// query-time comparisons greater/less/num_equal) carries ONLY the event variable;
// the operands live in sibling role predicates. The flat evaluators above
// read the head's own args and never see the numbers, so every surface
// numeric query used to return FALSE.

/// The verdict of a numeric-group evaluation, tagged with the route taken
/// (the tag feeds the traced evaluator's ComputeCheck step).
pub(super) struct NumericGroupVerdict {
    pub relation: String,
    /// "numeric" (comparison), "arithmetic" (built-in), "backend" (dispatch ok),
    /// or "backend_unavailable" (dispatch failed → Unknown, never False).
    pub method: &'static str,
    pub verdict: QueryResult,
}

/// Evaluate an event-decomposed numeric/compute group at its `∃ev` boundary.
///
/// Fires only on the EXACT group shape (the strictness is the soundness
/// guard): the body's And-tree must consist of one head — `ComputeNode(rel,
/// [Var ev])`, or `Predicate(rel, [Var ev])` with rel ∈ {greater, less, num_equal}
/// — plus role predicates `rel_xN(Var ev, arg)` for the same rel with
/// contiguous N starting at 1. Any other conjunct (pair modifier roles,
/// tense nodes in hand-built buffers, a different event variable) returns
/// None and normal evaluation proceeds, so stored facts stay reachable.
///
/// Routing is by RELATION NAME, arithmetic-first (matching the documented
/// design, nibli-host's host evaluate(), and the batch path): comparison →
/// built-in arithmetic → (ComputeNode heads only) external backend dispatch.
/// A backend error (or no backend at all) yields
/// `Unknown(BackendUnavailable)` — successful results are query-local and are
/// never reused during an outage.
///
/// A computed `false` is DEFINITIVE, matching the flat ComputeNode arm. Results
/// never enter the logical fact store: ingesting this decomposed group would
/// mint a fresh Skolem event per query.
pub(super) fn try_evaluate_numeric_group(
    inner: &KnowledgeBaseInner,
    buffer: &LogicBuffer,
    exists_var: &str,
    body_id: u32,
    subs: &HashMap<String, GroundTerm>,
    compute_memo: &mut QueryComputeMemo,
) -> Option<NumericGroupVerdict> {
    // Flatten the And-tree; bail on anything that is not And/Predicate/Compute.
    let mut conjuncts: Vec<u32> = Vec::new();
    let mut stack = vec![body_id];
    while let Some(id) = stack.pop() {
        match get_node(buffer, id).ok()? {
            LogicNode::AndNode((l, r)) => {
                stack.push(*l);
                stack.push(*r);
            }
            LogicNode::Predicate(_) | LogicNode::ComputeNode(_) => conjuncts.push(id),
            _ => return None,
        }
    }

    // Identify exactly one head over our event variable.
    let is_head_var =
        |args: &[LogicalTerm]| matches!(args, [LogicalTerm::Variable(v)] if v == exists_var);
    let mut head: Option<(&str, bool)> = None; // (relation, head_is_compute_node)
    for &id in &conjuncts {
        match get_node(buffer, id).ok()? {
            LogicNode::ComputeNode((rel, args)) if is_head_var(args) => {
                if head.is_some() {
                    return None; // two heads — not a single group
                }
                head = Some((rel.as_str(), true));
            }
            LogicNode::Predicate((rel, args))
                if is_head_var(args)
                    && nibli_types::relations::is_numeric_comparison(rel.as_str()) =>
            {
                if head.is_some() {
                    return None;
                }
                head = Some((rel.as_str(), false));
            }
            _ => {}
        }
    }
    let (rel, head_is_compute) = head?;

    // Every other conjunct must be a role predicate rel_xN(Var ev, arg).
    let role_prefix = format!("{rel}_x");
    let mut roles: Vec<Option<&LogicalTerm>> = Vec::new();
    for &id in &conjuncts {
        match get_node(buffer, id).ok()? {
            LogicNode::ComputeNode((r, args)) if is_head_var(args) && r.as_str() == rel => {}
            LogicNode::Predicate((r, args)) if is_head_var(args) && r.as_str() == rel => {}
            LogicNode::Predicate((r, args)) if r.starts_with(&role_prefix) => {
                let n: usize = r[role_prefix.len()..].parse().ok()?;
                if n == 0 {
                    return None;
                }
                match args.as_slice() {
                    [LogicalTerm::Variable(v), arg] if v == exists_var => {
                        if roles.len() < n {
                            roles.resize(n, None);
                        }
                        if roles[n - 1].is_some() {
                            return None; // duplicate role index
                        }
                        roles[n - 1] = Some(arg);
                    }
                    _ => return None,
                }
            }
            _ => return None, // unrelated conjunct — not a pure group
        }
    }
    // Roles must be contiguous x1..=xN (nibli-semantics always emits the full arity).
    if roles.is_empty() || roles.iter().any(|r| r.is_none()) {
        return None;
    }
    let collected: Vec<LogicalTerm> = roles.into_iter().map(|r| r.unwrap().clone()).collect();

    // Non-finite numeric input (a literal too large for an f64 overflows to ±inf), or a
    // finite-operand arithmetic whose RESULT overflows, makes any comparison/arithmetic
    // undetermined — surface `Unknown(NonFinite)`, NEVER a confident TRUE/FALSE. (Returning
    // None here would degrade to `PredicateNotFound` → a confident FALSE.) Divide-by-zero
    // over finite operands stays a decided FALSE: `eval_arithmetic` returns `Some(false)`,
    // not `None`, for it.
    {
        let operands: Vec<f64> = collected
            .iter()
            .filter_map(|t| extract_num_value(t, subs))
            .collect();
        let non_finite = match rel {
            r if nibli_types::relations::is_builtin_arithmetic(r) => {
                operands.len() == 3 && nibli_types::eval_arithmetic(rel, &operands).is_none()
            }
            r if nibli_types::relations::is_numeric_comparison(r) => {
                operands.len() >= 2 && operands.iter().take(2).any(|n| !n.is_finite())
            }
            _ => false,
        };
        if non_finite {
            return Some(NumericGroupVerdict {
                relation: rel.to_string(),
                method: "non_finite",
                verdict: QueryResult::Unknown(UnknownReason::NonFinite),
            });
        }
    }

    // Route by relation name, arithmetic-first. (The non-finite guard above
    // already returned for non-finite comparison operands, so the verdict here
    // is always definitive; the match keeps the two guards mirror-consistent.)
    if let Some(verdict) = try_numeric_comparison(rel, &collected, subs) {
        return Some(NumericGroupVerdict {
            relation: rel.to_string(),
            method: if matches!(verdict, QueryResult::Unknown(_)) {
                "non_finite"
            } else {
                "numeric"
            },
            verdict,
        });
    }
    if let Some(holds) = try_arithmetic_evaluation(rel, &collected, subs) {
        return Some(NumericGroupVerdict {
            relation: rel.to_string(),
            method: "arithmetic",
            verdict: bool_verdict(holds),
        });
    }
    if head_is_compute {
        // External dispatch accepts the same public LogicalTerm surface as a
        // flat ComputeNode: numbers, user constants, opaque descriptions,
        // Unspecified, and any variable the caller deliberately leaves free.
        // `resolve_args_for_dispatch` rejects engine-minted identities before
        // presentation conversion; that refusal is non-definitive rather than
        // falling through to ordinary event lookup and becoming a CWA FALSE.
        return Some(match resolve_args_for_dispatch(&collected, subs) {
            Ok(resolved) => {
                let evaluation = evaluate_external_compute(inner, rel, &resolved, compute_memo);
                NumericGroupVerdict {
                    relation: rel.to_string(),
                    method: evaluation.method,
                    verdict: evaluation.verdict,
                }
            }
            Err(_) => NumericGroupVerdict {
                relation: rel.to_string(),
                method: "backend_unavailable",
                verdict: QueryResult::Unknown(UnknownReason::BackendUnavailable),
            },
        });
    }
    None
}

/// True → `QueryResult::True`, false → `QueryResult::False`.
fn bool_verdict(holds: bool) -> QueryResult {
    if holds {
        QueryResult::True
    } else {
        QueryResult::False
    }
}

pub(super) fn resolve_args_for_dispatch(
    args: &[LogicalTerm],
    subs: &HashMap<String, GroundTerm>,
) -> Result<Vec<LogicalTerm>, String> {
    for arg in args {
        if let LogicalTerm::Variable(v) = arg
            && let Some(gt) = subs.get(v.as_str())
            && matches!(
                gt,
                GroundTerm::Skolem(_)
                    | GroundTerm::SkolemFn(_, _)
                    | GroundTerm::DepPair(_, _)
                    | GroundTerm::SkolemPlaceholder(_)
            )
        {
            return Err(format!(
                "compute dispatch cannot represent internal witness `{}` as a user constant",
                gt.to_display_string()
            ));
        }
    }
    Ok(args
        .iter()
        .map(|a| match a {
            LogicalTerm::Variable(v) => {
                if let Some(gt) = subs.get(v.as_str()) {
                    ground_term_to_logical_term(gt)
                } else {
                    a.clone()
                }
            }
            _ => a.clone(),
        })
        .collect())
}

/// Forward a single predicate to the operator-configured external backend.
///
/// The caller trusts a successful reply for the current compute step. It never
/// inserts or caches the reply in the logical KB. The stock TCP dispatcher is
/// unauthenticated; a custom dispatcher owns any stronger admission policy — see
/// the trust-boundary note on `KnowledgeBase::set_compute_dispatch`.
/// Refusal message for a dispatch attempted during witness enumeration.
///
/// Enumeration runs its body once per candidate, so calling out from there costs one
/// request per candidate over a transport with no request binding, idempotency, or
/// replay detection. The budget is ZERO, and this is the single choke point every
/// evaluation route funnels through, so no new route can forget it. See
/// `KnowledgeBaseInner::find_enumeration`.
const NO_DISPATCH_IN_ENUMERATION: &str =
    "external compute is not dispatched during witness enumeration";

pub(super) fn dispatch_to_backend(
    inner: &KnowledgeBaseInner,
    rel: &str,
    args: &[LogicalTerm],
) -> Result<bool, String> {
    if inner.find_enumeration {
        return Err(NO_DISPATCH_IN_ENUMERATION.to_string());
    }
    match inner.compute_eval {
        Some(eval) => eval(rel, args),
        None => Err("Compute backend not registered".to_string()),
    }
}

/// Evaluate one external call at most once during the current top-level query.
/// The memo is proof-local evidence, not logical KB state: its owner creates it
/// at query ingress and drops it before returning to the caller.
pub(super) fn evaluate_external_compute(
    inner: &KnowledgeBaseInner,
    rel: &str,
    resolved: &[LogicalTerm],
    memo: &mut QueryComputeMemo,
) -> ComputeEvaluation {
    let key = ComputeCallKey::new(rel, resolved);
    if let Some(evaluation) = memo.entries.get(&key) {
        return evaluation.clone();
    }
    let evaluation = match dispatch_to_backend(inner, rel, resolved) {
        Ok(holds) => ComputeEvaluation {
            method: "backend",
            verdict: bool_verdict(holds),
        },
        Err(_) => ComputeEvaluation {
            method: "backend_unavailable",
            verdict: QueryResult::Unknown(UnknownReason::BackendUnavailable),
        },
    };
    memo.entries.insert(key, evaluation.clone());
    evaluation
}

/// Batch compute request.
pub struct ComputeRequest {
    pub relation: String,
    pub args: Vec<LogicalTerm>,
}

fn dispatch_batch_to_backend(
    inner: &KnowledgeBaseInner,
    requests: &[ComputeRequest],
) -> Vec<Result<bool, String>> {
    if inner.find_enumeration {
        return requests
            .iter()
            .map(|_| Err(NO_DISPATCH_IN_ENUMERATION.to_string()))
            .collect();
    }
    match inner.compute_batch_eval {
        Some(batch_eval) => batch_eval(requests),
        None => requests
            .iter()
            .map(|_| Err("Compute backend not registered".to_string()))
            .collect(),
    }
}

/// Result of batch compute. Results are query-local and do not mutate the KB.
pub(super) struct BatchComputeResult {
    pub results: Vec<bool>,
    pub methods: Vec<&'static str>,
}

pub(super) fn batch_evaluate_compute_for_members(
    inner: &KnowledgeBaseInner,
    rel: &str,
    args: &[LogicalTerm],
    var: &str,
    members: &[GroundTerm],
    subs: &HashMap<String, GroundTerm>,
) -> Option<BatchComputeResult> {
    let mut compute_memo = QueryComputeMemo::default();
    batch_evaluate_compute_for_members_with_memo(
        inner,
        rel,
        args,
        var,
        members,
        subs,
        &mut compute_memo,
    )
}

pub(super) fn batch_evaluate_compute_for_members_with_memo(
    inner: &KnowledgeBaseInner,
    rel: &str,
    args: &[LogicalTerm],
    var: &str,
    members: &[GroundTerm],
    subs: &HashMap<String, GroundTerm>,
    compute_memo: &mut QueryComputeMemo,
) -> Option<BatchComputeResult> {
    let mut results = vec![false; members.len()];
    let mut methods = vec!["arithmetic"; members.len()];
    let mut pending: Vec<(ComputeCallKey, Vec<LogicalTerm>, Vec<usize>)> = Vec::new();

    for (i, member) in members.iter().enumerate() {
        let mut s = subs.clone();
        s.insert(var.to_string(), member.clone());

        if let Some(r) = try_arithmetic_evaluation(rel, args, &s) {
            results[i] = r;
        } else {
            let resolved = resolve_args_for_dispatch(args, &s).ok()?;
            let key = ComputeCallKey::new(rel, &resolved);
            if let Some(evaluation) = compute_memo.entries.get(&key) {
                methods[i] = evaluation.method;
                match evaluation.verdict {
                    QueryResult::True => results[i] = true,
                    QueryResult::False => results[i] = false,
                    _ => return None,
                }
            } else if let Some((_, _, member_indices)) = pending
                .iter_mut()
                .find(|(pending_key, _, _)| *pending_key == key)
            {
                member_indices.push(i);
            } else {
                pending.push((key, resolved, vec![i]));
            }
        }
    }

    if pending.is_empty() {
        return Some(BatchComputeResult { results, methods });
    }

    let requests: Vec<ComputeRequest> = pending
        .iter()
        .map(|(_, resolved, _)| ComputeRequest {
            relation: rel.to_string(),
            args: resolved.clone(),
        })
        .collect();
    let batch_results = dispatch_batch_to_backend(inner, &requests);
    // The injectable batch seam must preserve one response per request. A
    // short response must not leave default `false` entries (a confident
    // undercount/counterexample), and a long one must not index past `pending`.
    // Returning None sends the caller through the scalar path, where each
    // malformed/unavailable request becomes non-definitive.
    if batch_results.len() != pending.len() {
        for (key, _, _) in pending {
            compute_memo.entries.insert(
                key,
                ComputeEvaluation {
                    method: "backend_unavailable",
                    verdict: QueryResult::Unknown(UnknownReason::BackendUnavailable),
                },
            );
        }
        return None;
    }

    let mut saw_error = false;
    for ((key, _, member_indices), result) in pending.into_iter().zip(batch_results) {
        let evaluation = match result {
            Ok(holds) => ComputeEvaluation {
                method: "backend",
                verdict: bool_verdict(holds),
            },
            Err(_) => {
                saw_error = true;
                ComputeEvaluation {
                    method: "backend_unavailable",
                    verdict: QueryResult::Unknown(UnknownReason::BackendUnavailable),
                }
            }
        };
        for member_idx in member_indices {
            methods[member_idx] = evaluation.method;
            if let QueryResult::True | QueryResult::False = evaluation.verdict {
                results[member_idx] = evaluation.verdict.is_true();
            }
        }
        compute_memo.entries.insert(key, evaluation);
    }
    if saw_error {
        None
    } else {
        Some(BatchComputeResult { results, methods })
    }
}
