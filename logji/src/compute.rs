use super::*;

// ─── Injectable compute dispatch (per-KB; see `KnowledgeBase::set_compute_dispatch`) ───

/// Single-predicate external compute dispatch function (stored on `KnowledgeBaseInner`).
pub(crate) type EvalFn = fn(&str, &[LogicalTerm]) -> Result<bool, String>;
/// Batch external compute dispatch function (stored on `KnowledgeBaseInner`).
pub(crate) type BatchEvalFn = fn(&[ComputeRequest]) -> Vec<Result<bool, String>>;

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
    let a = extract_num_value(args.get(0)?, subs)?;
    let b = extract_num_value(args.get(1)?, subs)?;
    let holds = match rel {
        "zmadu" => a > b,
        "mleca" => a < b,
        "dunli" => a == b,
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
    let x1 = extract_num_value(args.get(0)?, subs)?;
    let x2 = extract_num_value(args.get(1)?, subs)?;
    let x3 = extract_num_value(args.get(2)?, subs)?;
    // The relation match + tolerant-equality comparison is shared with the gasnu
    // host fast path (and the Python reference backend) so the three agree.
    nibli_types::eval_arithmetic(rel, &[x1, x2, x3])
}

/// Convert a GroundTerm back to a LogicalTerm for compute backend dispatch.
pub(super) fn ground_term_to_logical_term(gt: &GroundTerm) -> LogicalTerm {
    match gt {
        GroundTerm::Constant(c) => LogicalTerm::Constant(c.clone()),
        GroundTerm::Number(bits) => LogicalTerm::Number(f64::from_bits(*bits)),
        GroundTerm::Description(d) => LogicalTerm::Description(d.clone()),
        GroundTerm::Unspecified => LogicalTerm::Unspecified,
        GroundTerm::PatternVar(v) => LogicalTerm::Variable(v.clone()),
        GroundTerm::SkolemFn(name, _) => LogicalTerm::Constant(name.clone()),
        GroundTerm::DepPair(_, _) => LogicalTerm::Unspecified,
    }
}

/// Witness-surface conversion: unlike the compute-dispatch conversion above
/// (which only needs an opaque token), dependent Skolem terms keep their
/// functional form — SkolemFn("sk_1", adam) renders as `sk_1(adam)` — so
/// distinct dependent witnesses stay distinguishable in `[Find]` results and
/// `ExistsWitness` proof steps.
pub(super) fn witness_term_to_logical_term(gt: &GroundTerm) -> LogicalTerm {
    match gt {
        GroundTerm::SkolemFn(..) | GroundTerm::DepPair(..) => {
            LogicalTerm::Constant(gt.to_display_string())
        }
        other => ground_term_to_logical_term(other),
    }
}

// ─── Decomposed numeric-group evaluation ────────────────────────────────────
//
// Neo-Davidsonian event decomposition compiles a surface numeric bridi to
// `∃ev. head(ev) ∧ rel_x1(ev, a) ∧ rel_x2(ev, b) ∧ ...` — the head
// (ComputeNode for registered compute predicates, a plain Predicate for the
// query-time comparisons zmadu/mleca/dunli) carries ONLY the event variable;
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

/// Evaluate an event-decomposed numeric group at its `∃ev` boundary.
///
/// Fires only on the EXACT group shape (the strictness is the soundness
/// guard): the body's And-tree must consist of one head — `ComputeNode(rel,
/// [Var ev])`, or `Predicate(rel, [Var ev])` with rel ∈ {zmadu, mleca, dunli}
/// — plus role predicates `rel_xN(Var ev, arg)` for the same rel with
/// contiguous N starting at 1. Any other conjunct (tanru modifier roles,
/// tense nodes in hand-built buffers, a different event variable) returns
/// None and normal evaluation proceeds, so asserted facts stay reachable.
///
/// Routing is by RELATION NAME, arithmetic-first (matching the documented
/// design, gasnu's host evaluate(), and the batch path): comparison →
/// built-in arithmetic → (ComputeNode heads only) external backend dispatch.
/// A backend error degrades to None (store/NAF fallback), so no-backend
/// configs neither error nor hang.
///
/// A computed `false` is DEFINITIVE, matching the flat ComputeNode/Predicate
/// arms (the store-shadowing policy question is tracked in todo.md).
///
/// Deliberately performs NO auto-ingestion: unlike the flat path, whose
/// ground fact is byte-identical on every query (HashSet-deduped), ingesting
/// a group would mint a fresh Skolem event per query and accumulate
/// duplicate facts. Recomputation is free.
pub(super) fn try_evaluate_numeric_group(
    inner: &KnowledgeBaseInner,
    buffer: &LogicBuffer,
    exists_var: &str,
    body_id: u32,
    subs: &HashMap<String, GroundTerm>,
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
                if is_head_var(args) && matches!(rel.as_str(), "zmadu" | "mleca" | "dunli") =>
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
    // Roles must be contiguous x1..=xN (smuni always emits the full arity).
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
            "pilji" | "sumji" | "dilcu" => {
                operands.len() == 3 && nibli_types::eval_arithmetic(rel, &operands).is_none()
            }
            "zmadu" | "mleca" | "dunli" => {
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
        // External dispatch: every non-Unspecified role must resolve numeric.
        let resolved = resolve_args_for_dispatch(&collected, subs);
        let dispatchable = resolved
            .iter()
            .all(|t| matches!(t, LogicalTerm::Number(_) | LogicalTerm::Unspecified));
        if dispatchable {
            return Some(match dispatch_to_backend(inner, rel, &resolved) {
                Ok(holds) => NumericGroupVerdict {
                    relation: rel.to_string(),
                    method: "backend",
                    verdict: bool_verdict(holds),
                },
                // Backend unreachable/unregistered: the computation is genuinely
                // undetermined — surface Unknown(BackendUnavailable), never FALSE.
                // (This path does not auto-assert, so there is no cached result to
                // honor; returning here is equivalent to the no-witness fallback.)
                Err(_) => NumericGroupVerdict {
                    relation: rel.to_string(),
                    method: "backend_unavailable",
                    verdict: QueryResult::Unknown(UnknownReason::BackendUnavailable),
                },
            });
        }
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
) -> Vec<LogicalTerm> {
    args.iter()
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
        .collect()
}

/// Forward a single predicate to the operator-configured external backend.
///
/// On `Ok(true)` the caller (the ComputeNode arm in `reasoning.rs`) auto-asserts the
/// predicate as a ground fact via `assert_typed_fact`, which downstream rules may then
/// chain on. The channel is unauthenticated — see the trust-boundary note on
/// `register_compute_dispatch`. `assert_typed_fact` invalidates the predicate result
/// cache on every insert, so an auto-asserted fact never leaves a stale verdict cached
/// within the same query.
pub(super) fn dispatch_to_backend(
    inner: &KnowledgeBaseInner,
    rel: &str,
    args: &[LogicalTerm],
) -> Result<bool, String> {
    match inner.compute_eval {
        Some(eval) => eval(rel, args),
        None => Err("Compute backend not registered".to_string()),
    }
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
    match inner.compute_batch_eval {
        Some(batch_eval) => batch_eval(requests),
        None => requests
            .iter()
            .map(|_| Err("Compute backend not registered".to_string()))
            .collect(),
    }
}

/// Build a typed StoredFact from resolved LogicalTerm arguments.
pub(super) fn build_ground_fact_from_resolved(
    rel: &str,
    resolved_args: &[LogicalTerm],
) -> Option<StoredFact> {
    for arg in resolved_args {
        if matches!(arg, LogicalTerm::Variable(_)) {
            return None;
        }
    }
    let args: Vec<GroundTerm> = resolved_args
        .iter()
        .map(|arg| match arg {
            LogicalTerm::Number(n) => GroundTerm::from_f64(*n),
            LogicalTerm::Constant(c) => GroundTerm::Constant(c.clone()),
            LogicalTerm::Description(d) => GroundTerm::Description(d.clone()),
            LogicalTerm::Unspecified => GroundTerm::Unspecified,
            LogicalTerm::Variable(v) => {
                unreachable!("Variable '{}' in compute result — should be ground", v)
            }
        })
        .collect();
    Some(StoredFact::Bare(GroundFact::new(rel, args)))
}

/// Result of batch compute: boolean results + facts to ingest into the KB.
/// The caller is responsible for ingesting the deferred facts, which allows
/// the domain member slice borrow to be released before mutating the KB.
pub(super) struct BatchComputeResult {
    pub results: Vec<bool>,
    pub deferred_facts: Vec<StoredFact>,
}

pub(super) fn batch_evaluate_compute_for_members(
    inner: &KnowledgeBaseInner,
    rel: &str,
    args: &[LogicalTerm],
    var: &str,
    members: &[GroundTerm],
    subs: &HashMap<String, GroundTerm>,
) -> Option<BatchComputeResult> {
    let mut results = vec![false; members.len()];
    let mut deferred_facts = Vec::new();
    let mut pending: Vec<(usize, Vec<LogicalTerm>)> = Vec::new();

    for (i, member) in members.iter().enumerate() {
        let mut s = subs.clone();
        s.insert(var.to_string(), member.clone());

        if let Some(r) = try_arithmetic_evaluation(rel, args, &s) {
            results[i] = r;
            if r {
                let resolved = resolve_args_for_dispatch(args, &s);
                if let Some(fact) = build_ground_fact_from_resolved(rel, &resolved) {
                    deferred_facts.push(fact);
                }
            }
        } else {
            let resolved = resolve_args_for_dispatch(args, &s);
            pending.push((i, resolved));
        }
    }

    if pending.is_empty() {
        return Some(BatchComputeResult {
            results,
            deferred_facts,
        });
    }

    let requests: Vec<ComputeRequest> = pending
        .iter()
        .map(|(_, resolved)| ComputeRequest {
            relation: rel.to_string(),
            args: resolved.clone(),
        })
        .collect();
    let batch_results = dispatch_batch_to_backend(inner, &requests);

    for (batch_idx, result) in batch_results.into_iter().enumerate() {
        let member_idx = pending[batch_idx].0;
        match result {
            Ok(r) => {
                results[member_idx] = r;
                if r {
                    if let Some(fact) = build_ground_fact_from_resolved(rel, &pending[batch_idx].1)
                    {
                        deferred_facts.push(fact);
                    }
                }
            }
            Err(_) => return None,
        }
    }
    Some(BatchComputeResult {
        results,
        deferred_facts,
    })
}
