use super::*;
use std::cell::RefCell;

// ─── Injectable compute dispatch ───

type EvalFn = fn(&str, &[LogicalTerm]) -> Result<bool, String>;
type BatchEvalFn = fn(&[ComputeRequest]) -> Vec<Result<bool, String>>;

thread_local! {
    static EVAL_FN: RefCell<Option<EvalFn>> = RefCell::new(None);
    static BATCH_EVAL_FN: RefCell<Option<BatchEvalFn>> = RefCell::new(None);
}

/// Register external compute dispatch functions. Called once by the host (lasna or gasnu).
pub fn register_compute_dispatch(eval: EvalFn, batch_eval: BatchEvalFn) {
    EVAL_FN.with(|f| *f.borrow_mut() = Some(eval));
    BATCH_EVAL_FN.with(|f| *f.borrow_mut() = Some(batch_eval));
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

pub(super) fn try_numeric_comparison(
    rel: &str,
    args: &[LogicalTerm],
    subs: &HashMap<String, GroundTerm>,
) -> Option<bool> {
    let a = extract_num_value(args.get(0)?, subs)?;
    let b = extract_num_value(args.get(1)?, subs)?;
    match rel {
        "zmadu" => Some(a > b),
        "mleca" => Some(a < b),
        "dunli" => Some(a == b),
        _ => None,
    }
}

pub(super) fn try_arithmetic_evaluation(
    rel: &str,
    args: &[LogicalTerm],
    subs: &HashMap<String, GroundTerm>,
) -> Option<bool> {
    let x1 = extract_num_value(args.get(0)?, subs)?;
    let x2 = extract_num_value(args.get(1)?, subs)?;
    let x3 = extract_num_value(args.get(2)?, subs)?;
    match rel {
        "pilji" => Some(x1 == x2 * x3),
        "sumji" => Some(x1 == x2 + x3),
        "dilcu" => {
            if x3 == 0.0 {
                return Some(false);
            }
            Some(x1 == x2 / x3)
        }
        _ => None,
    }
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
    /// "numeric" (comparison), "arithmetic" (built-in), or "backend" (dispatch).
    pub method: &'static str,
    pub holds: bool,
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

    // Route by relation name, arithmetic-first.
    if let Some(holds) = try_numeric_comparison(rel, &collected, subs) {
        return Some(NumericGroupVerdict {
            relation: rel.to_string(),
            method: "numeric",
            holds,
        });
    }
    if let Some(holds) = try_arithmetic_evaluation(rel, &collected, subs) {
        return Some(NumericGroupVerdict {
            relation: rel.to_string(),
            method: "arithmetic",
            holds,
        });
    }
    if head_is_compute {
        // External dispatch: every non-Unspecified role must resolve numeric.
        let resolved = resolve_args_for_dispatch(&collected, subs);
        let dispatchable = resolved
            .iter()
            .all(|t| matches!(t, LogicalTerm::Number(_) | LogicalTerm::Unspecified));
        if dispatchable {
            if let Ok(holds) = dispatch_to_backend(rel, &resolved) {
                return Some(NumericGroupVerdict {
                    relation: rel.to_string(),
                    method: "backend",
                    holds,
                });
            }
        }
    }
    None
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

pub(super) fn dispatch_to_backend(rel: &str, args: &[LogicalTerm]) -> Result<bool, String> {
    EVAL_FN.with(|f| match *f.borrow() {
        Some(eval) => eval(rel, args),
        None => Err("Compute backend not registered".to_string()),
    })
}

/// Batch compute request.
pub struct ComputeRequest {
    pub relation: String,
    pub args: Vec<LogicalTerm>,
}

fn dispatch_batch_to_backend(requests: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    BATCH_EVAL_FN.with(|f| match *f.borrow() {
        Some(batch_eval) => batch_eval(requests),
        None => requests
            .iter()
            .map(|_| Err("Compute backend not registered".to_string()))
            .collect(),
    })
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
    let batch_results = dispatch_batch_to_backend(&requests);

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
