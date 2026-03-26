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
) -> Option<i64> {
    match term {
        LogicalTerm::Number(n) => Some(*n as i64),
        LogicalTerm::Variable(v) => {
            let gt = subs.get(v.as_str())?;
            gt.as_f64().map(|f| f as i64)
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
            if x3 == 0 {
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
            LogicalTerm::Variable(_) => unreachable!(),
        })
        .collect();
    Some(StoredFact::Bare(GroundFact::new(rel, args)))
}

pub(super) fn batch_evaluate_compute_for_members(
    rel: &str,
    args: &[LogicalTerm],
    var: &str,
    members: &[GroundTerm],
    subs: &HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
) -> Option<Vec<bool>> {
    let mut results = vec![false; members.len()];
    let mut pending: Vec<(usize, Vec<LogicalTerm>)> = Vec::new();

    for (i, member) in members.iter().enumerate() {
        let mut s = subs.clone();
        s.insert(var.to_string(), member.clone());

        if let Some(r) = try_arithmetic_evaluation(rel, args, &s) {
            results[i] = r;
            if r {
                let resolved = resolve_args_for_dispatch(args, &s);
                if let Some(fact) = build_ground_fact_from_resolved(rel, &resolved) {
                    assert_typed_fact(fact, inner);
                }
            }
        } else {
            let resolved = resolve_args_for_dispatch(args, &s);
            pending.push((i, resolved));
        }
    }

    if pending.is_empty() {
        return Some(results);
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
                    if let Some(fact) = build_ground_fact_from_resolved(rel, &pending[batch_idx].1) {
                        assert_typed_fact(fact, inner);
                    }
                }
            }
            Err(_) => return None,
        }
    }
    Some(results)
}
