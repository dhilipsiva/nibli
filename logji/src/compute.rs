use super::*;

pub(super) fn extract_num_value(
    term: &LogicalTerm,
    subs: &HashMap<String, String>,
) -> Option<i64> {
    match term {
        LogicalTerm::Number(n) => Some(*n as i64),
        LogicalTerm::Variable(v) => {
            let s = subs.get(v.as_str())?;
            s.strip_prefix("(Num ")?
                .strip_suffix(')')?
                .parse::<i64>()
                .ok()
        }
        _ => None,
    }
}

pub(super) fn try_numeric_comparison(
    rel: &str,
    args: &[LogicalTerm],
    subs: &HashMap<String, String>,
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
    subs: &HashMap<String, String>,
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

pub(super) fn parse_repr_to_term(fact_repr: &str) -> LogicalTerm {
    if let Some(name) = fact_repr
        .strip_prefix("(Const \"")
        .and_then(|s| s.strip_suffix("\")"))
    {
        LogicalTerm::Constant(name.to_string())
    } else if let Some(n) = fact_repr.strip_prefix("(Num ").and_then(|s| s.strip_suffix(')')) {
        LogicalTerm::Number(n.parse::<f64>().unwrap_or(0.0))
    } else if let Some(name) = fact_repr
        .strip_prefix("(Desc \"")
        .and_then(|s| s.strip_suffix("\")"))
    {
        LogicalTerm::Description(name.to_string())
    } else if fact_repr == "(Zoe)" {
        LogicalTerm::Unspecified
    } else if let Some(name) = fact_repr
        .strip_prefix("(Var \"")
        .and_then(|s| s.strip_suffix("\")"))
    {
        LogicalTerm::Variable(name.to_string())
    } else {
        LogicalTerm::Variable(fact_repr.to_string())
    }
}

pub(super) fn resolve_args_for_dispatch(
    args: &[LogicalTerm],
    subs: &HashMap<String, String>,
) -> Vec<LogicalTerm> {
    args.iter()
        .map(|a| match a {
            LogicalTerm::Variable(v) => {
                if let Some(s) = subs.get(v.as_str()) {
                    parse_repr_to_term(s)
                } else {
                    a.clone()
                }
            }
            _ => a.clone(),
        })
        .collect()
}

#[cfg(target_arch = "wasm32")]
pub(super) fn dispatch_to_backend(rel: &str, args: &[LogicalTerm]) -> Result<bool, String> {
    crate::bindings::lojban::nibli::compute_backend::evaluate(rel, args)
        .map_err(|e| format!("{}", e))
}

#[cfg(not(target_arch = "wasm32"))]
pub(super) fn dispatch_to_backend(_rel: &str, _args: &[LogicalTerm]) -> Result<bool, String> {
    Err("Compute backend unavailable in native mode".to_string())
}

struct ComputeRequest {
    relation: String,
    args: Vec<LogicalTerm>,
}

#[cfg(target_arch = "wasm32")]
fn dispatch_batch_to_backend(requests: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    use crate::bindings::lojban::nibli::compute_backend as cb;
    let wit_requests: Vec<cb::ComputeRequest> = requests
        .iter()
        .map(|r| cb::ComputeRequest {
            relation: r.relation.clone(),
            args: r.args.clone(),
        })
        .collect();
    let results = cb::evaluate_batch(&wit_requests);
    results
        .into_iter()
        .map(|r| match r {
            cb::ComputeResult::Ok(b) => Ok(b),
            cb::ComputeResult::Err(msg) => Err(msg),
        })
        .collect()
}

#[cfg(not(target_arch = "wasm32"))]
fn dispatch_batch_to_backend(requests: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    requests
        .iter()
        .map(|_| Err("Compute backend unavailable in native mode".to_string()))
        .collect()
}

#[cfg(target_arch = "wasm32")]
pub(super) fn dispatch_check_membership(
    rel: &str,
    args: &[LogicalTerm],
    place_index: u32,
) -> Result<Vec<LogicalTerm>, String> {
    crate::bindings::lojban::nibli::compute_backend::check_membership(rel, args, place_index)
        .map_err(|e| format!("{}", e))
}

#[cfg(not(target_arch = "wasm32"))]
pub(super) fn dispatch_check_membership(
    _rel: &str,
    _args: &[LogicalTerm],
    _place_index: u32,
) -> Result<Vec<LogicalTerm>, String> {
    Ok(vec![])
}

pub(super) fn build_ground_predicate_repr(
    rel: &str,
    resolved_args: &[LogicalTerm],
) -> Option<String> {
    for arg in resolved_args {
        if matches!(arg, LogicalTerm::Variable(_)) {
            return None;
        }
    }
    let mut args_str = String::from("(Nil)");
    for arg in resolved_args.iter().rev() {
        let term_str = match arg {
            LogicalTerm::Number(n) => format!("(Num {})", *n as i64),
            LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
            LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
            LogicalTerm::Unspecified => "(Zoe)".to_string(),
            LogicalTerm::Variable(_) => unreachable!(),
        };
        args_str = format!("(Cons {} {})", term_str, args_str);
    }
    Some(format!("(Pred \"{}\" {})", rel, args_str))
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
    members: &[(String, LogicalTerm)],
    subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
) -> Option<Vec<bool>> {
    let mut results = vec![false; members.len()];
    let mut pending: Vec<(usize, Vec<LogicalTerm>)> = Vec::new();

    for (i, (member_repr, _)) in members.iter().enumerate() {
        let mut s = subs.clone();
        s.insert(var.to_string(), member_repr.clone());

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
