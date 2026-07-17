use super::*;

// ─── Numeric Comparison Tests ────────────────────────────────

#[test]
fn test_greater_numeric_true() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("greater", 2.0, 1.0)));
}

#[test]
fn test_greater_numeric_false() {
    let kb = new_kb();
    assert!(query_false(&kb, make_numeric_query("greater", 1.0, 2.0)));
}

#[test]
fn test_greater_numeric_equal_false() {
    let kb = new_kb();
    assert!(query_false(&kb, make_numeric_query("greater", 2.0, 2.0)));
}

#[test]
fn test_less_numeric_true() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("less", 1.0, 2.0)));
}

#[test]
fn test_less_numeric_false() {
    let kb = new_kb();
    assert!(query_false(&kb, make_numeric_query("less", 2.0, 1.0)));
}

#[test]
fn test_num_equal_numeric_true() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("num_equal", 5.0, 5.0)));
}

#[test]
fn test_num_equal_numeric_false() {
    let kb = new_kb();
    assert!(query_false(&kb, make_numeric_query("num_equal", 5.0, 3.0)));
}

#[test]
fn test_greater_negated() {
    let kb = new_kb();
    // NOT (1 > 2) should be TRUE
    let mut nodes = Vec::new();
    let cmp = make_numeric_pred(&mut nodes, "greater", 1.0, 2.0);
    let root = not(&mut nodes, cmp);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_greater_non_numeric_fallback() {
    let kb = new_kb();
    // Non-numeric zmadu: assert then query via standard KB path
    let mut a_nodes = Vec::new();
    let a_root = pred(
        &mut a_nodes,
        "greater",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Unspecified,
            LogicalTerm::Unspecified,
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![a_root],
        },
    );

    let mut q_nodes = Vec::new();
    let q_root = pred(
        &mut q_nodes,
        "greater",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Unspecified,
            LogicalTerm::Unspecified,
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_greater_large_numbers() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_numeric_query("greater", 1_000_000.0, 999_999.0)
    ));
}

#[test]
fn test_greater_negative_numbers() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("greater", -1.0, -2.0)));
    assert!(query_false(&kb, make_numeric_query("greater", -2.0, -1.0)));
}

// ─── ComputeNode Tests ───────────────────────────────────────

#[test]
fn test_compute_pilji_true() {
    let kb = new_kb();
    // 6 = 2 * 3
    assert!(query(&kb, make_compute_query("product", 6.0, 2.0, 3.0)));
}

#[test]
fn test_compute_pilji_false() {
    let kb = new_kb();
    // 7 != 2 * 3
    assert!(query_false(
        &kb,
        make_compute_query("product", 7.0, 2.0, 3.0)
    ));
}

#[test]
fn test_compute_sumji_true() {
    let kb = new_kb();
    // 5 = 2 + 3
    assert!(query(&kb, make_compute_query("sum", 5.0, 2.0, 3.0)));
}

#[test]
fn test_compute_sumji_false() {
    let kb = new_kb();
    // 4 != 2 + 3
    assert!(query_false(&kb, make_compute_query("sum", 4.0, 2.0, 3.0)));
}

#[test]
fn test_compute_dilcu_true() {
    let kb = new_kb();
    // 3 = 6 / 2
    assert!(query(&kb, make_compute_query("quotient", 3.0, 6.0, 2.0)));
}

#[test]
fn test_compute_dilcu_division_by_zero() {
    let kb = new_kb();
    // x / 0 is always false
    assert!(query_false(
        &kb,
        make_compute_query("quotient", 0.0, 5.0, 0.0)
    ));
}

#[test]
fn test_compute_sumji_float_tolerance() {
    let kb = new_kb();
    // 0.1 + 0.2 = 0.30000000000000004 in IEEE-754; tolerant equality answers
    // TRUE (the user means 0.3). Exact `==` would wrongly say FALSE.
    assert!(query(&kb, make_compute_query("sum", 0.3, 0.1, 0.2)));
    // A genuinely-wrong claim stays FALSE.
    assert!(query_false(&kb, make_compute_query("sum", 0.4, 0.1, 0.2)));
}

// ─── Decomposed numeric groups (surface-Lojban shape) ─────────────
//
// Surface numeric proposition event-decompose to ∃ev. head(ev) ∧ rel_x1(ev, a) ∧
// rel_x2(ev, b) ∧ ... — a LEFT-nested And where the head carries only the
// event variable and the operands live in sibling role predicates. These
// tests build that exact shape (mirroring nibli-semantics's event_decompose output)
// and pin that the numeric evaluators reach the operands.

/// Decomposed compute group: ∃_ev0. (((Compute(rel,[ev]) ∧ rel_x1(ev,x1))
/// ∧ rel_x2(ev,x2)) ∧ rel_x3(ev,x3)) — the surface shape for pilji/sumji/dilcu.
fn make_decomposed_compute_query(rel: &str, x1: f64, x2: f64, x3: f64) -> LogicBuffer {
    let mut nodes = Vec::new();
    let ev = || LogicalTerm::Variable("_ev0".to_string());
    let head = compute(&mut nodes, rel, vec![ev()]);
    let mut acc = head;
    for (i, v) in [x1, x2, x3].iter().enumerate() {
        let role = pred(
            &mut nodes,
            &format!("{rel}_x{}", i + 1),
            vec![ev(), LogicalTerm::Number(*v)],
        );
        acc = and(&mut nodes, acc, role);
    }
    let root = exists(&mut nodes, "_ev0", acc);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Decomposed comparison group: ∃_ev0. head Pred(rel,[ev]) ∧ rel_x1(ev,a) ∧
/// rel_x2(ev,b) ∧ Zoe-padded trailing roles (zmadu/mleca arity 4, dunli 3).
fn make_decomposed_comparison_query(rel: &str, a: f64, b: f64) -> LogicBuffer {
    let mut nodes = Vec::new();
    let ev = || LogicalTerm::Variable("_ev0".to_string());
    let head = pred(&mut nodes, rel, vec![ev()]);
    let arity = if rel == "num_equal" { 3 } else { 4 };
    let mut acc = head;
    for i in 1..=arity {
        let arg = match i {
            1 => LogicalTerm::Number(a),
            2 => LogicalTerm::Number(b),
            _ => LogicalTerm::Unspecified,
        };
        let role = pred(&mut nodes, &format!("{rel}_x{i}"), vec![ev(), arg]);
        acc = and(&mut nodes, acc, role);
    }
    let root = exists(&mut nodes, "_ev0", acc);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_decomposed_pilji_true() {
    let kb = new_kb();
    // 10 = 2 * 5 through the decomposed surface shape
    assert!(query(
        &kb,
        make_decomposed_compute_query("product", 10.0, 2.0, 5.0)
    ));
}

/// The UNKNOWN(non-finite) contract, pinned on BOTH numeric paths. Since the
/// `li` parse-boundary overflow guard landed, no overflowing literal can reach
/// these from the surface — but flat/raw-FOL buffers can still carry non-finite
/// Numbers, and a comparison over ±inf must NEVER be a confident TRUE/FALSE
/// (pre-guard, flat `dunli(inf, inf)` returned a confident TRUE).
#[test]
fn non_finite_comparison_is_unknown_on_both_paths() {
    let kb = new_kb();
    let inf = f64::INFINITY;

    // Flat path (try_numeric_comparison): bare Predicate node.
    let flat = |rel: &str, a: f64, b: f64| {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            rel,
            vec![LogicalTerm::Number(a), LogicalTerm::Number(b)],
        );
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    };
    for (rel, a, b) in [
        ("num_equal", inf, inf),
        ("num_equal", inf, 1.0),
        ("greater", inf, 1.0),
        ("less", 1.0, f64::NEG_INFINITY),
    ] {
        assert_eq!(
            query_result(&kb, flat(rel, a, b)),
            QueryResult::Unknown(UnknownReason::NonFinite),
            "flat {rel}({a}, {b}) must be UNKNOWN(non-finite), never definitive"
        );
    }
    // Finite controls: the guard must not widen onto meaningful comparisons.
    assert!(query(&kb, flat("num_equal", 2.0, 2.0)));
    assert!(matches!(
        query_result(&kb, flat("greater", 1.0, 2.0)),
        QueryResult::False
    ));

    // Event-decomposed path (the numeric-group guard): same contract.
    assert_eq!(
        query_result(&kb, make_decomposed_comparison_query("num_equal", inf, inf)),
        QueryResult::Unknown(UnknownReason::NonFinite),
        "decomposed dunli(inf, inf) must be UNKNOWN(non-finite)"
    );
    assert_eq!(
        query_result(&kb, make_decomposed_comparison_query("greater", inf, 1.0)),
        QueryResult::Unknown(UnknownReason::NonFinite),
        "decomposed zmadu(inf, 1) must be UNKNOWN(non-finite)"
    );
}

#[test]
fn test_decomposed_sumji_float_tolerance() {
    let kb = new_kb();
    // The surface (event-decomposed) path also uses tolerant equality:
    // 0.3 = 0.1 + 0.2 is TRUE despite IEEE-754 rounding.
    assert!(query(
        &kb,
        make_decomposed_compute_query("sum", 0.3, 0.1, 0.2)
    ));
}

#[test]
fn test_decomposed_pilji_false() {
    let kb = new_kb();
    assert!(query_false(
        &kb,
        make_decomposed_compute_query("product", 11.0, 2.0, 5.0)
    ));
}

#[test]
fn test_decomposed_sumji_true_false() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_decomposed_compute_query("sum", 5.0, 2.0, 3.0)
    ));
    assert!(query_false(
        &kb,
        make_decomposed_compute_query("sum", 6.0, 2.0, 3.0)
    ));
}

#[test]
fn test_decomposed_dilcu_true_and_division_by_zero() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_decomposed_compute_query("quotient", 3.0, 6.0, 2.0)
    ));
    // Division by zero is a definitive FALSE, not an error or fall-through.
    assert!(query_false(
        &kb,
        make_decomposed_compute_query("quotient", 3.0, 6.0, 0.0)
    ));
}

#[test]
fn test_decomposed_greater_true_false() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_decomposed_comparison_query("greater", 5.0, 3.0)
    ));
    assert!(query_false(
        &kb,
        make_decomposed_comparison_query("greater", 3.0, 5.0)
    ));
}

#[test]
fn test_decomposed_less_true_false() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_decomposed_comparison_query("less", 2.0, 3.0)
    ));
    assert!(query_false(
        &kb,
        make_decomposed_comparison_query("less", 3.0, 2.0)
    ));
}

#[test]
fn test_decomposed_num_equal_true_false() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_decomposed_comparison_query("num_equal", 3.0, 3.0)
    ));
    assert!(query_false(
        &kb,
        make_decomposed_comparison_query("num_equal", 3.0, 2.0)
    ));
}

#[test]
fn test_decomposed_negated() {
    // Not(∃ev. group) — the Not arm recurses into the Exists arm, so the
    // group verdict flips with no special handling.
    let kb = new_kb();
    let mut buf = make_decomposed_comparison_query("greater", 3.0, 5.0);
    let inner_root = buf.roots[0];
    let neg = {
        let id = buf.nodes.len() as u32;
        buf.nodes.push(LogicNode::NotNode(inner_root));
        id
    };
    buf.roots = vec![neg];
    assert!(query(&kb, buf), "NOT(3 > 5) must be TRUE");
}

#[test]
fn test_decomposed_extra_conjunct_falls_through() {
    // A group with an unrelated conjunct must NOT shortcut: the strict
    // same-relation rule bails, normal evaluation runs, and the unprovable
    // extra conjunct makes the query FALSE even though the arithmetic is true.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let ev = || LogicalTerm::Variable("_ev0".to_string());
    let head = compute(&mut nodes, "product", vec![ev()]);
    let x1 = pred(
        &mut nodes,
        "pilji_x1",
        vec![ev(), LogicalTerm::Number(10.0)],
    );
    let x2 = pred(&mut nodes, "pilji_x2", vec![ev(), LogicalTerm::Number(2.0)]);
    let x3 = pred(&mut nodes, "pilji_x3", vec![ev(), LogicalTerm::Number(5.0)]);
    let extra = pred(&mut nodes, "broda", vec![ev()]);
    let a1 = and(&mut nodes, head, x1);
    let a2 = and(&mut nodes, a1, x2);
    let a3 = and(&mut nodes, a2, x3);
    let body = and(&mut nodes, a3, extra);
    let root = exists(&mut nodes, "_ev0", body);
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };
    assert!(
        query_false(&kb, buf),
        "an unrelated conjunct must disable the numeric-group shortcut"
    );
}

#[test]
fn test_decomposed_non_numeric_falls_through_to_store() {
    // Non-numeric operands can't compute; the group must fall through to
    // normal evaluation, where the asserted decomposed facts satisfy it.
    let kb = new_kb();
    let make = || {
        let mut nodes = Vec::new();
        let ev = || LogicalTerm::Variable("_ev0".to_string());
        let head = pred(&mut nodes, "greater", vec![ev()]);
        let x1 = pred(
            &mut nodes,
            "zmadu_x1",
            vec![ev(), LogicalTerm::Constant("alis".to_string())],
        );
        let x2 = pred(
            &mut nodes,
            "zmadu_x2",
            vec![ev(), LogicalTerm::Constant("bob".to_string())],
        );
        let a1 = and(&mut nodes, head, x1);
        let body = and(&mut nodes, a1, x2);
        let root = exists(&mut nodes, "_ev0", body);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    };
    assert_buf(&kb, make());
    assert!(
        query(&kb, make()),
        "asserted non-numeric zmadu group must stay queryable via the store"
    );
}

#[test]
fn test_decomposed_asserted_true_group_still_true() {
    // Asserting an arithmetically-true group then querying it: the computed
    // verdict agrees with the store, so shadowing is invisible for true facts.
    let kb = new_kb();
    assert_buf(
        &kb,
        make_decomposed_compute_query("product", 10.0, 2.0, 5.0),
    );
    assert!(query(
        &kb,
        make_decomposed_compute_query("product", 10.0, 2.0, 5.0)
    ));
}

#[test]
fn test_assert_flat_numeric_comparison_rejected() {
    // The flat 2-arg form `zmadu(5, 3)` over number literals is computed ground
    // truth, not an assertable fact — reject it at assert time (the surface path
    // decomposes, so this guards the flat detection arm). A non-numeric flat
    // comparison still asserts (covered by test_greater_non_numeric_fallback).
    let kb = new_kb();
    assert!(
        kb.assert_fact_inner(make_numeric_query("greater", 5.0, 3.0), String::new())
            .is_err(),
        "asserting a flat numeric comparison must be rejected"
    );
}

#[test]
fn test_decomposed_traced_compute_check() {
    // The traced evaluator must agree with the untraced verdict and record
    // a ComputeCheck step for the group.
    let kb = new_kb();
    let (result, trace) = query_with_proof(
        &kb,
        make_decomposed_compute_query("product", 10.0, 2.0, 5.0),
    );
    assert!(result, "traced 10 = 2 × 5 must be TRUE");
    assert!(
        trace
            .steps
            .iter()
            .any(|s| matches!(&s.rule, ProofRule::ComputeCheck { .. }) && s.holds),
        "trace must contain a holding ComputeCheck step"
    );

    let (result_f, trace_f) = kb
        .query_entailment_with_proof_inner(make_decomposed_comparison_query("greater", 3.0, 5.0))
        .unwrap();
    assert!(result_f.is_false(), "traced 3 > 5 must be FALSE");
    assert!(
        trace_f
            .steps
            .iter()
            .any(|s| matches!(&s.rule, ProofRule::ComputeCheck { .. }) && !s.holds),
        "trace must contain a non-holding ComputeCheck step"
    );
}

#[test]
fn test_compute_negated() {
    let kb = new_kb();
    // NOT(7 = 2 * 3) → TRUE (because 7 != 6)
    let mut nodes = Vec::new();
    let inner = compute(
        &mut nodes,
        "product",
        vec![
            LogicalTerm::Number(7.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    let root = not(&mut nodes, inner);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_compute_node_kb_fallback() {
    // ComputeNode with non-arithmetic predicate falls back to KB lookup
    let kb = new_kb();

    // Assert: klama(alis, zarci) as a regular fact
    let mut a_nodes = Vec::new();
    let a_root = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Constant("zarci".to_string()),
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![a_root],
        },
    );

    // Query as ComputeNode — unknown to arithmetic, should fall through to KB lookup
    let mut q_nodes = Vec::new();
    let q_root = compute(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Constant("zarci".to_string()),
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}
