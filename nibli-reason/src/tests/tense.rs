use super::*;

// ─── Tense wrapper tests ─────────────────────────────────────

fn future(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::FutureNode(inner));
    id
}

#[test]
fn test_past_tense_wrapper_assert_query() {
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = past(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    // Query same tense wrapper → TRUE
    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = past(&mut q_nodes, q_inner);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_tense_not_transparent() {
    // Assert Past(klama(alis)), query klama(alis) without tense → FALSE
    // (tense is NOT transparent — tensed assertion ≠ timeless query)
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = past(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    assert!(query_false(&kb, make_query("alis", "klama")));
}

#[test]
fn test_tense_discrimination_past_vs_future() {
    // Assert Past(klama(alis)), query Future(klama(alis)) → FALSE
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = past(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = future(&mut q_nodes, q_inner);
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_tense_discrimination_present_vs_past() {
    // Assert Present(klama(alis)), query Past(klama(alis)) → FALSE
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = present(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = past(&mut q_nodes, q_inner);
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_untensed_assert_tensed_query() {
    // Assert klama(alis) (bare/timeless), query Past(klama(alis)) → FALSE
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "klama"));

    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = past(&mut q_nodes, q_inner);
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_temporal_rule_lifting() {
    // Assert: ∀x. gerku(x) → danlu(x) (timeless rule)
    // Assert: Past(gerku(alis))
    // Query: Past(danlu(alis)) → TRUE (temporal lifting)
    let kb = new_kb();

    // Compile the universal rule: ForAll(x, Or(Not(gerku(x)), danlu(x)))
    let mut r_nodes = Vec::new();
    let dog = pred(
        &mut r_nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let danlu = pred(
        &mut r_nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_dog = not(&mut r_nodes, dog);
    let impl_body = or(&mut r_nodes, neg_dog, danlu);
    let forall = {
        let id = r_nodes.len() as u32;
        r_nodes.push(LogicNode::ForAllNode(("_v0".into(), impl_body)));
        id
    };
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: r_nodes,
            roots: vec![forall],
        },
    );

    // Assert Past(gerku(alis))
    let mut a_nodes = Vec::new();
    let dog_alis = pred(
        &mut a_nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let past_dog = past(&mut a_nodes, dog_alis);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![past_dog],
        },
    );

    // Query Past(danlu(alis)) → TRUE (lifted rule fires on Past premises)
    let mut q_nodes = Vec::new();
    let danlu_alis = pred(
        &mut q_nodes,
        "danlu",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let past_danlu = past(&mut q_nodes, danlu_alis);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![past_danlu]
        }
    ));
}

#[test]
fn test_temporal_rule_no_cross_tense() {
    // Assert: ∀x. gerku(x) → danlu(x) (timeless rule)
    // Assert: Past(gerku(alis))
    // Query: Future(danlu(alis)) → FALSE (no cross-tense derivation)
    let kb = new_kb();

    // Universal rule
    let mut r_nodes = Vec::new();
    let dog = pred(
        &mut r_nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let danlu = pred(
        &mut r_nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_dog = not(&mut r_nodes, dog);
    let impl_body = or(&mut r_nodes, neg_dog, danlu);
    let forall = {
        let id = r_nodes.len() as u32;
        r_nodes.push(LogicNode::ForAllNode(("_v0".into(), impl_body)));
        id
    };
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: r_nodes,
            roots: vec![forall],
        },
    );

    // Assert Past(gerku(alis))
    let mut a_nodes = Vec::new();
    let dog_alis = pred(
        &mut a_nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let past_dog = past(&mut a_nodes, dog_alis);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![past_dog],
        },
    );

    // Query Future(danlu(alis)) → FALSE (Past ≠ Future)
    let mut q_nodes = Vec::new();
    let danlu_alis = pred(
        &mut q_nodes,
        "danlu",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let future_danlu = future(&mut q_nodes, danlu_alis);
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![future_danlu]
        }
    ));
}

// ─── Tensed rule antecedents (compile + fire) ────────────────

/// Assert the tensed-antecedent rule `∀x. Past(citka(x)) → xagji(x)`
/// ("everything that ATE is hungry"). Pre-fix this panics (the rule is
/// rejected at compile time because the tensed condition cannot be templated).
fn assert_past_eats_then_hungry(kb: &KnowledgeBase) {
    let mut r = Vec::new();
    let eats = pred(
        &mut r,
        "citka",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let past_citka = past(&mut r, eats);
    let neg = not(&mut r, past_citka);
    let hungry = pred(
        &mut r,
        "xagji",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let body = or(&mut r, neg, hungry);
    let forall = {
        let id = r.len() as u32;
        r.push(LogicNode::ForAllNode(("_v0".into(), body)));
        id
    };
    assert_buf(
        kb,
        LogicBuffer {
            nodes: r,
            roots: vec![forall],
        },
    );
}

/// Query bare `xagji(rex)`.
fn query_hungry_rex(kb: &KnowledgeBase) -> bool {
    let mut q = Vec::new();
    let hungry = pred(
        &mut q,
        "xagji",
        vec![
            LogicalTerm::Constant("rex".into()),
            LogicalTerm::Unspecified,
        ],
    );
    query(
        kb,
        LogicBuffer {
            nodes: q,
            roots: vec![hungry],
        },
    )
}

/// Assert a `citka(rex)` fact under the given tense wrapper (`None` = bare).
fn assert_eats_rex(kb: &KnowledgeBase, tense: Option<&str>) {
    let mut a = Vec::new();
    let citka_rex = pred(
        &mut a,
        "citka",
        vec![
            LogicalTerm::Constant("rex".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = match tense {
        Some("Past") => past(&mut a, citka_rex),
        Some("Future") => future(&mut a, citka_rex),
        Some("Present") => present(&mut a, citka_rex),
        _ => citka_rex,
    };
    assert_buf(
        kb,
        LogicBuffer {
            nodes: a,
            roots: vec![root],
        },
    );
}

#[test]
fn test_tensed_antecedent_rule_compiles_and_fires() {
    // ∀x. Past(citka(x)) → xagji(x); given Past(citka(rex)), derive bare xagji(rex).
    let kb = new_kb();
    assert_past_eats_then_hungry(&kb);
    assert_eats_rex(&kb, Some("Past"));
    assert!(
        query_hungry_rex(&kb),
        "tensed-antecedent rule must fire on a matching Past premise"
    );
}

#[test]
fn test_tensed_antecedent_no_premise_does_not_fire() {
    // The rule compiles, but with no premise the tensed condition fails.
    let kb = new_kb();
    assert_past_eats_then_hungry(&kb);
    assert!(
        !query_hungry_rex(&kb),
        "tensed-antecedent rule must NOT fire with no supporting premise"
    );
}

#[test]
fn test_tensed_antecedent_wrong_tense_does_not_fire() {
    // A Future premise must not satisfy a Past antecedent (strict tense).
    let kb = new_kb();
    assert_past_eats_then_hungry(&kb);
    assert_eats_rex(&kb, Some("Future"));
    assert!(
        !query_hungry_rex(&kb),
        "Past antecedent must NOT fire on a Future premise"
    );
}

#[test]
fn test_tensed_antecedent_bare_premise_does_not_fire() {
    // A bare premise must not satisfy a Past antecedent.
    let kb = new_kb();
    assert_past_eats_then_hungry(&kb);
    assert_eats_rex(&kb, None);
    assert!(
        !query_hungry_rex(&kb),
        "Past antecedent must NOT fire on a bare premise"
    );
}

// ─── Tensed rule CONCLUSIONS ─────────────────────────────────

/// Assert ∀x. citka(x) → Past(xagji(x)) — a BARE antecedent with a tensed (Past)
/// CONCLUSION. The rule derives the PAST fact xagji, not a bare/future one.
fn assert_eats_then_past_hungry(kb: &KnowledgeBase) {
    let mut r = Vec::new();
    let eats = pred(
        &mut r,
        "citka",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg = not(&mut r, eats);
    let hungry = pred(
        &mut r,
        "xagji",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let past_xagji = past(&mut r, hungry);
    let body = or(&mut r, neg, past_xagji);
    let forall = {
        let id = r.len() as u32;
        r.push(LogicNode::ForAllNode(("_v0".into(), body)));
        id
    };
    assert_buf(
        kb,
        LogicBuffer {
            nodes: r,
            roots: vec![forall],
        },
    );
}

/// Query `xagji(rex)` under the given tense wrapper (`None` = bare).
fn query_hungry_rex_tense(kb: &KnowledgeBase, tense: Option<&str>) -> bool {
    let mut q = Vec::new();
    let hungry = pred(
        &mut q,
        "xagji",
        vec![
            LogicalTerm::Constant("rex".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = match tense {
        Some("Past") => past(&mut q, hungry),
        Some("Future") => future(&mut q, hungry),
        Some("Present") => present(&mut q, hungry),
        _ => hungry,
    };
    query(
        kb,
        LogicBuffer {
            nodes: q,
            roots: vec![root],
        },
    )
}

#[test]
fn test_tensed_conclusion_rule_fires_on_matching_tense() {
    // ∀x. citka(x) → Past(xagji(x)); a bare citka(rex) premise derives Past(xagji(rex)),
    // and ONLY the Past fact (not bare, not Future) — tense-exact via unify_facts.
    let kb = new_kb();
    assert_eats_then_past_hungry(&kb);
    assert_eats_rex(&kb, None); // bare antecedent premise
    assert!(
        query_hungry_rex_tense(&kb, Some("Past")),
        "tensed conclusion derives the Past fact"
    );
    assert!(
        !query_hungry_rex_tense(&kb, None),
        "tensed conclusion must NOT derive a bare fact"
    );
    assert!(
        !query_hungry_rex_tense(&kb, Some("Future")),
        "tensed conclusion must NOT derive a Future fact"
    );
}

#[test]
fn test_tensed_conclusion_no_premise_does_not_fire() {
    let kb = new_kb();
    assert_eats_then_past_hungry(&kb);
    assert!(
        !query_hungry_rex_tense(&kb, Some("Past")),
        "tensed-conclusion rule must NOT fire without the antecedent premise"
    );
}

// ─── Whole-rule tense/deontic is fail-closed ─────────────────

/// `Wrap(ForAll("_v0", Or(Not(restrictor), consequent)))` — a tense/deontic
/// wrapping the WHOLE universal (`pu ro lo gerku cu danlu` → Past(ForAll(...))).
fn make_wrapped_universal(
    restrictor: &str,
    consequent: &str,
    wrap: fn(&mut Vec<LogicNode>, u32) -> u32,
) -> LogicBuffer {
    let mut nodes = Vec::new();
    let restrict = pred(
        &mut nodes,
        restrictor,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let body = pred(
        &mut nodes,
        consequent,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg = not(&mut nodes, restrict);
    let disj = or(&mut nodes, neg, body);
    let fa = forall(&mut nodes, "_v0", disj);
    let root = wrap(&mut nodes, fa);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// `ForAll("_v0", Wrap(Or(Not(restrictor), consequent)))` — a tense/deontic on
/// the rule's matrix, INSIDE a top-level universal (a prenex with a tensed body:
/// `ro da zo'u pu ...`). The wrapper sits on the rule spine.
fn make_universal_tensed_body(
    restrictor: &str,
    consequent: &str,
    wrap: fn(&mut Vec<LogicNode>, u32) -> u32,
) -> LogicBuffer {
    let mut nodes = Vec::new();
    let restrict = pred(
        &mut nodes,
        restrictor,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let body = pred(
        &mut nodes,
        consequent,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg = not(&mut nodes, restrict);
    let disj = or(&mut nodes, neg, body);
    let wrapped = wrap(&mut nodes, disj);
    let root = forall(&mut nodes, "_v0", wrapped);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Distinctive substring of the whole-rule-tense/deontic rejection — pins the
/// clear message (vs the misleading "bare disjunction" zero-ingest message).
const WHOLE_RULE_ERR: &str = "whole universal/conditional";

#[test]
fn test_whole_rule_past_tense_universal_rejected() {
    // `pu ro lo gerku cu danlu` → Past(ForAll(...)). Rejected with the clear
    // whole-rule message — routed to the rule path (pre-fix: the ground path's
    // misleading "bare disjunction" zero-ingest rejection).
    let kb = new_kb();
    let err = kb
        .assert_fact_inner(
            make_wrapped_universal("gerku", "danlu", past),
            String::new(),
        )
        .unwrap_err();
    assert!(
        err.contains(WHOLE_RULE_ERR),
        "expected the whole-rule rejection, got: {err}"
    );
}

#[test]
fn test_whole_rule_obligatory_universal_rejected() {
    // `ei ro lo prenu cu xamgu` → Obligatory(ForAll(...)) — same class (an
    // actuality derived from an obligation), same clear message.
    let kb = new_kb();
    let err = kb
        .assert_fact_inner(
            make_wrapped_universal("prenu", "xamgu", obligatory),
            String::new(),
        )
        .unwrap_err();
    assert!(
        err.contains(WHOLE_RULE_ERR),
        "expected the whole-rule rejection, got: {err}"
    );
}

#[test]
fn test_tensed_body_universal_rejected() {
    // `ro da zo'u pu ...` → ForAll(Past(Or(...))) — a tense on the rule spine,
    // INSIDE the universal. Rejected (pre-fix: silently stripped → timeless).
    let kb = new_kb();
    let err = kb
        .assert_fact_inner(
            make_universal_tensed_body("gerku", "danlu", past),
            String::new(),
        )
        .unwrap_err();
    assert!(
        err.contains(WHOLE_RULE_ERR),
        "expected the whole-rule rejection, got: {err}"
    );
}

#[test]
fn test_tensed_body_universal_does_not_derive_timeless() {
    // Soundness guard (the genuine RED→GREEN): the rejected ForAll(Past(gerku→
    // danlu)) registers NO timeless rule, so bare `gerku(rex)` does NOT derive
    // bare `danlu(rex)`. Pre-fix the stripped rule fires on the untensed fact
    // (wrongly TRUE).
    let kb = new_kb();
    let rejected = kb.assert_fact_inner(
        make_universal_tensed_body("gerku", "danlu", past),
        String::new(),
    );
    assert!(
        rejected.is_err(),
        "the tensed-body universal must be rejected"
    );
    assert_buf(&kb, make_assertion("rex", "gerku"));
    assert!(
        query_false(&kb, make_query("rex", "danlu")),
        "a rejected tensed-body universal must not leave a timeless rule that fires on bare facts"
    );
}
