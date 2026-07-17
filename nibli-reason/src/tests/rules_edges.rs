use super::*;

// ─── SE-conversion + universal rule + targeted witness tests ────

/// Build a 2-arg universal rule with different argument structures:
/// ∀x. restrictor(x, _) → consequent(fixed_entity, x, _)
/// This simulates "ro lo gerku cu se nelci la .bob." where SE swaps x1↔x2,
/// producing: ∀x. gerku(x) → nelci(bob, x)
fn make_universal_2arg(restrictor: &str, consequent: &str, fixed_entity: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    // restrictor(x, _)
    let restrict = pred(
        &mut nodes,
        restrictor,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    // consequent(fixed_entity, x, _)
    let body = pred(
        &mut nodes,
        consequent,
        vec![
            LogicalTerm::Constant(fixed_entity.to_string()),
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg = not(&mut nodes, restrict);
    let disj = or(&mut nodes, neg, body);
    let root = forall(&mut nodes, "_v0", disj);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_x2_conversion_universal_rule() {
    // Simulates the REPL demo:
    //   la .alis. gerku          → gerku(alis)
    //   ro lo gerku cu se nelci la .bob.  → ∀x. gerku(x) → nelci(bob, x)
    //   ? la .bob. nelci la .alis.        → nelci(bob, alis) = TRUE
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

    // Query: nelci(bob, alis) — should be TRUE via universal rule
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_x2_conversion_universal_multiple_entities() {
    // Two dogs: both should be liked by bob via universal rule
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("rex", "gerku"));
    assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

    // nelci(bob, alis) = TRUE
    let mut n1 = Vec::new();
    let r1 = pred(
        &mut n1,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: n1,
            roots: vec![r1]
        }
    ));

    // nelci(bob, rex) = TRUE
    let mut n2 = Vec::new();
    let r2 = pred(
        &mut n2,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("rex".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: n2,
            roots: vec![r2]
        }
    ));

    // nelci(bob, carol) = FALSE (carol is not a dog)
    let mut n3 = Vec::new();
    let r3 = pred(
        &mut n3,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("carol".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes: n3,
            roots: vec![r3]
        }
    ));
}

#[test]
fn test_targeted_witness_search_with_fixed_entity() {
    // Simulates the REPL demo:
    //   la .alis. gerku          → gerku(alis)
    //   ro lo gerku cu se nelci la .bob.  → ∀x. gerku(x) → nelci(bob, x)
    //   ?? ma se nelci la .bob.           → ∃x. nelci(bob, x) → includes alis
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

    // Query: ∃x. nelci(bob, x) — should find alis (+ presupposition Skolem)
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(results.len() >= 1);
    let found: Vec<String> = results
        .iter()
        .filter_map(|bs| match &bs[0].term {
            LogicalTerm::Constant(c) => Some(c.clone()),
            _ => None,
        })
        .collect();
    assert!(
        found.contains(&"alis".to_string()),
        "alis should be a witness"
    );
}

#[test]
fn test_targeted_witness_search_multiple_matches() {
    // Two dogs → both should appear as witnesses for "who does bob like?"
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("rex", "gerku"));
    assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

    // Query: ∃x. nelci(bob, x) — should find alis AND rex (+ presupposition Skolem)
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(results.len() >= 2);
    let found: Vec<String> = results
        .iter()
        .filter_map(|bs| match &bs[0].term {
            LogicalTerm::Constant(c) => Some(c.clone()),
            _ => None,
        })
        .collect();
    assert!(
        found.contains(&"alis".to_string()),
        "alis should be a witness"
    );
    assert!(
        found.contains(&"rex".to_string()),
        "rex should be a witness"
    );
}

#[test]
fn test_conjunction_introduction_multiple_entities() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("alis", "barda"));
    assert_buf(&kb, make_assertion("bob", "mlatu"));
    assert_buf(&kb, make_assertion("bob", "cmalu"));

    // alis predicates should conjoin with each other
    assert!(query_conjunction(&kb, "gerku", "alis", "barda", "alis"));
    // bob predicates should conjoin with each other
    assert!(query_conjunction(&kb, "mlatu", "bob", "cmalu", "bob"));
    // cross-entity conjunction also holds (both sides individually true)
    assert!(query_conjunction(&kb, "gerku", "alis", "mlatu", "bob"));
}

// ─── KB Reset Tests ──────────────────────────────────────────

#[test]
fn test_kb_reset_clears_facts() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(query(&kb, make_query("alis", "gerku")));

    // Reset the knowledge base
    kb.inner.borrow_mut().reset();

    // After reset, previously asserted fact should no longer hold
    assert!(query_false(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_kb_reset_clears_rules() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert!(query(&kb, make_query("alis", "danlu")));

    kb.inner.borrow_mut().reset();

    // After reset, re-assert the fact but not the rule
    assert_buf(&kb, make_assertion("alis", "gerku"));
    // Rule should not exist anymore
    assert!(query_false(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_kb_reset_resets_skolem_counter() {
    let kb = new_kb();
    // Assert a universal to trigger Skolem generation
    assert_buf(&kb, make_universal("gerku", "danlu"));
    let counter_before = kb.inner.borrow().skolem_counter;
    assert!(counter_before > 0);

    kb.inner.borrow_mut().reset();
    assert_eq!(kb.inner.borrow().skolem_counter, 0);
}

// ─── Empty buffer / edge case tests ──────────────────────────

#[test]
fn test_query_with_no_facts() {
    let kb = new_kb();
    assert!(query_false(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_assert_and_query_same_fact_twice() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    // Should still hold and not cause issues
    assert!(query(&kb, make_query("alis", "gerku")));
}

// ─── Disjunction query tests ─────────────────────────────────

#[test]
fn test_disjunction_left_true() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));

    let mut nodes = Vec::new();
    let left = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let right = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = or(&mut nodes, left, right);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_disjunction_right_true() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "mlatu"));

    let mut nodes = Vec::new();
    let left = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let right = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = or(&mut nodes, left, right);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_disjunction_both_false() {
    let kb = new_kb();

    let mut nodes = Vec::new();
    let left = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let right = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = or(&mut nodes, left, right);
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

// ─── Double negation tests ───────────────────────────────────

#[test]
fn test_double_negation_elimination() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // Query Not(Not(gerku(alis))) → should be TRUE
    let mut nodes = Vec::new();
    let inner = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg1 = not(&mut nodes, inner);
    let root = not(&mut nodes, neg1);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}
