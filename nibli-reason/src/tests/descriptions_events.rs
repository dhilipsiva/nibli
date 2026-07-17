use super::*;

// ─── C5: Description term opacity tests ──────────────────────

/// Helper: make an assertion with a Description term in x1.
fn make_desc_assertion(desc_name: &str, predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        predicate,
        vec![
            LogicalTerm::Description(desc_name.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Helper: make a query with a Description term in x1.
fn make_desc_query(desc_name: &str, predicate: &str) -> LogicBuffer {
    make_desc_assertion(desc_name, predicate)
}

#[test]
fn test_desc_gets_indomain() {
    // Assert a fact with Description term → Desc should be in InDomain
    let kb = new_kb();
    assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
    let inner = kb.inner.borrow();
    assert!(
        inner.known_descriptions.contains("gerku"),
        "expected 'gerku' in known_descriptions"
    );
}

#[test]
fn test_desc_conjunction_introduction() {
    // Two facts about same Desc term → conjunction should be derivable
    let kb = new_kb();
    assert_buf(&kb, make_desc_assertion("gerku", "danlu"));
    assert_buf(&kb, make_desc_assertion("gerku", "sutra"));

    // Query And(danlu(Desc "gerku"), sutra(Desc "gerku"))
    let mut nodes = Vec::new();
    let p1 = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Description("gerku".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let p2 = pred(
        &mut nodes,
        "sutra",
        vec![
            LogicalTerm::Description("gerku".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = and(&mut nodes, p1, p2);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes,
                roots: vec![root]
            }
        ),
        "conjunction of two Desc-term facts should hold via conjunction introduction"
    );
}

#[test]
fn test_desc_does_not_trigger_rule_without_restrictor() {
    // Assert sutra(Desc "gerku") (but NOT gerku(Desc "gerku"))
    // Assert rule: ro lo gerku cu danlu (∀x. gerku(x) → danlu(x))
    // Query danlu(Desc "gerku") → should FAIL (the restrictor isn't satisfied)
    let kb = new_kb();
    assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert!(
        query_false(&kb, make_desc_query("gerku", "danlu")),
        "universal rule should NOT fire without restrictor being satisfied for Desc term"
    );
}

#[test]
fn test_desc_triggers_rule_when_restrictor_satisfied() {
    // Assert gerku(Desc "gerku") AND sutra(Desc "gerku")
    // Assert rule: ro lo gerku cu danlu
    // Query danlu(Desc "gerku") → should SUCCEED
    let kb = new_kb();
    assert_buf(&kb, make_desc_assertion("gerku", "gerku"));
    assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert!(
        query(&kb, make_desc_query("gerku", "danlu")),
        "universal rule should fire when restrictor IS satisfied for Desc term"
    );
}

#[test]
fn test_desc_exists_witness() {
    // Assert sutra(Desc "gerku") → ∃x. sutra(x) should find Desc "gerku" as witness
    let kb = new_kb();
    assert_buf(&kb, make_desc_assertion("gerku", "sutra"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "sutra",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes,
                roots: vec![root]
            }
        ),
        "existential query should find Desc term as witness"
    );
}

#[test]
fn test_backward_chain_derives_facts() {
    // Assert a fact and a rule, then verify backward-chaining derives conclusions
    let kb = new_kb();
    // Assert: gerku(alis)
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // Assert: ∀x. ¬gerku(x) ∨ danlu(x) (i.e., gerku → danlu)
    assert_buf(&kb, make_universal("gerku", "danlu"));

    // Query: danlu(alis) — should be derived via backward-chaining
    assert!(
        query(&kb, make_query("alis", "danlu")),
        "backward-chaining should derive danlu(alis) from gerku(alis) and universal rule"
    );
}

// ─── Event-decomposed universal rule tests ──────────────────────

#[test]
fn test_event_decomposed_rule_fires() {
    let kb = new_kb();
    assert_buf(&kb, make_event_assertion("alis", "gerku"));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert!(
        query(&kb, make_event_query("alis", "danlu")),
        "event-decomposed rule should derive danlu(alis) from gerku(alis)"
    );
}

/// Build a NEGATED event-decomposed universal rule (`ro lo X poi na P cu Q`):
///   ForAll(_v0, Or(
///     Not(Not(Exists(_ev0, And(P(_ev0), P_x1(_ev0, _v0))))),  // poi na P restrictor
///     Exists(_ev1, And(Q(_ev1), Q_x1(_ev1, _v0)))             // consequent
///   ))
/// `decompose_implication` strips the OUTER `Not`, leaving `Not(Exists(...))` as the
/// CONDITION — the negated existential group this fix compiles into a NAF check.
fn make_negated_event_universal(restrictor: &str, consequent: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let p_type = pred(
        &mut nodes,
        restrictor,
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let p_role = pred(
        &mut nodes,
        &format!("{}_x1", restrictor),
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Variable("_v0".to_string()),
        ],
    );
    let p_and = and(&mut nodes, p_type, p_role);
    let p_exists = exists(&mut nodes, "_ev0", p_and);
    let neg_restrictor = not(&mut nodes, p_exists); // Not(Exists(...)) — "x does NOT P"

    let q_type = pred(
        &mut nodes,
        consequent,
        vec![LogicalTerm::Variable("_ev1".to_string())],
    );
    let q_role = pred(
        &mut nodes,
        &format!("{}_x1", consequent),
        vec![
            LogicalTerm::Variable("_ev1".to_string()),
            LogicalTerm::Variable("_v0".to_string()),
        ],
    );
    let q_and = and(&mut nodes, q_type, q_role);
    let q_exists = exists(&mut nodes, "_ev1", q_and);

    let neg = not(&mut nodes, neg_restrictor); // Not(Not(Exists(...)))
    let disj = or(&mut nodes, neg, q_exists);
    let root = forall(&mut nodes, "_v0", disj);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_negated_event_decomposed_rule_compiles_and_fires() {
    let kb = new_kb();
    // "every X that does NOT zanru (consent) is bilga (obligated)".
    assert_buf(&kb, make_negated_event_universal("zanru", "bilga"));
    // alis is a known entity (a person) but has NOT consented.
    assert_buf(&kb, make_event_assertion("alis", "prenu"));
    assert!(
        query(&kb, make_event_query("alis", "bilga")),
        "no consent witness → ¬∃ holds (NAF) → the rule fires: bilga(alis) TRUE"
    );
    // Now alis consents → ¬∃ is false → the rule must not fire.
    assert_buf(&kb, make_event_assertion("alis", "zanru"));
    assert!(
        matches!(
            query_result(&kb, make_event_query("alis", "bilga")),
            QueryResult::False
        ),
        "consent asserted → ¬∃ false → rule does not fire: bilga(alis) FALSE"
    );
}

#[test]
fn test_negated_event_group_rule_shape() {
    let kb = new_kb();
    assert_buf(&kb, make_negated_event_universal("zanru", "bilga"));
    let inner = kb.inner.borrow();
    let rule = inner
        .universal_rules
        .values()
        .flatten()
        .find(|r| r.typed_conclusions.iter().any(|c| c.relation() == "bilga"))
        .expect("the bilga rule should be registered");
    assert_eq!(
        rule.negated_exists_groups.len(),
        1,
        "one negated-exists group"
    );
    let rels: Vec<&str> = rule.negated_exists_groups[0]
        .conditions
        .iter()
        .map(|c| c.relation())
        .collect();
    assert_eq!(rels, vec!["zanru", "zanru_x1"], "group inner conjuncts");
    assert!(
        rule.typed_conditions.is_empty(),
        "the negated group is NOT a flat typed condition"
    );
}

#[test]
fn test_negated_event_group_self_reference_rejected() {
    let kb = new_kb();
    // "every X that does NOT danlu is danlu" — the negated group anchors the rule's
    // own conclusion → negative self-loop → unstratifiable → rejected.
    let r = kb.assert_fact_inner(
        make_negated_event_universal("danlu", "danlu"),
        String::new(),
    );
    assert!(
        r.is_err(),
        "a negated group anchoring its own conclusion must be rejected as unstratifiable"
    );
}

/// Build `Exists(ev, And(P(ev), P_x1(ev, entity)))` for a GROUND entity constant.
fn event_operand(nodes: &mut Vec<LogicNode>, ev: &str, predicate: &str, entity: &str) -> u32 {
    let p_type = pred(
        nodes,
        predicate,
        vec![LogicalTerm::Variable(ev.to_string())],
    );
    let p_role = pred(
        nodes,
        &format!("{}_x1", predicate),
        vec![
            LogicalTerm::Variable(ev.to_string()),
            LogicalTerm::Constant(entity.to_string()),
        ],
    );
    let p_and = and(nodes, p_type, p_role);
    exists(nodes, ev, p_and)
}

/// Ground event-decomposed material conditional: Or(Not(A), B), operands over a constant.
fn make_event_material_conditional(
    entity: &str,
    antecedent: &str,
    consequent: &str,
) -> LogicBuffer {
    let mut nodes = Vec::new();
    let a = event_operand(&mut nodes, "_ev0", antecedent, entity);
    let b = event_operand(&mut nodes, "_ev1", consequent, entity);
    let neg_a = not(&mut nodes, a);
    let root = or(&mut nodes, neg_a, b);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Ground event-decomposed biconditional: And(Or(Not(A),B), Or(Not(B),A)).
fn make_event_biconditional(entity: &str, a: &str, b: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let a1 = event_operand(&mut nodes, "_ev0", a, entity);
    let b1 = event_operand(&mut nodes, "_ev1", b, entity);
    let neg_a1 = not(&mut nodes, a1);
    let impl1 = or(&mut nodes, neg_a1, b1);
    let b2 = event_operand(&mut nodes, "_ev2", b, entity);
    let a2 = event_operand(&mut nodes, "_ev3", a, entity);
    let neg_b2 = not(&mut nodes, b2);
    let impl2 = or(&mut nodes, neg_b2, a2);
    let root = and(&mut nodes, impl1, impl2);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_event_decomposed_ground_material_conditional() {
    // Or(Not(∃e. gerku(e) ∧ gerku_x1(e, adam)), ∃e2. danlu(e2) ∧ danlu_x1(e2, adam))
    // + gerku(adam) ⇒ danlu(adam) (modus ponens over event-decomposed operands).
    let kb = new_kb();
    assert_buf(
        &kb,
        make_event_material_conditional("adam", "gerku", "danlu"),
    );
    assert_buf(&kb, make_event_assertion("adam", "gerku"));
    assert!(
        query(&kb, make_event_query("adam", "danlu")),
        "ground material conditional should derive danlu(adam) from gerku(adam)"
    );
}

#[test]
fn test_event_decomposed_ground_material_conditional_no_antecedent() {
    // Negative control: without the antecedent fact the conclusion is not derivable.
    let kb = new_kb();
    assert_buf(
        &kb,
        make_event_material_conditional("adam", "gerku", "danlu"),
    );
    assert!(
        query_false(&kb, make_event_query("adam", "danlu")),
        "danlu(adam) must NOT hold without gerku(adam)"
    );
}

#[test]
fn test_event_decomposed_ground_biconditional_both_directions() {
    // A ↔ B reasons both ways over event-decomposed operands (no CycleCut).
    let kb = new_kb();
    assert_buf(&kb, make_event_biconditional("adam", "gerku", "danlu"));
    assert_buf(&kb, make_event_assertion("adam", "gerku"));
    assert!(
        query(&kb, make_event_query("adam", "danlu")),
        "biconditional: danlu(adam) should derive from gerku(adam) (forward)"
    );

    let kb2 = new_kb();
    assert_buf(&kb2, make_event_biconditional("adam", "gerku", "danlu"));
    assert_buf(&kb2, make_event_assertion("adam", "danlu"));
    assert!(
        query(&kb2, make_event_query("adam", "gerku")),
        "biconditional: gerku(adam) should derive from danlu(adam) (reverse)"
    );
}

#[test]
fn test_event_decomposed_rule_selective() {
    let kb = new_kb();
    assert_buf(&kb, make_event_assertion("alis", "gerku"));
    assert_buf(&kb, make_event_assertion("bob", "mlatu"));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert!(
        query(&kb, make_event_query("alis", "danlu")),
        "danlu(alis) should hold (alis is a gerku)"
    );
    assert!(
        query_false(&kb, make_event_query("bob", "danlu")),
        "danlu(bob) should NOT hold (bob is a mlatu, not gerku)"
    );
}

#[test]
fn test_event_decomposed_entity_after_rule() {
    let kb = new_kb();
    // Add rule first, then fact — should still fire after saturation
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert_buf(&kb, make_event_assertion("alis", "gerku"));
    assert!(
        query(&kb, make_event_query("alis", "danlu")),
        "rule should fire even when added before fact"
    );
}

#[test]
fn test_event_decomposed_temporal_rule() {
    let kb = new_kb();
    // Assert: Past(Exists(_ev0, And(gerku(_ev0), gerku_x1(_ev0, alis))))
    let mut a_nodes = Vec::new();
    let p_type = pred(
        &mut a_nodes,
        "gerku",
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let p_role = pred(
        &mut a_nodes,
        "gerku_x1",
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Constant("alis".to_string()),
        ],
    );
    let p_and = and(&mut a_nodes, p_type, p_role);
    let p_exists = exists(&mut a_nodes, "_ev0", p_and);
    let a_root = past(&mut a_nodes, p_exists);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![a_root],
        },
    );

    // Add timeless rule: ro lo gerku ku danlu (event-decomposed)
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    // Query: Past(Exists(_ev0, And(danlu(_ev0), danlu_x1(_ev0, alis))))
    let mut q_nodes = Vec::new();
    let q_type = pred(
        &mut q_nodes,
        "danlu",
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let q_role = pred(
        &mut q_nodes,
        "danlu_x1",
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Constant("alis".to_string()),
        ],
    );
    let q_and = and(&mut q_nodes, q_type, q_role);
    let q_exists = exists(&mut q_nodes, "_ev0", q_and);
    let q_root = past(&mut q_nodes, q_exists);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes: q_nodes,
                roots: vec![q_root],
            }
        ),
        "temporal lifting should derive Past(danlu(alis)) from Past(gerku(alis)) and timeless rule"
    );
}

#[test]
fn test_event_decomposed_multi_hop() {
    let kb = new_kb();
    assert_buf(&kb, make_event_assertion("alis", "gerku"));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "xanlu"));
    assert!(
        query(&kb, make_event_query("alis", "xanlu")),
        "multi-hop: gerku→danlu→xanlu should derive xanlu(alis)"
    );
}

#[test]
fn test_event_decomposed_proof_trace() {
    let kb = new_kb();
    assert_buf(&kb, make_event_assertion("alis", "gerku"));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    // Query with proof trace
    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_event_query("alis", "danlu"))
        .unwrap();
    assert!(
        holds.is_true(),
        "entailment should hold for derived event-decomposed fact"
    );

    // Check that the proof trace contains a Derived step
    let has_derived = trace
        .steps
        .iter()
        .any(|step| matches!(&step.rule, ProofRule::Derived { .. }));
    assert!(
        has_derived,
        "proof trace should contain at least one Derived step for rule-derived fact"
    );
}

#[test]
fn test_event_decomposed_existential_import() {
    let kb = new_kb();
    // Only add the rule (no ground facts) — existential-import presupposition should
    // create Skolem constants that make the restrictor domain non-empty
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    // The existential-import presupposition should have created event + entity Skolems
    // such that gerku(sk_ev) and gerku_x1(sk_ev, sk_entity) hold.
    // Query: exists something that is a gerku (via existential-import presupposition)
    let mut q_nodes = Vec::new();
    let q_type = pred(
        &mut q_nodes,
        "gerku",
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let q_role = pred(
        &mut q_nodes,
        "gerku_x1",
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Variable("_v0".to_string()),
        ],
    );
    let q_and = and(&mut q_nodes, q_type, q_role);
    let q_ev = exists(&mut q_nodes, "_ev0", q_and);
    let q_root = exists(&mut q_nodes, "_v0", q_ev);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes: q_nodes,
                roots: vec![q_root],
            }
        ),
        "xorlo presupposition should make ∃x.∃e. gerku(e)∧gerku_x1(e,x) hold"
    );
}
