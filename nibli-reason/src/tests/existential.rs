use super::*;

// ─── Cooperative cancellation (server watchdog) ──────────────

#[test]
fn cancelled_query_returns_err() {
    use std::sync::atomic::{AtomicBool, Ordering};
    // A pre-set cancel flag makes any query abort via the Err channel
    // rather than running to completion. The native server's watchdog
    // sets this flag when the request timeout elapses.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));

    let flag = std::sync::Arc::new(AtomicBool::new(true));
    kb.set_cancel_flag(flag.clone());

    let result = kb.query_entailment_inner(make_query("alis", "danlu"));
    assert!(
        result.is_err(),
        "cancelled query must return Err, got {result:?}"
    );
    assert!(
        result.unwrap_err().to_lowercase().contains("cancel"),
        "cancellation error should mention 'cancel'"
    );

    // Clearing the flag restores normal evaluation.
    flag.store(false, Ordering::Relaxed);
    kb.clear_cancel_flag();
    assert!(query(&kb, make_query("alis", "danlu")));
}

// ─── Existential introduction (existential-import presupposition) ─────────

#[test]
fn test_existential_import_presupposition_basic() {
    // ro lo gerku cu danlu → presupposition: ∃x. gerku(x)
    // Query ∃x. gerku(x) should find the presupposition Skolem
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));

    // Query: ∃x. gerku(x)
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_existential_import_presupposition_consequent() {
    // ro lo gerku cu danlu → presupposition creates sk entity → rule fires
    // Query ∃x. danlu(x) should find the derived fact
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_existential_import_presupposition_conjunction() {
    // THE BUG FIX: ro lo gerku cu danlu, then ? lo gerku cu danlu
    // (∃x. gerku(x) ∧ danlu(x)) should be TRUE
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));

    let mut nodes = Vec::new();
    let p1 = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let p2 = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let conj = and(&mut nodes, p1, p2);
    let root = exists(&mut nodes, "x", conj);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_existential_import_presupposition_with_real_entity() {
    // Real entity + presupposition Skolem both satisfy BOOLEAN queries, but
    // the phantom is NOT an enumerable "thing": witness enumeration excludes
    // existential-import presupposition witnesses (GUARANTEES §Aggregation — pre-change
    // this test pinned the opposite: the phantom appeared in [Find] results).
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // Both alis and the presupposition Skolem are in the KB
    assert!(query(&kb, make_query("alis", "danlu")));

    // Witness search finds ONLY the real entity.
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "danlu",
        vec![
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
    assert_eq!(
        results.len(),
        1,
        "only the real entity is enumerable, not the presupposition phantom: {results:?}"
    );
    assert!(
        results[0]
            .iter()
            .any(|b| matches!(&b.term, LogicalTerm::Constant(c) if c == "alis")),
        "the surviving witness is alis: {results:?}"
    );
}

#[test]
fn test_prenex_universal_asserts_no_presupposition_witness() {
    // A PRENEX universal (var `da`, no `lo`/`le` determiner) is a pure logical ∀ with
    // NO existential import, so it must NOT assert a presupposition witness —
    // unlike a DESCRIPTION universal (`_v`-named, from `ro lo`/`ro le`). This
    // guards both the suppression (the DDI alert prenex would otherwise assert a
    // phantom `pilno(adam, sk)`, polluting the regimen count) and the preserved
    // `ro lo` contract.
    let kb = new_kb();
    // ForAll("da", Or(Not(broda(da)), brodb(da))) — a prenex-named universal var.
    let mut nodes = Vec::new();
    let restrict = pred(
        &mut nodes,
        "broda",
        vec![
            LogicalTerm::Variable("da".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let body = pred(
        &mut nodes,
        "brodb",
        vec![
            LogicalTerm::Variable("da".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg = not(&mut nodes, restrict);
    let disj = or(&mut nodes, neg, body);
    let root = forall(&mut nodes, "da", disj);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    // ∃x. broda(x) must be FALSE — no presupposition witness was asserted.
    let mut q = Vec::new();
    let qb = pred(
        &mut q,
        "broda",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let qroot = exists(&mut q, "x", qb);
    assert!(
        query_false(
            &kb,
            LogicBuffer {
                nodes: q,
                roots: vec![qroot]
            }
        ),
        "a prenex universal must NOT assert a presupposition witness"
    );

    // Contrast: a DESCRIPTION universal (`_v`-named) DOES assert the witness.
    let kb2 = new_kb();
    assert_buf(&kb2, make_universal("gerku", "danlu"));
    let mut q2 = Vec::new();
    let qb2 = pred(
        &mut q2,
        "gerku",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let qroot2 = exists(&mut q2, "x", qb2);
    assert!(
        query(
            &kb2,
            LogicBuffer {
                nodes: q2,
                roots: vec![qroot2]
            }
        ),
        "a description universal must still assert its presupposition witness"
    );
}

#[test]
fn test_bare_universal_asserts_no_presupposition_witness() {
    // A BARE universal `ForAll("da", brodb(da))` ("everything is brodb") — a
    // restrictor-less prenex body, no `Or(Not(R), ..)`. `decompose_implication`
    // returns None, so it takes the BARE branch of `compile_forall_to_rule`,
    // which (correctly) asserts no existential-import witness: a prenex `ro da` is a plain ∀
    // with no existential import. The existing prenex test exercises the
    // IMPLICATION-branch prenex (it has a restrictor condition); this pins the
    // bare branch itself.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "brodb",
        vec![
            LogicalTerm::Variable("da".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = forall(&mut nodes, "da", body);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    // ∃x. brodb(x) must be FALSE — no presupposition witness, empty domain.
    let mut q = Vec::new();
    let qb = pred(
        &mut q,
        "brodb",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let qroot = exists(&mut q, "x", qb);
    assert!(
        query_false(
            &kb,
            LogicBuffer {
                nodes: q,
                roots: vec![qroot]
            }
        ),
        "a bare (restrictor-less) universal must NOT assert a presupposition witness"
    );
}

#[test]
fn test_existential_import_presupposition_transitive() {
    // ro lo gerku cu danlu, ro lo danlu cu xanlu
    // Each universal creates its own presupposition Skolem
    // Query ∃x. xanlu(x) should find witnesses via chain
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "xanlu"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "xanlu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_existential_import_presupposition_no_false_positives() {
    // ro lo gerku cu danlu should NOT make mlatu(x) exist
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_native_rule_transitive_chain() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "xanlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(query(&kb, make_query("alis", "xanlu")));
}

#[test]
fn test_native_rule_multiple_entities() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert!(query(&kb, make_query("alis", "danlu")));
    assert!(query(&kb, make_query("bob", "danlu")));
}

#[test]
fn test_native_rule_negated_universal() {
    // A universal with a NEGATED conclusion — ∀x. gerku(x) → ¬danlu(x), encoded as
    // ∀x. ¬gerku(x) ∨ ¬danlu(x). The conclusion atom ¬danlu(x) is not a flat
    // predicate, so it cannot be compiled into a backward-chaining template.
    //
    // This used to be silently dropped to an empty-conclusion `__fallback__` rule
    // (dead, never matched), and the test "passed for the wrong reason": danlu(alis)
    // was simply never derivable. The compiler now FAILS CLOSED — and since the
    // hygiene pass, register_rule itself also rejects empty-conclusion rules
    // (the __fallback__ bucket is gone) — the assertion is rejected rather than
    // registering a misleading dead rule.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));

    let mut nodes = Vec::new();
    let restrict = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let body_pred = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_body = not(&mut nodes, body_pred);
    let neg_restrict = not(&mut nodes, restrict);
    let disj = or(&mut nodes, neg_restrict, neg_body);
    let root = forall(&mut nodes, "_v0", disj);
    let result = kb.assert_fact_inner(
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
        String::new(),
    );
    assert!(
        result.is_err(),
        "negated-conclusion universal must be rejected (fail-closed), got {result:?}"
    );

    // danlu(alis) must not be derivable either way.
    assert!(query_false(&kb, make_query("alis", "danlu")));
}

/// Regression: a negated antecedent condition must be evaluated via
/// negation-as-failure, not as a positive requirement. Untraced path.
#[test]
fn test_naf_negated_antecedent_untraced() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_negated_antecedent_rule());

    // mlatu(alis) is unprovable → ¬mlatu holds (NAF) → the rule fires.
    assert!(
        query(&kb, make_query("alis", "danlu")),
        "danlu(alis) should hold: gerku true and mlatu unprovable (NAF)"
    );

    // Asserting mlatu(alis) makes ¬mlatu false → the rule must no longer fire.
    assert_buf(&kb, make_assertion("alis", "mlatu"));
    assert!(
        matches!(
            query_result(&kb, make_query("alis", "danlu")),
            QueryResult::False
        ),
        "danlu(alis) should be FALSE once mlatu(alis) is asserted"
    );
}

/// Regression: the traced (proof) path must agree with the untraced verdict
/// and record the negated condition as a negation-as-failure dependency.
#[test]
fn test_naf_negated_antecedent_traced() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_negated_antecedent_rule());

    let (result, trace) = kb
        .query_entailment_with_proof_inner(make_query("alis", "danlu"))
        .unwrap();
    assert!(
        result.is_true(),
        "traced verdict should be TRUE before mlatu"
    );
    assert!(
        trace.has_naf_dependency(),
        "proof should record a negation-as-failure dependency for ¬mlatu"
    );

    assert_buf(&kb, make_assertion("alis", "mlatu"));
    let (result2, _trace2) = kb
        .query_entailment_with_proof_inner(make_query("alis", "danlu"))
        .unwrap();
    assert!(
        result2.is_false(),
        "traced verdict should be FALSE after mlatu(alis) is asserted"
    );
}

/// White-box guard for the And-flattening prerequisite: the negated-antecedent
/// rule must register with two conditions [gerku, mlatu], mlatu (index 1) flagged
/// negated, and a positive danlu conclusion.
#[test]
fn test_naf_negated_antecedent_rule_shape() {
    let kb = new_kb();
    assert_buf(&kb, make_negated_antecedent_rule());

    let inner = kb.inner.borrow();
    let rule = inner
        .universal_rules
        .values()
        .flatten()
        .find(|r| r.typed_conclusions.iter().any(|c| c.relation() == "danlu"))
        .expect("a rule concluding danlu should be registered");

    let cond_rels: Vec<&str> = rule.typed_conditions.iter().map(|c| c.relation()).collect();
    assert_eq!(
        cond_rels,
        vec!["gerku", "mlatu"],
        "antecedent And should flatten into two conditions"
    );
    assert_eq!(
        rule.negated_condition_indices,
        vec![1],
        "mlatu (index 1) should be the negated condition"
    );
}

/// Conformance bridge to `proofs/RuleFiring.lean` (`firing_sound` / `firing_no_fabrication`):
/// firing the rule ∀x. (gerku(x) ∧ ¬mlatu(x)) → danlu(x) concludes danlu(E) EXACTLY when its
/// conditions are discharged for that E — positive gerku(E) present AND negated mlatu(E) absent —
/// and the derived head is the σ-instantiated conclusion (danlu(alis), not danlu(bob)). Exercises
/// modus ponens (both conditions genuinely required), no fabrication, and correct head
/// instantiation (composing the unifier's `unify_sound`).
#[test]
fn rule_firing_conformance() {
    // (1) Both conditions discharged for alis → the rule fires (danlu(alis) TRUE), and the head is
    //     instantiated to alis: danlu(bob) is NOT derived (σ binds x = alis, not universally).
    let kb = new_kb();
    assert_buf(&kb, make_negated_antecedent_rule());
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(
        query(&kb, make_query("alis", "danlu")),
        "gerku(alis) present and mlatu(alis) absent → the rule fires → danlu(alis)"
    );
    assert!(
        query_false(&kb, make_query("bob", "danlu")),
        "head instantiated to the matched entity: danlu(bob) must NOT be derived"
    );

    // The traced firing records the σ-instantiated conclusion (a Derived step naming danlu(alis))
    // and marks the ¬mlatu condition as a negation-as-failure dependency.
    let (ok, trace) = query_with_proof(&kb, make_query("alis", "danlu"));
    assert!(ok);
    assert!(
        trace.has_naf_dependency(),
        "the ¬mlatu condition must be a negation-as-failure dependency"
    );
    assert!(
        trace.steps.iter().any(|s| matches!(
            &s.rule,
            ProofRule::Derived { fact, .. } if fact.contains("danlu") && fact.contains("alis")
        )),
        "a Derived step must record the instantiated head danlu(alis)"
    );

    // (2) NO FABRICATION — the negated condition's witness is present (mlatu(alis)) → the rule must
    //     NOT fire (¬mlatu undischarged).
    let kb2 = new_kb();
    assert_buf(&kb2, make_negated_antecedent_rule());
    assert_buf(&kb2, make_assertion("alis", "gerku"));
    assert_buf(&kb2, make_assertion("alis", "mlatu"));
    assert!(
        query_false(&kb2, make_query("alis", "danlu")),
        "mlatu(alis) present → the negated condition fails → no firing (no fabrication)"
    );

    // (3) NO FABRICATION — the positive condition is missing (no gerku(alis)) → the rule must NOT
    //     fire (the positive condition is undischarged).
    let kb3 = new_kb();
    assert_buf(&kb3, make_negated_antecedent_rule());
    assert!(
        query_false(&kb3, make_query("alis", "danlu")),
        "gerku(alis) missing → the positive condition is undischarged → no firing (no fabrication)"
    );
}

#[test]
fn test_native_rule_duplicate_rule_no_panic() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_query_result_false_for_missing_fact() {
    let kb = new_kb();
    let result = query_result(&kb, make_query("alis", "gerku"));
    assert!(matches!(result, QueryResult::False));
}

#[test]
fn test_query_result_unknown_for_cycle_cut() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "gerku"));

    let result = query_result(&kb, make_query("alis", "gerku"));
    assert!(matches!(
        result,
        QueryResult::Unknown(UnknownReason::CycleCut)
    ));

    let (result, _) = kb
        .query_entailment_with_proof_inner(make_query("alis", "gerku"))
        .unwrap();
    assert!(matches!(
        result,
        QueryResult::Unknown(UnknownReason::CycleCut)
    ));
}

#[test]
fn test_query_result_resource_exceeded_for_depth_limit() {
    let kb = new_kb();
    kb.inner.borrow_mut().max_chain_depth = 1;

    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "xanlu"));

    let result = query_result(&kb, make_query("alis", "xanlu"));
    assert!(matches!(
        result,
        QueryResult::ResourceExceeded(ResourceKind::Depth)
    ));

    let (result, _) = kb
        .query_entailment_with_proof_inner(make_query("alis", "xanlu"))
        .unwrap();
    assert!(matches!(
        result,
        QueryResult::ResourceExceeded(ResourceKind::Depth)
    ));
}
