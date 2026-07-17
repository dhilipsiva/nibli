use super::*;

// ─── Proof trace tests ───────────────────────────────────────

#[test]
fn test_proof_trace_simple_predicate() {
    // Assert klama(mi), query it → single asserted step, result true
    let kb = new_kb();
    assert_buf(&kb, make_assertion("mi", "klama"));
    let (result, trace) = query_with_proof(&kb, make_query("mi", "klama"));

    assert!(result);
    assert!(!trace.steps.is_empty());
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Asserted { .. }));
}

#[test]
fn test_proof_trace_false_predicate() {
    // Query non-existent fact → PredicateNotFound with result false
    let kb = new_kb();
    let (result, trace) = kb
        .query_entailment_with_proof_inner(make_query("mi", "klama"))
        .unwrap();

    assert!(result.is_false());
    let root_step = &trace.steps[trace.root as usize];
    assert!(!root_step.holds);
    assert!(
        matches!(&root_step.rule, ProofRule::PredicateNotFound { .. }),
        "expected PredicateNotFound, got {:?}",
        root_step.rule
    );
}

#[test]
fn test_proof_trace_conjunction() {
    // Assert klama(mi), prami(mi), query conjunction → conjunction root with two children
    let kb = new_kb();
    assert_buf(&kb, make_assertion("mi", "klama"));
    assert_buf(&kb, make_assertion("mi", "prami"));

    let mut nodes = Vec::new();
    let p1 = pred(
        &mut nodes,
        "klama",
        vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
    );
    let p2 = pred(
        &mut nodes,
        "prami",
        vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
    );
    let root = and(&mut nodes, p1, p2);
    let (result, trace) = query_with_proof(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Conjunction));
    assert_eq!(root_step.children.len(), 2);
    // Both children should be asserted with result true
    for &child in &root_step.children {
        let child_step = &trace.steps[child as usize];
        assert!(child_step.holds);
        assert!(matches!(&child_step.rule, ProofRule::Asserted { .. }));
    }
}

#[test]
fn test_proof_trace_negation() {
    // Query negation of non-existent fact → negation root with result true
    let kb = new_kb();
    let mut nodes = Vec::new();
    let inner = pred(
        &mut nodes,
        "klama",
        vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
    );
    let root = not(&mut nodes, inner);
    let (result, trace) = query_with_proof(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Negation));
    assert_eq!(root_step.children.len(), 1);
    // Inner should be predicate-check with result false
    let inner_step = &trace.steps[root_step.children[0] as usize];
    assert!(!inner_step.holds);
}

#[test]
fn test_proof_trace_exists_witness() {
    // Assert klama(alis), query ∃x.klama(x) → exists-witness with x = alis
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "klama"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "klama",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = exists(&mut nodes, "x", body);
    let (result, trace) = query_with_proof(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::ExistsWitness { .. }));
    if let ProofRule::ExistsWitness { var, term } = &root_step.rule {
        assert_eq!(var, "x");
        assert!(matches!(term, LogicalTerm::Constant(c) if c == "alis"));
    }
}

#[test]
fn test_proof_trace_exists_failed() {
    // Query ∃x.klama(x) with no facts → exists-failed
    let kb = new_kb();

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "klama",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = exists(&mut nodes, "x", body);
    let (result, trace) = kb
        .query_entailment_with_proof_inner(LogicBuffer {
            nodes,
            roots: vec![root],
        })
        .unwrap();

    assert!(result.is_false());
    let root_step = &trace.steps[trace.root as usize];
    assert!(!root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::ExistsFailed));
}

#[test]
fn test_proof_trace_forall() {
    // Assert gerku(alis), gerku(bob), query ∀x.gerku(x)→gerku(x) [trivially true]
    // Actually: assert gerku for both entities, query ∀x.(gerku(x)→gerku(x))
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));

    // Query: ∀x. gerku(x) — should be ForAll verified for both entities
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = forall(&mut nodes, "x", body);
    let (result, trace) = query_with_proof(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::ForallVerified { .. }));
    if let ProofRule::ForallVerified { entities } = &root_step.rule {
        assert_eq!(entities.len(), 2);
    }
    // Each child should be a predicate-check with result true
    for &child in &root_step.children {
        let child_step = &trace.steps[child as usize];
        assert!(child_step.holds);
    }
}

/// The `cwa_false` flag (dual of `naf_dependent`) marks an absence-driven FALSE that
/// rests on the closed-world assumption ("not derivable"). The complementary direction
/// — a numeric/arithmetic FALSE (`5 = 3`) must NOT be flagged — is pinned end-to-end in
/// `nibli-engine`'s `closed_world_false_carries_cwa_note_but_numeric_false_does_not`,
/// because the flat helper here skips the event/compute decomposition that records the
/// deciding `ComputeCheck(numeric)` step.
#[test]
fn cwa_false_flag_set_for_absence_false() {
    let kb = new_kb();
    let (verdict, trace) = kb
        .query_entailment_with_proof_inner(make_query("bob", "danlu"))
        .unwrap();
    assert!(
        verdict.is_false(),
        "a missing fact must be FALSE: got {verdict:?}"
    );
    assert!(
        trace.cwa_false,
        "an absence-driven FALSE must set cwa_false (the closed-world caveat)"
    );
}

/// Pins that the engine's `False`-for-a-missing-fact and a `True` `ForallVerified`
/// are BOTH relative to the Closed-World / Closed-Domain Assumption — not absolute
/// truths. Under an open-world / open-domain reading the same queries would be
/// Unknown. This regression documents that boundary: a future change that (say)
/// makes a missing fact `Unknown`, or verifies a `∀` against an open domain, must
/// be a deliberate, test-visible decision rather than a silent drift.
#[test]
fn cwa_cda_relativity_of_false_and_forall_verified() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    assert_buf(&kb, make_assertion("alis", "danlu"));
    assert_buf(&kb, make_assertion("bob", "danlu"));

    // (1) CWA: a ground fact that was never asserted is *definitively FALSE*, NOT
    // Unknown. The engine treats the KB as complete (closed world), so the absence
    // of `danlu(carl)` is read as ¬danlu(carl). Under an open-world assumption the
    // honest verdict would instead be Unknown(IncompleteKnowledge).
    assert_eq!(
        query_result(&kb, make_query("carl", "danlu")),
        QueryResult::False,
        "a missing fact must be FALSE under the closed-world assumption, not Unknown"
    );

    // (2) CDA: `∀x. gerku(x) → danlu(x)` is verified TRUE by ENUMERATING the closed
    // domain of known individuals {alis, bob} and checking each — a `ForallVerified`.
    // This True is relative to that closed domain; it is not a claim about all
    // possible gerku, only the ones the KB knows about.
    let (verdict, trace) = kb
        .query_entailment_with_proof_inner(make_universal("gerku", "danlu"))
        .unwrap();
    assert_eq!(
        verdict,
        QueryResult::True,
        "a ∀ satisfied across the whole closed domain must be TRUE"
    );
    let root_rule = &trace.steps[trace.root as usize].rule;
    assert!(
        matches!(root_rule, ProofRule::ForallVerified { entities } if entities.len() == 2),
        "the True verdict must be a ForallVerified over the 2 known individuals, got {root_rule:?}"
    );

    // (3) CDA-relativity made concrete: introduce a NEW domain member that breaks
    // the rule. The SAME ∀ query now flips to FALSE (ForallCounterexample), proving
    // the earlier True was an artifact of the closed domain — not an absolute truth.
    assert_buf(&kb, make_assertion("carl", "gerku")); // carl is dog but NOT danlu
    let (verdict2, trace2) = kb
        .query_entailment_with_proof_inner(make_universal("gerku", "danlu"))
        .unwrap();
    assert_eq!(
        verdict2,
        QueryResult::False,
        "adding a counterexample to the closed domain must flip the ∀ to FALSE"
    );
    assert!(
        matches!(
            &trace2.steps[trace2.root as usize].rule,
            ProofRule::ForallCounterexample { .. }
        ),
        "the flipped verdict must be a ForallCounterexample over the new member"
    );
}

// ─── Derivation Provenance Tests ──────────────────────────────────

#[test]
fn test_proof_trace_asserted_fact() {
    // Directly asserted fact should show Asserted, not PredicateCheck
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let (result, trace) = query_with_proof(&kb, make_query("alis", "gerku"));
    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Asserted { .. }));
    if let ProofRule::Asserted { fact } = &root_step.rule {
        assert!(fact.contains("gerku"));
        assert!(fact.contains("alis"));
    }
}

#[test]
fn test_proof_trace_single_hop_derived() {
    // gerku(alis) + rule gerku→danlu → danlu(alis) should show Derived with Asserted child
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    let (result, trace) = query_with_proof(&kb, make_query("alis", "danlu"));
    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Derived { .. }));
    if let ProofRule::Derived { label, fact } = &root_step.rule {
        assert!(fact.contains("danlu"));
        assert!(label.contains("gerku"));
        assert!(label.contains("danlu"));
    }
    assert_eq!(root_step.children.len(), 1);
    // The child should be Asserted (gerku(alis))
    let child_step = &trace.steps[root_step.children[0] as usize];
    assert!(child_step.holds);
    assert!(matches!(&child_step.rule, ProofRule::Asserted { .. }));
}

#[test]
fn test_proof_trace_multi_hop_derived() {
    // Chain: gerku(alis) → danlu(alis) → xanlu(alis) via two rules
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "xanlu"));
    let (result, trace) = query_with_proof(&kb, make_query("alis", "xanlu"));
    assert!(result);

    // Root: Derived(danlu → xanlu)
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Derived { .. }));
    if let ProofRule::Derived { label, .. } = &root_step.rule {
        assert!(label.contains("xanlu"));
    }
    assert_eq!(root_step.children.len(), 1);

    // Child: Derived(gerku → danlu)
    let mid_step = &trace.steps[root_step.children[0] as usize];
    assert!(mid_step.holds);
    assert!(matches!(&mid_step.rule, ProofRule::Derived { .. }));
    assert_eq!(mid_step.children.len(), 1);

    // Grandchild: Asserted(gerku(alis))
    let leaf_step = &trace.steps[mid_step.children[0] as usize];
    assert!(leaf_step.holds);
    assert!(matches!(&leaf_step.rule, ProofRule::Asserted { .. }));
}

#[test]
fn test_proof_trace_derived_depth_limit() {
    // Self-referencing rule: gerku → gerku. Asserted fact should be found first,
    // preventing infinite backward-chaining.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "gerku"));
    let (result, trace) = query_with_proof(&kb, make_query("alis", "gerku"));
    assert!(result);
    // Should not panic or infinite-loop. Asserted is checked first.
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Asserted { .. }));
}

#[test]
fn test_proof_trace_existential_import_presup_is_asserted() {
    // Universal "animal(every dog)." creates existential-import presupposition Skolem.
    // That fact should show as Asserted, not trigger backward-chaining.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    // existential-import presupposition creates sk_0 as a gerku
    let (result, trace) = query_with_proof(&kb, make_query("sk_0", "gerku"));
    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Asserted { .. }));
}

// ─── Conjunction Introduction (Guarded) Tests ────────────────────

#[test]
fn test_conjunction_introduction_basic() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("alis", "barda"));

    // Both share entity "alis" in x1 → conjunction should hold
    assert!(
        query_conjunction(&kb, "gerku", "alis", "barda", "alis"),
        "And(gerku(alis), barda(alis)) should hold"
    );
    // Commutativity: reversed order should also hold
    assert!(
        query_conjunction(&kb, "barda", "alis", "gerku", "alis"),
        "And(barda(alis), gerku(alis)) should hold (commutativity)"
    );
}

#[test]
fn test_conjunction_both_individually_true() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "mlatu"));

    // Both are individually true, so their conjunction holds
    // (no shared entity requirement in demand-driven reasoning)
    assert!(
        query_conjunction(&kb, "gerku", "alis", "mlatu", "bob"),
        "And(gerku(alis), mlatu(bob)) should hold when both are individually true"
    );
}

#[test]
fn test_conjunction_introduction_with_derived() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu")); // All dogs are animals
    assert_buf(&kb, make_assertion("alis", "gerku")); // Alice is a dog
    assert_buf(&kb, make_assertion("alis", "barda")); // Alice is big

    // Rule derives danlu(alis). Conjunction should combine derived + asserted.
    assert!(
        query_conjunction(&kb, "danlu", "alis", "barda", "alis"),
        "And(danlu(alis), barda(alis)) should hold via rule + conjunction"
    );
    // Also: gerku(alis) ∧ danlu(alis) (asserted + derived)
    assert!(
        query_conjunction(&kb, "gerku", "alis", "danlu", "alis"),
        "And(gerku(alis), danlu(alis)) should hold"
    );
}

#[test]
fn test_conjunction_introduction_cross_position() {
    // nelci(bob, alis) and gerku(alis) share "alis" across x2 and x1
    let kb = new_kb();

    // gerku(alis, _)
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // nelci(bob, alis, _)
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
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    // Check: And(gerku(alis,_), nelci(bob,alis,_)) should hold
    let mut nodes2 = Vec::new();
    let p1 = pred(
        &mut nodes2,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let p2 = pred(
        &mut nodes2,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root2 = and(&mut nodes2, p1, p2);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes: nodes2,
                roots: vec![root2]
            }
        ),
        "Cross-position entity sharing should allow conjunction query"
    );
}
