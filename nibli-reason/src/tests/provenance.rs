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
    if let ProofRule::ExistsWitness { var, term, origin } = &root_step.rule {
        assert_eq!(var, "x");
        assert!(matches!(term, LogicalTerm::Constant(c) if c == "alis"));
        assert_eq!(*origin, nibli_types::logic::WitnessOrigin::KnowledgeBase);
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
/// — a compute-decided FALSE (`5 = 3`, or a trusted backend false) must NOT be flagged — is pinned end-to-end in
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
    if let ProofRule::Asserted { fact, .. } = &root_step.rule {
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
    if let ProofRule::Derived { label, fact, .. } = &root_step.rule {
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
fn forward_derived_exact_store_hit_keeps_rule_and_premise_provenance() {
    // A forward conclusion physically occupies `fact_store`, but it is still a
    // derivation. The exact-hit fast path must not relabel it as an assertion.
    let kb = new_kb();
    let rule_id = assert_id(
        &kb,
        make_universal("gerku", "danlu"),
        "all dogs are animals",
    );
    kb.set_rule_forward("danlu", true);
    let premise_id = assert_id(&kb, make_assertion("alis", "gerku"), "Alice is a dog");

    let derived_fact = StoredFact::Bare(GroundFact::new(
        "danlu",
        vec![GroundTerm::Constant("alis".into()), GroundTerm::Unspecified],
    ));
    assert!(
        kb.inner.borrow().fact_store.contains(&derived_fact),
        "sanity: the forward rule must eagerly place danlu(alis) in the store"
    );

    let (result, trace) = query_with_proof(&kb, make_query("alis", "danlu"));
    assert!(result);
    let root = &trace.steps[trace.root as usize];
    let ProofRule::Derived { sources, .. } = &root.rule else {
        panic!(
            "a forward-only exact store hit must be Derived, never Asserted: {:?}",
            root.rule
        );
    };
    assert_eq!(sources.len(), 1, "one rule assertion supports this rule");
    assert_eq!(sources[0].assertion_id, rule_id);
    assert_eq!(sources[0].rule_ordinal, 0);
    assert_eq!(sources[0].assertion_label, "all dogs are animals");
    assert_eq!(root.children.len(), 1, "the rule has one positive premise");
    match &trace.steps[root.children[0] as usize].rule {
        ProofRule::Asserted { sources, .. } => {
            assert_eq!(sources.len(), 1);
            assert_eq!(sources[0].id, premise_id);
            assert_eq!(sources[0].label, "Alice is a dog");
        }
        other => panic!("the forward certificate must retain its asserted premise: {other:?}"),
    }

    // The exact same tuple can later gain a direct user source. Direct support
    // is then a terminal Asserted certificate; retracting only that source
    // exposes the still-valid rule derivation again rather than erasing or
    // relabelling it.
    let direct_id = assert_id(
        &kb,
        make_assertion("alis", "danlu"),
        "Alice is directly an animal",
    );
    let (_, direct_trace) = query_with_proof(&kb, make_query("alis", "danlu"));
    match &direct_trace.steps[direct_trace.root as usize].rule {
        ProofRule::Asserted { sources, .. } => {
            assert_eq!(
                sources.iter().map(|source| source.id).collect::<Vec<_>>(),
                vec![direct_id]
            );
        }
        other => panic!("direct support must take precedence over eager support: {other:?}"),
    }
    kb.retract_fact_inner(direct_id).unwrap();
    let (_, derived_again) = query_with_proof(&kb, make_query("alis", "danlu"));
    match &derived_again.steps[derived_again.root as usize].rule {
        ProofRule::Derived { sources, .. } => {
            assert_eq!(sources[0].assertion_id, rule_id);
        }
        other => panic!("after direct-source retraction the rule proof must remain: {other:?}"),
    }
}

#[test]
fn forward_cycle_keeps_earliest_presupposition_as_acyclic_primary_support() {
    // Seed P with a semantic presupposition, then let enabled P→Q and Q→P
    // rules add later forward supports. Choosing "any forward origin" would
    // trace P←Q←P forever; choosing the earliest non-direct support bottoms
    // out at the presupposition. Build the cycle through the public profile/rule
    // paths so the regression covers real insertion order rather than a hand-
    // assembled sidecar.
    let kb = new_kb();
    kb.set_existential_import(true).unwrap();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    kb.set_rule_forward("danlu", true);
    assert_buf(&kb, make_universal("danlu", "gerku"));
    kb.set_rule_forward("gerku", true);
    // This third description universal mints a fresh gerku presupposition.
    // P→Q then derives danlu for that witness and Q→P adds a later forward
    // support back onto the same gerku tuple.
    assert_buf(&kb, make_universal("gerku", "xanlu"));

    let cycle_fact = {
        let inner = kb.inner.borrow();
        inner
            .fact_origins
            .iter()
            .find(|(_, origins)| {
                origins.iter().any(|origin| {
                    matches!(origin, crate::kb::StoredFactOrigin::Presupposition { .. })
                }) && origins.iter().any(|origin| {
                    matches!(origin, crate::kb::StoredFactOrigin::ForwardDerived { .. })
                })
            })
            .map(|(fact, _)| fact.clone())
            .expect("the fresh P witness must gain a later P←Q forward support")
    };

    let inner = kb.inner.borrow();
    let mut steps = Vec::new();
    let root = trace_predicate_provenance_typed(
        &cycle_fact,
        &inner,
        &mut steps,
        0,
        &mut HashMap::new(),
        &mut HashSet::new(),
    );
    assert!(matches!(
        steps[root as usize].rule,
        ProofRule::Presupposed { .. }
    ));
    assert_eq!(
        steps.len(),
        1,
        "the earliest presupposition is a terminal proof leaf"
    );
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
fn rule_source_ordinals_and_duplicate_citations_survive_rebuild() {
    fn push_universal(nodes: &mut Vec<LogicNode>, from: &str, to: &str) -> u32 {
        let restrict = pred(
            nodes,
            from,
            vec![
                LogicalTerm::Variable("_v0".into()),
                LogicalTerm::Unspecified,
            ],
        );
        let conclusion = pred(
            nodes,
            to,
            vec![
                LogicalTerm::Variable("_v0".into()),
                LogicalTerm::Unspecified,
            ],
        );
        let negated = not(nodes, restrict);
        let implication = or(nodes, negated, conclusion);
        forall(nodes, "_v0", implication)
    }

    // One FactRecord produces two executable rules. Their public identity is
    // the source assertion id plus deterministic local registration ordinal.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let first = push_universal(&mut nodes, "gerku", "danlu");
    let second = push_universal(&mut nodes, "gerku", "jmive");
    let multi_rule_id = assert_id(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![first, second],
        },
        "two dog rules",
    );
    assert_id(&kb, make_assertion("alis", "gerku"), "Alice is a dog");

    let ordinal_for = |predicate: &str| {
        let (_, trace) = query_with_proof(&kb, make_query("alis", predicate));
        match &trace.steps[trace.root as usize].rule {
            ProofRule::Derived { sources, .. } => {
                assert_eq!(sources.len(), 1);
                assert_eq!(sources[0].assertion_id, multi_rule_id);
                assert_eq!(sources[0].assertion_label, "two dog rules");
                sources[0].rule_ordinal
            }
            other => panic!("{predicate} should be rule-derived: {other:?}"),
        }
    };
    assert_eq!(ordinal_for("danlu"), 0);
    assert_eq!(ordinal_for("jmive"), 1);
    kb.rebuild().unwrap();
    assert_eq!(
        ordinal_for("danlu"),
        0,
        "rebuild must preserve rule ordinal"
    );
    assert_eq!(
        ordinal_for("jmive"),
        1,
        "rebuild must preserve rule ordinal"
    );

    // Executable-rule dedup must not collapse the separately retractable source
    // assertions that make the canonical rule citable.
    let duplicate = new_kb();
    let first_id = assert_id(
        &duplicate,
        make_universal("gerku", "danlu"),
        "rule copy one",
    );
    let second_id = assert_id(
        &duplicate,
        make_universal("gerku", "danlu"),
        "rule copy two",
    );
    assert_buf(&duplicate, make_assertion("alis", "gerku"));
    let (_, trace) = query_with_proof(&duplicate, make_query("alis", "danlu"));
    let ProofRule::Derived { sources, .. } = &trace.steps[trace.root as usize].rule else {
        panic!("duplicate canonical rule should still derive danlu(alis)");
    };
    assert_eq!(
        sources
            .iter()
            .map(|source| (source.assertion_id, source.rule_ordinal))
            .collect::<Vec<_>>(),
        vec![(first_id, 0), (second_id, 0)],
        "both duplicate rule assertions must remain separately citable"
    );
}

#[test]
fn duplicate_flat_assertions_retain_each_citation_through_rebuild_and_retraction() {
    fn identity(a: &str, b: &str) -> LogicBuffer {
        LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                nibli_types::relations::IDENTITY.to_string(),
                vec![
                    LogicalTerm::Constant(a.into()),
                    LogicalTerm::Constant(b.into()),
                ],
            ))],
            roots: vec![0],
        }
    }

    fn source_ids(kb: &KnowledgeBase) -> Vec<u64> {
        let (_, trace) = query_with_proof(kb, identity("adam", "bob"));
        match &trace.steps[trace.root as usize].rule {
            ProofRule::Asserted { sources, .. } => sources.iter().map(|source| source.id).collect(),
            other => panic!("the exact stored identity must be asserted: {other:?}"),
        }
    }

    let kb = new_kb();
    let first = assert_id(&kb, identity("adam", "bob"), "identity copy one");
    let second = assert_id(&kb, identity("adam", "bob"), "identity copy two");
    assert_eq!(source_ids(&kb), vec![first, second]);

    kb.rebuild().unwrap();
    assert_eq!(
        source_ids(&kb),
        vec![first, second],
        "rebuild must regenerate both direct supports in fact-id order"
    );

    kb.retract_fact_inner(first).unwrap();
    assert_eq!(
        source_ids(&kb),
        vec![second],
        "retracting one duplicate must leave the other citation and the fact"
    );
}

#[test]
fn equality_substitution_cites_the_real_transitive_path() {
    fn identity(a: &str, b: &str) -> LogicBuffer {
        LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                nibli_types::relations::IDENTITY.to_string(),
                vec![
                    LogicalTerm::Constant(a.into()),
                    LogicalTerm::Constant(b.into()),
                ],
            ))],
            roots: vec![0],
        }
    }

    let kb = new_kb();
    let ab = assert_id(&kb, identity("adam", "bob"), "Adam equals Bob");
    let bc = assert_id(&kb, identity("bob", "cy"), "Bob equals Cy");
    let premise = assert_id(&kb, make_assertion("adam", "gerku"), "Adam is a dog");

    let (result, trace) = query_with_proof(&kb, make_query("cy", "gerku"));
    assert!(result);
    let root = &trace.steps[trace.root as usize];
    assert!(matches!(root.rule, ProofRule::EqualitySubstitution { .. }));
    assert_eq!(
        root.children.len(),
        3,
        "child 0 is the substituted fact; the remaining children are the two real equality edges"
    );
    match &trace.steps[root.children[0] as usize].rule {
        ProofRule::Asserted { sources, .. } => {
            assert_eq!(
                sources.iter().map(|s| s.id).collect::<Vec<_>>(),
                vec![premise]
            );
        }
        other => panic!("the substituted gerku(adam) proof must retain its source: {other:?}"),
    }
    let mut equality_sources: Vec<u64> = root.children[1..]
        .iter()
        .flat_map(|child| match &trace.steps[*child as usize].rule {
            ProofRule::Asserted { sources, .. } => {
                sources.iter().map(|source| source.id).collect::<Vec<_>>()
            }
            other => panic!("equality path child must cite an asserted edge: {other:?}"),
        })
        .collect();
    equality_sources.sort_unstable();
    assert_eq!(
        equality_sources,
        vec![ab, bc],
        "the trace must cite the actual Adam=Bob and Bob=Cy path, not invent Adam=Cy"
    );
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
fn test_proof_trace_existential_import_presupposition_is_not_asserted() {
    // Universal "animal(every dog)." creates existential-import presupposition Skolem.
    // That fact is generated by the profile and must never be presented as a
    // user assertion. It cites the rule assertion that requested the import.
    let kb = new_kb();
    kb.set_existential_import(true).unwrap();
    let rule_id = assert_id(
        &kb,
        make_universal("gerku", "danlu"),
        "all dogs are animals",
    );
    // The friendly witness label is `sk_0`, but a user constant with that spelling
    // must not name the internal witness.
    let (colliding_user_result, _) = query_with_proof(&kb, make_query("sk_0", "gerku"));
    assert!(!colliding_user_result);

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
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
    assert!(matches!(
        &root_step.rule,
        ProofRule::ExistsWitness {
            term: LogicalTerm::Constant(name),
            origin: nibli_types::logic::WitnessOrigin::ExistentialImport,
            ..
        } if name == "sk_0"
    ));
    match &trace.steps[root_step.children[0] as usize].rule {
        ProofRule::Presupposed { label, sources, .. } => {
            assert!(
                label.contains("gerku") && label.contains("danlu"),
                "{label}"
            );
            assert_eq!(sources.len(), 1);
            assert_eq!(sources[0].assertion_id, rule_id);
            assert_eq!(sources[0].rule_ordinal, 0);
            assert_eq!(sources[0].assertion_label, "all dogs are animals");
        }
        other => panic!("an imported restrictor witness must be Presupposed: {other:?}"),
    }
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

// ─── Rule execution settings are session configuration ───────────────────

/// `set_rule_forward` / `set_rule_priority` survive the rebuild an UNRELATED
/// retraction performs: replay re-registers the surviving rules under the
/// recorded overrides. Configuration, eager firing, and the verdict must all
/// come back; eager facts derived BEFORE the rebuild are re-derived lazily
/// (enabling never retro-fires — the documented contract), so the conclusion
/// stays backward-derivable throughout.
#[test]
fn rule_execution_settings_survive_unrelated_retraction() {
    let kb = new_kb();
    assert_id(&kb, make_universal("gerku", "danlu"), "dogs are animals");
    kb.set_rule_forward("danlu", true);
    kb.set_rule_priority("danlu", 7);
    let unrelated = assert_id(&kb, make_assertion("bob", "mlatu"), "unrelated cat");
    assert_id(&kb, make_assertion("alis", "gerku"), "Alice is a dog");

    let eager = |who: &str| {
        StoredFact::Bare(GroundFact::new(
            "danlu",
            vec![GroundTerm::Constant(who.into()), GroundTerm::Unspecified],
        ))
    };
    assert!(
        kb.inner.borrow().fact_store.contains(&eager("alis")),
        "sanity: forward rule fires eagerly before the retraction"
    );

    kb.retract_fact(unrelated).expect("retraction must succeed");

    assert_eq!(
        kb.rule_execution_settings("danlu"),
        vec![("gerku → danlu".to_string(), true, 7)],
        "forward/priority must survive the unrelated retraction's rebuild"
    );
    // Enabling never retro-fires: the pre-rebuild eager fact is re-derived
    // lazily, not resurrected into the store by the rebuild itself.
    assert!(
        !kb.inner.borrow().fact_store.contains(&eager("alis")),
        "documented no-retro-fire contract: rebuild replay does not re-fire"
    );
    // …but the verdict is unaffected (backward chaining derives it),
    let (result, _) = query_with_proof(&kb, make_query("alis", "danlu"));
    assert!(result, "the conclusion stays backward-derivable");
    // …and eager firing works for NEW triggering insertions.
    assert_id(&kb, make_assertion("cyan", "gerku"), "Cyan is a dog");
    assert!(
        kb.inner.borrow().fact_store.contains(&eager("cyan")),
        "the surviving forward setting must fire on a post-rebuild insertion"
    );
}

/// The overrides are configuration by CONCLUSION PREDICATE, not per-rule
/// mutation: a setter call made BEFORE the rule exists applies at that rule's
/// registration — the same uniform semantics that make rebuild reapplication
/// correct by construction.
#[test]
fn rule_execution_override_applies_to_later_registered_rules() {
    let kb = new_kb();
    kb.set_rule_forward("danlu", true);
    assert_id(&kb, make_universal("gerku", "danlu"), "dogs are animals");
    assert_eq!(
        kb.rule_execution_settings("danlu"),
        vec![("gerku → danlu".to_string(), true, 0)],
        "an override recorded before registration must apply at registration"
    );
    assert_id(&kb, make_assertion("alis", "gerku"), "Alice is a dog");
    let derived = StoredFact::Bare(GroundFact::new(
        "danlu",
        vec![GroundTerm::Constant("alis".into()), GroundTerm::Unspecified],
    ));
    assert!(
        kb.inner.borrow().fact_store.contains(&derived),
        "the registration-applied override must actually forward-fire"
    );
}

/// The NAF refusal is re-checked per rule at every application: a forward
/// override on a NAF-bearing rule's conclusion is refused live AND at every
/// rebuild re-registration — an unrelated retraction cannot resurrect forward
/// firing on a rule where it is unsound.
#[test]
fn naf_rule_stays_backward_only_across_rebuild_despite_forward_override() {
    let kb = new_kb();
    assert_id(
        &kb,
        compile_surface("eats(every cat where ~awake)."),
        "naf rule",
    );
    kb.set_rule_forward("eats", true);
    let settings = kb.rule_execution_settings("eats");
    assert_eq!(settings.len(), 1);
    assert!(
        !settings[0].1,
        "live NAF refusal: the rule must stay backward-only"
    );

    let unrelated = assert_id(&kb, make_assertion("bob", "mlatu"), "unrelated");
    kb.retract_fact(unrelated).expect("retraction must succeed");

    let settings = kb.rule_execution_settings("eats");
    assert_eq!(settings.len(), 1);
    assert!(
        !settings[0].1,
        "rebuild reapplication must re-refuse forward on a NAF rule"
    );
}

/// `reset()` clears the overrides with the KB content they configure: a rule
/// registered after reset gets registration defaults.
#[test]
fn reset_clears_rule_execution_overrides() {
    let kb = new_kb();
    kb.set_rule_forward("danlu", true);
    kb.set_rule_priority("danlu", 5);
    kb.reset().unwrap();
    assert_id(&kb, make_universal("gerku", "danlu"), "dogs are animals");
    assert_eq!(
        kb.rule_execution_settings("danlu"),
        vec![("gerku → danlu".to_string(), false, 0)],
        "reset must drop the session overrides"
    );
}
