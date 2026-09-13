// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

#[test]
fn domain_planning_compares_shared_identities_once_and_keeps_value_deduplication() {
    let kb = surface_kb(&["person(Adam).", "likes(every person, some cat)."]);
    let mut inner = kb.inner.borrow_mut();
    let original = inner
        .universal_rules
        .values()
        .flatten()
        .next()
        .unwrap()
        .clone();
    let indexed_references = inner.universal_rules.values().map(Vec::len).sum::<usize>();
    assert!(
        indexed_references > 1,
        "surface rule is indexed under multiple heads"
    );

    TEST_DOMAIN_IDENTITY_CHECKS.set(0);
    assert_eq!(distinct_domain_rules(&inner).count(), 1);
    assert_eq!(TEST_DOMAIN_IDENTITY_CHECKS.get(), 1);

    // Even a separately allocated but value-equal identity must be deduplicated.
    // Keep both different rule objects to check first-seen selection as well.
    let mut detached = original.as_ref().clone();
    detached.identity = Arc::new(original.identity.as_ref().clone());
    inner
        .universal_rules
        .values_mut()
        .next()
        .unwrap()
        .push(Arc::new(detached));
    let mut old_seen = HashSet::new();
    let expected: Vec<_> = inner
        .universal_rules
        .values()
        .flatten()
        .filter(|rule| old_seen.insert(rule.identity.clone()))
        .map(Arc::as_ptr)
        .collect();
    TEST_DOMAIN_IDENTITY_CHECKS.set(0);
    let actual: Vec<_> = distinct_domain_rules(&inner).map(Arc::as_ptr).collect();
    assert_eq!(actual, expected);
    assert_eq!(actual.len(), 1);
    assert_eq!(TEST_DOMAIN_IDENTITY_CHECKS.get(), 2);
}

#[test]
fn completed_witness_closure_reuses_only_unchanged_state_and_mode() {
    let kb = surface_kb(&["person(Adam).", "likes(every person, some cat)."]);
    kb.ensure_materialized(&compile_surface("person(Adam)."), true);
    TEST_CLOSURE_RUNS.set(0);
    assert_eq!(verdict(&kb, "likes(Adam, some cat)."), QueryResult::True);
    let first = TEST_CLOSURE_RUNS.get();
    assert!(first > 0);
    assert_eq!(verdict(&kb, "cat(exactly 1 cat)."), QueryResult::True);
    assert_eq!(
        TEST_CLOSURE_RUNS.get(),
        first,
        "unchanged closure should be reused"
    );

    let cancel = Arc::new(std::sync::atomic::AtomicBool::new(true));
    kb.set_cancel_flag(Arc::clone(&cancel));
    assert!(
        kb.query_entailment(compile_surface("person(Adam)."))
            .is_err()
    );
    cancel.store(false, std::sync::atomic::Ordering::Relaxed);

    let new_person = assert_id(&kb, compile_surface("person(Bob)."), "new person");
    assert_eq!(verdict(&kb, "cat(exactly 2 cat)."), QueryResult::True);
    assert!(
        TEST_CLOSURE_RUNS.get() > first,
        "new facts invalidate domain closure"
    );
    kb.retract_fact(new_person).unwrap();
    assert_eq!(verdict(&kb, "cat(exactly 1 cat)."), QueryResult::True);
    assert_eq!(verdict(&kb, "likes(Bob, some cat)."), QueryResult::False);

    let before_proof = TEST_CLOSURE_RUNS.get();
    let (result, proof) = kb
        .query_entailment_with_proof_inner(compile_surface("likes(Adam, some cat)."))
        .unwrap();
    assert_eq!(result, QueryResult::True);
    assert!(!proof.steps.is_empty());
    assert!(
        TEST_CLOSURE_RUNS.get() > before_proof,
        "proof mode rebuilds activation evidence"
    );

    kb.set_max_chain_depth(1).unwrap();
    let before_depth = TEST_CLOSURE_RUNS.get();
    assert_eq!(verdict(&kb, "person(Adam)."), QueryResult::True);
    assert!(
        TEST_CLOSURE_RUNS.get() > before_depth,
        "depth/profile changes invalidate closure"
    );
}

#[test]
fn incomplete_witness_closure_is_never_reused_as_complete() {
    let kb = surface_kb(&["person(Adam).", "likes(every person, some cat)."]);
    kb.ensure_materialized(&compile_surface("person(Adam)."), true);
    assert_eq!(verdict(&kb, "cat(exactly 1 cat)."), QueryResult::True);
    TEST_CLOSURE_LIMIT.set(Some(1));
    let result = verdict(&kb, "cat(exactly 1 cat).");
    TEST_CLOSURE_LIMIT.set(None);
    assert!(matches!(result, QueryResult::ResourceExceeded(_)));
    assert!(kb.inner.borrow().query_domain.completed_at.get().is_none());
    assert_eq!(verdict(&kb, "cat(exactly 1 cat)."), QueryResult::True);
}

#[test]
fn cached_witness_closure_matches_fresh_across_mutations_and_profiles() {
    fn run(reuse: bool) -> Vec<QueryResult> {
        let kb = surface_kb(&[
            "person(Adam).",
            "likes(every person, some cat).",
            "all $x: cat($x) & ~dog($x) -> animal($x).",
        ]);
        let mut results = Vec::new();
        let mut sample = || {
            for text in [
                "likes(Adam, some cat).",
                "cat(exactly 1 cat).",
                "cat(exactly 2 cat).",
                "animal(some cat).",
                "likes(Bob, some cat).",
                "person(Bob).",
            ] {
                if !reuse {
                    kb.inner.borrow().query_domain.completed_at.set(None);
                }
                results.push(verdict(&kb, text));
            }
        };
        sample();
        let bob = assert_id(&kb, compile_surface("person(Bob)."), "second person");
        sample();
        kb.retract_fact(bob).unwrap();
        sample();
        kb.set_materialization(false);
        sample();
        kb.set_materialization(true);
        sample();
        kb.set_rule_priority("likes", 10);
        sample();
        kb.set_rule_forward("likes", false);
        sample();
        kb.set_max_chain_depth(1).unwrap();
        sample();
        kb.set_max_chain_depth(10).unwrap();
        sample();
        kb.reset().unwrap();
        sample();
        results
    }
    assert_eq!(run(true), run(false));
}

#[test]
fn complete_unary_witness_filter_tracks_growth_and_proof_mode() {
    let kb = surface_kb(&["person(Adam).", "likes(every person, some cat)."]);
    kb.set_materialization(true);
    kb.ensure_materialized(&compile_surface("person(Adam)."), true);
    {
        let inner = kb.inner.borrow();
        let rule = inner.universal_rules.values().flatten().next().unwrap();
        let variable = rule
            .pattern_var_names
            .iter()
            .find(|name| !name.starts_with("ev__"))
            .unwrap();
        let allowed =
            materialize::complete_unary_condition_members(&inner, rule, variable).unwrap();
        assert_eq!(
            allowed,
            HashSet::from([GroundTerm::Constant("adam".into())])
        );
        inner.positive_lookup.set(false);
        assert!(materialize::complete_unary_condition_members(&inner, rule, variable).is_none());
        inner.positive_lookup.set(true);
    }
    assert_buf(&kb, compile_surface("bird(Bob)."));
    assert_eq!(verdict(&kb, "likes(Bob, some cat)."), QueryResult::False);
    assert_buf(&kb, compile_surface("person(Bob)."));
    assert_eq!(verdict(&kb, "likes(Bob, some cat)."), QueryResult::True);
    assert_eq!(verdict(&kb, "cat(exactly 2 cat)."), QueryResult::True);
    let (result, proof) = kb
        .query_entailment_with_proof_inner(compile_surface("likes(Bob, some cat)."))
        .unwrap();
    assert_eq!(result, QueryResult::True);
    assert!(!proof.steps.is_empty());
    let first = kb.list_facts().unwrap()[0].id;
    kb.retract_fact(first).unwrap();
    assert_eq!(verdict(&kb, "likes(Adam, some cat)."), QueryResult::False);
    assert_eq!(verdict(&kb, "cat(exactly 1 cat)."), QueryResult::True);
}

#[test]
fn shared_assertion_records_detach_on_scoped_withdrawal() {
    let kb = surface_kb(&["dog(Adam).", "likes(every dog, some cat)."]);
    let id = kb.list_facts().unwrap()[0].id;
    kb.with_assumptions(&[], |candidate| {
        assert!(Arc::ptr_eq(
            &kb.inner.borrow().fact_registry[&id],
            &candidate.inner.borrow().fact_registry[&id]
        ));
        candidate.retract_fact(id).unwrap();
        assert_eq!(verdict(candidate, "dog(Adam)."), QueryResult::False);
        assert!(!kb.inner.borrow().fact_registry[&id].retracted);
        assert!(candidate.inner.borrow().fact_registry[&id].retracted);
        assert!(!Arc::ptr_eq(
            &kb.inner.borrow().fact_registry[&id],
            &candidate.inner.borrow().fact_registry[&id]
        ));
    })
    .unwrap();
    assert_eq!(verdict(&kb, "dog(Adam)."), QueryResult::True);
    assert_eq!(verdict(&kb, "likes(Adam, some cat)."), QueryResult::True);
}

#[test]
fn compact_batch_graph_preserves_polarities_refusals_and_retraction() {
    let lines = [
        "dog(Adam).",
        "all $x: dog($x) & bird($x) -> mouse($x).",
        "all $x: dog($x) & ~bird($x) -> mouse($x).",
        "all $x: dog($x) -> cat($x) & animal($x).",
        "all $x: dog($x) & bird($x) -> cat($x).",
    ];
    let sequential = surface_kb(&lines);
    let (batch, ids) = KnowledgeBase::from_compiled_batch(
        lines
            .iter()
            .map(|line| (compile_surface(line), (*line).to_owned()))
            .collect(),
    )
    .unwrap();
    let graph = batch.inner.borrow().pred_dep_graph.clone();
    for edges in graph.values() {
        let unique: HashSet<_> = edges.iter().collect();
        assert_eq!(edges.len(), unique.len());
    }
    let shape = |kb: &KnowledgeBase| format!("{:?}", kb.stratification_report().unwrap());
    assert_eq!(shape(&batch), shape(&sequential));
    for query in ["mouse(Adam).", "cat(Adam).", "animal(Adam)."] {
        assert_eq!(verdict(&batch, query), verdict(&sequential, query));
    }
    let before = shape(&batch);
    assert!(
        batch
            .assert_fact(
                compile_surface("all $x: mouse($x) -> bird($x)."),
                "forbidden negative cycle".into()
            )
            .is_err()
    );
    assert_eq!(shape(&batch), before);
    assert_eq!(verdict(&batch, "mouse(Adam)."), QueryResult::True);
    batch.retract_fact(ids[2][0]).unwrap();
    assert_eq!(verdict(&batch, "mouse(Adam)."), QueryResult::False);
    batch
        .assert_fact(compile_surface("bird(Adam)."), "new bird".into())
        .unwrap();
    assert_eq!(verdict(&batch, "mouse(Adam)."), QueryResult::True);
}

#[test]
fn reusable_domain_plan_matches_fresh_planning_across_mutations() {
    fn run(reuse: bool, materialization: bool) -> Vec<QueryResult> {
        let kb = surface_kb(&["dog(Adam).", "likes(every dog, some cat)."]);
        kb.set_materialization(materialization);
        let mut results = Vec::new();
        for source in [None, Some("dog(Bob)."), Some("bird(Cia).")] {
            if let Some(source) = source {
                assert_buf(&kb, compile_surface(source));
            }
            for query in [
                "cat(some cat).",
                "likes(Adam, exactly 1 cat).",
                "likes(Bob, some cat).",
                "likes(Cia, some cat).",
            ] {
                if !reuse {
                    kb.inner.borrow().materialization_plan.borrow_mut().take();
                }
                results.push(verdict(&kb, query));
            }
        }
        let before = kb.list_facts().unwrap().len();
        let (verdict, proof) = kb
            .query_entailment_with_proof_inner(compile_surface("likes(Adam, some cat)."))
            .unwrap();
        assert_eq!(verdict, QueryResult::True);
        assert!(!proof.steps.is_empty());
        assert_eq!(kb.list_facts().unwrap().len(), before);
        results
    }
    let reference = run(false, false);
    assert_eq!(run(true, false), reference);
    assert_eq!(run(false, true), reference);
    assert_eq!(run(true, true), reference);
}

fn surface_kb(lines: &[&str]) -> KnowledgeBase {
    let kb = new_kb();
    kb.set_materialization(false);
    for line in lines {
        assert_buf(&kb, compile_surface(line));
    }
    kb
}

fn verdict(kb: &KnowledgeBase, text: &str) -> QueryResult {
    kb.query_entailment_inner(compile_surface(text)).unwrap()
}

#[test]
fn equality_alternatives_preserve_depth_and_proofs() {
    for equality in ["Adam = Bob.", "Bob = Adam."] {
        let kb = surface_kb(&[
            "dog(Adam).",
            "dog(Adam) -> cat(Adam).",
            "cat(Adam) -> animal(Adam).",
            equality,
        ]);
        kb.inner.borrow_mut().max_chain_depth = 1;
        assert_eq!(
            verdict(&kb, "animal(Bob)."),
            QueryResult::ResourceExceeded(ResourceKind::Depth)
        );
        assert!(!verdict(&kb, "~animal(Bob).").is_true());
        kb.inner.borrow_mut().max_chain_depth = 10;
        for _ in 0..2 {
            assert_eq!(verdict(&kb, "animal(Bob)."), QueryResult::True);
            let (result, proof) = kb
                .query_entailment_with_proof_inner(compile_surface("animal(Bob)."))
                .unwrap();
            assert_eq!(result, QueryResult::True);
            assert!(
                proof
                    .steps
                    .iter()
                    .any(|step| matches!(&step.rule, ProofRule::Asserted { .. }))
            );
        }
        assert_eq!(verdict(&kb, "bird(Bob)."), QueryResult::False);
    }
}

#[test]
fn generated_individual_exists_zero_count_and_find_agree() {
    let kb = surface_kb(&["dog(Adam).", "likes(every dog, some cat)."]);
    for _ in 0..2 {
        assert_eq!(verdict(&kb, "likes(Adam, some cat)."), QueryResult::True);
        assert_eq!(verdict(&kb, "likes(Adam, no cat)."), QueryResult::False);
        assert_eq!(
            verdict(&kb, "likes(Adam, exactly 1 cat)."),
            QueryResult::True
        );
        let witnesses = kb
            .query_find_inner(compile_surface("likes(Adam, $w)."))
            .unwrap();
        assert_eq!(witnesses.len(), 1, "{witnesses:?}");
    }
    assert_eq!(kb.list_facts().unwrap().len(), 2);
}

#[test]
fn finite_nested_witness_chain_reaches_fixed_point() {
    let kb = surface_kb(&[
        "dog(Adam).",
        "likes(every dog, some cat).",
        "likes(every cat, some mouse).",
        "likes(every mouse, some bird).",
    ]);
    kb.inner.borrow_mut().max_chain_depth = 16;
    for species in ["cat", "mouse", "bird"] {
        assert_eq!(
            verdict(&kb, &format!("{species}(some {species}).")),
            QueryResult::True
        );
    }
    assert_eq!(
        verdict(&kb, "likes(some mouse, exactly 1 bird)."),
        QueryResult::True
    );
    assert_eq!(
        kb.query_find_inner(compile_surface("bird($w)."))
            .unwrap()
            .len(),
        1
    );
}

#[test]
fn generated_dependencies_deduplicate_after_equality_and_retraction() {
    let kb = surface_kb(&["dog(Adam).", "dog(Bob).", "likes(every dog, some cat)."]);
    assert_eq!(
        kb.query_find_inner(compile_surface("cat($w)."))
            .unwrap()
            .len(),
        2
    );
    let equality = assert_id(&kb, compile_surface("Adam = Bob."), "identity");
    assert_eq!(
        verdict(&kb, "likes(Adam, exactly 1 cat)."),
        QueryResult::True
    );
    assert_eq!(
        kb.query_find_inner(compile_surface("cat($w)."))
            .unwrap()
            .len(),
        1
    );
    kb.retract_fact(equality).unwrap();
    assert_eq!(
        kb.query_find_inner(compile_surface("cat($w)."))
            .unwrap()
            .len(),
        2
    );
}

#[test]
fn nested_multi_dependency_families_normalize_each_equal_argument() {
    for connects_second_variable in [false, true] {
        let rule = if connects_second_variable {
            "all $x: all $y: dog($x) & cat($y) -> owns($x, some mouse, $y)."
        } else {
            // The existential depends only on x, but proving its guard still
            // requires finding a generated individual for the body-only y.
            "all $x: all $y: dog($x) & cat($y) -> owns($x, some mouse)."
        };
        let kb = surface_kb(&[
            "dog(Adam).",
            "dog(Bob).",
            "likes(every dog, some cat).",
            rule,
        ]);
        let expected = if connects_second_variable { 4 } else { 2 };
        assert_eq!(
            kb.query_find_inner(compile_surface("mouse($w)."))
                .unwrap()
                .len(),
            expected
        );
        assert_eq!(
            verdict(&kb, &format!("mouse(exactly {expected} mouse).")),
            QueryResult::True
        );
        let equality = assert_id(&kb, compile_surface("Adam = Bob."), "identity");
        assert_eq!(
            kb.query_find_inner(compile_surface("mouse($w)."))
                .unwrap()
                .len(),
            1
        );
        assert_eq!(verdict(&kb, "mouse(exactly 1 mouse)."), QueryResult::True);
        let query = if connects_second_variable {
            "owns(Bob, exactly 1 mouse, ?)."
        } else {
            "owns(Bob, exactly 1 mouse)."
        };
        let (result, proof) = kb
            .query_entailment_with_proof_inner(compile_surface(query))
            .unwrap();
        assert_eq!(result, QueryResult::True);
        assert!(
            proof
                .steps
                .iter()
                .any(|step| matches!(step.rule, ProofRule::EqualitySubstitution { .. }))
        );
        kb.retract_fact(equality).unwrap();
        assert_eq!(
            kb.query_find_inner(compile_surface("mouse($w)."))
                .unwrap()
                .len(),
            expected
        );
    }
}

#[test]
fn witness_congruence_is_symbolic_across_many_equal_dependencies() {
    let kb = surface_kb(&["Adam = Bob."]);
    let repeated = |name: &str| {
        let terms = vec![GroundTerm::Constant(name.into()); 21];
        build_skolem_fn_term(SkolemSymbol::for_test(900), &terms)
    };
    let original = repeated("bob");
    let canonical = repeated("adam");
    let mut inner = kb.inner.borrow_mut();
    let variants = get_equivalence_class_readonly(
        &inner.equivalence_parent,
        &inner.equivalence_classes,
        &original,
    );
    assert_eq!(
        variants.len(),
        2,
        "retain original and canonical terms, never 2^21 spellings"
    );
    assert!(variants.contains(&canonical));
    let stored = StoredFact::Bare(GroundFact::new("symbolic", vec![original.clone()]));
    assert_typed_fact(stored, &mut inner);
    let query = StoredFact::Bare(GroundFact::new("symbolic", vec![canonical.clone()]));
    assert!(typed_fact_is_stored(&query, &inner));
    assert_eq!(
        equality_path_facts(&inner, &original, &canonical)
            .unwrap()
            .into_iter()
            .collect::<HashSet<_>>()
            .len(),
        1
    );
    let other_source = build_skolem_fn_term(
        SkolemSymbol::for_test(901),
        &vec![GroundTerm::Constant("adam".into()); 21],
    );
    assert!(!typed_fact_is_stored(
        &StoredFact::Bare(GroundFact::new("symbolic", vec![other_source])),
        &inner
    ));
}

#[test]
fn failed_guard_creates_no_individual_and_growing_chase_refuses_count() {
    let kb = surface_kb(&["dog(Adam).", "likes(every cat, some mouse)."]);
    assert_eq!(verdict(&kb, "mouse(some mouse)."), QueryResult::False);
    assert!(kb.inner.borrow().query_domain.incomplete.is_none());
    let growing = surface_kb(&["dog(Adam).", "likes(every dog, some dog)."]);
    growing.inner.borrow_mut().max_chain_depth = 3;
    assert_eq!(
        verdict(&growing, "likes(Adam, some dog)."),
        QueryResult::True
    );
    assert!(!verdict(&growing, "likes(Adam, no dog).").is_true());
    assert!(!verdict(&growing, "likes(Adam, exactly 1 dog).").is_definitive());
    assert!(
        growing
            .query_find_inner(compile_surface("dog($w)."))
            .is_err()
    );
}

#[test]
fn witness_closure_finishes_lower_strata_before_negative_activation() {
    let rules = [
        "all $x: dog($x) -> likes($x, some cat).",
        "all $x: cat($x) -> animal($x).",
        "all $x: cat($x) & ~animal($x) -> likes($x, some mouse).",
        "all $x: cat($x) & ~bird($x) -> likes($x, some fish).",
    ];
    for reversed in [false, true] {
        let kb = surface_kb(&["dog(Adam)."]);
        for rule in if reversed {
            rules.iter().rev().collect::<Vec<_>>()
        } else {
            rules.iter().collect()
        } {
            assert_buf(&kb, compile_surface(rule));
        }
        assert_eq!(verdict(&kb, "mouse(some mouse)."), QueryResult::False);
        assert_eq!(
            verdict(&kb, "likes(some cat, exactly 1 fish)."),
            QueryResult::True
        );
        assert_eq!(
            kb.query_find_inner(compile_surface("fish($x)."))
                .unwrap()
                .len(),
            1
        );
    }
}

#[test]
fn witness_closure_keeps_source_identity_and_import_profile() {
    for import in [false, true] {
        let kb = surface_kb(&[
            "dog(Adam).",
            "animal(Adam).",
            "likes(every dog, some cat).",
            "likes(every animal, some cat).",
        ]);
        kb.set_existential_import(import).unwrap();
        assert_eq!(
            verdict(&kb, "likes(Adam, exactly 2 cat)."),
            QueryResult::True
        );
        let (result, proof) = kb
            .query_entailment_with_proof_inner(compile_surface("likes(Adam, exactly 2 cat)."))
            .unwrap();
        assert_eq!(result, QueryResult::True);
        assert!(
            proof
                .steps
                .iter()
                .any(|step| matches!(&step.rule, ProofRule::CountResult { actual: 2, .. }))
        );
    }
}

#[test]
fn witness_closure_memory_and_cancellation_never_return_partial_counts() {
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            crate::domain::TEST_CLOSURE_LIMIT.with(|cap| cap.set(None));
        }
    }
    let _reset = Reset;
    let kb = surface_kb(&["dog(Adam).", "likes(every dog, some cat)."]);
    crate::domain::TEST_CLOSURE_LIMIT.with(|cap| cap.set(Some(0)));
    assert_eq!(
        verdict(&kb, "likes(Adam, exactly 0 cat)."),
        QueryResult::ResourceExceeded(ResourceKind::Memory)
    );
    assert!(kb.query_find_inner(compile_surface("cat($x).")).is_err());
    crate::domain::TEST_CLOSURE_LIMIT.with(|cap| cap.set(None));
    assert_eq!(
        verdict(&kb, "likes(Adam, exactly 1 cat)."),
        QueryResult::True
    );
    let cancel = Arc::new(std::sync::atomic::AtomicBool::new(true));
    kb.set_cancel_flag(cancel);
    assert!(
        kb.query_entailment_inner(compile_surface("likes(Adam, exactly 0 cat)."))
            .is_err()
    );
    kb.clear_cancel_flag();
    assert_eq!(
        verdict(&kb, "likes(Adam, exactly 1 cat)."),
        QueryResult::True
    );
}

#[test]
fn incomplete_lower_witness_closure_cannot_enable_negative_guards() {
    let kb = surface_kb(&[
        "dog(Adam).",
        "likes(every dog, some cat).",
        "likes(every cat, some cat).",
        "all $x: cat($x) -> bird($x).",
        // Raises `likes` to the negative stratum without raising its sibling
        // generative head `cat`: activation must schedule by the rule body.
        "all $x: dog($x) & ~bird($x) -> likes($x, Adam).",
        "all $x: dog($x) & ~bird($x) -> owns($x, some mouse).",
    ]);
    kb.set_max_chain_depth(2).unwrap();
    assert!(!verdict(&kb, "mouse(some mouse).").is_definitive());
    assert!(kb.query_find_inner(compile_surface("mouse($x).")).is_err());
}
