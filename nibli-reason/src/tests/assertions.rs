// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

#[test]
fn condition_events_do_not_copy_unused_conclusion_dependencies() {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("dog(Rex)."));
    let mut conditions = vec!["dog($x)".to_string()];
    let mut first_fact = None;
    for index in 0..30 {
        let fact = assert_id(
            &kb,
            compile_surface(&format!("authorized(Rex, Wanted, Record{index}).")),
            "required condition",
        );
        first_fact.get_or_insert(fact);
        conditions.push(format!("authorized($x, Wanted, Record{index})"));
    }
    TEST_DEPENDENCY_NAME_COPIES.set(0);
    assert_buf(
        &kb,
        compile_surface(&format!(
            "all $x: {} -> animal($x).",
            conditions.join(" & ")
        )),
    );
    assert_eq!(
        TEST_DEPENDENCY_NAME_COPIES.get(),
        1,
        "only the head event needs a copy of the universal dependency list"
    );
    assert!(query(&kb, compile_surface("animal(Rex).")));
    kb.retract_fact(first_fact.unwrap()).unwrap();
    assert!(query_false(&kb, compile_surface("animal(Rex).")));
}

#[test]
fn batches_preflight_single_roots_once_and_multi_roots_before_allocation() {
    TEST_ASSERTION_PREFLIGHT_COUNT.set(0);
    let (kb, ids) = KnowledgeBase::from_compiled_batch(vec![(
        compile_surface("dog(Rex)."),
        "singleton".into(),
    )])
    .unwrap();
    assert_eq!(TEST_ASSERTION_PREFLIGHT_COUNT.get(), 1);
    assert_eq!(ids.len(), 1);
    assert_eq!(ids[0].len(), 1);

    TEST_ASSERTION_PREFLIGHT_COUNT.set(0);
    kb.assert_compiled_batch(vec![(compile_surface("cat(Bel)."), "singleton".into())])
        .unwrap();
    assert_eq!(TEST_ASSERTION_PREFLIGHT_COUNT.get(), 1);

    TEST_ASSERTION_PREFLIGHT_COUNT.set(0);
    kb.assert_compiled_batch(vec![(
        compile_surface("bird(Ara). mouse(Bob)."),
        "multi".into(),
    )])
    .unwrap();
    assert_eq!(
        TEST_ASSERTION_PREFLIGHT_COUNT.get(),
        3,
        "the complete statement and each independently allocated root are checked"
    );

    let next = kb.next_fact_id().unwrap();
    TEST_ASSERTION_PREFLIGHT_COUNT.set(0);
    let bad = compile_surface("dog(Phantom). cat(exactly 1 cat).");
    let error = kb
        .assert_compiled_batch(vec![(bad, "query-only late root".into())])
        .unwrap_err();
    assert!(error.to_string().contains("query-only"), "{error}");
    assert_eq!(
        TEST_ASSERTION_PREFLIGHT_COUNT.get(),
        1,
        "late structural failure must precede every root assertion"
    );
    assert_eq!(kb.next_fact_id().unwrap(), next);
    assert!(query_false(&kb, compile_surface("dog(Phantom).")));
    assert!(query(&kb, compile_surface("dog(Rex).")));
}

#[test]
fn refused_candidates_are_discarded_without_registry_replay() {
    for ingress in ["single", "preassigned", "batch", "fresh"] {
        let kb = new_kb();
        let setup = ["derived_only(\"fit\").", "dog(Rex)."];
        for text in setup {
            assert_buf(&kb, compile_surface(text));
        }
        let next_id = kb.next_fact_id().unwrap();
        let before = kb.active_typed_facts().unwrap();
        let records = kb.list_assertion_records().unwrap();
        TEST_REBUILD_COUNT.set(0);
        let bad = compile_surface("dog(Phantom). fit(Phantom).");
        assert!(bad.roots.len() > 1, "exercise a late-root failure");
        match ingress {
            "single" => {
                kb.assert_fact(bad, "refused".into()).unwrap_err();
            }
            "preassigned" => {
                kb.assert_fact_with_id(bad, "refused".into(), next_id)
                    .unwrap_err();
            }
            "batch" => {
                kb.assert_compiled_batch(vec![(bad, "refused".into())])
                    .unwrap_err();
            }
            "fresh" => {
                let mut statements = setup
                    .into_iter()
                    .map(|text| (compile_surface(text), text.into()))
                    .collect::<Vec<_>>();
                statements.push((bad, "refused".into()));
                assert!(KnowledgeBase::from_compiled_batch(statements).is_err());
            }
            _ => unreachable!(),
        }
        assert_eq!(
            TEST_REBUILD_COUNT.get(),
            0,
            "{ingress} replayed a doomed candidate"
        );
        assert_eq!(
            kb.next_fact_id().unwrap(),
            next_id,
            "{ingress} consumed a live ID"
        );
        assert_eq!(
            kb.active_typed_facts().unwrap(),
            before,
            "{ingress} leaked facts"
        );
        assert_eq!(
            kb.list_assertion_records().unwrap(),
            records,
            "{ingress} leaked records"
        );
        assert!(query_false(&kb, compile_surface("dog(Phantom).")));
        assert!(query(&kb, compile_surface("dog(Rex).")));
        let id = kb
            .assert_fact(compile_surface("cat(Bel)."), "accepted".into())
            .unwrap();
        assert_eq!(id, next_id);
        kb.retract_fact(id).unwrap();
        assert_eq!(
            TEST_REBUILD_COUNT.get(),
            1,
            "ordinary withdrawal still replays"
        );
    }
}

// ─── Multiple roots test ─────────────────────────────────────

#[test]
fn test_assert_multiple_roots() {
    let kb = new_kb();
    let mut nodes = Vec::new();
    let r1 = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let r2 = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("bob".into()),
            LogicalTerm::Unspecified,
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![r1, r2],
        },
    );

    assert!(query(&kb, make_query("alis", "gerku")));
    assert!(query(&kb, make_query("bob", "mlatu")));
}

// ─── Assertion atomicity (rebuild-on-failure) ────────────────

#[test]
fn multi_root_partial_failure_is_atomic() {
    // A 2-root assertion: root0 is a valid ground fact, root1 fails (a bare
    // disjunction ingests no fact and registers no rule → "no representable
    // content" Err). The whole assertion must roll back — root0's fact must NOT
    // survive, and no orphan FactRecord may be left behind.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let root0 = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("adam".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let g = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("zelda".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let m = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("zelda".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root1 = or(&mut nodes, g, m); // bare disjunction → process_assertion Err

    let result = kb.assert_fact_inner(
        LogicBuffer {
            nodes,
            roots: vec![root0, root1],
        },
        String::new(),
    );
    assert!(result.is_err(), "the assertion must fail on root1");
    assert!(
        query_false(&kb, make_query("adam", "gerku")),
        "root0's fact must be rolled back, not orphaned"
    );
    assert!(
        kb.list_facts_inner().unwrap().is_empty(),
        "a failed assertion must leave no FactRecord"
    );
}

#[test]
fn failed_assertion_does_not_leak_assertion_id() {
    // The error path must clear current_assertion_id; a stale id would
    // mis-attribute the NEXT assertion's rules in the rule-source citations.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let g = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("zelda".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let m = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("zelda".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let bad = or(&mut nodes, g, m);
    let result = kb.assert_fact_inner(
        LogicBuffer {
            nodes,
            roots: vec![bad],
        },
        String::new(),
    );
    assert!(result.is_err());
    assert!(
        kb.inner.borrow().current_assertion_id.is_none(),
        "current_assertion_id must be cleared after a failed assertion"
    );
}

#[test]
fn rebuild_preserves_user_arg_sorts() {
    // User-declared arg sorts (set_predicate_sorts) must survive a rebuild.
    let kb = new_kb();
    kb.set_predicate_sorts("gerku", vec!["animal".to_string(), String::new()]);
    // EVERY retraction takes the one rebuild path (the incremental branch was
    // retired 2026-08-01); a ForAll record makes the replay's sort
    // restoration the thing under test.
    let throwaway = assert_id(&kb, make_universal("foo", "bar"), "throwaway");
    assert_buf(&kb, make_assertion("adam", "gerku"));
    kb.retract_fact_inner(throwaway).unwrap(); // forces rebuild_inner

    let inner = kb.inner.borrow();
    let sig = inner
        .predicate_registry
        .get("gerku")
        .expect("gerku should be registered after rebuild");
    assert_eq!(
        sig.arg_sorts,
        vec!["animal".to_string(), String::new()],
        "user-declared arg sorts must survive a rebuild"
    );
}

// ─── Count quantifier test ───────────────────────────────────

#[test]
fn test_count_exact_match() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));

    // Count(x, 2, gerku(x, _)) → exactly 2 dogs
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = count(&mut nodes, "x", 2, body);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_count_mismatch() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // Count(x, 2, gerku(x, _)) → only 1 dog, not 2
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = count(&mut nodes, "x", 2, body);
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn raw_count_assertions_reject_before_state_or_id_mutation() {
    let kb = new_kb();
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = count(&mut nodes, "x", 2, body);
    let count_buffer = LogicBuffer {
        nodes,
        roots: vec![root],
    };

    let error = kb
        .assert_fact_inner(count_buffer.clone(), "count".to_string())
        .expect_err("CountNode must be query-only at raw assertion ingress");
    assert!(
        error.contains("query-only") && error.contains("cannot be asserted"),
        "the rejection must explain the contract: {error}"
    );
    assert_eq!(
        kb.count_witnesses(make_find_query("gerku")).unwrap(),
        0,
        "a rejected count must mint no entity or fact"
    );
    assert!(kb.list_facts_inner().unwrap().is_empty());
    assert_eq!(kb.next_fact_id().unwrap(), 0, "no id may be consumed");

    let replay_error = kb
        .assert_fact_with_id(count_buffer, "legacy count".to_string(), 41)
        .expect_err("preassigned/replay CountNode must fail closed");
    assert!(replay_error.contains("query-only"), "{replay_error}");
    assert_eq!(
        kb.next_fact_id().unwrap(),
        0,
        "a rejected preassigned id must not advance the allocator"
    );

    let id = assert_id(&kb, make_assertion("alis", "gerku"), "ordinary");
    assert_eq!(id, 0, "the first real assertion retains the first id");
    assert!(query(&kb, make_query("alis", "gerku")));
}

#[test]
fn asserted_count_classifier_respects_roots_opacity_and_cycles() {
    let nested = LogicBuffer {
        nodes: vec![
            LogicNode::Predicate(("gerku".to_string(), Vec::new())),
            LogicNode::CountNode(("x".to_string(), 1, 0)),
            LogicNode::NotNode(1),
        ],
        roots: vec![2],
    };
    assert!(contains_asserted_count_node(&nested));

    let mut ordinary_root = nested.clone();
    ordinary_root.roots = vec![0];
    assert!(
        !contains_asserted_count_node(&ordinary_root),
        "a sibling root's shared-arena count is unreachable and inert"
    );

    let opaque = LogicBuffer {
        nodes: vec![
            LogicNode::Predicate(("gerku".to_string(), Vec::new())),
            LogicNode::CountNode(("x".to_string(), 1, 0)),
            LogicNode::Predicate((
                format!(
                    "{}test",
                    nibli_types::abstraction::ABSTRACTION_MARKER_PREFIX
                ),
                vec![LogicalTerm::Constant("content".to_string())],
            )),
            LogicNode::AndNode((2, 1)),
        ],
        roots: vec![3],
    };
    assert!(
        !contains_asserted_count_node(&opaque),
        "a count inside opaque abstraction content is not asserted"
    );

    let cyclic = LogicBuffer {
        nodes: vec![LogicNode::NotNode(0)],
        roots: vec![0],
    };
    assert!(
        !contains_asserted_count_node(&cyclic),
        "untrusted cyclic buffers must terminate without inventing a count"
    );
}

#[test]
fn count_assumptions_are_rejected_without_mutating_the_real_kb() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = count(&mut nodes, "x", 1, body);
    let count_buffer = LogicBuffer {
        nodes,
        roots: vec![root],
    };

    let error = kb
        .with_assumptions(&[count_buffer], |_| ())
        .expect_err("an exact-count assumption is still an assertion into the snapshot");
    assert!(error.to_string().contains("query-only"), "{error}");
    assert!(
        query(&kb, make_query("alis", "gerku")),
        "failed hypothetical must leave the real KB unchanged"
    );
}

#[test]
fn count_content_inside_an_opaque_abstraction_does_not_join_the_outer_domain() {
    let kb = new_kb();

    // Valid v1 abstraction identity: event-kind + Predicate("p", []).
    let mut key = vec![0xa0, 0x10];
    key.extend_from_slice(&1_u64.to_be_bytes());
    key.push(b'p');
    key.extend_from_slice(&0_u64.to_be_bytes());
    let marker_relation = nibli_types::abstraction::encode_v1(&key);

    let nodes = vec![
        LogicNode::Predicate((
            "dog".to_string(),
            vec![
                LogicalTerm::Constant("Hidden".to_string()),
                LogicalTerm::Number(42.0),
            ],
        )),
        LogicNode::CountNode(("x".to_string(), 1, 0)),
        LogicNode::Predicate((
            marker_relation,
            vec![LogicalTerm::Constant("OpaqueRef".to_string())],
        )),
        LogicNode::AndNode((2, 1)),
    ];
    kb.assert_fact_inner(
        LogicBuffer {
            nodes,
            roots: vec![3],
        },
        "opaque count content".to_string(),
    )
    .expect("quoted count content must remain assertable");

    let inner = kb.inner.borrow();
    assert!(
        inner
            .known_entities
            .contains(&GroundTerm::Constant("OpaqueRef".to_string())),
        "the abstraction referent is outer-KB content"
    );
    assert!(
        !inner
            .known_entities
            .contains(&GroundTerm::Constant("Hidden".to_string())),
        "a quoted constant must not enter the outer quantifier domain"
    );
    assert!(
        !inner.known_numbers.contains(&42.0_f64.to_bits()),
        "a quoted number must not enter the outer quantifier domain"
    );
}

// ─── Compute builtin arithmetic tests ────────────────────────

#[test]
fn raw_compute_assertions_reject_in_fact_and_every_rule_position() {
    let direct = make_compute_query("product", 6.0, 2.0, 3.0);

    let antecedent = {
        let mut nodes = Vec::new();
        let compute = compute(
            &mut nodes,
            "greater",
            vec![
                LogicalTerm::Variable("x".to_string()),
                LogicalTerm::Number(0.0),
            ],
        );
        let head = pred(
            &mut nodes,
            "positive",
            vec![LogicalTerm::Variable("x".to_string())],
        );
        let not_compute = not(&mut nodes, compute);
        let implication = or(&mut nodes, not_compute, head);
        let root = forall(&mut nodes, "x", implication);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    };

    let naf_condition = {
        let mut nodes = Vec::new();
        let candidate = pred(
            &mut nodes,
            "candidate",
            vec![LogicalTerm::Variable("x".to_string())],
        );
        let compute = compute(
            &mut nodes,
            "greater",
            vec![
                LogicalTerm::Variable("x".to_string()),
                LogicalTerm::Number(0.0),
            ],
        );
        let not_compute = not(&mut nodes, compute);
        let rule_body = and(&mut nodes, candidate, not_compute);
        let head = pred(
            &mut nodes,
            "eligible",
            vec![LogicalTerm::Variable("x".to_string())],
        );
        let not_rule_body = not(&mut nodes, rule_body);
        let implication = or(&mut nodes, not_rule_body, head);
        let root = forall(&mut nodes, "x", implication);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    };

    let rule_head = {
        let mut nodes = Vec::new();
        let antecedent = pred(
            &mut nodes,
            "candidate",
            vec![LogicalTerm::Variable("x".to_string())],
        );
        let compute = compute(
            &mut nodes,
            "greater",
            vec![
                LogicalTerm::Variable("x".to_string()),
                LogicalTerm::Number(0.0),
            ],
        );
        let not_antecedent = not(&mut nodes, antecedent);
        let implication = or(&mut nodes, not_antecedent, compute);
        let root = forall(&mut nodes, "x", implication);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    };

    for (position, buffer) in [
        ("direct fact", direct.clone()),
        ("rule antecedent", antecedent),
        ("rule NAF condition", naf_condition),
        ("rule head", rule_head),
    ] {
        let kb = new_kb();
        let error = kb
            .assert_fact_inner(buffer, position.to_string())
            .unwrap_err();
        assert!(
            error.contains("query-only") && error.contains("cannot be asserted"),
            "{position} must fail with the compute assertion contract: {error}"
        );
        assert!(
            kb.list_facts_inner().unwrap().is_empty(),
            "{position} rejection must leave no registry record"
        );
        assert_eq!(
            kb.next_fact_id().unwrap(),
            0,
            "{position} rejection must not consume an assertion id"
        );
    }

    let kb = new_kb();
    let error = kb
        .assert_fact_with_id(direct, "persisted compute".to_string(), 41)
        .expect_err("preassigned/replay ComputeNode must fail closed");
    assert!(error.contains("query-only"), "{error}");
    assert_eq!(
        kb.next_fact_id().unwrap(),
        0,
        "a rejected preassigned id must not advance the allocator"
    );
    let id = assert_id(&kb, make_assertion("alis", "gerku"), "ordinary");
    assert_eq!(id, 0, "the first real assertion retains the first id");
}

#[test]
fn asserted_compute_classifier_respects_roots_opacity_and_cycles() {
    let nested = LogicBuffer {
        nodes: vec![
            LogicNode::ComputeNode(("product".to_string(), Vec::new())),
            LogicNode::NotNode(0),
        ],
        roots: vec![1],
    };
    assert!(contains_asserted_compute_node(&nested));

    let unreachable = LogicBuffer {
        nodes: vec![
            LogicNode::Predicate((
                "gerku".to_string(),
                vec![
                    LogicalTerm::Constant("alis".to_string()),
                    LogicalTerm::Unspecified,
                ],
            )),
            LogicNode::ComputeNode(("product".to_string(), Vec::new())),
        ],
        roots: vec![0],
    };
    assert!(
        !contains_asserted_compute_node(&unreachable),
        "a sibling root's shared-arena compute is unreachable and inert"
    );
    new_kb()
        .assert_fact_inner(unreachable, "unreachable compute".to_string())
        .expect("unreachable arena content must not reject an ordinary assertion");

    // Valid v1 abstraction identity: event-kind + Predicate("p", []).
    let mut key = vec![0xa0, 0x10];
    key.extend_from_slice(&1_u64.to_be_bytes());
    key.push(b'p');
    key.extend_from_slice(&0_u64.to_be_bytes());
    let marker_relation = nibli_types::abstraction::encode_v1(&key);
    let opaque = LogicBuffer {
        nodes: vec![
            LogicNode::ComputeNode(("product".to_string(), Vec::new())),
            LogicNode::Predicate((
                marker_relation,
                vec![LogicalTerm::Constant("OpaqueRef".to_string())],
            )),
            LogicNode::AndNode((1, 0)),
        ],
        roots: vec![2],
    };
    assert!(
        !contains_asserted_compute_node(&opaque),
        "compute inside opaque abstraction content is quoted, not asserted"
    );
    new_kb()
        .assert_fact_inner(opaque, "opaque compute content".to_string())
        .expect("quoted compute content must remain assertable");

    // A marker-looking predicate is not an opacity boundary until its full
    // versioned identity validates. Preflight must reject this malformed marker
    // before either the ordinary or preassigned-id allocator can advance, even
    // though the structural classifier alone conservatively treats its right
    // branch as quoted.
    let malformed_marker = LogicBuffer {
        nodes: vec![
            LogicNode::ComputeNode(("product".to_string(), Vec::new())),
            LogicNode::Predicate((
                "__abs_v1_short_00".to_string(),
                vec![LogicalTerm::Constant("FakeRef".to_string())],
            )),
            LogicNode::AndNode((1, 0)),
        ],
        roots: vec![2],
    };
    assert!(!contains_asserted_compute_node(&malformed_marker));
    let kb = new_kb();
    let error = kb
        .assert_fact_inner(malformed_marker.clone(), "malformed marker".to_string())
        .expect_err("a malformed marker must fail before it can hide compute");
    assert!(
        error.contains("malformed opaque-abstraction marker"),
        "{error}"
    );
    assert_eq!(kb.next_fact_id().unwrap(), 0);
    let replay_error = kb
        .assert_fact_with_id(malformed_marker, "malformed replay".to_string(), 41)
        .expect_err("a malformed replay marker must fail before id advancement");
    assert!(
        replay_error.contains("malformed opaque-abstraction marker"),
        "{replay_error}"
    );
    assert_eq!(kb.next_fact_id().unwrap(), 0);

    let cyclic = LogicBuffer {
        nodes: vec![LogicNode::NotNode(0)],
        roots: vec![0],
    };
    assert!(
        !contains_asserted_compute_node(&cyclic),
        "untrusted cyclic buffers must terminate without inventing compute content"
    );
}

#[test]
fn test_compute_pilji_correct() {
    let kb = new_kb();
    let buf = make_compute_query("product", 6.0, 2.0, 3.0);
    assert!(query(&kb, buf));
}

#[test]
fn test_compute_pilji_incorrect() {
    let kb = new_kb();
    let buf = make_compute_query("product", 7.0, 2.0, 3.0);
    assert!(query_false(&kb, buf));
}

#[test]
fn test_compute_sumji_correct() {
    let kb = new_kb();
    let buf = make_compute_query("sum", 5.0, 2.0, 3.0);
    assert!(query(&kb, buf));
}

#[test]
fn test_compute_sumji_incorrect() {
    let kb = new_kb();
    let buf = make_compute_query("sum", 6.0, 2.0, 3.0);
    assert!(query_false(&kb, buf));
}

#[test]
fn test_compute_dilcu_correct() {
    let kb = new_kb();
    let buf = make_compute_query("quotient", 2.0, 6.0, 3.0);
    assert!(query(&kb, buf));
}

#[test]
fn test_compute_dilcu_incorrect() {
    let kb = new_kb();
    let buf = make_compute_query("quotient", 3.0, 6.0, 3.0);
    assert!(query_false(&kb, buf));
}

// ─── Numerical comparison predicate tests ────────────────────

#[test]
fn test_greater_holds() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("greater", 5.0, 3.0)));
}

#[test]
fn test_greater_rejects_smaller() {
    let kb = new_kb();
    assert!(query_false(&kb, make_numeric_query("greater", 3.0, 5.0)));
}

#[test]
fn test_less_holds() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("less", 3.0, 5.0)));
}

#[test]
fn test_num_equal_holds() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("num_equal", 5.0, 5.0)));
}

#[test]
fn test_num_equal_rejects_unequal() {
    let kb = new_kb();
    assert!(query_false(&kb, make_numeric_query("num_equal", 5.0, 3.0)));
}

// ─── Assert fact with various term types ──────────────────────

#[test]
fn test_assert_fact_with_number_terms() {
    let kb = new_kb();
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "product",
        vec![
            LogicalTerm::Number(6.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    // Query the same fact back
    let mut q_nodes = Vec::new();
    let q_root = pred(
        &mut q_nodes,
        "product",
        vec![
            LogicalTerm::Number(6.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
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
fn test_assert_fact_with_description_terms() {
    let kb = new_kb();
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Description("some_dog".to_string()),
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    // Query back
    let mut q_nodes = Vec::new();
    let q_root = pred(
        &mut q_nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Description("some_dog".to_string()),
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

/// Kills kb.rs `replace match guard subs.contains_key(v.as_str()) with false
/// in register_ground_material_conditional`. The guard peels a SKOLEMIZED
/// root ∃ so the conditional under it registers as a rule. The KR front-end
/// distributes ∃-closure per operand (the compiled root is an And whose Or
/// conjunct sits at the top level), so the peel only fires on RAW-FOL
/// buffers — `assert_fact` is a public buffer API, and this is exactly the
/// shape: ∃x.(goes(x) → eats(x)). Under the mutant the ∃ never peels: no
/// rule registers AND nothing was collected, so the assertion is wrongly
/// rejected as having no representable content — and the chained entailment
/// below is lost.
#[test]
fn skolemized_root_exists_over_conditional_registers_and_chains() {
    let kb = new_kb();
    let mut nodes = Vec::new();
    let goes = pred(
        &mut nodes,
        "goes",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let eats = pred(
        &mut nodes,
        "eats",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let n_goes = not(&mut nodes, goes);
    let cond = or(&mut nodes, n_goes, eats);
    let root = exists(&mut nodes, "x", cond);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    // Everything goes (a bare prenex universal), so the ∃-witness goes,
    // hence — through the registered conditional — it eats.
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "goes",
        vec![
            LogicalTerm::Variable("_y0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = forall(&mut nodes, "_y0", body);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    assert!(
        query(&kb, make_find_query("eats")),
        "the ∃-scoped conditional must register and chain: something eats"
    );
}
