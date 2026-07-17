use super::*;

// ══════════════════════════════════════════════���════════════════════
// AGGREGATION TESTS
// ═════════���════════════════════════════���════════════════════════════

// THROWAWAY diagnostic repro for the find-path non-termination on event-decomposed
// cyclic rules. #[ignore]d so it never runs in CI. Default max_chain_depth → hangs.
// Used only to capture a stack sample; removed before commit.
// Event-decomposed find query: ∃x. ∃_ev0. gerku(_ev0) ∧ gerku_x1(_ev0, x)
// (what the real pipeline compiles `da gerku` into — NOT the flat make_find_query).
fn make_event_find_query(predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let p_type = pred(
        &mut nodes,
        predicate,
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let p_role = pred(
        &mut nodes,
        &format!("{}_x1", predicate),
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Variable("x".to_string()),
        ],
    );
    let p_and = and(&mut nodes, p_type, p_role);
    let inner = exists(&mut nodes, "_ev0", p_and);
    let root = exists(&mut nodes, "x", inner);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Regression: event-decomposed cyclic rules must NOT hang the witness search.
/// `gerku ⟺ danlu` is a relation-level cycle; each backward-chain step mints a
/// fresh dependent Skolem (`sk_5(rex)`, `sk_5(sk_2)`, …), so before the `cycle_key`
/// guard the raw `visited` set never matched and the search re-derived the relation
/// exponentially out to the depth horizon — a ~30-minute, 100%-CPU query-level DoS.
/// With `cycle_key`, the relation re-entry on a path is cut (`CycleCut`), so the
/// enumeration is incomplete and find/count REFUSE with `Err` (consistent with the
/// depth/cycle UNDERCOUNT contract). Runs on a watchdog thread at DEFAULT depth (so
/// it exercises the real cycle, not a shallow depth-horizon cutoff) and FAILS rather
/// than hangs CI if the guard ever regresses.
#[test]
fn test_find_event_cycle_terminates_and_errs() {
    use std::sync::mpsc;
    use std::time::Duration;
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let kb = new_kb();
        assert_buf(&kb, make_event_universal("gerku", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "gerku"));
        assert_buf(&kb, make_event_assertion("rex", "mlatu"));
        let find_err = kb.query_find(make_event_find_query("gerku")).is_err();
        let count_err = kb.count_witnesses(make_event_find_query("gerku")).is_err();
        let _ = tx.send(find_err && count_err);
    });
    match rx.recv_timeout(Duration::from_secs(20)) {
        Ok(true) => {}
        Ok(false) => panic!("cyclic event-decomposed find/count must refuse (Err)"),
        Err(_) => panic!(
            "cyclic event-decomposed find did NOT terminate within 20s — \
             the cycle_key guard is not cutting the relation-level cycle"
        ),
    }
}

#[test]
fn test_count_witnesses_zero() {
    let kb = new_kb();
    let count = kb.count_witnesses(make_find_query("gerku")).unwrap();
    assert_eq!(count, 0, "no gerku asserted → 0 witnesses");
}

#[test]
fn test_count_witnesses_multiple() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    assert_buf(&kb, make_assertion("carol", "gerku"));
    let count = kb.count_witnesses(make_find_query("gerku")).unwrap();
    assert!(count >= 3, "at least 3 gerku witnesses, got {}", count);
}

#[test]
fn test_aggregate_sum() {
    // Assert numeric facts: tenfa(2, zo'e), tenfa(3, zo'e), tenfa(5, zo'e)
    // Sum over x in ∃x. tenfa(x, zo'e) → 2+3+5 = 10
    let kb = new_kb();
    for val in [2.0, 3.0, 5.0] {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "exponential",
            vec![LogicalTerm::Number(val), LogicalTerm::Unspecified],
        );
        assert_buf(
            &kb,
            LogicBuffer {
                nodes,
                roots: vec![root],
            },
        );
    }
    // Build ∃x. tenfa(x, zo'e)
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "exponential",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };
    use nibli_types::logic::AggregateOp;
    let sum = kb.aggregate(buf, "x", AggregateOp::Sum).unwrap();
    assert_eq!(sum, Some(10.0), "sum of 2+3+5 should be 10");
}

#[test]
fn test_count_with_backward_chain() {
    // Rule: gerku → danlu. Assert gerku for 2 entities.
    // Count ∃x. danlu(x) should find at least 2 (+ existential-import Skolems).
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    let count = kb.count_witnesses(make_find_query("danlu")).unwrap();
    assert!(
        count >= 2,
        "at least 2 danlu witnesses via backward chain, got {}",
        count
    );
}

// ═══════════════════════════════════════════════════════════════════
// ITERATIVE DEEPENING TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_iterative_deepening_finds_shallow() {
    // Chain: gerku→danlu→jmive (depth 2). Should find proof.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(
        query(&kb, make_query("alis", "jmive")),
        "jmive(alis) should hold via 2-step chain"
    );
}

#[test]
fn test_iterative_deepening_returns_false_not_exceeded() {
    // Query something genuinely underivable → should be False, not ResourceExceeded.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let result = query_result(&kb, make_query("alis", "mlatu"));
    assert!(
        result.is_false(),
        "underivable predicate should return False, got {:?}",
        result
    );
}

#[test]
fn test_iterative_deepening_exceeds_max() {
    // Set max_chain_depth=2, chain of depth 3 → ResourceExceeded.
    let kb = new_kb();
    kb.inner.borrow_mut().max_chain_depth = 2;
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    assert_buf(&kb, make_universal("jmive", "xanlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let result = query_result(&kb, make_query("alis", "xanlu"));
    assert!(
        matches!(result, QueryResult::ResourceExceeded(ResourceKind::Depth)),
        "depth-3 chain with max_chain_depth=2 should exceed, got {:?}",
        result
    );
}

// ═══════════════════════════════════════════════════════════════════
// FIND/COUNT/AGGREGATE INCOMPLETENESS AT THE DEPTH/CYCLE HORIZON
// ═══════════════════════════════════════════════════════════════════

/// Build a `max_chain_depth=2` KB whose only `xanlu` witnesses (alis, bob) sit
/// behind a depth-3 rule chain — so every witness leaf hits ResourceExceeded(Depth).
fn kb_with_witnesses_beyond_depth() -> KnowledgeBase {
    let kb = new_kb();
    kb.inner.borrow_mut().max_chain_depth = 2;
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    assert_buf(&kb, make_universal("jmive", "xanlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    kb
}

#[test]
fn test_count_undercount_at_depth_horizon_errs() {
    // Pre-fix: `count_witnesses` returned a confident wrong count (the witnesses were
    // silently dropped at the depth horizon). Now it REFUSES with an Err rather than
    // undercount.
    let kb = kb_with_witnesses_beyond_depth();
    assert!(
        kb.count_witnesses(make_find_query("xanlu")).is_err(),
        "count must refuse (Err) when a witness exceeds the depth budget, not undercount"
    );
}

#[test]
fn test_find_at_depth_horizon_errs() {
    let kb = kb_with_witnesses_beyond_depth();
    assert!(
        kb.query_find(make_find_query("xanlu")).is_err(),
        "find must refuse (Err) an incomplete witness enumeration"
    );
}

#[test]
fn test_aggregate_at_depth_horizon_errs() {
    // aggregate funnels through query_find, so it inherits the incompleteness refusal
    // before it ever sums — no confident under-sum.
    let kb = kb_with_witnesses_beyond_depth();
    assert!(
        kb.aggregate(
            make_find_query("xanlu"),
            "x",
            nibli_types::logic::AggregateOp::Sum,
        )
        .is_err(),
        "aggregate must refuse (Err) when the witness enumeration is incomplete"
    );
}

#[test]
fn test_count_within_budget_is_exact() {
    // Control: the SAME depth-3 chain is within the default budget (10), so the
    // enumeration is complete and count is exact — no false-positive incompleteness.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    assert_buf(&kb, make_universal("jmive", "xanlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    let count = kb
        .count_witnesses(make_find_query("xanlu"))
        .expect("within-budget enumeration must succeed");
    assert!(
        count >= 2,
        "both witnesses are within the depth budget, got {count}"
    );
}

#[test]
fn test_find_cycle_cut_errs() {
    // A cyclic rule (gerku ⟸ danlu ⟸ gerku) makes a witness leaf hit CycleCut, which
    // is incompleteness (the search was cut), not a genuine absence → find refuses.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "gerku"));
    assert_buf(&kb, make_assertion("rex", "mlatu")); // a domain member to enumerate
    assert!(
        kb.query_find(make_find_query("gerku")).is_err(),
        "a cycle-cut witness leaf must make find refuse (Err), not silently drop"
    );
}

// ═══════════════════════════════════════════════════════════════════
// ARGUMENT-POSITION INDEX TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_arg_index_populated() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    let inner = kb.inner.borrow();
    // Index should have entries for (gerku, 0) and (gerku, 1).
    let key0 = ("gerku".to_string(), 0usize);
    assert!(
        inner.arg_position_index.contains_key(&key0),
        "index should have (gerku, 0)"
    );
    let values_at_0 = &inner.arg_position_index[&key0];
    // Position 0 should have entries for "alis" and "bob".
    assert!(
        values_at_0.contains_key(&GroundTerm::Constant("alis".to_string())),
        "index should map alis at position 0"
    );
    assert!(
        values_at_0.contains_key(&GroundTerm::Constant("bob".to_string())),
        "index should map bob at position 0"
    );
}

#[test]
fn arg_index_dedups_reingested_fact() {
    // Re-ingesting an Eq-identical ground fact (e.g. compute auto-assert firing
    // on every query) must NOT append a duplicate to the arg_position_index leaf.
    // Duplicates would grow the index unboundedly AND inflate
    // bind_join_vars_from_index's `matching.len() == 1` uniqueness check,
    // suppressing a valid join binding. The store (a HashSet) already dedups; the
    // index now stays consistent with it. RED pre-fix (leaf len would be 2).
    let kb = new_kb();
    assert_buf(&kb, make_assertion("rex", "gerku"));
    assert_buf(&kb, make_assertion("rex", "gerku")); // identical fact, re-ingested
    let inner = kb.inner.borrow();
    let leaf = &inner.arg_position_index[&("gerku".to_string(), 0)]
        [&GroundTerm::Constant("rex".to_string())];
    assert_eq!(
        leaf.len(),
        1,
        "re-ingesting an identical fact must not duplicate its arg-index entry"
    );
}

#[test]
fn test_arg_index_cleared_on_reset() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    {
        let inner = kb.inner.borrow();
        assert!(!inner.arg_position_index.is_empty());
    }
    kb.reset().unwrap();
    {
        let inner = kb.inner.borrow();
        assert!(
            inner.arg_position_index.is_empty(),
            "arg index should be empty after reset"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════
// INCREMENTAL TRUTH MAINTENANCE TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_incremental_retract_fact() {
    let kb = new_kb();
    let id1 = assert_id(&kb, make_assertion("alis", "gerku"), "alis gerku");
    let _id2 = assert_id(&kb, make_assertion("bob", "gerku"), "bob gerku");
    let _id3 = assert_id(&kb, make_assertion("carol", "mlatu"), "carol mlatu");

    assert!(query(&kb, make_query("alis", "gerku")));
    assert!(query(&kb, make_query("bob", "gerku")));
    assert!(query(&kb, make_query("carol", "mlatu")));

    // Retract alis's fact.
    kb.retract_fact_inner(id1).unwrap();

    assert!(
        query_false(&kb, make_query("alis", "gerku")),
        "alis gerku should be gone after retraction"
    );
    assert!(
        query(&kb, make_query("bob", "gerku")),
        "bob gerku should survive"
    );
    assert!(
        query(&kb, make_query("carol", "mlatu")),
        "carol mlatu should survive"
    );
}

#[test]
fn test_incremental_retract_rule() {
    let kb = new_kb();
    let rule_id = assert_id(&kb, make_universal("gerku", "danlu"), "rule");
    assert_buf(&kb, make_assertion("alis", "gerku"));

    assert!(
        query(&kb, make_query("alis", "danlu")),
        "danlu(alis) should hold via rule"
    );

    // Retract the rule.
    kb.retract_fact_inner(rule_id).unwrap();

    assert!(
        query_false(&kb, make_query("alis", "danlu")),
        "danlu(alis) should be gone after retracting the rule"
    );
    assert!(
        query(&kb, make_query("alis", "gerku")),
        "base fact gerku(alis) should survive"
    );
}

#[test]
fn test_incremental_retract_equals() {
    let kb = new_kb();
    let equals_id = assert_id(&kb, make_equals("alis", "bob"), "equals");
    assert_buf(&kb, make_assertion("alis", "gerku"));

    assert!(
        query(&kb, make_query("bob", "gerku")),
        "gerku(bob) should hold via du(alis, bob)"
    );

    // Retract the du fact.
    kb.retract_fact_inner(equals_id).unwrap();

    assert!(
        query_false(&kb, make_query("bob", "gerku")),
        "gerku(bob) should be gone after retracting du"
    );
    assert!(
        query(&kb, make_query("alis", "gerku")),
        "gerku(alis) should survive"
    );
}

// ═══════════════════════════════════════════════════════════════════
// CONTRADICTIONS SCAN TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_contradictions_none() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let violations = kb.check_contradictions();
    assert!(violations.is_empty(), "no contradictions expected");
}

#[test]
fn test_contradictions_integrity_violation() {
    let kb = new_kb();
    kb.register_constraint(
        "no-gerku-and-mlatu".into(),
        vec![
            constraint_fact("gerku", "adam"),
            constraint_fact("mlatu", "adam"),
        ],
    );
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert_buf(&kb, make_assertion("adam", "mlatu"));
    let violations = kb.check_contradictions();
    assert!(!violations.is_empty(), "should detect integrity violation");
    assert!(
        violations[0].contains("Integrity violation"),
        "violation message should mention integrity: {}",
        violations[0]
    );
}

#[test]
fn test_contradictions_arity_inconsistency() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku")); // arity 2
    // Assert gerku with arity 1 (single arg).
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Constant("bob".to_string())],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    let violations = kb.check_contradictions();
    assert!(
        violations.iter().any(|v| v.contains("Arity inconsistency")),
        "should detect arity mismatch: {:?}",
        violations
    );
}

#[test]
fn check_contradictions_order_is_deterministic() {
    // §4 (negation) iterates the `negative_facts` HashSet, so the violation
    // order is hasher-seed dependent without the global sort. Two FRESH KB
    // instances (each std HashSet gets its own RandomState in-process) with the
    // SAME multi-contradiction content — asserted in opposite orders — must
    // return byte-identical ordered violations.
    let preds = ["gerku", "mlatu", "cipni", "finpe", "since", "cribe"];
    let build = |rev: bool| {
        let kb = new_kb();
        let order: Vec<&str> = if rev {
            preds.iter().rev().copied().collect()
        } else {
            preds.to_vec()
        };
        for p in order {
            assert_id(&kb, make_negated_assertion("adam", p), "na");
            assert_id(&kb, make_assertion("adam", p), "pos");
        }
        kb
    };
    let v1 = build(false).check_contradictions();
    let v2 = build(true).check_contradictions();
    assert_eq!(
        v1.len(),
        preds.len(),
        "one negation contradiction per predicate: {v1:?}"
    );
    assert_eq!(
        v1, v2,
        "check_contradictions order must be deterministic across fresh KB instances"
    );
}

// ═══════════════════════════════════════════════════════════════════
// SELECTIVE FORWARD CHAINING TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_forward_chain_basic() {
    // Rule: gerku→danlu (forward). Assert gerku(alis) → danlu(alis) auto-derived.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    kb.set_rule_forward("danlu", true);
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // danlu(alis) should be directly in the fact store (forward-derived),
    // not just backward-chainable.
    let inner = kb.inner.borrow();
    let danlu_facts = inner.fact_store.lookup_predicate("danlu");
    assert!(
        danlu_facts.is_some() && !danlu_facts.unwrap().is_empty(),
        "danlu(alis) should be forward-derived into the fact store"
    );
}

#[test]
fn test_forward_chain_no_flag() {
    // Same rule without forward flag → danlu(alis) NOT in fact store.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    // Do NOT call set_rule_forward.
    assert_buf(&kb, make_assertion("alis", "gerku"));

    let inner = kb.inner.borrow();
    let danlu_facts = inner.fact_store.lookup_predicate("danlu");
    // danlu should not be forward-derived (only available via backward chain).
    let has_danlu_alis = danlu_facts
        .map(|set| {
            set.iter().any(|f| {
                f.inner().relation == "danlu"
                    && f.inner().args.first() == Some(&GroundTerm::Constant("alis".to_string()))
            })
        })
        .unwrap_or(false);
    assert!(
        !has_danlu_alis,
        "danlu(alis) should NOT be forward-derived without forward flag"
    );
}

#[test]
fn test_forward_chain_transitive() {
    // Chain: gerku→danlu (forward), danlu→jmive (forward).
    // Assert gerku(alis) → danlu(alis) auto-derived → jmive(alis) auto-derived.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    kb.set_rule_forward("danlu", true);
    kb.set_rule_forward("jmive", true);
    assert_buf(&kb, make_assertion("alis", "gerku"));

    let inner = kb.inner.borrow();
    let jmive_facts = inner.fact_store.lookup_predicate("jmive");
    assert!(
        jmive_facts.is_some() && !jmive_facts.unwrap().is_empty(),
        "jmive(alis) should be transitively forward-derived"
    );
}

#[test]
fn test_forward_chain_skipped_during_rebuild() {
    // Forward chain should not fire during retraction rebuild.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    kb.set_rule_forward("danlu", true);
    let id = assert_id(&kb, make_assertion("alis", "gerku"), "gerku");

    // danlu(alis) should be forward-derived.
    assert!(query(&kb, make_query("alis", "danlu")));

    // Retract gerku(alis) — triggers rebuild. Forward chains should not re-fire.
    kb.retract_fact_inner(id).unwrap();

    // After retraction, danlu(alis) should NOT hold.
    assert!(
        query_false(&kb, make_query("alis", "danlu")),
        "danlu(alis) should be gone after retracting gerku(alis)"
    );
}

#[test]
fn test_forward_chain_naf_rule_kept_backward_only() {
    // A forward rule with a negation-as-failure condition must stay BACKWARD-ONLY:
    // forward chaining + NAF has no truth maintenance (a forward-derived conclusion
    // would go stale when the negated dependency flips). Backward chaining stays
    // sound — it re-evaluates ¬xange at query time. RED before the fail-closed fix:
    // danlu(alis) was forward-derived and survived the later xange(alis) assertion.
    let kb = new_kb();
    assert_buf(&kb, make_universal_naf("gerku", "xange", "danlu"));

    // Sanity: the test buffer really produces a negated-condition rule.
    {
        let inner = kb.inner.borrow();
        let rules = inner.universal_rules.get("danlu").expect("rule registered");
        assert!(
            rules
                .iter()
                .any(|r| !r.negated_condition_indices.is_empty()),
            "test buffer must produce a negated-condition rule"
        );
    }

    // Attempt to forward-enable: the NAF rule must be REFUSED (stays backward-only).
    kb.set_rule_forward("danlu", true);
    {
        let inner = kb.inner.borrow();
        let rules = inner.universal_rules.get("danlu").unwrap();
        assert!(
            rules.iter().all(|r| !r.forward),
            "a NAF rule must not be forward-enabled"
        );
    }

    // Assert gerku(alis): danlu(alis) must NOT be forward-derived into the store.
    assert_buf(&kb, make_assertion("alis", "gerku"));
    {
        let inner = kb.inner.borrow();
        let has_danlu_alis = inner
            .fact_store
            .lookup_predicate("danlu")
            .map(|set| {
                set.iter().any(|f| {
                    f.inner().relation == "danlu"
                        && f.inner().args.first() == Some(&GroundTerm::Constant("alis".to_string()))
                })
            })
            .unwrap_or(false);
        assert!(
            !has_danlu_alis,
            "a NAF rule must not forward-derive danlu(alis)"
        );
    }

    // Backward chaining is sound: while xange(alis) is absent, ¬xange holds and
    // gerku(alis) holds → danlu(alis) is TRUE on demand.
    assert!(
        query(&kb, make_query("alis", "danlu")),
        "backward chaining derives danlu while xange is absent"
    );

    // Flip the negated dependency: assert xange(alis). Backward chaining
    // re-evaluates ¬xange → danlu(alis) must now be FALSE (no stale fact).
    assert_buf(&kb, make_assertion("alis", "xange"));
    assert!(
        query_false(&kb, make_query("alis", "danlu")),
        "backward chaining re-evaluates ¬xange — danlu must no longer hold"
    );
}

#[test]
fn test_forward_chain_positive_still_enabled() {
    // The fail-closed guard restricts ONLY NAF rules — a positive (negation-free)
    // forward rule is still enabled and forward-derives eagerly.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    kb.set_rule_forward("danlu", true);
    {
        let inner = kb.inner.borrow();
        let rules = inner.universal_rules.get("danlu").unwrap();
        assert!(
            rules.iter().all(|r| r.forward),
            "a positive (negation-free) rule must be forward-enabled"
        );
    }
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let inner = kb.inner.borrow();
    let danlu_facts = inner.fact_store.lookup_predicate("danlu");
    assert!(
        danlu_facts.is_some() && !danlu_facts.unwrap().is_empty(),
        "a positive forward rule should forward-derive danlu(alis)"
    );
}

// ═══════════════════════════════════════════════════════════════════
// TABLING / PERSISTENT MEMOIZATION TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_tabling_cache_survives_queries() {
    // Query P(a) twice — second should use cached result (same answer).
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // First query — populates cache.
    assert!(query(&kb, make_query("alis", "danlu")));
    // Second query — uses cache (same result).
    assert!(query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_tabling_invalidated_on_assert() {
    // Query P(a) → False, assert P(a), query again → True.
    let kb = new_kb();
    assert!(query_false(&kb, make_query("alis", "gerku")));
    // Cache now has gerku(alis) → False.
    assert_buf(&kb, make_assertion("alis", "gerku"));
    // After assertion, cache should be invalidated.
    assert!(
        query(&kb, make_query("alis", "gerku")),
        "gerku(alis) should be True after assertion (cache invalidated)"
    );
}

#[test]
fn test_tabling_invalidated_on_retract() {
    // Assert P(a), query → True, retract, query → False.
    let kb = new_kb();
    let id = assert_id(&kb, make_assertion("alis", "gerku"), "gerku");
    assert!(query(&kb, make_query("alis", "gerku")));
    // Cache now has gerku(alis) → True.
    kb.retract_fact_inner(id).unwrap();
    // After retraction, cache should be invalidated.
    assert!(
        query_false(&kb, make_query("alis", "gerku")),
        "gerku(alis) should be False after retraction (cache invalidated)"
    );
}

// ═══════════════════════════════════════════════════════════════════
// DEFEASIBLE / PRIORITIZED RULES TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_priority_higher_rule_wins() {
    // Two rules for danlu: gerku→danlu (priority 0) and mlatu→danlu (priority 10).
    // Assert both gerku(alis) and mlatu(alis). Both rules match.
    // The higher-priority rule (mlatu→danlu) should be tried first.
    // Since both succeed, the result is the same — but we verify the mechanism works.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("mlatu", "danlu"));
    kb.set_rule_priority("danlu", 10); // Both danlu rules get priority 10.
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("alis", "mlatu"));
    assert!(query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_priority_default_zero() {
    // Rules without explicit priority should default to 0.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    let inner = kb.inner.borrow();
    if let Some(rules) = inner.universal_rules.get("danlu") {
        for rule in rules {
            assert_eq!(rule.priority, 0, "default priority should be 0");
        }
    }
}

#[test]
fn test_priority_set_and_query() {
    // Set priority for a specific predicate's rules.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    kb.set_rule_priority("danlu", 5);
    let inner = kb.inner.borrow();
    if let Some(rules) = inner.universal_rules.get("danlu") {
        for rule in rules {
            assert_eq!(rule.priority, 5, "priority should be 5 after set");
        }
    }
}

#[test]
fn matching_rules_bucket_stays_descending_after_late_registration() {
    // INVARIANT: universal_rules buckets are kept sorted by descending priority
    // at mutation time, so the backward-chain read path (matching_rules_typed)
    // can borrow a pre-sorted slice without cloning or re-sorting. A
    // low-priority rule registered AFTER a high-priority rule for the same
    // conclusion must land AFTER it. (The suite-wide debug_assert in
    // matching_rules_typed is the broader net; this pins one explicit case.)
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    kb.set_rule_priority("danlu", 10); // the dog→danlu rule now has priority 10
    assert_buf(&kb, make_universal("mlatu", "danlu")); // new rule, default priority 0
    let inner = kb.inner.borrow();
    let bucket = inner
        .universal_rules
        .get("danlu")
        .expect("danlu bucket exists");
    assert_eq!(
        bucket.len(),
        2,
        "both rules concluding danlu are in the bucket"
    );
    assert!(
        bucket.is_sorted_by_key(|r| std::cmp::Reverse(r.priority)),
        "bucket must stay descending-sorted: {:?}",
        bucket.iter().map(|r| r.priority).collect::<Vec<_>>()
    );
    assert_eq!(bucket[0].priority, 10, "high-priority rule comes first");
    assert_eq!(bucket[1].priority, 0, "late low-priority rule comes last");
}

// ═══════════════════════════════════════════════════════════════════
// SORTED LOGIC / TYPE HIERARCHY TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_sort_valid_entity() {
    // person ⊂ animal, adam: person, gerku expects (animal, _).
    // adam is compatible with animal via subsort → no warning.
    let kb = new_kb();
    kb.declare_subsort("person", "animal");
    kb.declare_entity_sort("adam", "person");
    kb.set_predicate_sorts("gerku", vec!["animal".into(), String::new()]);
    assert_buf(&kb, make_assertion("adam", "gerku"));
    // Should succeed without sort warning (person ⊂ animal).
    assert!(query(&kb, make_query("adam", "gerku")));
}

#[test]
fn test_sort_invalid_entity() {
    // adam: number_sort, gerku expects (animal, _).
    // number_sort is NOT a subsort of animal → sort warning printed.
    let kb = new_kb();
    kb.declare_entity_sort("adam", "number_sort");
    kb.set_predicate_sorts("gerku", vec!["animal".into(), String::new()]);
    // This should print a sort warning but still insert (permissive mode).
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert!(query(&kb, make_query("adam", "gerku")));
}

#[test]
fn test_sort_hierarchy_transitive() {
    // person ⊂ animal ⊂ entity.
    // adam: person. Predicate expects entity.
    // person is transitively compatible with entity.
    let kb = new_kb();
    kb.declare_subsort("person", "animal");
    kb.declare_subsort("animal", "entity");
    kb.declare_entity_sort("adam", "person");
    kb.set_predicate_sorts("gerku", vec!["entity".into(), String::new()]);
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert!(query(&kb, make_query("adam", "gerku")));
}

#[test]
fn test_sort_unset_no_check() {
    // No sorts declared → no checking (fully backward compatible).
    let kb = new_kb();
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert!(query(&kb, make_query("adam", "gerku")));
    // No sort warning — sorts not declared.
}

/// Cross-depth tabling: a 3-step transitive chain must resolve True across
/// iterative-deepening passes. Passes 1 and 2 return ResourceExceeded(Depth);
/// because the cache write is gated to definitive (True/False) results only,
/// those Depth verdicts are never cached, so pass 3 re-derives the chain and
/// returns True. Before the gating fix, persisting a stale Depth across passes
/// would poison pass 3 and the query would wrongly return ResourceExceeded.
#[test]
fn test_tabling_cross_depth_persistence() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    assert_buf(&kb, make_universal("jmive", "xanlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(
        query(&kb, make_query("alis", "xanlu")),
        "xanlu(alis) should hold via a 3-step chain across depth iterations"
    );
    // A fresh query (entry clear) must remain True.
    assert!(
        query(&kb, make_query("alis", "xanlu")),
        "re-query of xanlu(alis) should remain True"
    );
}

/// A cycle-cut must not poison a sibling goal within a single query. Proving the
/// left conjunct a(alis) first explores the cyclic rule `f→a → a→f → a` (a on the
/// visited stack) which yields Unknown(CycleCut) for f(alis); a is then proved via
/// seed→a. The right conjunct f(alis) must NOT read a cached CycleCut — it is
/// derivable via a→f. The cyclic rule f→a is registered before the resolver seed→a
/// so the cyclic branch is tried first. Before the gating fix the cached CycleCut
/// poisoned the second conjunct and And(a, f) came back not-True.
#[test]
fn test_cycle_cut_does_not_poison_sibling_conjunct() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "seed"));
    assert_buf(&kb, make_universal("f", "a")); // cyclic rule registered FIRST
    assert_buf(&kb, make_universal("a", "f"));
    assert_buf(&kb, make_universal("seed", "a")); // resolver registered AFTER

    let mut nodes = Vec::new();
    let left = pred(
        &mut nodes,
        "a",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let right = pred(
        &mut nodes,
        "f",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = and(&mut nodes, left, right);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes,
                roots: vec![root],
            }
        ),
        "And(a(alis), f(alis)) should hold; sibling f must not read a poisoned CycleCut"
    );
}

/// A fact true only via a du-equivalent, RULE-DERIVED variant must get an honest
/// EqualitySubstitution proof step — not a holds:true "unknown" leaf with no
/// derivation. The ground material conditional `seed(adam) -> danlu(adam)` has a
/// GROUND conclusion, so `danlu(betty)` does not unify with it and routes through the
/// du-equivalence fallback that the traced path previously lacked.
#[test]
fn test_proof_trace_equals_substitution_rule_derived() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("adam", "seed"));

    // Ground material conditional: Or(Not(seed(adam)), danlu(adam)) — a ground
    // conclusion danlu(adam), auto-registered as a zero-variable rule.
    let mut nodes = Vec::new();
    let seed_adam = pred(
        &mut nodes,
        "seed",
        vec![
            LogicalTerm::Constant("adam".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let danlu_adam = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Constant("adam".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_seed = not(&mut nodes, seed_adam);
    let cond = or(&mut nodes, neg_seed, danlu_adam);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![cond],
        },
    );
    assert_buf(&kb, make_equals("adam", "betty"));

    // Sanity: danlu(betty) holds (untraced) via the du-equivalence fallback over the
    // rule-derived danlu(adam).
    assert!(
        query(&kb, make_query("betty", "danlu")),
        "danlu(betty) should hold via rule-derived danlu(adam) + adam du betty"
    );

    let (result, trace) = query_with_proof(&kb, make_query("betty", "danlu"));
    assert!(result, "traced verdict for danlu(betty) should be True");
    assert!(
        trace
            .steps
            .iter()
            .any(|s| matches!(s.rule, ProofRule::EqualitySubstitution { .. }) && s.holds),
        "trace should contain a holds:true EqualitySubstitution step"
    );
    assert!(
        !trace.steps.iter().any(|s| {
            matches!(&s.rule, ProofRule::PredicateCheck { method: src, .. } if src == "unknown")
                && s.holds
        }),
        "trace must not contain a holds:true PredicateCheck(\"unknown\", ...) leaf"
    );
    assert!(
        trace.steps[trace.root as usize].holds,
        "root step holds must match the True verdict"
    );
}

/// du-equivalent ASSERTED facts must render as EqualitySubstitution, not Asserted.
/// xukmi(coumadin) is DIRECTLY asserted; coumadin du warfarin. Querying
/// xukmi(warfarin) holds only by substituting warfarin → coumadin through the du
/// equality — the queried fact was never asserted, so labeling it Asserted hides
/// the substitution. The honest proof is EqualitySubstitution whose child is the
/// genuinely-asserted xukmi(coumadin). RED pre-fix (the trace had a bare
/// Asserted(xukmi(warfarin)) and no EqualitySubstitution).
#[test]
fn test_proof_trace_equals_substitution_directly_asserted() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("coumadin", "xukmi"));
    assert_buf(&kb, make_equals("coumadin", "warfarin"));

    assert!(
        query(&kb, make_query("warfarin", "xukmi")),
        "xukmi(warfarin) should hold via asserted xukmi(coumadin) + coumadin du warfarin"
    );

    let (result, trace) = query_with_proof(&kb, make_query("warfarin", "xukmi"));
    assert!(result, "traced verdict for xukmi(warfarin) should be True");
    // Honest: a holds:true EqualitySubstitution step is present.
    assert!(
        trace
            .steps
            .iter()
            .any(|s| matches!(s.rule, ProofRule::EqualitySubstitution { .. }) && s.holds),
        "trace should contain a holds:true EqualitySubstitution step for the asserted-via-du case"
    );
    // Dishonest label gone: no Asserted step claims the QUERIED xukmi(warfarin)
    // fact was asserted (only xukmi(coumadin) genuinely was).
    assert!(
        !trace.steps.iter().any(|s| {
            matches!(&s.rule, ProofRule::Asserted { fact: d } if d.contains("warfarin") && d.contains("xukmi"))
        }),
        "no Asserted step may claim xukmi(warfarin) — it holds only via substitution"
    );
    // The substitution's child IS the genuinely-asserted xukmi(coumadin).
    assert!(
        trace.steps.iter().any(|s| {
            matches!(&s.rule, ProofRule::Asserted { fact: d } if d.contains("coumadin") && d.contains("xukmi"))
                && s.holds
        }),
        "the substitution's child must be the asserted xukmi(coumadin)"
    );
    assert!(
        trace.steps[trace.root as usize].holds,
        "root step holds must match the True verdict"
    );
}

// ═══════════════════════════════════════════════════════════════════
// DETERMINISM PINS (todo.md: witness/proof output ordering was
// HashSet-derived and varied with the process hasher seed)
// ═══════════════════════════════════════════════════════════════════

#[test]
fn find_witness_ordering_is_deterministic_across_kb_instances() {
    // Same facts, two DIFFERENT assertion orders, two fresh KB instances
    // (each std HashSet gets its own RandomState even in-process). The FULL
    // ordered binding list must be identical: query_find_inner sorts binding
    // sets canonically at its return boundary, so the order is hasher-seed
    // independent by construction. NOTE: an in-process pin is weaker than a
    // two-process check (which exercises different global seeds); the sort
    // makes order seed-independent by construction, and the nibli-host script-mode
    // byte-identity check covers the two-process case empirically.
    let names = ["zeta", "alis", "mike", "bob", "carol", "dave", "erin"];
    let kb1 = new_kb();
    for n in names {
        assert_buf(&kb1, make_assertion(n, "gerku"));
    }
    let kb2 = new_kb();
    for n in names.iter().rev() {
        assert_buf(&kb2, make_assertion(n, "gerku"));
    }

    let r1a = query_find(&kb1, make_find_query("gerku"));
    let r1b = query_find(&kb1, make_find_query("gerku"));
    let r2 = query_find(&kb2, make_find_query("gerku"));

    assert_eq!(r1a.len(), names.len(), "one binding set per asserted gerku");
    assert_eq!(r1a, r1b, "same KB, repeated query: order must be stable");
    assert_eq!(
        r1a, r2,
        "different assertion order: canonical witness order must agree"
    );
}

#[test]
fn domain_member_cache_order_is_deterministic() {
    // Domain-iteration-order probe: the typed domain member cache must be
    // sorted regardless of HashSet insertion order. This cache drives ForAll
    // member iteration and the ForallVerified entity order in proof output.
    let names = ["zeta", "alis", "mike", "bob"];
    let kb1 = new_kb();
    for n in names {
        assert_buf(&kb1, make_assertion(n, "gerku"));
    }
    let kb2 = new_kb();
    for n in names.iter().rev() {
        assert_buf(&kb2, make_assertion(n, "gerku"));
    }

    let m1: Vec<GroundTerm> = {
        let mut inner = kb1.inner.borrow_mut();
        inner.ensure_domain_members_cached();
        inner.all_typed_domain_members().to_vec()
    };
    let m2: Vec<GroundTerm> = {
        let mut inner = kb2.inner.borrow_mut();
        inner.ensure_domain_members_cached();
        inner.all_typed_domain_members().to_vec()
    };
    assert_eq!(
        m1, m2,
        "domain member order must be insertion/hasher independent"
    );
    let mut sorted = m1.clone();
    sorted.sort();
    assert_eq!(m1, sorted, "domain member cache must be sorted");
}

#[test]
fn forall_does_not_quantify_over_event_skolems() {
    // A ForAll variable is an INDIVIDUAL; an event Skolem must never be a spurious
    // counterexample. Hand-build a BARE `∀x. p(x)` (no guard — no current
    // compilation produces one, so this pins the defensive sort invariant
    // directly). KB: p(adam) asserted (known_entities = {adam}) + an injected
    // event Skolem `sk_ev0`. Ranging over individuals only, p(adam) holds → TRUE.
    // If the event Skolem leaked into the domain, p(sk_ev0) would be a false
    // counterexample → FALSE.
    let kb = new_kb();
    let fact = {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "p",
            vec![LogicalTerm::Constant("adam".to_string())],
        );
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    };
    assert_buf(&kb, fact);
    {
        let mut inner = kb.inner.borrow_mut();
        inner.note_event_entity("sk_ev0");
        inner.domain_members_dirty = true;
    }
    let bare_forall = {
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "p",
            vec![LogicalTerm::Variable("_v0".to_string())],
        );
        let root = forall(&mut nodes, "_v0", body);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    };
    assert!(
        query(&kb, bare_forall),
        "bare ∀x.p(x) must be TRUE over individuals (p(adam) holds); an event \
         Skolem must not be a spurious counterexample"
    );
}
