use super::*;

// ── Compute result ingestion tests ──

#[test]
fn test_compute_result_ingested_into_kb() {
    let kb = new_kb();

    // Query pilji(6, 2, 3) via ComputeNode → TRUE (built-in arithmetic)
    // This should auto-ingest the fact into the KB
    let mut q_nodes = Vec::new();
    let q_root = compute(
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

    // Now query the SAME fact as a plain Predicate (not ComputeNode)
    // It should be found directly in the KB because of auto-ingestion
    let mut p_nodes = Vec::new();
    let p_root = pred(
        &mut p_nodes,
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
            nodes: p_nodes,
            roots: vec![p_root]
        }
    ));
}

#[test]
fn test_compute_false_not_ingested() {
    let kb = new_kb();

    // Query pilji(7, 2, 3) via ComputeNode → FALSE (7 != 2*3)
    let mut q_nodes = Vec::new();
    let q_root = compute(
        &mut q_nodes,
        "product",
        vec![
            LogicalTerm::Number(7.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));

    // Verify the false fact was NOT ingested as a plain Predicate
    let mut p_nodes = Vec::new();
    let p_root = pred(
        &mut p_nodes,
        "product",
        vec![
            LogicalTerm::Number(7.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes: p_nodes,
            roots: vec![p_root]
        }
    ));
}

#[test]
fn test_ingested_result_available_for_reasoning() {
    let kb = new_kb();

    // Step 1: Query sumji(5, 2, 3) via ComputeNode → TRUE, auto-ingests
    let mut q_nodes = Vec::new();
    let q_root = compute(
        &mut q_nodes,
        "sum",
        vec![
            LogicalTerm::Number(5.0),
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

    // Step 2: Assert another fact
    assert_buf(&kb, make_assertion("ok", "derived"));

    // Step 3: Query conjunction: And(sumji(5,2,3), derived("ok", Zoe))
    // Both facts should be in KB: sumji from compute ingestion, derived from assertion
    let mut q2_nodes = Vec::new();
    let left = pred(
        &mut q2_nodes,
        "sum",
        vec![
            LogicalTerm::Number(5.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    let right = pred(
        &mut q2_nodes,
        "derived",
        vec![
            LogicalTerm::Constant("ok".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = and(&mut q2_nodes, left, right);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q2_nodes,
            roots: vec![root]
        }
    ));

    // Step 4: Conjunctive query with a non-ingested compute fact fails
    let mut q3_nodes = Vec::new();
    let l2 = pred(
        &mut q3_nodes,
        "sum",
        vec![
            LogicalTerm::Number(99.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    let r2 = pred(
        &mut q3_nodes,
        "derived",
        vec![
            LogicalTerm::Constant("ok".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root2 = and(&mut q3_nodes, l2, r2);
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes: q3_nodes,
            roots: vec![root2]
        }
    ));
}

#[test]
fn assert_typed_fact_invalidates_pred_cache() {
    // The cache-freshness invariant AT THE MUTATION POINT: cache a derived
    // predicate as False, then assert (via `assert_typed_fact` — the path ALL
    // five mid-query compute auto-ingestion sites funnel through) the base fact
    // that makes it derivable. The stale False must NOT survive. Pre-fix the
    // re-check returned the cached False (order-dependent wrong answers);
    // post-fix `assert_typed_fact` clears the cache so the re-check re-derives.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu")); // ∀x. dog(x) → danlu(x)

    let danlu_adam = StoredFact::Bare(GroundFact::new(
        "danlu",
        vec![
            GroundTerm::Constant("adam".to_string()),
            GroundTerm::Unspecified,
        ],
    ));
    let dog_adam = StoredFact::Bare(GroundFact::new(
        "gerku",
        vec![
            GroundTerm::Constant("adam".to_string()),
            GroundTerm::Unspecified,
        ],
    ));

    clear_and_enable_pred_cache(&kb.inner.borrow());

    // (1) danlu(adam) is not derivable yet (gerku(adam) absent) → caches False.
    {
        let inner = kb.inner.borrow();
        let mut visited = std::collections::HashSet::new();
        let r = check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited);
        assert!(
            r.is_false(),
            "danlu(adam) is not derivable before gerku(adam)"
        );
    }

    // (2) Assert gerku(adam) through the mutation point.
    {
        let mut inner = kb.inner.borrow_mut();
        assert_typed_fact(dog_adam, &mut inner);
    }

    // (3) Re-check: a stale cached False here means the cache was NOT invalidated.
    {
        let inner = kb.inner.borrow();
        let mut visited = std::collections::HashSet::new();
        let r = check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited);
        assert!(
            r.is_true(),
            "danlu(adam) must derive True once dog(adam) is asserted — a stale \
             cached False means assert_typed_fact failed to invalidate the cache"
        );
    }
}

#[test]
fn pred_cache_is_per_instance_no_cross_kb_leak() {
    // Two KBs on the same thread. KB-A enables its cache and caches a False for
    // danlu(adam) (gerku(adam) absent). KB-B has gerku(adam), so danlu(adam) IS
    // derivable. With the old THREAD-LOCAL cache, KB-A's enabled+cached False
    // leaked to KB-B on the same thread; per-instance caches keep them isolated.
    let danlu_adam = StoredFact::Bare(GroundFact::new(
        "danlu",
        vec![
            GroundTerm::Constant("adam".to_string()),
            GroundTerm::Unspecified,
        ],
    ));

    let kb_a = new_kb();
    assert_buf(&kb_a, make_universal("gerku", "danlu")); // ∀x. dog(x) → danlu(x)
    {
        let inner = kb_a.inner.borrow();
        clear_and_enable_pred_cache(&inner);
        let mut visited = std::collections::HashSet::new();
        let r = check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited);
        assert!(
            r.is_false(),
            "KB-A: danlu(adam) is not derivable (no gerku) → caches False"
        );
    }

    let kb_b = new_kb();
    assert_buf(&kb_b, make_universal("gerku", "danlu"));
    assert_buf(&kb_b, make_assertion("adam", "gerku")); // dog(adam)
    {
        let inner = kb_b.inner.borrow();
        let mut visited = std::collections::HashSet::new();
        let r = check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited);
        assert!(
            r.is_true(),
            "KB-B: danlu(adam) IS derivable (dog(adam) present); KB-A's cached \
             False must not leak across per-instance caches"
        );
    }
}

#[test]
fn compute_autoassert_invalidates_stale_cache() {
    // End-to-end through the actual compute auto-assert caller, in a SINGLE query
    // (the bug window — the cache is cleared once at query entry, then persists).
    // Rule `sumji(5,2,3) ⇒ derived(c)` (a ground material conditional), with
    // sumji NOT stored. One query: a probe that returns True but caches
    // derived(c)=False, then a compute conjunct that auto-asserts sumji(5,2,3),
    // then a re-check of derived(c). Pre-fix the re-check reads the stale False
    // (query wrongly False); post-fix the auto-assert clears the cache and
    // derived(c) re-derives True.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("c", "marker")); // always-true right branch

    // Material conditional: Or(Not(sumji(5,2,3)), derived(c)) ⇒ zero-var rule.
    let mut r_nodes = Vec::new();
    let cond = pred(
        &mut r_nodes,
        "sum",
        vec![
            LogicalTerm::Number(5.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    let concl = pred(
        &mut r_nodes,
        "derived",
        vec![
            LogicalTerm::Constant("c".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let ncond = not(&mut r_nodes, cond);
    let rule_root = or(&mut r_nodes, ncond, concl);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: r_nodes,
            roots: vec![rule_root],
        },
    );

    // Query: And( Or(derived(c), marker(c)) , And( sumji(5,2,3)[compute] , derived(c) ) )
    let mut q = Vec::new();
    let derived_probe = pred(
        &mut q,
        "derived",
        vec![
            LogicalTerm::Constant("c".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let marker = pred(
        &mut q,
        "marker",
        vec![
            LogicalTerm::Constant("c".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let probe = or(&mut q, derived_probe, marker); // True overall, caches derived(c)=False
    let compute_node = compute(
        &mut q,
        "sum",
        vec![
            LogicalTerm::Number(5.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    ); // computes True, auto-asserts sumji(5,2,3)
    let derived_final = pred(
        &mut q,
        "derived",
        vec![
            LogicalTerm::Constant("c".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let inner_and = and(&mut q, compute_node, derived_final);
    let root = and(&mut q, probe, inner_and);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes: q,
                roots: vec![root]
            }
        ),
        "derived(c) must re-derive True after the compute conjunct auto-asserts \
         sumji(5,2,3) — a stale cached False makes this query wrongly False"
    );
}
