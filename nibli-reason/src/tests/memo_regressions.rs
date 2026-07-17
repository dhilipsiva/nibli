use super::*;

// ---- Proof trace memoization tests ----

#[test]
fn test_proof_memo_deduplication() {
    // Multi-hop event-decomposed trace should use ProofRef for repeated sub-proofs.
    // Without memoization: mlatu base facts appear 12× in a 2-hop 3-role chain.
    // With memoization: repeated facts get ProofRef nodes instead.
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
    assert_buf(&kb, make_event_universal("mlatu", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "jmive"));

    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_temporal_event_query("bob", "jmive", present))
        .unwrap();
    assert!(holds.is_true(), "Present(jmive(bob)) should hold");

    // Count ProofRef steps — should be present due to repeated condition proofs
    let proof_ref_count = trace
        .steps
        .iter()
        .filter(|step| matches!(&step.rule, ProofRule::ProofRef { .. }))
        .count();
    assert!(
        proof_ref_count > 0,
        "2-hop event-decomposed trace should have ProofRef nodes for deduplicated sub-proofs, got {}",
        proof_ref_count
    );

    // With memoization, condition proofs that repeat across different
    // conclusion derivations get ProofRef instead of full re-expansion.
    // The ExistsNode witness search also generates overhead (failed candidates),
    // but the key improvement is visible in the successful derivation path.
    assert!(
        proof_ref_count >= 3,
        "2-hop event trace should have at least 3 ProofRef nodes (deduplicated conditions), got {}",
        proof_ref_count
    );
}

#[test]
fn proof_ref_children_are_holds_true() {
    // Stage 2d invariant: every ProofRef leaf resolves to a holds:true step, because
    // only holds:true derivations (Asserted / Derived / EqualitySubstitution) are
    // memoized — the depth-relative PredicateNotFound no longer is, so a stale
    // not-found can never be reached via a ProofRef. Exercised across several
    // memo-bearing trace shapes. (A direct RED reproduction of the cross-recursion-
    // depth poisoning is unconstructible in the same way the 2a/2b divergence tests
    // were — the verdict cache + horizon short-circuit collapse the scenario — so
    // this asserts the resulting PROPERTY rather than the elusive walk order.)

    // (a) Multi-hop event chain — heavy ProofRef dedup of repeated role conditions.
    {
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
        assert_buf(&kb, make_event_universal("mlatu", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "jmive"));
        let (_holds, trace) = kb
            .query_entailment_with_proof_inner(make_temporal_event_query("bob", "jmive", present))
            .unwrap();
        assert_proof_refs_resolve_to_holds_true(&trace);
    }
    // (b) du-equivalence — exercises the EqualitySubstitution memo path.
    {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("adam", "gerku"));
        assert_buf(&kb, make_equals("adam", "betty"));
        let (_holds, trace) = kb
            .query_entailment_with_proof_inner(make_query("betty", "gerku"))
            .unwrap();
        assert_proof_refs_resolve_to_holds_true(&trace);
    }
    // (c) Flat universal-rule syllogism.
    {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_assertion("alis", "gerku"));
        let (_holds, trace) = kb
            .query_entailment_with_proof_inner(make_query("alis", "danlu"))
            .unwrap();
        assert_proof_refs_resolve_to_holds_true(&trace);
    }
}

#[test]
fn proof_trace_byte_deterministic_3x() {
    // The proof trace must be byte-reproducible run-to-run (no HashSet-order leakage
    // into the recorded structure). Build a memo-heavy 2-hop event chain in three
    // fresh KB instances and assert the serialized trace is identical each time.
    let render = || {
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
        assert_buf(&kb, make_event_universal("mlatu", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "jmive"));
        let (_holds, trace) = kb
            .query_entailment_with_proof_inner(make_temporal_event_query("bob", "jmive", present))
            .unwrap();
        format!("{trace:?}")
    };
    let a = render();
    let b = render();
    let c = render();
    assert_eq!(a, b, "proof trace not deterministic (run 1 vs run 2)");
    assert_eq!(b, c, "proof trace not deterministic (run 2 vs run 3)");
}

#[test]
fn proof_trace_equals_pinned_resolving_depth() {
    // The iterative-deepening proof query returns the trace built at the RESOLVING
    // depth (the shallowest non-ResourceExceeded(Depth) depth). This locks that
    // invariant: the deepening loop's trace == a single proof build pinned at the
    // resolving depth — the property the build-once-at-resolving-depth optimization
    // relies on. A 2-hop chain (proof at depth >1) exercises it: querying the
    // shallow depths hits the depth horizon (RE) before the chain resolves.

    // (A) Build the trace ONCE, pinned at the resolving depth. The resolving depth
    //     is found with the cheap UNTRACED walk on a freshly-cleared per-KB cache
    //     (clear it so a prior query's cached True can't make a shallow probe
    //     spuriously resolve).
    let kb_pin = new_kb();
    assert_buf(&kb_pin, make_assertion("alis", "gerku"));
    assert_buf(&kb_pin, make_universal("gerku", "danlu"));
    assert_buf(&kb_pin, make_universal("danlu", "xanlu"));
    let configured_max = {
        let inner = kb_pin.inner.borrow();
        clear_and_enable_pred_cache(&inner);
        inner.max_chain_depth
    };
    let mut resolving_depth = configured_max;
    for depth_limit in 1..=configured_max {
        kb_pin.inner.borrow_mut().max_chain_depth = depth_limit;
        let r = kb_pin
            .run_entailment_check(&make_query("alis", "xanlu"))
            .unwrap();
        if !matches!(r, QueryResult::ResourceExceeded(ResourceKind::Depth)) {
            resolving_depth = depth_limit;
            break;
        }
    }
    kb_pin.inner.borrow_mut().max_chain_depth = resolving_depth;
    let (r_pin, t_pin) = kb_pin
        .run_entailment_check_with_proof(&make_query("alis", "xanlu"))
        .unwrap();
    kb_pin.inner.borrow_mut().max_chain_depth = configured_max;

    // (B) The full iterative-deepening proof query (clears the cache at its start).
    let kb_loop = new_kb();
    assert_buf(&kb_loop, make_assertion("alis", "gerku"));
    assert_buf(&kb_loop, make_universal("gerku", "danlu"));
    assert_buf(&kb_loop, make_universal("danlu", "xanlu"));
    let (r_loop, t_loop) = kb_loop
        .query_entailment_with_proof_inner(make_query("alis", "xanlu"))
        .unwrap();

    assert!(
        r_loop.is_true(),
        "xanlu(alis) should hold via the 2-hop chain"
    );
    assert!(
        resolving_depth > 1,
        "expected a multi-hop proof (resolving depth >1), got {resolving_depth}"
    );
    assert_eq!(
        r_loop, r_pin,
        "verdict mismatch: deepening loop vs pinned at resolving depth"
    );
    assert_eq!(
        format!("{t_loop:?}"),
        format!("{t_pin:?}"),
        "trace mismatch: deepening loop vs single build at resolving depth {resolving_depth}"
    );
}

#[test]
fn test_proof_memo_correctness() {
    // Memoized trace still reports the correct result and contains proper Derived + Asserted steps.
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_temporal_event_query("alis", "danlu", past))
        .unwrap();
    assert!(holds.is_true(), "Past(danlu(alis)) should hold");

    // Should still have Derived steps from the rule application
    let derived_count = trace
        .steps
        .iter()
        .filter(|step| matches!(&step.rule, ProofRule::Derived { .. }))
        .count();
    assert!(
        derived_count >= 1,
        "should have at least 1 Derived step from gerku→danlu rule, got {}",
        derived_count
    );

    // First occurrence of base facts should be Asserted or PredicateCheck (not ProofRef)
    let has_asserted_or_check = trace.steps.iter().any(|step| {
        matches!(&step.rule, ProofRule::Asserted { .. })
            || matches!(&step.rule, ProofRule::PredicateCheck { .. })
    });
    assert!(
        has_asserted_or_check,
        "first occurrence of base facts should be Asserted or PredicateCheck, not ProofRef"
    );
}

#[test]
fn test_proof_memo_single_hop_no_unnecessary_refs() {
    // Single-hop with one entity: each condition is unique,
    // so no ProofRef should be needed.
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_temporal_event_query("alis", "danlu", past))
        .unwrap();
    assert!(holds.is_true(), "Past(danlu(alis)) should hold");

    // In a single-hop scenario, conditions are gerku(e), gerku_x1(e, alis), gerku_x2(e, zo'e)
    // These are all unique facts, so no ProofRef should be needed for condition proofs.
    // ProofRef may still appear if the same fact is checked multiple times through
    // different paths, but the count should be very low.
    let proof_ref_count = trace
        .steps
        .iter()
        .filter(|step| matches!(&step.rule, ProofRule::ProofRef { .. }))
        .count();
    // Allow a small number — the point is it's not the cubic blowup
    assert!(
        proof_ref_count <= 3,
        "single-hop trace should have very few ProofRef nodes (unique conditions), got {}",
        proof_ref_count
    );
}

// ─── Book example regression test (event Skolem InDomain blowup) ────

/// Build a 2-argument event-decomposed assertion:
///   ∃ev0. P(ev0) ∧ P_x1(ev0, entity1) ∧ P_x2(ev0, entity2)
/// This models sentences like "lo prenu cu ponse lo datni" where both
/// the subject and object are concrete entities.
fn make_event_assertion_2arg(entity1: &str, entity2: &str, predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let p_type = pred(
        &mut nodes,
        predicate,
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let p_role1 = pred(
        &mut nodes,
        &format!("{}_x1", predicate),
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Constant(entity1.to_string()),
        ],
    );
    let p_role2 = pred(
        &mut nodes,
        &format!("{}_x2", predicate),
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Constant(entity2.to_string()),
        ],
    );
    let a1 = and(&mut nodes, p_type, p_role1);
    let a2 = and(&mut nodes, a1, p_role2);
    let root = exists(&mut nodes, "_ev0", a2);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_book_example_no_oom() {
    // Regression test for the book example that was crashing with OOM:
    //   .i lo prenu cu ponse lo datni
    //   .i ro lo prenu poi ponse lo datni cu bilga lo nu curmi
    //   ?! lo prenu cu bilga lo nu curmi
    //
    // The crash was caused by event Skolem constants being registered in
    // `known_entities`, causing O(N²) blowup in guarded
    // conjunction introduction. With 2-arg predicates and universal rules,
    // each event constant linked ~6 predicates → C(6,2)=15 conjunctions
    // → commutativity doubled them → exponential growth.
    //
    // This test models the scenario with multiple entities and predicates
    // to verify no memory explosion occurs.
    let kb = new_kb();

    // Assert: "A person possesses data"
    // ∃ev0. ponse(ev0) ∧ ponse_x1(ev0, prenu_sk) ∧ ponse_x2(ev0, datni_sk)
    assert_buf(
        &kb,
        make_event_assertion_2arg("prenu_sk", "datni_sk", "ponse"),
    );

    // Also assert the determiner decompositions (what `lo prenu` and `lo datni` produce):
    // ∃ev1. prenu(ev1) ∧ prenu_x1(ev1, prenu_sk)
    assert_buf(&kb, make_event_assertion("prenu_sk", "prenu"));
    // ∃ev2. datni(ev2) ∧ datni_x1(ev2, datni_sk)
    assert_buf(&kb, make_event_assertion("datni_sk", "datni"));

    // Assert universal rule: "Every person who possesses data is obligated"
    // This is simplified as: ∀x. prenu(x) → bilga(x)
    assert_buf(&kb, make_event_universal("prenu", "bilga"));

    // Add another universal rule to increase backward-chaining depth
    assert_buf(&kb, make_event_universal("bilga", "zukte"));

    // Query: "A person is obligated" — should hold via prenu→bilga derivation
    assert!(
        query(&kb, make_event_assertion("prenu_sk", "bilga")),
        "prenu_sk should be derived as bilga via universal rule"
    );

    // Query with proof trace — this is what was crashing before the fix
    let (holds, _trace) = kb
        .query_entailment_with_proof_inner(make_event_assertion("prenu_sk", "bilga"))
        .unwrap();
    assert!(
        holds.is_true(),
        "proof-traced query should hold for bilga(prenu_sk)"
    );

    // Multi-hop: prenu→bilga→zukte
    assert!(
        query(&kb, make_event_assertion("prenu_sk", "zukte")),
        "multi-hop prenu→bilga→zukte should derive zukte(prenu_sk)"
    );

    // Proof trace for multi-hop should complete without OOM
    let (holds2, _trace2) = kb
        .query_entailment_with_proof_inner(make_event_assertion("prenu_sk", "zukte"))
        .unwrap();
    assert!(
        holds2.is_true(),
        "proof-traced multi-hop should hold for zukte(prenu_sk)"
    );
}

// ─── And flattening regression test ────

#[test]
fn test_and_flattening_prevents_rewrite_explosion() {
    // Regression test: a deeply nested And tree with 7 leaves (matching the
    // real Neo-Davidsonian decomposition of "owns(some person, some data).")
    // previously caused combinatorial explosion. After flattening, each leaf
    // is asserted individually, so the fact count should be bounded.
    let kb = new_kb();

    // Build: ∃ev. P1(ev) ∧ P2(ev,a) ∧ P3(ev,b) ∧ P4(a) ∧ P5(b) ∧ P6(a) ∧ P7(b)
    // This simulates a 2-arg predicate with existential-import restrictors.
    let mut nodes = Vec::new();
    let p1 = pred(
        &mut nodes,
        "ponse",
        vec![LogicalTerm::Variable("_ev0".into())],
    );
    let p2 = pred(
        &mut nodes,
        "ponse_x1",
        vec![
            LogicalTerm::Variable("_ev0".into()),
            LogicalTerm::Variable("_v0".into()),
        ],
    );
    let p3 = pred(
        &mut nodes,
        "ponse_x2",
        vec![
            LogicalTerm::Variable("_ev0".into()),
            LogicalTerm::Variable("_v1".into()),
        ],
    );
    let p4 = pred(
        &mut nodes,
        "prenu",
        vec![LogicalTerm::Variable("_v0".into())],
    );
    let p5 = pred(
        &mut nodes,
        "datni",
        vec![LogicalTerm::Variable("_v1".into())],
    );
    let p6 = pred(
        &mut nodes,
        "prenu_x1",
        vec![
            LogicalTerm::Variable("_ev1".into()),
            LogicalTerm::Variable("_v0".into()),
        ],
    );
    let p7 = pred(
        &mut nodes,
        "datni_x1",
        vec![
            LogicalTerm::Variable("_ev2".into()),
            LogicalTerm::Variable("_v1".into()),
        ],
    );

    // Build deeply nested And tree (7 leaves, 6 And nodes)
    let a1 = and(&mut nodes, p1, p2);
    let a2 = and(&mut nodes, a1, p3);
    let a3 = and(&mut nodes, a2, p4);
    let a4 = and(&mut nodes, a3, p5);
    let a5 = and(&mut nodes, a4, p6);
    let a6 = and(&mut nodes, a5, p7);

    // Wrap in existentials (these will be Skolemized)
    let e0 = exists(&mut nodes, "_ev0", a6);
    let e1 = exists(&mut nodes, "_ev1", e0);
    let e2 = exists(&mut nodes, "_ev2", e1);
    let e3 = exists(&mut nodes, "_v0", e2);
    let root = exists(&mut nodes, "_v1", e3);

    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };

    assert_buf(&kb, buf);

    // Verify the fact count is bounded — each leaf gets a single entry
    // in the fact store (no combinatorial And explosion).
    let inner = kb.inner.borrow();
    let fact_count = inner.fact_store.len();
    eprintln!("[Test] fact_store count: {}", fact_count);
    assert!(
        fact_count < 100,
        "Asserted facts should be < 100 after flattening, got {}",
        fact_count
    );
}

// ─── Compute error propagation tests ─────────────────────────

fn tenfa_query() -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = compute(
        &mut nodes,
        "exponential", // external compute predicate, not built-in arithmetic
        vec![
            LogicalTerm::Number(8.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

fn failing_eval(_rel: &str, _args: &[LogicalTerm]) -> Result<bool, String> {
    Err("backend unreachable".to_string())
}
fn failing_batch(reqs: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    reqs.iter()
        .map(|_| Err("backend unreachable".to_string()))
        .collect()
}
fn ok_eval(_rel: &str, _args: &[LogicalTerm]) -> Result<bool, String> {
    Ok(true)
}
fn ok_batch(reqs: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    reqs.iter().map(|_| Ok(true)).collect()
}

#[test]
fn test_compute_no_backend_is_unknown_not_false() {
    // A compute predicate with NO backend registered (the in-browser / native case)
    // must surface Unknown(BackendUnavailable) — a backend that cannot be consulted is
    // not a derived falsehood. Previously this returned a definitive FALSE.
    let kb = new_kb();
    let r = query_result(&kb, tenfa_query());
    assert!(
        matches!(r, QueryResult::Unknown(UnknownReason::BackendUnavailable)),
        "no backend → Unknown(BackendUnavailable), got {r:?}"
    );
}

#[test]
fn test_compute_backend_failure_is_unknown_not_false() {
    // A registered backend that ERRORS (unreachable mid-session) must also surface
    // Unknown(BackendUnavailable), never FALSE.
    let kb = new_kb();
    kb.set_compute_dispatch(failing_eval, failing_batch);
    let r = query_result(&kb, tenfa_query());
    assert!(
        matches!(r, QueryResult::Unknown(UnknownReason::BackendUnavailable)),
        "backend error → Unknown(BackendUnavailable), got {r:?}"
    );
}

#[test]
fn test_cached_compute_result_survives_backend_outage() {
    // A prior SUCCESSFUL computation auto-asserts its fact; that result must keep
    // answering TRUE even after the backend starts failing — only genuinely
    // undetermined compute predicates degrade to Unknown.
    let kb = new_kb();
    kb.set_compute_dispatch(ok_eval, ok_batch);
    assert!(
        query(&kb, tenfa_query()),
        "working backend → TRUE (auto-asserted into the KB)"
    );
    // Backend goes away.
    kb.set_compute_dispatch(failing_eval, failing_batch);
    let r = query_result(&kb, tenfa_query());
    assert!(
        matches!(r, QueryResult::True),
        "the auto-asserted prior result survives the outage, got {r:?}"
    );
}

// ─── ProofRef memo back-reference validation ─────────────────

#[test]
fn test_proof_ref_carries_cached_index() {
    // Verify that ProofRef steps carry the original step index in children.
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
    assert_buf(&kb, make_event_universal("mlatu", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "jmive"));

    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_temporal_event_query("bob", "jmive", present))
        .unwrap();
    assert!(holds.is_true());

    // Every ProofRef step should have exactly one child pointing to the
    // original step, and its holds value should match the referenced step.
    for step in &trace.steps {
        if let ProofRule::ProofRef { .. } = &step.rule {
            assert_eq!(
                step.children.len(),
                1,
                "ProofRef should have exactly 1 child (back-reference)"
            );
            let referenced_idx = step.children[0] as usize;
            assert!(
                referenced_idx < trace.steps.len(),
                "ProofRef back-reference {} out of bounds ({})",
                referenced_idx,
                trace.steps.len()
            );
            assert_eq!(
                step.holds, trace.steps[referenced_idx].holds,
                "ProofRef.holds should match the referenced step's holds"
            );
        }
    }
}
