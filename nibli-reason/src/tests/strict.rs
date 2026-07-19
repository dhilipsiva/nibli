use super::*;

// ─── STRICT MODE (opt-in): reject instead of warn-and-insert ─────────

/// Strict arity: the mismatching fact is rejected and the assertion fails
/// atomically; the permissive default (pinned above in
/// `test_predicate_arity_mismatch_detected`) is unchanged.
#[test]
fn strict_mode_rejects_arity_mismatch() {
    let kb = new_kb();
    kb.set_strict(true);
    assert_buf(&kb, make_assertion("alis", "gerku")); // registers arity 2

    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Constant("bob".to_string())],
    );
    let err = kb
        .assert_fact_inner(
            LogicBuffer {
                nodes,
                roots: vec![root],
            },
            String::new(),
        )
        .expect_err("strict mode must fail an arity-mismatched assertion");
    assert!(
        err.contains("strict mode rejected") && err.contains("arity mismatch"),
        "unexpected error: {err}"
    );

    // The mismatching fact must NOT be in the store; the original must be.
    let inner = kb.inner.borrow();
    let dog_facts = inner.fact_store.lookup_predicate("gerku").unwrap();
    assert!(
        !dog_facts.iter().any(|f| f.inner().args.len() == 1),
        "the rejected arity-1 fact must not be stored"
    );
}

/// Strict constraints: an assertion completing a violating set is rejected and
/// rolled back atomically — the KB is byte-identical to the pre-assertion
/// state, and the earlier (non-violating) fact survives.
#[test]
fn strict_mode_rejects_constraint_violation_atomically() {
    let kb = new_kb();
    kb.set_strict(true);

    // Constraint: gerku(alis) and mlatu(alis) must not both hold.
    let c1 = StoredFact::Bare(GroundFact::new(
        "gerku",
        vec![GroundTerm::Constant("alis".to_string())],
    ));
    let c2 = StoredFact::Bare(GroundFact::new(
        "mlatu",
        vec![GroundTerm::Constant("alis".to_string())],
    ));
    kb.register_constraint("not-both".to_string(), vec![c1, c2]);

    let flat = |rel: &str| {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            rel,
            vec![LogicalTerm::Constant("alis".to_string())],
        );
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    };

    assert_buf(&kb, flat("gerku")); // fine — the set is incomplete
    let err = kb
        .assert_fact_inner(flat("mlatu"), String::new())
        .expect_err("strict mode must fail the violation-completing assertion");
    assert!(
        err.contains("strict mode rejected") && err.contains("integrity constraint"),
        "unexpected error: {err}"
    );

    // The violating fact is gone; the earlier fact survives; verdicts agree.
    assert!(query(&kb, flat("gerku")), "the pre-existing fact survives");
    assert!(
        query_false(&kb, flat("mlatu")),
        "the rejected fact must not be queryable"
    );

    // The permissive default is untouched: same sequence on a fresh KB
    // warns and inserts.
    let kb2 = new_kb();
    kb2.register_constraint(
        "not-both".to_string(),
        vec![
            StoredFact::Bare(GroundFact::new(
                "gerku",
                vec![GroundTerm::Constant("alis".to_string())],
            )),
            StoredFact::Bare(GroundFact::new(
                "mlatu",
                vec![GroundTerm::Constant("alis".to_string())],
            )),
        ],
    );
    assert_buf(&kb2, flat("gerku"));
    assert_buf(&kb2, flat("mlatu")); // warns, does not error
    assert!(query(&kb2, flat("mlatu")), "permissive mode still inserts");
}

/// Strict mode is inert during retraction-replay rebuilds: facts accepted
/// before strict was enabled replay faithfully.
#[test]
fn strict_mode_is_inert_during_rebuild() {
    let kb = new_kb();
    // Permissively insert an arity mismatch (warned, stored).
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Constant("bob".to_string())],
    );
    let id = kb
        .assert_fact_inner(
            LogicBuffer {
                nodes,
                roots: vec![root],
            },
            String::new(),
        )
        .unwrap();

    // Turn strict ON, then force a rebuild by retracting an unrelated fact:
    // the mismatched fact must survive the replay.
    kb.set_strict(true);
    let unrelated = kb
        .assert_fact_inner(make_assertion("kim", "mlatu"), String::new())
        .unwrap();
    kb.retract_fact(unrelated).unwrap();

    let inner = kb.inner.borrow();
    let dog_facts = inner.fact_store.lookup_predicate("gerku").unwrap();
    assert!(
        dog_facts.iter().any(|f| f.inner().args.len() == 1),
        "fact {id}: a previously-accepted mismatch must survive a strict-era rebuild"
    );
}

// ─── Mid-query strict rollback (unassert_typed_fact) ─────────────────

fn always_true_eval(_rel: &str, _args: &[LogicalTerm]) -> Result<bool, String> {
    Ok(true)
}
fn always_true_batch(reqs: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    reqs.iter().map(|_| Ok(true)).collect()
}

/// Kills three rules.rs mutants in `unassert_typed_fact`:
/// `replace unassert_typed_fact with ()` (the rejected fact would stay in the
/// store), `delete !` (early return after the store remove — the index leaves
/// keep the ghost), and `replace != with ==` (the leaf `retain` flips polarity
/// and scrubs the INNOCENT co-leaf facts instead of the rejected one).
///
/// The mid-query compute auto-assert is the one strict-rejection path with no
/// registry-rebuild rollback behind it (`assert_fact_inner`'s rebuild masks
/// the assert-path twin), so `unassert_typed_fact` itself must surgically undo
/// the insert: store AND every index leaf, innocents untouched.
#[test]
fn strict_mid_query_constraint_rejection_scrubs_store_and_index() {
    let kb = new_kb();
    kb.set_compute_dispatch(always_true_eval, always_true_batch);

    // Innocent co-leaf fact: same relation, shares the (relation, position,
    // value) index leaves at positions 0 and 1 with the fact the constraint
    // will reject. Asserted BEFORE strict so nothing rejects it.
    let flat_num = |a: f64, b: f64, c: f64| {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "zzoracle",
            vec![
                LogicalTerm::Number(a),
                LogicalTerm::Number(b),
                LogicalTerm::Number(c),
            ],
        );
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    };
    assert_buf(&kb, flat_num(8.0, 2.0, 9.0));

    kb.set_strict(true);
    let stored = |c: f64| {
        StoredFact::Bare(GroundFact::new(
            "zzoracle",
            vec![
                GroundTerm::from_f64(8.0),
                GroundTerm::from_f64(2.0),
                GroundTerm::from_f64(c),
            ],
        ))
    };
    kb.register_constraint("no-zzoracle-8-2-3".to_string(), vec![stored(3.0)]);

    // The query dispatches zzoracle(8,2,3) to the always-true backend, which
    // auto-asserts it mid-query; the constraint then rejects it and strict
    // mode rolls it back out (verdict stays the backend's TRUE).
    assert!(
        query(&kb, make_compute_query("zzoracle", 8.0, 2.0, 3.0)),
        "the backend's TRUE still answers the query"
    );

    let inner = kb.inner.borrow();
    let rejected = stored(3.0);
    let innocent = stored(9.0);
    assert!(
        !inner.fact_store.contains(&rejected),
        "the constraint-rejected fact must not remain in the store"
    );
    assert!(
        inner.fact_store.contains(&innocent),
        "the innocent same-relation fact must survive the rollback"
    );
    for (pos, val) in [(0usize, 8.0f64), (1, 2.0)] {
        let leaf = inner
            .arg_position_index
            .get(&("zzoracle".to_string(), pos))
            .expect("index position map must exist")
            .get(&GroundTerm::from_f64(val))
            .expect("shared index leaf must exist");
        assert!(
            !leaf.contains(&rejected),
            "index leaf ({pos}, {val}) must be scrubbed of the rejected fact: {leaf:?}"
        );
        assert!(
            leaf.contains(&innocent),
            "index leaf ({pos}, {val}) must retain the innocent co-leaf fact: {leaf:?}"
        );
    }
}

#[test]
fn numeric_comparison_set_matches_the_evaluator_domain() {
    // Conformance: try_numeric_comparison handles exactly
    // relations::NUMERIC_COMPARISONS (the single-source name sets) —
    // built-in arithmetic falls through to the tolerant evaluator instead.
    use nibli_types::logic::LogicalTerm;
    let subs = std::collections::HashMap::new();
    let args = vec![LogicalTerm::Number(2.0), LogicalTerm::Number(1.0)];
    for r in nibli_types::relations::NUMERIC_COMPARISONS {
        assert!(
            crate::compute::try_numeric_comparison(r, &args, &subs).is_some(),
            "{r} must be a decidable comparison"
        );
    }
    for r in nibli_types::relations::BUILTIN_ARITHMETIC {
        assert!(
            crate::compute::try_numeric_comparison(r, &args, &subs).is_none(),
            "{r} must not be treated as a comparison"
        );
    }
}
