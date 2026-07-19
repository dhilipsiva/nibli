use super::*;

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
    // mis-attribute the NEXT assertion's rules in rule_source_map.
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
    // Retracting a ForAll record takes the full-rebuild path (a ground-fact
    // retraction is incremental and would not rebuild).
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
fn retract_count_quantified_fact_removes_witnesses() {
    // `Count(x, 2, gerku(x, _))` generates count-1 = 1 extra Skolem dog and
    // asserts gerku(sk) for it. Retracting the count assertion must remove that
    // generated witness — pre-fix a flat CountNode buffer took the incremental
    // path (has_skolems matched only Exists/ForAll), leaking the witness fact +
    // entity. Now CountNode routes to rebuild, which excludes the retracted
    // assertion and never regenerates its witnesses.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = count(&mut nodes, "x", 2, body);
    let id = assert_id(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
        "count",
    );
    assert!(
        kb.count_witnesses(make_find_query("gerku")).unwrap() >= 1,
        "the count assertion should have generated a witness dog"
    );

    kb.retract_fact_inner(id).unwrap();
    assert_eq!(
        kb.count_witnesses(make_find_query("gerku")).unwrap(),
        0,
        "count-generated witnesses must not survive retraction"
    );
}

// ─── Compute builtin arithmetic tests ────────────────────────

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
