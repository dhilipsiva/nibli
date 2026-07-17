use super::*;

// ─── Dependent Skolem (Phase B) Tests ────────────────────────────

fn make_exists_query(entity: &str, predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        predicate,
        vec![
            LogicalTerm::Constant(entity.to_string()),
            LogicalTerm::Variable("_v1".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "_v1", body);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_dependent_skolem_native_rule() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
    assert!(query(&kb, make_exists_query("alis", "zdani")));
}

#[test]
fn test_dependent_skolem_entity_after_rule() {
    let kb = new_kb();
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert!(query(&kb, make_exists_query("alis", "zdani")));
}

#[test]
fn test_dependent_skolem_query_existential() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
    assert!(query(&kb, make_exists_query("alis", "zdani")));
    assert!(query_false(&kb, make_exists_query("bob", "zdani")));
}

#[test]
fn test_skolem_fn_multiple_entities() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_assertion("bob", "prenu"));
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
    assert!(query(&kb, make_exists_query("alis", "zdani")));
    assert!(query(&kb, make_exists_query("bob", "zdani")));
}

#[test]
fn test_skolem_fn_registry_populated() {
    let kb = new_kb();
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
    let inner = kb.inner.borrow();
    assert!(
        !inner.skolem_fn_registry.is_empty(),
        "SkolemFn registry should have entries"
    );
    assert_eq!(inner.skolem_fn_registry[0].base_name, "sk_0");
    assert_eq!(inner.skolem_fn_registry[0].dep_count, 1);
}

// ─── Multi-Dependency SkolemFn Tests ─────────────────────────

/// Build: ∀_v0. ∀_v1. (¬(prenu(_v0, zo'e) ∧ mlatu(_v1, zo'e)) ∨ ∃_v2. zdani(_v0, _v1, _v2))
/// Meaning: for all persons x and cats y, there exists a z such that zdani(x, y, z).
fn make_multi_dep_skolem_universal() -> LogicBuffer {
    let mut nodes = Vec::new();
    let p = pred(
        &mut nodes,
        "prenu",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let q = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Variable("_v1".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let conj = and(&mut nodes, p, q);
    let body = pred(
        &mut nodes,
        "zdani",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Variable("_v1".to_string()),
            LogicalTerm::Variable("_v2".to_string()),
        ],
    );
    let ex = exists(&mut nodes, "_v2", body);
    let neg = not(&mut nodes, conj);
    let disj = or(&mut nodes, neg, ex);
    let inner_forall = forall(&mut nodes, "_v1", disj);
    let root = forall(&mut nodes, "_v0", inner_forall);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Query: ∃_v2. zdani(entity_a, entity_b, _v2)
fn make_multi_dep_exists_query(entity_a: &str, entity_b: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "zdani",
        vec![
            LogicalTerm::Constant(entity_a.to_string()),
            LogicalTerm::Constant(entity_b.to_string()),
            LogicalTerm::Variable("_v2".to_string()),
        ],
    );
    let root = exists(&mut nodes, "_v2", body);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_multi_dep_skolem_two_universals() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_assertion("felix", "mlatu"));
    assert_buf(&kb, make_multi_dep_skolem_universal());
    // ∃z. zdani(alis, felix, z) should be TRUE via SkolemFn with 2 deps
    assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
}

#[test]
fn test_multi_dep_skolem_registry() {
    let kb = new_kb();
    assert_buf(&kb, make_multi_dep_skolem_universal());
    let inner = kb.inner.borrow();
    assert!(!inner.skolem_fn_registry.is_empty());
    assert_eq!(inner.skolem_fn_registry[0].dep_count, 2);
}

/// CYP-shape: ∀_v0. ∀_v1. ∀_v3. ¬(prenu(_v0) ∧ mlatu(_v1) ∧ gerku(_v3)) ∨ ∃_v2. zdani(_v1, _v2)
/// The conclusion existential _v2 references ONLY _v1, so its dependent Skolem depends on a
/// single universal even though 3 universals are in scope (dependency precision).
fn make_cyp_shape_universal() -> LogicBuffer {
    let mut nodes = Vec::new();
    let p = pred(
        &mut nodes,
        "prenu",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let q = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Variable("_v1".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let r = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("_v3".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let conj_pq = and(&mut nodes, p, q);
    let conj = and(&mut nodes, conj_pq, r);
    let body = pred(
        &mut nodes,
        "zdani",
        vec![
            LogicalTerm::Variable("_v1".to_string()),
            LogicalTerm::Variable("_v2".to_string()),
        ],
    );
    let ex = exists(&mut nodes, "_v2", body);
    let neg = not(&mut nodes, conj);
    let disj = or(&mut nodes, neg, ex);
    let f3 = forall(&mut nodes, "_v3", disj);
    let f1 = forall(&mut nodes, "_v1", f3);
    let root = forall(&mut nodes, "_v0", f1);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_dependent_skolem_precise_deps_single_universal() {
    let kb = new_kb();
    assert_buf(&kb, make_cyp_shape_universal());
    let inner = kb.inner.borrow();
    assert!(!inner.skolem_fn_registry.is_empty());
    // The conclusion existential references only _v1, so dep_count is 1 — NOT 3, even though
    // three universals are in scope. The old over-approximation gave 3, inflating the firing
    // candidate cartesian to members^3 (the prenex CYP-join blowup).
    assert_eq!(inner.skolem_fn_registry[0].dep_count, 1);
}

#[test]
fn test_multi_dep_skolem_different_entities() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_assertion("bob", "prenu"));
    assert_buf(&kb, make_assertion("felix", "mlatu"));
    assert_buf(&kb, make_assertion("garfield", "mlatu"));
    assert_buf(&kb, make_multi_dep_skolem_universal());
    // All combinations of person × cat should have zdani witnesses
    assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
    assert!(query(&kb, make_multi_dep_exists_query("alis", "garfield")));
    assert!(query(&kb, make_multi_dep_exists_query("bob", "felix")));
    assert!(query(&kb, make_multi_dep_exists_query("bob", "garfield")));
    // Non-prenu or non-mlatu entities should NOT have zdani witnesses
    assert!(query_false(
        &kb,
        make_multi_dep_exists_query("felix", "alis")
    ));
}

#[test]
fn test_multi_dep_skolem_rule_before_facts() {
    let kb = new_kb();
    // Rule first, then facts
    assert_buf(&kb, make_multi_dep_skolem_universal());
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_assertion("felix", "mlatu"));
    assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
}
