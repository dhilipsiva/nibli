use super::*;

// ─── Fact Registry / Retraction Tests ────────────────────────────

#[test]
fn test_retract_basic() {
    let kb = new_kb();
    let id = assert_id(&kb, make_assertion("alis", "gerku"), "dog(Alis).");
    assert!(query(&kb, make_query("alis", "gerku")));
    kb.retract_fact_inner(id).unwrap();
    assert!(query_false(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_retract_preserves_other_facts() {
    let kb = new_kb();
    let id1 = assert_id(&kb, make_assertion("alis", "gerku"), "");
    let _id2 = assert_id(&kb, make_assertion("bob", "mlatu"), "");
    kb.retract_fact_inner(id1).unwrap();
    assert!(query_false(&kb, make_query("alis", "gerku")));
    assert!(query(&kb, make_query("bob", "mlatu")));
}

#[test]
fn test_retract_derived_facts_gone() {
    let kb = new_kb();
    let base_id = assert_id(&kb, make_assertion("alis", "gerku"), "");
    let _rule_id = assert_id(&kb, make_universal("gerku", "danlu"), "");
    // "alis danlu" should be derivable via the rule
    assert!(query(&kb, make_query("alis", "danlu")));
    kb.retract_fact_inner(base_id).unwrap();
    // After retracting the base fact, "alis danlu" should no longer hold
    assert!(query_false(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_retract_rule_preserves_base_facts() {
    let kb = new_kb();
    let _base_id = assert_id(&kb, make_assertion("alis", "gerku"), "");
    let rule_id = assert_id(&kb, make_universal("gerku", "danlu"), "");
    assert!(query(&kb, make_query("alis", "danlu")));
    kb.retract_fact_inner(rule_id).unwrap();
    // Base fact preserved
    assert!(query(&kb, make_query("alis", "gerku")));
    // Derived fact gone (rule retracted)
    assert!(query_false(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_retract_and_reassert_new_id() {
    let kb = new_kb();
    let id1 = assert_id(&kb, make_assertion("alis", "gerku"), "");
    kb.retract_fact_inner(id1).unwrap();
    let id2 = assert_id(&kb, make_assertion("alis", "gerku"), "");
    assert!(id2 > id1);
    assert!(query(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_retract_nonexistent_errors() {
    let kb = new_kb();
    assert!(kb.retract_fact_inner(999).is_err());
}

#[test]
fn test_retract_idempotent() {
    let kb = new_kb();
    let id = assert_id(&kb, make_assertion("alis", "gerku"), "");
    kb.retract_fact_inner(id).unwrap();
    kb.retract_fact_inner(id).unwrap(); // second retract is no-op
    assert!(query_false(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_retract_duplicate_ground_fact_keeps_live_copy() {
    // Two records assert the SAME ground fact. Retracting one must NOT remove
    // the fact from the store while the other record is still live (the
    // HashSet store has no multiplicity — incremental retraction must consult
    // the surviving registry records).
    let kb = new_kb();
    let id1 = assert_id(&kb, make_assertion("alis", "gerku"), "copy 1");
    let id2 = assert_id(&kb, make_assertion("alis", "gerku"), "copy 2");
    kb.retract_fact_inner(id1).unwrap();
    assert!(
        query(&kb, make_query("alis", "gerku")),
        "fact must survive while record #{id2} still asserts it"
    );
    // Retracting the second (last) record removes the fact for real.
    kb.retract_fact_inner(id2).unwrap();
    assert!(query_false(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_retract_multi_root_removes_all_roots() {
    // A single record whose buffer has TWO roots: assertion processes both, so
    // retraction must remove both (it used to process only roots.first()).
    let mut nodes = Vec::new();
    let r1 = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let r2 = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let kb = new_kb();
    let id = assert_id(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![r1, r2],
        },
        "two roots",
    );
    assert!(query(&kb, make_query("alis", "gerku")));
    assert!(query(&kb, make_query("bob", "mlatu")));
    kb.retract_fact_inner(id).unwrap();
    assert!(
        query_false(&kb, make_query("alis", "gerku")),
        "first root's fact must be retracted"
    );
    assert!(
        query_false(&kb, make_query("bob", "mlatu")),
        "second root's fact must be retracted too (not just roots.first())"
    );
}

// ─── Negative-Fact Storage / Contradiction Detection Tests ───────

/// Build the event-decomposed form nibli-semantics emits for "<entity> cu <pred>":
/// ∃e. ((pred(e) ∧ pred_x1(e, entity)) ∧ pred_x2(e, zo'e)), optionally negated
/// (the negation wraps the OUTSIDE of the existential, as the pipeline emits).
fn make_event_decomposed(entity: &str, predicate: &str, negated: bool) -> LogicBuffer {
    let mut nodes = Vec::new();
    let ev = || LogicalTerm::Variable("_ev0".to_string());
    let type_pred = pred(&mut nodes, predicate, vec![ev()]);
    let x1 = pred(
        &mut nodes,
        &format!("{predicate}_x1"),
        vec![ev(), LogicalTerm::Constant(entity.to_string())],
    );
    let x2 = pred(
        &mut nodes,
        &format!("{predicate}_x2"),
        vec![ev(), LogicalTerm::Unspecified],
    );
    let a1 = and(&mut nodes, type_pred, x1);
    let a2 = and(&mut nodes, a1, x2);
    let ex = exists(&mut nodes, "_ev0", a2);
    let root = if negated { not(&mut nodes, ex) } else { ex };
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_negated_ground_fact_contradicts_contrary_positive() {
    // Assert ¬gerku(alis), then gerku(alis): both must be accepted (a negative
    // premise stays assertable), and check_contradictions must flag the pair.
    let kb = new_kb();
    assert_id(&kb, make_negated_assertion("alis", "gerku"), "~dog().");
    assert_id(&kb, make_assertion("alis", "gerku"), "gerku");
    let violations = kb.check_contradictions();
    assert!(
        violations
            .iter()
            .any(|v| v.contains("Negation contradiction")),
        "contrary positive after an asserted negation must be flagged: {violations:?}"
    );
}

#[test]
fn test_negated_ground_fact_alone_is_not_a_contradiction() {
    // A bare negative premise (no contrary positive) must not be flagged, and
    // NAF query semantics are unchanged: the positive is simply not derivable.
    let kb = new_kb();
    assert_id(&kb, make_negated_assertion("alis", "gerku"), "~dog().");
    assert!(query_false(&kb, make_query("alis", "gerku")));
    assert!(
        kb.check_contradictions().is_empty(),
        "a lone negative fact is not a contradiction"
    );
}

#[test]
fn test_negated_event_decomposed_fact_contradicts_contrary_positive() {
    // The pipeline shape (probe-verified): `la .adam. na gerku` compiles to
    // ¬∃e.(gerku(e) ∧ gerku_x1(e, adam) ∧ gerku_x2(e, zo'e)), and the later
    // contrary positive gets a DIFFERENT fresh event Skolem. The negative
    // templates generalize the event argument, so the contradiction must still
    // be detected across the Skolem mismatch.
    let kb = new_kb();
    assert_id(&kb, make_event_decomposed("adam", "gerku", true), "~dog().");
    assert_id(&kb, make_event_decomposed("adam", "gerku", false), "gerku");
    let violations = kb.check_contradictions();
    assert!(
        violations
            .iter()
            .any(|v| v.contains("Negation contradiction")),
        "event-decomposed contrary positive must be flagged: {violations:?}"
    );
}

#[test]
fn test_negated_event_decomposed_fact_ignores_other_entities() {
    // ¬gerku(adam) + gerku(bob) is NOT a contradiction: the whole negative
    // template group must unify under ONE event binding, so an unrelated
    // entity's dog-event cannot trigger a false positive.
    let kb = new_kb();
    assert_id(&kb, make_event_decomposed("adam", "gerku", true), "~dog().");
    assert_id(
        &kb,
        make_event_decomposed("bob", "gerku", false),
        "bob gerku",
    );
    assert!(
        kb.check_contradictions().is_empty(),
        "a different entity's positive must not contradict adam's negation"
    );
}

#[test]
fn test_negated_fact_retraction_clears_contradiction() {
    // Retracting the negative record must clear the contradiction (the
    // negation-bearing buffer takes the rebuild path, which repopulates the
    // negative registry from the surviving records).
    let kb = new_kb();
    let neg_id = assert_id(&kb, make_negated_assertion("alis", "gerku"), "~dog().");
    assert_id(&kb, make_assertion("alis", "gerku"), "gerku");
    assert!(!kb.check_contradictions().is_empty());
    kb.retract_fact_inner(neg_id).unwrap();
    assert!(
        kb.check_contradictions().is_empty(),
        "retracting the negation must clear the contradiction"
    );
    // The positive fact must survive the rebuild.
    assert!(query(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_list_facts_empty() {
    let kb = new_kb();
    let facts = kb.list_facts_inner().unwrap();
    assert!(facts.is_empty());
}

#[test]
fn test_list_facts_after_assert() {
    let kb = new_kb();
    assert_id(&kb, make_assertion("alis", "gerku"), "dog(Alis).");
    let facts = kb.list_facts_inner().unwrap();
    assert_eq!(facts.len(), 1);
    assert_eq!(facts[0].label, "dog(Alis).");
    assert_eq!(facts[0].root_count, 1);
}

#[test]
fn test_list_facts_excludes_retracted() {
    let kb = new_kb();
    let id = assert_id(&kb, make_assertion("alis", "gerku"), "");
    assert_id(&kb, make_assertion("bob", "mlatu"), "bob mlatu");
    kb.retract_fact_inner(id).unwrap();
    let facts = kb.list_facts_inner().unwrap();
    assert_eq!(facts.len(), 1);
    assert_eq!(facts[0].id, 1); // bob's fact
    assert_eq!(facts[0].label, "bob mlatu");
}

#[test]
fn test_reset_clears_registry() {
    let kb = new_kb();
    assert_id(&kb, make_assertion("alis", "gerku"), "");
    kb.inner.borrow_mut().reset();
    let facts = kb.list_facts_inner().unwrap();
    assert!(facts.is_empty());
    assert!(query_false(&kb, make_query("alis", "gerku")));
}

#[test]
fn split_roots_yields_independent_facts() {
    // A bare-`.i` multi-sentence compile splits (by root) into two INDEPENDENT
    // facts: each queryable, and retracting one leaves the other intact. Uses the
    // real surface shape (event-decomposed), so this exercises split + skolem
    // witness retraction end-to-end.
    let kb = new_kb();
    let buf = compile_surface("dog(Adam). dog(Betis).");
    let parts = buf.split_roots();
    assert_eq!(parts.len(), 2, "bare `.i` must split into two roots");

    let id0 = assert_id(&kb, parts[0].clone(), "adam");
    let _id1 = assert_id(&kb, parts[1].clone(), "betis");
    assert_eq!(
        kb.list_facts_inner().unwrap().len(),
        2,
        "two independent facts, not one multi-root fact"
    );

    assert!(query(&kb, compile_surface("dog(Adam).")));
    assert!(query(&kb, compile_surface("dog(Betis).")));

    // Retract one sentence — the other survives independently.
    kb.retract_fact_inner(id0).unwrap();
    assert!(query_false(&kb, compile_surface("dog(Adam).")));
    assert!(query(&kb, compile_surface("dog(Betis).")));
    assert_eq!(kb.list_facts_inner().unwrap().len(), 1);
}

#[test]
fn split_roots_keeps_connective_as_one_fact() {
    // `.i je` (afterthought AND) is a single compound proposition → one root → one
    // fact. Only bare `.i` splits.
    let buf = compile_surface("dog(Adam) & dog(Betis).");
    assert_eq!(
        buf.split_roots().len(),
        1,
        "a connective (`.i je`) must stay one compound fact"
    );
}

/// Kills kb.rs `replace match guard subs.contains_key(v.as_str()) with false
/// in record_negative_conjuncts`. The guard peels a SKOLEMIZED root ∃ so a
/// negated conjunct inside its And-spine reaches the negative-fact registry.
/// The KR front-end distributes ∃-closure per conjunct (the root is an And),
/// so the peel only fires on RAW-FOL buffers — `assert_fact` is a public
/// buffer API, and this is exactly the shape: ∃x.(person(x) ∧ ¬dog(kim)).
/// Under the mutant the walk falls to the single-negation arm, whose own
/// root-shape check sees a non-negation And under the ∃ and records nothing —
/// the later contrary positive then sails through check_contradictions.
#[test]
fn negated_conjunct_under_raw_root_exists_records_for_contradictions() {
    let kb = new_kb();
    let mut nodes = Vec::new();
    let person = pred(
        &mut nodes,
        "person",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let dog_kim = pred(
        &mut nodes,
        "dog",
        vec![
            LogicalTerm::Constant("kim".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg = not(&mut nodes, dog_kim);
    let both = and(&mut nodes, person, neg);
    let root = exists(&mut nodes, "x", both);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    assert_buf(&kb, make_assertion("kim", "dog"));
    let v = kb.check_contradictions();
    assert!(
        v.iter().any(|m| m.contains("dog")),
        "the ∃-scoped ¬dog(kim) must be recorded and contradicted by dog(kim): {v:?}"
    );
}
