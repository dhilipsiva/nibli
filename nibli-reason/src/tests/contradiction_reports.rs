// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

fn surface_kb(statements: &[&str]) -> KnowledgeBase {
    let kb = new_kb();
    for statement in statements {
        assert_buf(&kb, compile_surface(statement));
    }
    kb
}

#[test]
fn contradictions_report_direct_and_derived_negatives() {
    for rule in [false, true] {
        let kb = if rule {
            surface_kb(&["travel(every person).", "person(Adam).", "~travel(Adam)."])
        } else {
            surface_kb(&["travel(Adam).", "~travel(Adam)."])
        };
        let report = kb.check_contradictions_report();
        assert!(!report.violations.is_empty(), "{report:?}");
        assert!(report.unresolved.is_empty(), "{report:?}");
        assert_eq!(kb.check_contradictions(), report.violations);
    }
    for source in [
        vec!["~travel(Adam)."],
        vec!["travel(Bob).", "~travel(Adam)."],
        vec!["past travel(Adam).", "~travel(Adam)."],
        vec!["believe(Adam, event { ~travel(Bob) }).", "travel(Bob)."],
        vec!["travel(every person where ~prisoner).", "person(Adam)."],
    ] {
        let report = surface_kb(&source).check_contradictions_report();
        assert!(report.is_clean(), "{source:?}: {report:?}");
    }
}

#[test]
fn contradictions_report_derived_integrity_conjunction() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("dog", "animal"));
    assert_buf(&kb, make_assertion("adam", "dog"));
    let animal = StoredFact::Bare(GroundFact::new(
        "animal",
        vec![GroundTerm::Constant("adam".into()), GroundTerm::Unspecified],
    ));
    let cat = StoredFact::Bare(GroundFact::new(
        "cat",
        vec![GroundTerm::Constant("adam".into()), GroundTerm::Unspecified],
    ));
    kb.register_constraint("animal-and-cat".into(), vec![animal, cat])
        .unwrap();
    assert!(kb.check_contradictions_report().is_clean());
    assert_buf(&kb, make_assertion("adam", "cat"));
    let report = kb.check_contradictions_report();
    assert_eq!(report.violations.len(), 1, "{report:?}");
    assert!(report.unresolved.is_empty(), "{report:?}");
}

#[test]
fn contradictions_report_derived_disjunction_surface_and_retraction() {
    let kb = surface_kb(&[
        "dog(every person).",
        "all $x: dog($x) -> (animal($x) | travel($x)).",
        "person(Adam).",
        "~animal(Adam).",
    ]);
    assert!(kb.check_contradictions_report().is_clean());
    let denial = assert_id(&kb, compile_surface("~travel(Adam)."), "denial");
    let report = kb.check_contradictions_report();
    assert!(
        report
            .violations
            .iter()
            .any(|v| v.starts_with("Disjunctive constraint violated")),
        "{report:?}"
    );
    assert!(report.unresolved.is_empty(), "{report:?}");
    kb.retract_fact(denial).unwrap();
    assert!(kb.check_contradictions_report().is_clean());
}

#[test]
fn contradictions_report_incomplete_never_reads_as_clean() {
    let kb = new_kb();
    kb.set_materialization(false);
    kb.set_max_chain_depth(1).unwrap();
    for (from, to) in [("person", "dog"), ("dog", "cat"), ("cat", "travel")] {
        assert_buf(&kb, make_universal(from, to));
    }
    assert_buf(&kb, make_assertion("adam", "person"));
    assert_buf(&kb, make_negated_assertion("adam", "travel"));
    let report = kb.check_contradictions_report();
    assert!(report.violations.is_empty(), "{report:?}");
    assert!(
        matches!(
            report.unresolved[0].reason,
            ContradictionGapReason::ResourceExceeded(ResourceKind::Depth)
        ),
        "{report:?}"
    );
    assert!(!report.is_clean());

    kb.set_cancel_flag(Arc::new(std::sync::atomic::AtomicBool::new(true)));
    let report = kb.check_contradictions_report();
    assert!(
        matches!(
            report.unresolved[0].reason,
            ContradictionGapReason::EvaluationError(_)
        ),
        "{report:?}"
    );
    assert!(!report.is_clean());
}

#[test]
fn contradictions_report_discloses_unsupported_assertions_and_replays() {
    let kb = new_kb();
    // The KR surface rejects compound negation, while the native raw-IR
    // assertion boundary can retain it alongside an ordinary positive fact.
    let mut nodes = Vec::new();
    let args = vec![LogicalTerm::Constant("adam".into())];
    let person = pred(&mut nodes, "person", args.clone());
    let dog = pred(&mut nodes, "dog", args.clone());
    let cat = pred(&mut nodes, "cat", args);
    let not_cat = not(&mut nodes, cat);
    let body = and(&mut nodes, dog, not_cat);
    let negation = not(&mut nodes, body);
    let root = and(&mut nodes, person, negation);
    let id = assert_id(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
        "nested negation",
    );
    let report = kb.check_contradictions_report();
    assert!(report.violations.is_empty(), "{report:?}");
    assert_eq!(report.unresolved.len(), 1, "{report:?}");
    assert!(report.unresolved[0].context.contains("nested negation"));
    assert!(matches!(
        report.unresolved[0].reason,
        ContradictionGapReason::Unsupported(_)
    ));
    // A snapshot keeps the report, and replay after an unrelated retraction
    // must keep it until the unsupported assertion itself is removed.
    kb.with_assumptions(&[], |snapshot| {
        assert_eq!(snapshot.check_contradictions_report(), report);
    })
    .unwrap();
    let other = assert_id(&kb, compile_surface("person(Bob)."), "other");
    kb.retract_fact(other).unwrap();
    assert_eq!(kb.check_contradictions_report(), report);
    kb.retract_fact(id).unwrap();
    assert!(kb.check_contradictions_report().is_clean());
}

#[test]
fn contradictions_report_preserves_deontic_flavors() {
    // An obligation is not actuality. The negative registry must preserve the
    // wrapper even when it is outside the Not node.
    for positive in ["travel(Adam).", "may travel(Adam)."] {
        let kb = surface_kb(&[positive, "must ~travel(Adam)."]);
        let report = kb.check_contradictions_report();
        assert!(report.is_clean(), "{positive}: {report:?}");
    }
    let kb = surface_kb(&["must travel(Adam).", "must ~travel(Adam)."]);
    let report = kb.check_contradictions_report();
    assert!(!report.violations.is_empty(), "{report:?}");
    assert!(report.unresolved.is_empty(), "{report:?}");
}

#[test]
fn contradictions_report_keeps_unknown_separate_from_findings() {
    let kb = new_kb();
    kb.set_materialization(false);
    assert_buf(&kb, make_universal("dog", "cat"));
    assert_buf(&kb, make_universal("cat", "dog"));
    assert_buf(&kb, make_assertion("adam", "person"));
    assert_buf(&kb, make_negated_assertion("adam", "dog"));
    let report = kb.check_contradictions_report();
    assert!(report.violations.is_empty(), "{report:?}");
    assert!(
        report
            .unresolved
            .iter()
            .any(|gap| matches!(gap.reason, ContradictionGapReason::Unknown(_))),
        "{report:?}"
    );
    assert_buf(&kb, make_assertion("bob", "travel"));
    assert_buf(&kb, make_negated_assertion("bob", "travel"));
    let mixed = kb.check_contradictions_report();
    assert!(!mixed.violations.is_empty(), "{mixed:?}");
    assert_eq!(mixed.unresolved, report.unresolved);
}

#[test]
fn contradictions_report_disjunctive_matching_keeps_generated_identity() {
    // This native IR case binds one generated individual across positive and
    // negative clauses; the text front-end deliberately rejects that scope.
    let kb = new_kb();
    assert_buf(&kb, make_universal("person", "dog"));
    let args = vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified];
    let mut nodes = Vec::new();
    let dog = pred(&mut nodes, "dog", args.clone());
    let animal = pred(&mut nodes, "animal", args.clone());
    let travel = pred(&mut nodes, "travel", args.clone());
    let not_dog = not(&mut nodes, dog);
    let conclusion = or(&mut nodes, animal, travel);
    let implication = or(&mut nodes, not_dog, conclusion);
    let root = forall(&mut nodes, "x", implication);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    let mut nodes = Vec::new();
    let person = pred(&mut nodes, "person", args.clone());
    let animal = pred(&mut nodes, "animal", args.clone());
    let travel = pred(&mut nodes, "travel", args);
    let not_animal = not(&mut nodes, animal);
    let not_travel = not(&mut nodes, travel);
    let denials = and(&mut nodes, not_animal, not_travel);
    let body = and(&mut nodes, person, denials);
    let root = exists(&mut nodes, "x", body);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    let report = kb.check_contradictions_report();
    assert!(
        report
            .violations
            .iter()
            .any(|finding| { finding.starts_with("Disjunctive constraint violated") }),
        "matching must preserve the existential person's identity: {report:?}"
    );
    // The independent positive-counterpart query cannot spell this private
    // generated individual in public IR: it is disclosed, never treated as a
    // definitive negative or reconstructed from a display string.
    assert!(
        report
            .unresolved
            .iter()
            .all(|gap| { matches!(gap.reason, ContradictionGapReason::Unsupported(_)) }),
        "{report:?}"
    );
}

#[test]
fn contradictions_report_discloses_incomplete_disjunction_enumeration() {
    let kb = surface_kb(&[
        "dog(every cat).",
        "cat(every dog).",
        "all $x: dog($x) -> (animal($x) | travel($x)).",
        "person(Adam).",
        "~animal(Adam).",
        "~travel(Adam).",
    ]);
    kb.set_materialization(false);
    let report = kb.check_contradictions_report();
    assert!(report.violations.is_empty(), "{report:?}");
    assert!(
        report.unresolved.iter().any(|gap| {
            gap.context.starts_with("disjunctive constraint")
                && matches!(&gap.reason, ContradictionGapReason::EvaluationError(error)
                if error.contains("enumeration incomplete"))
        }),
        "{report:?}"
    );
    assert!(!report.is_clean());
}
