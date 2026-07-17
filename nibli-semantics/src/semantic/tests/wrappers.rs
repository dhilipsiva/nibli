use super::*;

// ─── Tense wrapper tests ──────────────────────────────────

#[test]
fn test_tense_past_produces_past() {
    // pu mi klama → Past(klama(mi, ...))
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![Argument::Atom("me".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: Some(Tense::Past),
        deontic: None,
    };
    let (form, _) = compile_one(predicates, arguments, proposition);
    assert!(matches!(form, IrForm::Past(_)));
}

#[test]
fn test_tense_now_produces_present() {
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![Argument::Atom("me".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: Some(Tense::Now),
        deontic: None,
    };
    let (form, _) = compile_one(predicates, arguments, proposition);
    assert!(matches!(form, IrForm::Present(_)));
}

#[test]
fn test_tense_future_produces_future() {
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![Argument::Atom("me".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: Some(Tense::Future),
        deontic: None,
    };
    let (form, _) = compile_one(predicates, arguments, proposition);
    assert!(matches!(form, IrForm::Future(_)));
}

// ─── DeonticMood tests ────────────────────────────────────

#[test]
fn test_deontic_must_produces_obligatory() {
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![Argument::Atom("me".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: Some(DeonticMood::Obligation),
    };
    let (form, _) = compile_one(predicates, arguments, proposition);
    assert!(matches!(form, IrForm::Obligatory(_)));
}

#[test]
fn test_deontic_may_produces_permitted() {
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![Argument::Atom("me".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: Some(DeonticMood::Permission),
    };
    let (form, _) = compile_one(predicates, arguments, proposition);
    assert!(matches!(form, IrForm::Permitted(_)));
}

// ─── Negation test ────────────────────────────────────────

#[test]
fn test_predication_negation_produces_not() {
    // na mi klama → Not(klama(mi, ...))
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![Argument::Atom("me".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: true,
        tense: None,
        deontic: None,
    };
    let (form, _) = compile_one(predicates, arguments, proposition);
    assert!(matches!(form, IrForm::Not(_)));
}

// ─── Conversion SE tests ──────────────────────────────────

#[test]
fn test_x2_conversion_swaps_args() {
    // se prami mi do → prami(do, mi, ...) (x1↔x2 swapped)
    let predicates = vec![
        Predicate::Root("loves".into()),
        Predicate::Converted((Conversion::Swap12, 0)),
    ];
    let arguments = vec![Argument::Atom("me".into()), Argument::Atom("you".into())];
    let proposition = Proposition {
        relation: 1,
        terms: vec![0, 1],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    // With event decomposition, form is Exists(ev, And(prami(ev), prami_x1(ev, ...), prami_x2(ev, ...)))
    // After se-conversion: x1 and x2 are swapped
    // head=mi goes to x1 position, tail=do goes to x2 position
    // se swaps these: mi→x2, do→x1
    assert!(
        matches!(&form, IrForm::Exists(_, _)),
        "expected Exists, got {:?}",
        form
    );
    assert!(
        has_pred(&form, "loves", &compiler),
        "expected prami type predicate"
    );
    // Check prami_x1 has do (originally x2, swapped to x1)
    let x1_args = get_pred_args(&form, "loves_x1", &compiler).unwrap();
    match &x1_args[1] {
        IrTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "you"),
        other => panic!(
            "expected Constant(do) in prami_x1 after se-swap, got {:?}",
            other
        ),
    }
    // Check prami_x2 has mi (originally x1, swapped to x2)
    let x2_args = get_pred_args(&form, "loves_x2", &compiler).unwrap();
    match &x2_args[1] {
        IrTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "me"),
        other => panic!(
            "expected Constant(mi) in prami_x2 after se-swap, got {:?}",
            other
        ),
    }
}

// ─── Unspecified argument (zo'e) test ────────────────────────

#[test]
fn test_something_compiles_to_unspecified() {
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![Argument::Unspecified];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    // With event decomposition, form is Exists(ev, And(klama(ev), klama_x1(ev, zo'e), ...))
    assert!(
        matches!(&form, IrForm::Exists(_, _)),
        "expected Exists, got {:?}",
        form
    );
    // Check that klama_x1 has Unspecified (zo'e) in its entity arg
    let x1_args =
        get_pred_args(&form, "goes_x1", &compiler).expect("expected klama_x1 role predicate");
    assert!(
        matches!(x1_args[1], IrTerm::Unspecified),
        "expected Unspecified in klama_x1, got {:?}",
        x1_args[1]
    );
}
