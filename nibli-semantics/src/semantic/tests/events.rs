use super::*;

// ─── Event decomposition (Neo-Davidsonian) tests ──────────

#[test]
fn test_event_decompose_basic() {
    // mi klama → ∃e. klama(e) ∧ klama_x1(e, mi) ∧ klama_x2(e, zo'e) ∧ ...
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![Argument::Atom("me".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);

    // Top level should be Exists (event variable)
    assert!(matches!(&form, IrForm::Exists(_, _)));
    // Type predicate exists
    assert!(has_pred(&form, "goes", &compiler));
    // x1 role has Constant("me")
    let x1 = get_pred_args(&form, "goes_x1", &compiler).unwrap();
    assert_eq!(
        x1[1],
        IrTerm::Constant(compiler.interner.get("me").unwrap())
    );
    // Event variable is shared between type and role predicates
    let type_args = get_pred_args(&form, "goes", &compiler).unwrap();
    assert!(matches!(&type_args[0], IrTerm::Variable(_)));
    assert_eq!(type_args[0], x1[0], "event var should be shared");
}

#[test]
fn test_event_decompose_all_roles_emitted() {
    // klama has arity 5, all roles should be emitted
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![Argument::Atom("me".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);

    for i in 1..=5 {
        let role = format!("goes_x{}", i);
        assert!(has_pred(&form, &role, &compiler), "expected {} role", role);
    }
    // No x6 for a 5-arity predicate
    assert!(!has_pred(&form, "goes_x6", &compiler));
}

#[test]
fn test_event_pair_shared_event() {
    // sutra gerku → ∃e. gerku(e) ∧ gerku_x1(e, x1) ∧ sutra_x1(e, x1)
    // modifier and head share the SAME event variable
    let predicates = vec![
        Predicate::Root("fast".into()), // 0
        Predicate::Root("dog".into()),  // 1
        Predicate::Pair((0, 1)),        // 2
    ];
    let arguments = vec![Argument::Atom("me".into())];
    let proposition = Proposition {
        relation: 2,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);

    // Should have head type predicate
    assert!(has_pred(&form, "dog", &compiler));
    // Should have head x1 role
    assert!(has_pred(&form, "dog_x1", &compiler));
    // Should have modifier x1 role (NOT a full sutra predicate)
    assert!(has_pred(&form, "fast_x1", &compiler));

    // Both roles should share the same event variable
    let gerku_x1 = get_pred_args(&form, "dog_x1", &compiler).unwrap();
    let sutra_x1 = get_pred_args(&form, "fast_x1", &compiler).unwrap();
    assert_eq!(
        gerku_x1[0], sutra_x1[0],
        "event var should be shared between head and modifier"
    );

    // Both x1 entity args should be mi
    let mi = IrTerm::Constant(compiler.interner.get("me").unwrap());
    assert_eq!(gerku_x1[1], mi);
    assert_eq!(sutra_x1[1], mi);
}

#[test]
fn test_event_pair_no_intersective_fallacy() {
    // barda gerku → NOT And(barda(x1), gerku(x1, ...))
    // Instead: ∃e. gerku(e) ∧ gerku_x1(e, x1) ∧ barda_x1(e, x1)
    // The modifier "big" is event-bound, not a standalone predication
    let predicates = vec![
        Predicate::Root("big".into()), // 0
        Predicate::Root("dog".into()), // 1
        Predicate::Pair((0, 1)),       // 2
    ];
    let arguments = vec![Argument::Atom("me".into())];
    let proposition = Proposition {
        relation: 2,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);

    // There should be NO standalone "big" type predicate
    // Only "big_x1" role predicate (event-bound modifier)
    let preds = collect_predicates(&form, &compiler);
    let barda_preds: Vec<_> = preds.iter().filter(|(n, _)| n == "big").collect();
    assert!(
        barda_preds.is_empty(),
        "should NOT have standalone barda predicate, got {:?}",
        barda_preds
    );
    assert!(
        has_pred(&form, "big_x1", &compiler),
        "should have event-bound barda_x1 role"
    );
}

#[test]
fn test_event_decompose_with_quantifier() {
    // lo gerku cu klama → ∃x. (∃e1. gerku(e1) ∧ gerku_x1(e1, x)) ∧ (∃e2. klama(e2) ∧ klama_x1(e2, x) ∧ ...)
    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("goes".into()), // 1
    ];
    let arguments = vec![
        Argument::Description((Determiner::Indefinite, 0)), // 0: lo gerku
    ];
    let proposition = Proposition {
        relation: 1,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);

    // Outer Exists for the description variable
    assert!(matches!(&form, IrForm::Exists(_, _)));
    // Both gerku and klama predicates exist
    assert!(has_pred(&form, "dog", &compiler));
    assert!(has_pred(&form, "goes", &compiler));
    // Both have x1 roles
    assert!(has_pred(&form, "dog_x1", &compiler));
    assert!(has_pred(&form, "goes_x1", &compiler));
}

#[test]
fn test_event_conversion_x2() {
    // mi se prami do → prami(do, mi, ...) with se-swapped args
    // Event form: ∃e. prami(e) ∧ prami_x1(e, do) ∧ prami_x2(e, mi)
    let predicates = vec![
        Predicate::Root("loves".into()),               // 0
        Predicate::Converted((Conversion::Swap12, 0)), // 1
    ];
    let arguments = vec![
        Argument::Atom("me".into()),  // 0
        Argument::Atom("you".into()), // 1
    ];
    let proposition = Proposition {
        relation: 1,
        terms: vec![0, 1],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);

    // se swaps x1 and x2: mi goes to x2, do goes to x1
    let x1 = get_pred_args(&form, "loves_x1", &compiler).unwrap();
    let x2 = get_pred_args(&form, "loves_x2", &compiler).unwrap();
    assert_eq!(
        x1[1],
        IrTerm::Constant(compiler.interner.get("you").unwrap())
    );
    assert_eq!(
        x2[1],
        IrTerm::Constant(compiler.interner.get("me").unwrap())
    );
}
