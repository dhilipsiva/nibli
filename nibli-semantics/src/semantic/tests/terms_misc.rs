use super::*;

// ─── Name (rigid Name) test ──────────────────────────────

#[test]
fn test_la_name_compiles_to_constant() {
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![Argument::Name("alis".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    // With event decomposition, form is Exists(ev, And(klama(ev), klama_x1(ev, alis), ...))
    assert!(
        matches!(&form, IrForm::Exists(_, _)),
        "expected Exists, got {:?}",
        form
    );
    let x1_args =
        get_pred_args(&form, "goes_x1", &compiler).expect("expected klama_x1 role predicate");
    match &x1_args[1] {
        IrTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "alis"),
        other => panic!("expected Constant(alis), got {:?}", other),
    }
}

// ─── Number argument (li PA) test ────────────────────────────

#[test]
fn test_number_argument_compiles_to_number() {
    let predicates = vec![Predicate::Root("number".into())];
    let arguments = vec![Argument::Number(42.0)];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    // With event decomposition, form is Exists(ev, And(namcu(ev), namcu_x1(ev, 42.0), ...))
    assert!(
        matches!(&form, IrForm::Exists(_, _)),
        "expected Exists, got {:?}",
        form
    );
    let x1_args =
        get_pred_args(&form, "number_x1", &compiler).expect("expected namcu_x1 role predicate");
    assert!(
        matches!(x1_args[1], IrTerm::Number(n) if n == 42.0),
        "expected Number(42.0) in namcu_x1, got {:?}",
        x1_args[1]
    );
}

// ─── Quoted literal test ──────────────────────────────────

#[test]
fn test_quoted_literal_compiles_to_constant() {
    let predicates = vec![Predicate::Root("word".into())];
    let arguments = vec![Argument::QuotedLiteral("coi".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    // With event decomposition, form is Exists(ev, And(valsi(ev), valsi_x1(ev, coi), ...))
    assert!(
        matches!(&form, IrForm::Exists(_, _)),
        "expected Exists, got {:?}",
        form
    );
    let x1_args =
        get_pred_args(&form, "word_x1", &compiler).expect("expected valsi_x1 role predicate");
    match &x1_args[1] {
        IrTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "coi"),
        other => panic!("expected Constant(coi), got {:?}", other),
    }
}

// ─── Predicate connective tests ──────────────────────────────

// ─── Arity from dictionary ────────────────────────────────

#[test]
fn test_known_gismu_gets_correct_arity() {
    // klama has arity 5, so there should be 5 role predicates (klama_x1..klama_x5)
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
    // With event decomposition, check that all 5 role predicates exist
    assert!(
        matches!(&form, IrForm::Exists(_, _)),
        "expected Exists, got {:?}",
        form
    );
    assert!(
        has_pred(&form, "goes", &compiler),
        "expected klama type predicate"
    );
    for i in 1..=5 {
        let role = format!("goes_x{}", i);
        assert!(
            has_pred(&form, &role, &compiler),
            "klama should have role predicate {}",
            role
        );
    }
}

#[test]
fn test_unknown_gismu_defaults_to_arity_2() {
    // An unrecognized word should default to arity 2 → 2 role predicates
    let predicates = vec![Predicate::Root("xyzzy".into())];
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
    // With event decomposition, check that there are 2 role predicates
    assert!(
        matches!(&form, IrForm::Exists(_, _)),
        "expected Exists, got {:?}",
        form
    );
    assert!(
        has_pred(&form, "xyzzy", &compiler),
        "expected xyzzy type predicate"
    );
    assert!(
        has_pred(&form, "xyzzy_x1", &compiler),
        "expected xyzzy_x1 role"
    );
    assert!(
        has_pred(&form, "xyzzy_x2", &compiler),
        "expected xyzzy_x2 role"
    );
    // Should NOT have xyzzy_x3
    assert!(
        !has_pred(&form, "xyzzy_x3", &compiler),
        "unknown word should default to arity 2, but found xyzzy_x3"
    );
}

// ─── Sentence connective tests ────────────────────────────

#[test]
fn test_sentence_connective_ge_gi_produces_and() {
    // ge mi klama gi do sutra → And(klama(mi,...), sutra(do,...))
    let predicates = vec![
        Predicate::Root("goes".into()),
        Predicate::Root("fast".into()),
    ];
    let arguments = vec![Argument::Atom("me".into()), Argument::Atom("you".into())];
    let sentences = vec![
        Sentence::Connected((
            SentenceConnective::And,
            1, // left sentence idx
            2, // right sentence idx
        )),
        Sentence::Simple(Proposition {
            relation: 0,
            terms: vec![0],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 1,
            terms: vec![1],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];
    let (form, _) = compile_sentence_full(predicates, arguments, sentences);
    assert!(matches!(form, IrForm::And(_, _)));
}

// ─── Fresh variable generation ────────────────────────────

#[test]
fn test_fresh_vars_are_unique() {
    let mut compiler = SemanticCompiler::new();
    let v1 = compiler.fresh_var();
    let v2 = compiler.fresh_var();
    let v3 = compiler.fresh_var();
    assert_ne!(v1, v2);
    assert_ne!(v2, v3);
    assert_ne!(v1, v3);
    assert_eq!(compiler.interner.resolve(&v1), "_v0");
    assert_eq!(compiler.interner.resolve(&v2), "_v1");
    assert_eq!(compiler.interner.resolve(&v3), "_v2");
}

// ─── via modal tag mapping ───────────────────────────────

// ─── inject_variable into conjunction ─────────────────────

#[test]
fn test_inject_variable_into_and() {
    let mut compiler = SemanticCompiler::new();
    let rel1 = compiler.interner.get_or_intern("dog");
    let rel2 = compiler.interner.get_or_intern("big");
    let var = compiler.interner.get_or_intern("_v0");
    let form = IrForm::And(
        Box::new(IrForm::Predicate {
            relation: rel1,
            args: vec![IrTerm::Unspecified],
        }),
        Box::new(IrForm::Predicate {
            relation: rel2,
            args: vec![IrTerm::Unspecified],
        }),
    );
    let injected = SemanticCompiler::inject_variable(form, var, &compiler.interner);
    match injected {
        IrForm::And(left, right) => {
            // inject_variable fills the FIRST unspecified in the first predicate found
            match left.as_ref() {
                IrForm::Predicate { args, .. } => {
                    assert!(matches!(args[0], IrTerm::Variable(_)));
                }
                other => panic!("expected Predicate, got {:?}", other),
            }
            match right.as_ref() {
                IrForm::Predicate { args, .. } => {
                    assert!(matches!(args[0], IrTerm::Variable(_)));
                }
                other => panic!("expected Predicate, got {:?}", other),
            }
        }
        other => panic!("expected And, got {:?}", other),
    }
}

// ─── No-arg predicate ─────────────────────────────────────

#[test]
fn test_predicate_with_no_explicit_args() {
    // Just "goes" alone → should produce event-decomposed form with all Unspecified role args
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments: Vec<Argument> = vec![];
    let proposition = Proposition {
        relation: 0,
        terms: vec![],
        x1_present: false,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    // With event decomposition, should be Exists(ev, And(klama(ev), klama_x1(ev, zo'e), ...))
    assert!(
        matches!(&form, IrForm::Exists(_, _)),
        "expected Exists, got {:?}",
        form
    );
    assert!(
        has_pred(&form, "goes", &compiler),
        "expected klama type predicate"
    );
    // All role predicates should have Unspecified in entity position
    for i in 1..=5 {
        let role = format!("goes_x{}", i);
        let role_args = get_pred_args(&form, &role, &compiler)
            .unwrap_or_else(|| panic!("expected {} role predicate", role));
        assert!(
            matches!(role_args[1], IrTerm::Unspecified),
            "expected Unspecified in {}, got {:?}",
            role,
            role_args[1]
        );
    }
}

// ─── C5: Description term opacity tests ──────────────────────

#[test]
fn test_le_description_stays_description() {
    // le gerku cu barda → Description("dog") in x1 role predicate
    let predicates = vec![Predicate::Root("dog".into()), Predicate::Root("big".into())];
    let arguments = vec![Argument::Description((Determiner::Definite, 0))];
    let proposition = Proposition {
        relation: 1,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    let args = get_pred_args(&form, "big_x1", &compiler).expect("expected barda_x1 role predicate");
    match &args[1] {
        IrTerm::Description(d) => assert_eq!(resolve(&compiler, d), "dog"),
        other => panic!("expected Description(gerku), got {:?}", other),
    }
}

#[test]
fn test_ro_le_uses_opaque_domain_restrictor() {
    // ro le gerku cu sutra → ForAll(_v0, Or(Not(the_domain_dog(_v0)), ...))
    let predicates = vec![
        Predicate::Root("dog".into()),
        Predicate::Root("fast".into()),
    ];
    let arguments = vec![Argument::Description((Determiner::EveryThe, 0))];
    let proposition = Proposition {
        relation: 1,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    // Must be ForAll at the top
    assert!(
        matches!(&form, IrForm::ForAll(_, _)),
        "expected ForAll, got {:?}",
        form
    );
    // The restrictor should be the_domain_dog (not gerku)
    assert!(
        has_pred(&form, "the_domain_dog", &compiler),
        "expected opaque the_domain_dog restrictor"
    );
    assert!(
        !has_pred(&form, "dog", &compiler),
        "veridical gerku should NOT appear as restrictor for ro le"
    );
}

#[test]
fn test_ro_lo_still_veridical() {
    // ro lo gerku cu sutra → ForAll with veridical gerku restrictor
    let predicates = vec![
        Predicate::Root("dog".into()),
        Predicate::Root("fast".into()),
    ];
    let arguments = vec![Argument::Description((Determiner::Every, 0))];
    let proposition = Proposition {
        relation: 1,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(
        matches!(&form, IrForm::ForAll(_, _)),
        "expected ForAll, got {:?}",
        form
    );
    // The restrictor should use veridical gerku (event-decomposed)
    assert!(
        has_pred(&form, "dog", &compiler),
        "expected veridical gerku restrictor for ro lo"
    );
    assert!(
        !has_pred(&form, "the_domain_dog", &compiler),
        "the_domain_dog should NOT appear for ro lo"
    );
}

#[test]
fn test_pa_le_uses_opaque_domain_restrictor() {
    // re le gerku cu sutra → Count with the_domain_dog restrictor
    let predicates = vec![
        Predicate::Root("dog".into()),
        Predicate::Root("fast".into()),
    ];
    let arguments = vec![Argument::QuantifiedDescription((
        2,
        Determiner::Definite,
        0,
    ))];
    let proposition = Proposition {
        relation: 1,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(
        matches!(&form, IrForm::Count { count: 2, .. }),
        "expected Count(2), got {:?}",
        form
    );
    assert!(
        has_pred(&form, "the_domain_dog", &compiler),
        "expected opaque the_domain_dog restrictor for PA le"
    );
    assert!(
        !has_pred(&form, "dog", &compiler),
        "veridical gerku should NOT appear for PA le"
    );
}

#[test]
fn test_pa_lo_still_veridical() {
    // re lo gerku cu sutra → Count with veridical gerku restrictor
    let predicates = vec![
        Predicate::Root("dog".into()),
        Predicate::Root("fast".into()),
    ];
    let arguments = vec![Argument::QuantifiedDescription((
        2,
        Determiner::Indefinite,
        0,
    ))];
    let proposition = Proposition {
        relation: 1,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(
        matches!(&form, IrForm::Count { count: 2, .. }),
        "expected Count(2), got {:?}",
        form
    );
    assert!(
        has_pred(&form, "dog", &compiler),
        "expected veridical gerku restrictor for PA lo"
    );
    assert!(
        !has_pred(&form, "the_domain_dog", &compiler),
        "the_domain_dog should NOT appear for PA lo"
    );
}
