use super::*;

// ─── inject_variable ambiguity tests ────────────────────────

#[test]
fn test_inject_variable_single_predicate_no_error() {
    // lo gerku poi barda cu klama
    // Rel clause body "big" has only 1 predicate with unspecified slot — no ambiguity.
    //
    // Buffer layout:
    //   predicates: [0: gerku, 1: barda, 2: klama]
    //   arguments:  [0: Description(Lo, 0), 1: Restricted(0, poi body=1)]
    //   sentences: [0: Simple(klama, head=[1]), 1: Simple(barda, head=[])]
    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("big".into()),  // 1
        Predicate::Root("goes".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Indefinite, 0)), // 0: lo gerku
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 1: lo gerku poi barda
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 2,
            terms: vec![1],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 1,
            terms: vec![],
            x1_present: false,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];

    let (_form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    // No errors — single predicate is unambiguous
    assert!(
        compiler.errors.is_empty(),
        "Expected no errors, got: {:?}",
        compiler.errors
    );
}

#[test]
fn test_nested_description_implicit_kea_rejected() {
    // lo gerku poi lo mlatu cu barda
    // The relative-clause body has NO unfilled subject (_x1) slot for the described
    // dog (the cat fills barda's x1), and ke'a is implicit. Per the firewall (book
    // Ch6), the engine REJECTS and demands explicit ke'a rather than guessing.
    //
    // Buffer layout:
    //   predicates: [0: gerku, 1: mlatu, 2: barda]
    //   arguments:  [0: Description(Lo, 0), 1: Description(Lo, 1), 2: Restricted(0, poi body=1)]
    //   sentences: [0: Simple(barda, head=[2]), 1: Simple(barda, head=[1])]
    let predicates = vec![
        Predicate::Root("dog".into()), // 0
        Predicate::Root("cat".into()), // 1
        Predicate::Root("big".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Indefinite, 0)), // 0: lo gerku
        Argument::Description((Determiner::Indefinite, 1)), // 1: lo mlatu
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 2: lo gerku poi ...
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 2,    // barda (main sentence)
            terms: vec![2], // lo gerku poi ...
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 2,    // barda (rel clause body: lo mlatu cu barda)
            terms: vec![1], // lo mlatu
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];

    let (_form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    // Firewall: no unambiguous subject slot for the implicit ke'a → rejected.
    assert!(
        !compiler.errors.is_empty(),
        "Expected an ambiguity/ke'a error for an implicit-ke'a nested description"
    );
    assert!(
        compiler.errors.iter().any(|e| e.contains("explicit `it`")),
        "Error should direct the user to an explicit `it`, got: {:?}",
        compiler.errors
    );
}

#[test]
fn test_inject_variable_with_explicit_kea_no_error() {
    // lo gerku poi ke'a barda cu klama
    // ke'a used explicitly — no injection needed, no error.
    //
    // Buffer layout:
    //   predicates: [0: gerku, 1: barda, 2: klama]
    //   arguments:  [0: Description(Lo, 0), 1: Atom("it"), 2: Restricted(0, poi body=1)]
    //   sentences: [0: Simple(klama, head=[2]), 1: Simple(barda, head=[1])]
    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("big".into()),  // 1
        Predicate::Root("goes".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Indefinite, 0)), // 0: lo gerku
        Argument::Marker(Marker::It),                       // 1: ke'a
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 2: lo gerku poi ke'a barda
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 2,
            terms: vec![2],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 1,
            terms: vec![1], // ke'a as head term
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];

    let (_form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    // No errors — ke'a was used explicitly
    assert!(
        compiler.errors.is_empty(),
        "Expected no errors, got: {:?}",
        compiler.errors
    );
}

#[test]
fn test_single_predicate_injects_head_into_subject() {
    // lo gerku poi barda cu klama
    // The relative-clause body `barda` has exactly one unfilled subject (_x1) slot,
    // so the described dog is injected there. Verify no error AND that the dog's
    // variable actually appears in barda_x1 (the same variable bound by gerku).
    //
    // Buffer layout:
    //   predicates: [0: gerku, 1: barda, 2: klama]
    //   arguments:  [0: Description(Lo, 0), 1: Restricted(0, poi body=1)]
    //   sentences: [0: Simple(klama, head=[1]), 1: Simple(barda, head=[])]
    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("big".into()),  // 1
        Predicate::Root("goes".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Indefinite, 0)), // 0: lo gerku
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 1: lo gerku poi barda
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 2,
            terms: vec![1],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 1,
            terms: vec![],
            x1_present: false,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];

    let (form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    assert!(
        compiler.errors.is_empty(),
        "Expected no errors for a single-predicate clause, got: {:?}",
        compiler.errors
    );
    let barda_args =
        get_pred_args(&form, "big_x1", &compiler).expect("big_x1 role predicate should be present");
    let gerku_args =
        get_pred_args(&form, "dog_x1", &compiler).expect("dog_x1 role predicate should be present");
    // The implicit ke'a (dog) variable is injected into barda's subject slot, and it
    // must be the SAME variable bound by the gerku description.
    assert!(
        matches!(barda_args[1], IrTerm::Variable(_)),
        "dog variable should be injected into barda_x1, got {:?}",
        barda_args[1]
    );
    assert_eq!(
        barda_args[1], gerku_args[1],
        "big_x1 must bind the same variable as gerku_x1 (the described dog)"
    );
}

#[test]
fn test_x1_tag_name_x2_tag_it_skips_x1_injection() {
    // `ro lo gerku poi prami fa la .alis. fe ke'a cu danlu` — the exact KR
    // spelling `animal(every dog where loves(lover: Alis, loved: it)).`
    // The all-named lowering leaves the body HEAD EMPTY with FA-tagged tail
    // terms (`fa alis`, `fe ke'a`). The implicit-ke'a x1 injection must SKIP
    // (an explicit ke'a rides at x2), or `fa alis` collides with the
    // pre-filled x1 → "place already filled" reject (the shipped-language
    // defect this fixes). alis lands at x1 (lover), ke'a/dog at x2 (loved).
    let predicates = vec![
        Predicate::Root("dog".into()),    // 0
        Predicate::Root("loves".into()),  // 1
        Predicate::Root("animal".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Every, 0)), // 0: ro lo gerku
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 1: ro lo gerku poi <body>
        Argument::Marker(Marker::It),                  // 2: ke'a
        Argument::Name("alis".into()),                 // 3: alis
        Argument::Tagged((0, 3)),                      // 4: fa alis  (x1, lover)
        Argument::Tagged((1, 2)),                      // 5: fe ke'a  (x2, loved)
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 2, // danlu (main: `animal(every dog)`)
            terms: vec![1],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 1, // prami (body: head EMPTY, all FA-tagged)
            terms: vec![4, 5],
            x1_present: false,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];
    let (form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    assert!(
        compiler.errors.is_empty(),
        "explicit fe-tagged ke'a must not collide with the implicit injection: {:?}",
        compiler.errors
    );
    let prami_x1 = get_pred_args(&form, "loves_x1", &compiler).expect("loves_x1 present");
    let prami_x2 = get_pred_args(&form, "loves_x2", &compiler).expect("loves_x2 present");
    let gerku_x1 = get_pred_args(&form, "dog_x1", &compiler).expect("dog_x1 present");
    assert_eq!(
        const_str(&compiler, &prami_x1[1]),
        "alis",
        "x1 must be the lover, alis"
    );
    assert_eq!(
        prami_x2[1], gerku_x1[1],
        "the fe-tagged ke'a must bind the described dog at x2 (the loved)"
    );
}

#[test]
fn test_x1_tagged_it_skips_x1_injection() {
    // `ro lo gerku poi prami fa ke'a fe la .alis. cu danlu` —
    // `animal(every dog where loves(lover: it, loved: Alis)).`
    // Mirror image of the above: the explicit ke'a rides UNDER the `fa` (x1)
    // tag. The scan must unwrap the place tag to see it and SKIP the
    // injection (otherwise `fa ke'a` collides with the pre-filled x1). ke'a/
    // dog lands at x1 (lover), alis at x2 (loved).
    let predicates = vec![
        Predicate::Root("dog".into()),    // 0
        Predicate::Root("loves".into()),  // 1
        Predicate::Root("animal".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Every, 0)), // 0: ro lo gerku
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 1
        Argument::Marker(Marker::It),                  // 2: ke'a
        Argument::Name("alis".into()),                 // 3: alis
        Argument::Tagged((0, 2)),                      // 4: fa ke'a (x1, lover)
        Argument::Tagged((1, 3)),                      // 5: fe alis (x2, loved)
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 2, // danlu (main)
            terms: vec![1],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 1, // prami (body: head EMPTY, fa ke'a + fe alis)
            terms: vec![4, 5],
            x1_present: false,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];
    let (form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    assert!(
        compiler.errors.is_empty(),
        "fa-tagged ke'a must not collide with the implicit injection: {:?}",
        compiler.errors
    );
    let prami_x1 = get_pred_args(&form, "loves_x1", &compiler).expect("loves_x1 present");
    let prami_x2 = get_pred_args(&form, "loves_x2", &compiler).expect("loves_x2 present");
    let gerku_x1 = get_pred_args(&form, "dog_x1", &compiler).expect("dog_x1 present");
    assert_eq!(
        prami_x1[1], gerku_x1[1],
        "the fa-tagged ke'a must bind the described dog at x1 (the lover)"
    );
    assert_eq!(
        const_str(&compiler, &prami_x2[1]),
        "alis",
        "x2 must be the loved, alis"
    );
}

#[test]
fn test_x2_tagged_lone_it_leaves_x1_unspecified() {
    // `ro lo gerku poi prami fe ke'a cu danlu` —
    // `animal(every dog where loves(loved: it)).` (x1 omitted).
    // Regression for the SILENT variant: the injection used to pre-fill x1
    // with the clause var while the fe-tagged ke'a resolved to the SAME var
    // at x2 → prami(dog, dog) ("dog that loves itself"). x1 must stay
    // Unspecified → prami(zo'e, dog) ("dog that is loved").
    let predicates = vec![
        Predicate::Root("dog".into()),    // 0
        Predicate::Root("loves".into()),  // 1
        Predicate::Root("animal".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Every, 0)), // 0: ro lo gerku
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 1
        Argument::Marker(Marker::It),                  // 2: ke'a
        Argument::Tagged((1, 2)),                      // 3: fe ke'a (x2, loved)
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 2, // danlu (main)
            terms: vec![1],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 1, // prami (body: head EMPTY, only fe ke'a)
            terms: vec![3],
            x1_present: false,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];
    let (form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    let prami_x1 = get_pred_args(&form, "loves_x1", &compiler).expect("loves_x1 present");
    let prami_x2 = get_pred_args(&form, "loves_x2", &compiler).expect("loves_x2 present");
    let gerku_x1 = get_pred_args(&form, "dog_x1", &compiler).expect("dog_x1 present");
    assert!(
        matches!(prami_x1[1], IrTerm::Unspecified),
        "x1 must stay Unspecified (not double-filled with the clause var), got {:?}",
        prami_x1[1]
    );
    assert_eq!(
        prami_x2[1], gerku_x1[1],
        "the fe-tagged ke'a must bind the described dog at x2"
    );
}

#[test]
fn test_nested_description_two_place_rejected() {
    // lo gerku poi lo mlatu cu batci  (book Ch6 canonical reject case)
    // batci is 2-place (x1 bites x2); the cat fills batci_x1, so the dog's place
    // would be the non-subject batci_x2. Implicit ke'a cannot safely target a
    // non-subject slot -> reject and demand explicit ke'a.
    //
    // Buffer layout:
    //   predicates: [0: gerku, 1: mlatu, 2: batci]
    //   arguments:  [0: Description(Lo, 0), 1: Description(Lo, 1), 2: Restricted(0, poi body=1)]
    //   sentences: [0: Simple(batci, head=[2]), 1: Simple(batci, head=[1])]
    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("cat".into()),  // 1
        Predicate::Root("bite".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Indefinite, 0)), // 0: lo gerku
        Argument::Description((Determiner::Indefinite, 1)), // 1: lo mlatu
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 2: lo gerku poi lo mlatu cu batci
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 2,
            terms: vec![2],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 2,
            terms: vec![1], // lo mlatu fills batci_x1; batci_x2 is the dog's place
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];

    let (_form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    assert!(
        !compiler.errors.is_empty(),
        "Expected a ke'a error: the dog's batci_x2 place cannot be filled implicitly"
    );
}

#[test]
fn test_count_unspecified_predicates_single() {
    let mut compiler = SemanticCompiler::new();
    let rel = compiler.interner.get_or_intern("dog");
    let form = IrForm::Predicate {
        relation: rel,
        args: vec![IrTerm::Unspecified],
    };
    assert_eq!(
        SemanticCompiler::count_unspecified_predicates(&form, &compiler.interner),
        1
    );
}

#[test]
fn test_count_unspecified_predicates_none() {
    let mut compiler = SemanticCompiler::new();
    let rel = compiler.interner.get_or_intern("dog");
    let var = compiler.interner.get_or_intern("x");
    let form = IrForm::Predicate {
        relation: rel,
        args: vec![IrTerm::Variable(var)],
    };
    assert_eq!(
        SemanticCompiler::count_unspecified_predicates(&form, &compiler.interner),
        0
    );
}

#[test]
fn test_count_unspecified_predicates_conjunction() {
    let mut compiler = SemanticCompiler::new();
    let rel1 = compiler.interner.get_or_intern("dog");
    let rel2 = compiler.interner.get_or_intern("cat");
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
    assert_eq!(
        SemanticCompiler::count_unspecified_predicates(&form, &compiler.interner),
        2
    );
}

#[test]
fn test_inject_variable_fills_first_unspecified() {
    let mut compiler = SemanticCompiler::new();
    let rel = compiler.interner.get_or_intern("dog");
    let var = compiler.interner.get_or_intern("_v0");
    let form = IrForm::Predicate {
        relation: rel,
        args: vec![IrTerm::Unspecified, IrTerm::Unspecified],
    };
    let injected = SemanticCompiler::inject_variable(form, var, &compiler.interner);
    match injected {
        IrForm::Predicate { args, .. } => {
            assert!(matches!(args[0], IrTerm::Variable(_)));
            assert!(matches!(args[1], IrTerm::Unspecified));
        }
        other => panic!("expected Predicate, got {:?}", other),
    }
}
