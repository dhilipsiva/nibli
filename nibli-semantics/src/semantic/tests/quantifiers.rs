use super::*;

// ─── Numeric quantifier tests ──────────────────────────────────

#[test]
fn test_re_lo_produces_count_2() {
    // re lo gerku cu barda → Count(_v0, 2, And(gerku(_v0,...), barda(_v0,...)))
    // Buffer:
    //   arguments: [0: QuantifiedDescription(2, Lo, 0)]
    //   predicates: [0: gerku, 1: barda]
    //   proposition: { relation: 1, terms: [0], x1_present: true }
    let predicates = vec![
        Predicate::Root("dog".into()), // 0
        Predicate::Root("big".into()), // 1
    ];
    let arguments = vec![
        Argument::QuantifiedDescription((2, Determiner::Indefinite, 0)), // 0
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

    // Should be Count { var: _v0, count: 2, body: And(gerku_event, barda_event) }
    // With event decomposition, restrictor and predicate are event-wrapped
    match &form {
        IrForm::Count { var, count, body } => {
            assert_eq!(*count, 2);
            assert!(resolve(&compiler, var).starts_with("_v"));
            // The body should contain both gerku and barda type predicates
            assert!(
                has_pred(body, "dog", &compiler),
                "expected gerku restrictor type pred"
            );
            assert!(has_pred(body, "big", &compiler), "expected barda type pred");
        }
        other => panic!("expected Count, got {:?}", other),
    }
}

#[test]
fn test_no_lo_produces_count_0() {
    // no lo gerku cu barda → Count(_v0, 0, And(gerku(_v0,...), barda(_v0,...)))
    let predicates = vec![
        Predicate::Root("dog".into()), // 0
        Predicate::Root("big".into()), // 1
    ];
    let arguments = vec![
        Argument::QuantifiedDescription((0, Determiner::Indefinite, 0)), // 0
    ];
    let proposition = Proposition {
        relation: 1,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };

    let (form, _) = compile_one(predicates, arguments, proposition);

    match &form {
        IrForm::Count { count, .. } => assert_eq!(*count, 0),
        other => panic!("expected Count with count=0, got {:?}", other),
    }
}

#[test]
fn test_pa_lo_produces_count_1() {
    // pa lo gerku cu barda → Count(_v0, 1, ...)
    let predicates = vec![Predicate::Root("dog".into()), Predicate::Root("big".into())];
    let arguments = vec![Argument::QuantifiedDescription((
        1,
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

    let (form, _) = compile_one(predicates, arguments, proposition);

    match &form {
        IrForm::Count { count, .. } => assert_eq!(*count, 1),
        other => panic!("expected Count with count=1, got {:?}", other),
    }
}

#[test]
fn test_lo_still_produces_exists() {
    // Regression: lo gerku cu barda → Exists (not Count)
    let predicates = vec![Predicate::Root("dog".into()), Predicate::Root("big".into())];
    let arguments = vec![Argument::Description((Determiner::Indefinite, 0))];
    let proposition = Proposition {
        relation: 1,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };

    let (form, _) = compile_one(predicates, arguments, proposition);

    assert!(
        matches!(&form, IrForm::Exists(_, _)),
        "expected Exists, got {:?}",
        form
    );
}

// ─── Afterthought sentence connective tests ───────────────────

/// Helper: compile a connected sentence from two simple proposition.
fn compile_connected(
    conn: SentenceConnective,
    left_predicate: &str,
    left_argument: &str,
    right_predicate: &str,
    right_argument: &str,
) -> (IrForm, SemanticCompiler) {
    let predicates = vec![
        Predicate::Root(left_predicate.into()),
        Predicate::Root(right_predicate.into()),
    ];
    let arguments = vec![
        Argument::Atom(left_argument.into()),
        Argument::Atom(right_argument.into()),
    ];
    let left_proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let right_proposition = Proposition {
        relation: 1,
        terms: vec![1],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let sentences = vec![
        Sentence::Simple(left_proposition),
        Sentence::Simple(right_proposition),
        Sentence::Connected((conn, 0, 1)),
    ];
    let mut compiler = SemanticCompiler::new();
    let form = compiler.compile_sentence(2, &predicates, &arguments, &sentences);
    (form, compiler)
}

#[test]
fn test_afterthought_je_compiles_to_and() {
    let conn = SentenceConnective::Afterthought(Connective::And);
    let (form, _) = compile_connected(conn, "goes", "me", "loves", "you");
    assert!(
        matches!(&form, IrForm::And(_, _)),
        "expected And, got {:?}",
        form
    );
}

#[test]
fn test_afterthought_ja_compiles_to_or() {
    let conn = SentenceConnective::Afterthought(Connective::Or);
    let (form, _) = compile_connected(conn, "goes", "me", "loves", "you");
    assert!(
        matches!(&form, IrForm::Or(_, _)),
        "expected Or, got {:?}",
        form
    );
}

// ─── da/de/di quantifier closure tests ──────────────────────

#[test]
fn test_da_produces_exists() {
    // da prami mi → ∃da. event_decomposed_prami(da, mi, ...)
    let predicates = vec![Predicate::Root("loves".into())];
    let arguments = vec![
        Argument::Atom("$da".into()), // 0
        Argument::Atom("me".into()),  // 1
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0, 1],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };

    let (form, compiler) = compile_one(predicates, arguments, proposition);

    // Outermost should be Exists(da, ...) wrapping the event form
    match &form {
        IrForm::Exists(var, _body) => {
            assert_eq!(resolve(&compiler, var), "$da");
            // Inside should have prami type pred and role preds
            assert!(
                has_pred(&form, "loves", &compiler),
                "expected prami type predicate"
            );
            // prami_x1 should have Variable(da)
            let x1_args = get_pred_args(&form, "loves_x1", &compiler).unwrap();
            match &x1_args[1] {
                IrTerm::Variable(v) => assert_eq!(resolve(&compiler, v), "$da"),
                other => panic!("expected Variable(da) in prami_x1, got {:?}", other),
            }
            // prami_x2 should have Constant(mi)
            let x2_args = get_pred_args(&form, "loves_x2", &compiler).unwrap();
            match &x2_args[1] {
                IrTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "me"),
                other => panic!("expected Constant(mi) in prami_x2, got {:?}", other),
            }
        }
        other => panic!("expected Exists, got {:?}", other),
    }
}

#[test]
fn test_da_de_both_produce_nested_exists() {
    // da prami de → ∃da. ∃de. event_decomposed_prami(da, de, ...)
    let predicates = vec![Predicate::Root("loves".into())];
    let arguments = vec![
        Argument::Atom("$da".into()), // 0
        Argument::Atom("$de".into()), // 1
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0, 1],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };

    let (form, compiler) = compile_one(predicates, arguments, proposition);

    // Should be Exists(da/de, Exists(da/de, Exists(ev, ...)))
    match &form {
        IrForm::Exists(v1, inner) => {
            let name1 = resolve(&compiler, v1);
            match inner.as_ref() {
                IrForm::Exists(v2, _body) => {
                    let name2 = resolve(&compiler, v2);
                    // Both da and de should appear (order may vary)
                    let mut names = vec![name1, name2];
                    names.sort();
                    assert_eq!(names, vec!["$da", "$de"]);
                    // The body is now an event-decomposed form (Exists wrapping event)
                    assert!(
                        has_pred(&form, "loves", &compiler),
                        "expected prami type predicate"
                    );
                }
                other => panic!("expected nested Exists, got {:?}", other),
            }
        }
        other => panic!("expected Exists, got {:?}", other),
    }
}

#[test]
fn test_da_repeated_wraps_once() {
    // da prami da → ∃da. event_decomposed_prami(da, da, ...) (only one entity Exists)
    let predicates = vec![Predicate::Root("loves".into())];
    let arguments = vec![
        Argument::Atom("$da".into()), // 0
        Argument::Atom("$da".into()), // 1 (same variable)
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0, 1],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };

    let (form, compiler) = compile_one(predicates, arguments, proposition);

    // Should be Exists(da, Exists(ev, ...)) — NOT Exists(da, Exists(da, ...))
    match &form {
        IrForm::Exists(var, body) => {
            assert_eq!(resolve(&compiler, var), "$da");
            // The body should be the event Exists, not another da Exists
            match body.as_ref() {
                IrForm::Exists(ev_var, _) => {
                    // The inner Exists should be for an event variable, not da again
                    assert!(
                        resolve(&compiler, ev_var).starts_with("_ev"),
                        "expected event variable inside, got: {}",
                        resolve(&compiler, ev_var)
                    );
                }
                other => panic!(
                    "expected Exists(ev, ...) inside Exists(da, ...), got {:?}",
                    other
                ),
            }
        }
        other => panic!("expected Exists, got {:?}", other),
    }
}

#[test]
fn test_di_produces_exists() {
    // di barda → ∃di. barda(di, ...)
    let predicates = vec![Predicate::Root("big".into())];
    let arguments = vec![Argument::Atom("$di".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };

    let (form, compiler) = compile_one(predicates, arguments, proposition);

    match &form {
        IrForm::Exists(var, _) => {
            assert_eq!(resolve(&compiler, var), "$di");
        }
        other => panic!("expected Exists for di, got {:?}", other),
    }
}

#[test]
fn test_da_with_negation() {
    // da na prami mi → ¬(∃da. prami(da, mi, ...))
    // negation wraps OUTSIDE the existential
    let predicates = vec![Predicate::Root("loves".into())];
    let arguments = vec![Argument::Atom("$da".into()), Argument::Atom("me".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0, 1],
        x1_present: true,
        negated: true,
        tense: None,
        deontic: None,
    };

    let (form, _) = compile_one(predicates, arguments, proposition);

    // Should be Not(Exists(da, Predicate))
    match &form {
        IrForm::Not(inner) => {
            assert!(
                matches!(inner.as_ref(), IrForm::Exists(_, _)),
                "expected Exists inside Not, got {:?}",
                inner
            );
        }
        other => panic!("expected Not(Exists(...)), got {:?}", other),
    }
}

#[test]
fn test_afterthought_jo_compiles_to_biconditional() {
    // .i jo → Biconditional IR node (expanded at flattening)
    let conn = SentenceConnective::Afterthought(Connective::Iff);
    let (form, _) = compile_connected(conn, "goes", "me", "loves", "you");
    assert!(
        matches!(&form, IrForm::Biconditional(_, _)),
        "expected Biconditional, got {:?}",
        form
    );
}

// ─── ma question pro-argument tests ─────────────────────────────

#[test]
fn test_ma_produces_exists() {
    // ma klama → ∃_v0. event_decomposed_klama(_v0, ...)
    // Each `ma` gets a fresh variable (independent query unknowns).
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![
        Argument::Atom("?".into()), // 0
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };

    let (form, compiler) = compile_one(predicates, arguments, proposition);

    // Outermost should be Exists wrapping the event form
    match &form {
        IrForm::Exists(var, _body) => {
            // ma now generates a fresh variable (_v0), not "?"
            assert!(resolve(&compiler, var).starts_with("_v"));
            // klama type pred should exist inside
            assert!(
                has_pred(&form, "goes", &compiler),
                "expected klama type predicate"
            );
            // klama_x1 should reference the ma variable
            let x1_args = get_pred_args(&form, "goes_x1", &compiler).unwrap();
            match &x1_args[1] {
                IrTerm::Variable(v) => assert_eq!(v, var),
                other => panic!("expected Variable in klama_x1, got {:?}", other),
            }
        }
        other => panic!("expected Exists, got {:?}", other),
    }
}

#[test]
fn test_two_ma_produce_independent_exists() {
    // ma nelci ma → ∃_v1. ∃_v0. event_decomposed_nelci(_v0, _v1, ...)
    // Two `ma` tokens must produce two *different* variables,
    // each wrapped in its own ∃.
    let predicates = vec![Predicate::Root("likes".into())];
    let arguments = vec![
        Argument::Atom("?".into()), // 0
        Argument::Atom("?".into()), // 1
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0, 1],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };

    let (form, compiler) = compile_one(predicates, arguments, proposition);

    // Should be ∃v1.(∃v0.(Exists(ev, nelci_event(v0, v1, ...))))
    match &form {
        IrForm::Exists(var1, inner) => {
            assert!(resolve(&compiler, var1).starts_with("_v"));
            match inner.as_ref() {
                IrForm::Exists(var0, _body) => {
                    assert!(resolve(&compiler, var0).starts_with("_v"));
                    // The two variables must be different
                    assert_ne!(var0, var1, "two ma should produce different variables");
                    // Check that nelci_x1 and nelci_x2 reference different variables
                    let x1_args = get_pred_args(&form, "likes_x1", &compiler).unwrap();
                    let x2_args = get_pred_args(&form, "likes_x2", &compiler).unwrap();
                    match (&x1_args[1], &x2_args[1]) {
                        (IrTerm::Variable(a), IrTerm::Variable(b)) => {
                            assert_ne!(a, b, "args should reference different vars");
                        }
                        other => {
                            panic!("expected two Variables in role preds, got {:?}", other)
                        }
                    }
                }
                other => panic!("expected inner Exists, got {:?}", other),
            }
        }
        other => panic!("expected outer Exists, got {:?}", other),
    }
}

// ─── Quantifier-closure scoping: question_vars frame isolation + da/de/di in
//     BAI modals / be-bei args get existential closure ───────────────

#[test]
fn test_ma_in_rel_clause_not_stolen() {
    // `ma prami lo gerku poi ke'a barda` — the outer `ma` (prami x1) must be
    // existentially closed at the OUTER matrix, not stolen by the nested
    // rel-clause compile_proposition's drain. Pre-fix the nested drain emptied the
    // shared `question_vars`, leaving the outer ma var FREE.
    let predicates = vec![
        Predicate::Root("loves".into()), // 0
        Predicate::Root("dog".into()),   // 1
        Predicate::Root("big".into()),   // 2
    ];
    let arguments = vec![
        Argument::Atom("?".into()),                         // 0: ma
        Argument::Description((Determiner::Indefinite, 1)), // 1: lo gerku
        Argument::Restricted((
            1,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 2: lo gerku poi ke'a barda
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 0,
            terms: vec![0, 2],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 2, // barda (rel-clause body; implicit ke'a fills x1)
            terms: vec![],
            x1_present: false,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];
    let (form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    assert!(
        free_vars(&form, &compiler).is_empty(),
        "the outer `ma` must be bound (not stolen by the rel clause): free={:?}",
        free_vars(&form, &compiler)
    );
}
