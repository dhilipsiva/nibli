use super::*;

// ─── Panel-finding regressions (2026-06-10): meaning loss ────

#[test]
fn test_place_tag_beyond_arity_errors() {
    // fu do gerku → `fu` targets x5 but gerku is 2-place: semantic error,
    // never a silent drop of `do`.
    let predicates = vec![Predicate::Root("dog".into())];
    let arguments = vec![
        Argument::Pronoun(Pronoun::You), // 0
        Argument::Tagged((4, 0)),        // 1: fu do
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![1],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (_form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(
        !compiler.errors.is_empty(),
        "over-arity FA tag must produce a semantic error"
    );
    assert!(
        compiler.errors.iter().any(|e| e.contains("x5")),
        "error should name the offending place, got: {:?}",
        compiler.errors
    );
}

#[test]
fn test_place_tag_within_arity_no_error() {
    // fe do gerku → `fe` targets x2; gerku is 2-place: fine.
    let predicates = vec![Predicate::Root("dog".into())];
    let arguments = vec![
        Argument::Pronoun(Pronoun::You), // 0
        Argument::Tagged((1, 0)),        // 1: fe do
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![1],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(
        compiler.errors.is_empty(),
        "in-range FA tag must not error, got: {:?}",
        compiler.errors
    );
    let x2 = get_pred_args(&form, "dog_x2", &compiler).unwrap();
    let do_term = IrTerm::Constant(compiler.interner.get("you").unwrap());
    assert_eq!(x2[1], do_term, "fe must place `do` into gerku_x2");
}

#[test]
fn test_untagged_overflow_known_arity_errors() {
    // `dog(me, you, this)` — dog is a KNOWN 2-place relation, so the 3rd
    // untagged argument overflows with no slot: fail closed instead of
    // silently dropping it.
    let predicates = vec![Predicate::Root("dog".into())];
    let arguments = vec![
        Argument::Pronoun(Pronoun::Me),   // 0
        Argument::Pronoun(Pronoun::You),  // 1
        Argument::Pronoun(Pronoun::This), // 2
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0, 1, 2],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (_form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(
        !compiler.errors.is_empty(),
        "untagged argument over a known arity must error"
    );
    assert!(
        compiler.errors.iter().any(|e| e.contains("overflow")),
        "error should mention the overflow, got: {:?}",
        compiler.errors
    );
}

#[test]
fn test_untagged_overflow_unknown_arity_no_error() {
    // An UNKNOWN predicate defaults to arity 2, but its real arity may be higher,
    // so an untagged overflow is NOT an error there (matches today's behavior —
    // the no-XML build defaults many proxy words to 2).
    let predicates = vec![Predicate::Root("zzzzz".into())];
    let arguments = vec![
        Argument::Pronoun(Pronoun::Me),   // 0
        Argument::Pronoun(Pronoun::You),  // 1
        Argument::Pronoun(Pronoun::This), // 2
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0, 1, 2],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (_form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(
        compiler.errors.is_empty(),
        "unknown-arity overflow must not error, got: {:?}",
        compiler.errors
    );
}

#[test]
fn test_tag_collision_errors() {
    // `fe do fe ti gerku` — both `fe` tags target x2: a place set twice must
    // error, not silently last-wins (dropping `do`).
    let predicates = vec![Predicate::Root("dog".into())];
    let arguments = vec![
        Argument::Pronoun(Pronoun::You),  // 0
        Argument::Pronoun(Pronoun::This), // 1
        Argument::Tagged((1, 0)),         // 2: fe do
        Argument::Tagged((1, 1)),         // 3: fe ti
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![2, 3],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (_form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(
        !compiler.errors.is_empty(),
        "a tag re-targeting a filled place must error"
    );
    assert!(
        compiler.errors.iter().any(|e| e.contains("already filled")),
        "error should mention the collision, got: {:?}",
        compiler.errors
    );
}

#[test]
fn test_compound_in_restrictive_not_falsely_rejected() {
    // lo gerku poi sutra bajra cu klama — the pair `sutra bajra` shares
    // ONE event, so its two unfilled x1 roles are one candidate subject
    // slot; the firewall must not reject, and injection must fill BOTH x1
    // roles with the dog's variable.
    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("fast".into()), // 1
        Predicate::Root("runs".into()), // 2
        Predicate::Pair((1, 2)),        // 3: sutra bajra
        Predicate::Root("goes".into()), // 4
    ];
    let arguments = vec![
        Argument::Description((Determiner::Indefinite, 0)), // 0: lo gerku
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 1: lo gerku poi sutra bajra
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 4,
            terms: vec![1],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 3,
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
        "valid pair-in-poi clause must not be rejected, got: {:?}",
        compiler.errors
    );
    let bajra_x1 = get_pred_args(&form, "runs_x1", &compiler).unwrap();
    let sutra_x1 = get_pred_args(&form, "fast_x1", &compiler).unwrap();
    let gerku_x1 = get_pred_args(&form, "dog_x1", &compiler).unwrap();
    assert_eq!(
        bajra_x1[1], gerku_x1[1],
        "pair head x1 must bind the dog variable"
    );
    assert_eq!(
        sutra_x1[1], gerku_x1[1],
        "pair modifier x1 must bind the dog variable"
    );
    assert_eq!(
        bajra_x1[0], sutra_x1[0],
        "pair must keep the shared event variable"
    );
}

#[test]
fn test_rel_clause_on_name_conjoined_not_dropped() {
    // la .adam. poi gerku cu klama → And(klama(adam...), gerku(adam...)):
    // the clause on a name (no quantifier) must be conjoined into the
    // matrix, not compiled-then-dropped. An assertion asserts both
    // conjuncts; a query requires both.
    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("goes".into()), // 1
    ];
    let arguments = vec![
        Argument::Name("adam".into()), // 0
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 1: la .adam. poi gerku
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 1,
            terms: vec![1],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 0,
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
        "single-subject-slot clause on a name must compile cleanly, got: {:?}",
        compiler.errors
    );
    let adam = IrTerm::Constant(compiler.interner.get("adam").unwrap());
    let klama_x1 =
        get_pred_args(&form, "goes_x1", &compiler).expect("matrix klama must be present");
    assert_eq!(klama_x1[1], adam);
    let gerku_x1 = get_pred_args(&form, "dog_x1", &compiler)
        .expect("the poi clause's gerku must be conjoined, not dropped");
    assert_eq!(
        gerku_x1[1], adam,
        "the name must be substituted into the clause's subject slot"
    );
}

#[test]
fn test_rel_clause_on_name_firewall_still_applies() {
    // la .adam. poi lo mlatu cu batci → the clause has NO unfilled subject
    // slot for Adam (the cat fills batci_x1): ambiguous implicit ke'a must
    // be rejected on names too, exactly like on lo descriptions.
    let predicates = vec![
        Predicate::Root("cat".into()),  // 0
        Predicate::Root("bite".into()), // 1
    ];
    let arguments = vec![
        Argument::Name("adam".into()),                      // 0
        Argument::Description((Determiner::Indefinite, 0)), // 1: lo mlatu
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 2: la .adam. poi lo mlatu cu batci
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 1,
            terms: vec![2],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 1,
            terms: vec![1], // lo mlatu fills batci_x1
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];
    let (_form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    assert!(
        !compiler.errors.is_empty(),
        "ambiguous implicit-ke'a clause on a name must be rejected"
    );
    assert!(
        compiler.errors.iter().any(|e| e.contains("explicit `it`")),
        "error should direct the user to an explicit `it`, got: {:?}",
        compiler.errors
    );
}

#[test]
fn test_da_after_universal_closes_inside_forall() {
    // ro lo gerku cu citka da → ∀x.(gerku(x) → ∃da. citka(x, da)):
    // left-to-right Lojban scope puts the bare-var existential INSIDE the
    // universal. The old Exists-over-ForAll root dead-ended nibli-reason's rule
    // dispatch and silently lost the whole assertion.
    fn exists_da_somewhere(f: &IrForm, c: &SemanticCompiler) -> bool {
        match f {
            IrForm::Exists(v, inner) => {
                c.interner.resolve(v) == "$da" || exists_da_somewhere(inner, c)
            }
            IrForm::And(l, r)
            | IrForm::Or(l, r)
            | IrForm::Biconditional(l, r)
            | IrForm::Xor(l, r) => exists_da_somewhere(l, c) || exists_da_somewhere(r, c),
            IrForm::Not(i)
            | IrForm::ForAll(_, i)
            | IrForm::Past(i)
            | IrForm::Present(i)
            | IrForm::Future(i)
            | IrForm::Obligatory(i)
            | IrForm::Permitted(i) => exists_da_somewhere(i, c),
            IrForm::Count { body, .. } => exists_da_somewhere(body, c),
            IrForm::Predicate { .. } => false,
        }
    }

    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("eats".into()), // 1
    ];
    let arguments = vec![
        Argument::Description((Determiner::Every, 0)), // 0: ro lo gerku
        Argument::Variable("$da".into()),              // 1: da
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
    match &form {
        IrForm::ForAll(_, body) => {
            assert!(
                exists_da_somewhere(body, &compiler),
                "∃da must be nested inside the ∀ body, got: {:?}",
                form
            );
        }
        other => panic!(
            "root must stay ForAll (nibli-reason rule shape), got {:?}",
            other
        ),
    }
}
