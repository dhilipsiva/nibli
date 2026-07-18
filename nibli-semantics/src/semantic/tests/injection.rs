//! The named-arg `it`-routing *shape* tests migrated to
//! `nibli-kr/src/shape_tests/injection.rs`. What stays here is the set with no
//! KR surface: the implicit-`it` firewall rejections (mandatory-`it` is
//! enforced at PARSE, so the ambiguous-nested-description forms are a
//! ParseError before nibli-semantics runs — only a hand-built buffer reaches
//! this guard), the inject-FILL positive path (via KR the bare-`where` sugar
//! emits an explicit `it` at x1, so only a hand-built empty head exercises the
//! injection machinery — the KR twin in shape_tests pins the observable), and
//! the internal-static white-box units (`count_unspecified_predicates`,
//! `inject_variable`).

use super::*;

#[test]
fn test_nested_description_implicit_kea_rejected() {
    // `some dog where big(some cat)` — the relative-clause body has NO unfilled
    // subject slot for the described dog (the cat fills big's x1), and `it` is
    // implicit. Per the firewall, the engine REJECTS and demands explicit `it`
    // rather than guessing. (Via KR the parser rejects mandatory-`it` first;
    // this pins the semantics-layer guard on the hand-built buffer.)
    let predicates = vec![
        Predicate::Root("dog".into()), // 0
        Predicate::Root("cat".into()), // 1
        Predicate::Root("big".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Indefinite, 0)), // 0: some dog
        Argument::Description((Determiner::Indefinite, 1)), // 1: some cat
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 2: some dog where ...
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 2,    // big (main sentence)
            terms: vec![2], // some dog where ...
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 2,    // big (rel clause body: some cat is big)
            terms: vec![1], // some cat
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];

    let (_form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    assert!(
        !compiler.errors.is_empty(),
        "Expected an ambiguity/it error for an implicit-it nested description"
    );
    assert!(
        compiler.errors.iter().any(|e| e.contains("explicit `it`")),
        "Error should direct the user to an explicit `it`, got: {:?}",
        compiler.errors
    );
}

#[test]
fn test_single_predicate_injects_head_into_subject() {
    // `some dog where big` — the relative-clause body `big` has exactly one
    // unfilled subject slot, so the described dog is injected there. The
    // described dog's variable must appear in big_x1 (the same variable bound
    // by the dog description). Stays hand-built: via KR the bare-`where` sugar
    // emits an explicit `it`, bypassing this implicit-injection FILL path (the
    // shape_tests KR twin pins the observable var-identity).
    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("big".into()),  // 1
        Predicate::Root("goes".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Indefinite, 0)), // 0: some dog
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 1: some dog where big
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
    let big_args =
        get_pred_args(&form, "big_x1", &compiler).expect("big_x1 role predicate should be present");
    let dog_args =
        get_pred_args(&form, "dog_x1", &compiler).expect("dog_x1 role predicate should be present");
    assert!(
        matches!(big_args[1], IrTerm::Variable(_)),
        "dog variable should be injected into big_x1, got {:?}",
        big_args[1]
    );
    assert_eq!(
        big_args[1], dog_args[1],
        "big_x1 must bind the same variable as dog_x1 (the described dog)"
    );
}

#[test]
fn test_nested_description_two_place_rejected() {
    // `some dog where bite(some cat)` — bite is 2-place (x1 bites x2); the cat
    // fills bite_x1, so the dog's place would be the non-subject bite_x2.
    // Implicit `it` cannot safely target a non-subject slot → reject and demand
    // explicit `it`.
    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("cat".into()),  // 1
        Predicate::Root("bite".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Indefinite, 0)), // 0: some dog
        Argument::Description((Determiner::Indefinite, 1)), // 1: some cat
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Restrictive,
                body_sentence: 1,
            },
        )), // 2: some dog where some cat bites
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
            terms: vec![1], // some cat fills bite_x1; bite_x2 is the dog's place
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];

    let (_form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    assert!(
        !compiler.errors.is_empty(),
        "Expected an `it` error: the dog's bite_x2 place cannot be filled implicitly"
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
