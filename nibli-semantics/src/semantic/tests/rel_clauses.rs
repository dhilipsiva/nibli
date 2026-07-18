use super::*;

// ─── noi (non-restrictive) vs poi (restrictive) relative clauses ────

/// Compile `ro lo gerku [kind] barda cu klama` (universal). The rel-clause
/// body (sentence 1) is `barda` with implicit ke'a filling its x1.
fn compile_ro_lo_gerku_rel_barda_klama(kind: RelClauseKind) -> (IrForm, SemanticCompiler) {
    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("big".into()),  // 1
        Predicate::Root("goes".into()), // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Every, 0)), // 0: ro lo gerku
        Argument::Restricted((
            0,
            RelClause {
                kind,
                body_sentence: 1,
            },
        )), // 1: ro lo gerku [kind] barda
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
            relation: 1, // barda (rel-clause body; implicit ke'a fills x1)
            terms: vec![],
            x1_present: false,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];
    compile_sentence_full(predicates, arguments, sentences)
}

/// Split a `ForAll(_, Or(antecedent, consequent))` into (antecedent, consequent).
fn forall_or_split(form: &IrForm) -> (&IrForm, &IrForm) {
    match form {
        IrForm::ForAll(_, body) => match body.as_ref() {
            IrForm::Or(l, r) => (l.as_ref(), r.as_ref()),
            other => panic!("expected Or under ForAll, got {:?}", other),
        },
        other => panic!("expected ForAll root, got {:?}", other),
    }
}

#[test]
fn incidental_restrictor_is_in_universal_consequent_not_antecedent() {
    // `ro lo gerku noi barda cu klama`: noi is NON-restrictive, so `barda`
    // must land in the rule's CONSEQUENT (matrix), not its antecedent
    // (domain guard). RED pre-fix (noi was folded into the antecedent).
    let (form, compiler) = compile_ro_lo_gerku_rel_barda_klama(RelClauseKind::Incidental);
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    let (ante, cons) = forall_or_split(&form);
    assert!(
        has_pred(cons, "big", &compiler),
        "noi: barda must be in the consequent (matrix)"
    );
    assert!(
        !has_pred(ante, "big", &compiler),
        "noi: barda must NOT be in the antecedent (domain restrictor)"
    );
}

#[test]
fn where_restrictor_stays_in_universal_antecedent() {
    // Guard: poi is RESTRICTIVE, so `barda` stays in the antecedent. Green
    // before AND after — pins that the noi fix does not leak into poi.
    let (form, compiler) = compile_ro_lo_gerku_rel_barda_klama(RelClauseKind::Restrictive);
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    let (ante, cons) = forall_or_split(&form);
    assert!(
        has_pred(ante, "big", &compiler),
        "poi: barda must be in the antecedent (domain restrictor)"
    );
    assert!(
        !has_pred(cons, "big", &compiler),
        "poi: barda must NOT be in the consequent"
    );
}

#[test]
fn incidental_under_exact_count_is_restrictive_documented_residual() {
    // DOCUMENTED RESIDUAL: under an exact-count quantifier, noi is folded into
    // the counted body (== restrictive), because the principled non-restrictive
    // form `Count(…) ∧ ∀x.(desc→noi)` would need close_quantifier to emit two
    // conjuncts. Pin the current behavior so the limitation stays discoverable.
    // `ci lo gerku noi barda cu klama` → Count{3, body} with barda IN the body.
    let predicates = vec![
        Predicate::Root("dog".into()),  // 0
        Predicate::Root("big".into()),  // 1
        Predicate::Root("goes".into()), // 2
    ];
    let arguments = vec![
        Argument::QuantifiedDescription((3, Determiner::Indefinite, 0)), // 0: ci lo gerku
        Argument::Restricted((
            0,
            RelClause {
                kind: RelClauseKind::Incidental,
                body_sentence: 1,
            },
        )), // 1: ci lo gerku noi barda
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
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    match &form {
        IrForm::Count { count, body, .. } => {
            assert_eq!(*count, 3);
            assert!(
                has_pred(body, "big", &compiler),
                "documented residual: noi under exact-count is folded into the counted body"
            );
        }
        other => panic!("expected Count root, got {:?}", other),
    }
}

#[test]
fn test_da_in_be_arg_closed() {
    // `mi klama be da` — the `da` in the be-arg must be existentially closed.
    let predicates = vec![
        Predicate::Root("goes".into()),    // 0
        Predicate::WithArgs((0, vec![1])), // 1: klama be da
    ];
    let arguments = vec![
        Argument::Pronoun(Pronoun::Me),   // 0
        Argument::Variable("$da".into()), // 1 (be-arg)
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
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    assert!(
        free_vars(&form, &compiler).is_empty(),
        "the be-arg `da` must be bound: free={:?}",
        free_vars(&form, &compiler)
    );
}

#[test]
fn test_abstraction_da_not_double_wrapped() {
    // `mi djuno lo nu da broda` — the abstraction body closes its own `da`;
    // the outer existential walk must NOT re-wrap it (binder tracking).
    let predicates = vec![
        Predicate::Root("knows".into()),                     // 0
        Predicate::Abstraction((AbstractionKind::Event, 1)), // 1 → sentences[1]
        Predicate::Root("broda".into()),                     // 2
    ];
    let arguments = vec![
        Argument::Pronoun(Pronoun::Me),                     // 0
        Argument::Description((Determiner::Indefinite, 1)), // 1: lo nu ...
        Argument::Variable("$da".into()),                   // 2 (broda body x1)
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 0,
            terms: vec![0, 1],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 2, // broda
            terms: vec![2],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
    ];
    let (form, compiler) = compile_sentence_full(predicates, arguments, sentences);
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    assert_eq!(
        count_exists_binding(&form, "$da", &compiler),
        1,
        "`da` must be wrapped exactly once (no double-wrap)"
    );
    assert!(
        free_vars(&form, &compiler).is_empty(),
        "free={:?}",
        free_vars(&form, &compiler)
    );
}
