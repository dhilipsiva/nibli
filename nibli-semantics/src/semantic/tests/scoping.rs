use super::*;

// ─── position-aware da/de/di quantifier scope ────────────────

#[test]
fn test_da_before_universal_outscopes_it() {
    // `da citka ro lo gerku` ("something eats every dog") — the leading bare
    // var is textually BEFORE the universal, so it OUTSCOPES it: ∃da.∀x.
    // RED before the fix (da was forced inside the universal → ∀x.∃da).
    let predicates = vec![
        Predicate::Root("eats".into()), // 0
        Predicate::Root("dog".into()),  // 1
    ];
    let arguments = vec![
        Argument::Variable("$da".into()),              // 0: da (x1)
        Argument::Description((Determiner::Every, 1)), // 1: ro lo gerku (x2)
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
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    assert_eq!(
        binder_spine(&form, &compiler),
        vec![Binder::Exists("$da".into()), Binder::ForAll],
        "leading `da` must outscope the universal (∃da.∀x): got {:?}",
        binder_spine(&form, &compiler)
    );
    assert!(
        exists_outscopes_forall(&form, "$da", &compiler),
        "`da` existential must dominate the universal"
    );
    assert!(free_vars(&form, &compiler).is_empty());
}

#[test]
fn test_da_after_universal_is_inside_it() {
    // `ro lo gerku cu citka da` ("every dog eats something") — the bare var is
    // textually AFTER the universal, so it stays INSIDE: ∀x.∃da. Contrasts
    // with the before-case; the pair proves surface order now matters (the two
    // were identical before the fix).
    let predicates = vec![
        Predicate::Root("eats".into()), // 0
        Predicate::Root("dog".into()),  // 1
    ];
    let arguments = vec![
        Argument::Description((Determiner::Every, 1)), // 0: ro lo gerku (x1)
        Argument::Variable("$da".into()),              // 1: da (x2)
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
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    assert_eq!(
        binder_spine(&form, &compiler).first(),
        Some(&Binder::ForAll),
        "trailing `da` must stay under the universal (∀x.∃da)"
    );
    assert!(
        !exists_outscopes_forall(&form, "$da", &compiler),
        "`da` must NOT outscope the universal in the after-case"
    );
    assert!(count_exists_binding(&form, "$da", &compiler) >= 1);
    assert!(free_vars(&form, &compiler).is_empty());
}

#[test]
fn test_da_interleaved_between_count_and_universal() {
    // `re lo gerku cu klama da ro lo mlatu` — a bare var between an
    // exact-count description (x1) and a universal (x3). The uniform fold
    // nests them Count > ∃da > ∀ by surface order.
    let predicates = vec![
        Predicate::Root("goes".into()), // 0
        Predicate::Root("dog".into()),  // 1
        Predicate::Root("cat".into()),  // 2
    ];
    let arguments = vec![
        Argument::QuantifiedDescription((2, Determiner::Indefinite, 1)), // 0: re lo gerku (x1)
        Argument::Variable("$da".into()),                                // 1: da (x2)
        Argument::Description((Determiner::Every, 2)),                   // 2: ro lo mlatu (x3)
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0, 1, 2],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    assert_eq!(
        binder_spine(&form, &compiler).first(),
        Some(&Binder::Count(2)),
        "root must be the exact-count quantifier: got {:?}",
        binder_spine(&form, &compiler)
    );
    assert!(
        exists_outscopes_forall(&form, "$da", &compiler),
        "`da` (x2) must outscope the universal (x3) it precedes"
    );
    assert_eq!(count_exists_binding(&form, "$da", &compiler), 1);
    assert!(free_vars(&form, &compiler).is_empty());
}

#[test]
fn test_be_arg_da_with_universal_stays_innermost() {
    // `ro lo gerku cu klama be da` — the be-arg `da` has no surface position
    // (merged inside apply_predicate), so the safety net closes it INNERMOST,
    // under the universal. The deferred-position default: bound, not free,
    // not double-wrapped.
    let predicates = vec![
        Predicate::Root("goes".into()),    // 0
        Predicate::WithArgs((0, vec![1])), // 1: klama be da
        Predicate::Root("dog".into()),     // 2
    ];
    let arguments = vec![
        Argument::Description((Determiner::Every, 2)), // 0: ro lo gerku (x1)
        Argument::Variable("$da".into()),              // 1: da (be-arg)
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
    assert_eq!(
        binder_spine(&form, &compiler).first(),
        Some(&Binder::ForAll),
        "root must stay ForAll (nibli-reason rule shape)"
    );
    assert!(
        !exists_outscopes_forall(&form, "$da", &compiler),
        "a be-arg `da` is closed innermost, under the universal"
    );
    assert_eq!(count_exists_binding(&form, "$da", &compiler), 1);
    assert!(free_vars(&form, &compiler).is_empty());
}

#[test]
fn test_restrictor_internal_da_closed_innermost() {
    // `ro lo gerku poi prami fe da cu klama` ("every dog that loves something
    // goes") — the `da` inside the poi-restrictor (x2, via `fe`, leaving x1 for
    // the implicit ke'a) has no proposition-level surface index, so it is bound
    // INSIDE the restrictor's own frame. A DELIBERATE sound default: surface
    // order cannot change a restrictor that defines the quantifier's domain.
    // Characterization lock — `da` is bound (never free) and the root stays a
    // universal.
    let predicates = vec![
        Predicate::Root("dog".into()),   // 0
        Predicate::Root("loves".into()), // 1
        Predicate::Root("goes".into()),  // 2
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
        Argument::Variable("$da".into()),              // 2: da
        Argument::Tagged((1, 2)),                      // 3: fe da (x2 of the poi body)
    ];
    let sentences = vec![
        Sentence::Simple(Proposition {
            relation: 2, // klama
            terms: vec![1],
            x1_present: true,
            negated: false,
            tense: None,
            deontic: None,
        }),
        Sentence::Simple(Proposition {
            relation: 1, // prami (rel-clause body: `prami fe da`; ke'a fills x1)
            terms: vec![3],
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
        "the restrictor-internal `da` must be bound: free={:?}",
        free_vars(&form, &compiler)
    );
    assert_eq!(
        binder_spine(&form, &compiler).first(),
        Some(&Binder::ForAll),
        "root must stay ForAll (the `da` is closed inside the restrictor)"
    );
    assert_eq!(count_exists_binding(&form, "$da", &compiler), 1);
}

#[test]
fn test_prenex_da_top_level_not_reclosed() {
    // `ro da zo'u da citka lo gerku` — `da` is universally bound by the
    // prenex; the new surface-marker hook must respect `prenex_vars` and NOT
    // record a Bare marker for the top-level `da` arg (no existential re-wrap).
    let predicates = vec![
        Predicate::Root("eats".into()), // 0
        Predicate::Root("dog".into()),  // 1
    ];
    let arguments = vec![
        Argument::Variable("$da".into()),                   // 0: da (x1)
        Argument::Description((Determiner::Indefinite, 1)), // 1: lo gerku (x2)
    ];
    let sentences = vec![
        Sentence::Prenex((vec!["$da".into()], 1)),
        Sentence::Simple(Proposition {
            relation: 0,
            terms: vec![0, 1],
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
        0,
        "prenex `da` must NOT be existentially re-closed"
    );
    assert_eq!(
        binder_spine(&form, &compiler).first(),
        Some(&Binder::ForAll),
        "prenex `da` is the outermost ∀"
    );
    assert!(free_vars(&form, &compiler).is_empty());
}

#[test]
fn test_da_repeated_dedups_to_one_exists() {
    // `da citka da` — the same bare var in two places co-refers and is
    // wrapped by exactly one Exists (the surface hook's `introduced` dedup +
    // the safety-net subtraction).
    let predicates = vec![Predicate::Root("eats".into())];
    let arguments = vec![
        Argument::Variable("$da".into()), // 0: da (x1)
        Argument::Variable("$da".into()), // 1: da (x2)
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
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    assert_eq!(
        count_exists_binding(&form, "$da", &compiler),
        1,
        "co-referring `da` must wrap exactly once"
    );
    assert!(free_vars(&form, &compiler).is_empty());
}

#[test]
fn test_equals_with_existential_closed() {
    // `da du mi` — flat du(da, mi); the `da` must be existentially closed
    // (the flat-du shape must not hide the logic var from the walk).
    let predicates = vec![Predicate::Root("equals".into())];
    let arguments = vec![
        Argument::Variable("$da".into()), // 0
        Argument::Pronoun(Pronoun::Me),   // 1
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
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    assert!(
        free_vars(&form, &compiler).is_empty(),
        "the du `da` must be bound: free={:?}",
        free_vars(&form, &compiler)
    );
    assert_eq!(count_exists_binding(&form, "$da", &compiler), 1, "da once");
}
