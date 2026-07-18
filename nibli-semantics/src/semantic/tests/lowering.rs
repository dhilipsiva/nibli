use super::*;

// ─── du (identity) predicate lowering ───────────────────────────

#[test]
fn test_equals_lowers_flat_not_event_decomposed() {
    // `la .X. cu du la .Y.` (Root("equals") + 2 argument) must lower to a FLAT
    // 2-arg du(X,Y) predicate — NOT the Neo-Davidsonian event form
    // (∃e. du(e) ∧ du_x1(e,X) ∧ du_x2(e,Y)) — so nibli-reason's union-find
    // ingestion (which matches relation=="equals" && args.len()==2) fires.
    let predicates = vec![Predicate::Root("equals".into())];
    let arguments = vec![
        Argument::Pronoun(Pronoun::Me),  // 0
        Argument::Pronoun(Pronoun::You), // 1
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
    let args =
        get_pred_args(&form, "equals", &compiler).expect("flat du predicate must be present");
    assert_eq!(args.len(), 2, "du must be a flat 2-arg predicate");
    assert!(
        !has_pred(&form, "du_x1", &compiler),
        "du must NOT be event-decomposed (no role predicates)"
    );
}

#[test]
fn test_equals_with_more_than_two_arguments_is_rejected() {
    // Fail-closed: n-ary du is unsupported (nibli-reason handles only binary
    // identity). A 3-argument du must push a semantic error rather than
    // silently dropping the third argument.
    let predicates = vec![Predicate::Root("equals".into())];
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
        ">2-place du must be rejected fail-closed"
    );
}

// ─── Argument connective expansion tests ────────────────────────

// ─── Connected argument under place tags / BAI modals + CLL place counter ───
// Soundness fix: a connected argument nested under a place tag or BAI modal
// (`fa mi .e do`, `ri'a do .e ti`) previously dropped the right operand;
// only the FIRST connected argument in a proposition was split; and untagged argument
// after a tag filled the first free slot instead of the CLL place counter.

#[test]
fn test_cll_place_counter_resumes_after_fi() {
    // `klama fi le zarci do` — CLL: `fi` sets the place counter to x3, so
    // `le zarci` is x3 and the following UNTAGGED `do` resumes at x4
    // (NOT x1, which is the pre-fix "first free slot" bug).
    let predicates = vec![
        Predicate::Root("goes".into()),   // 0
        Predicate::Root("market".into()), // 1
    ];
    let arguments = vec![
        Argument::Description((Determiner::Definite, 1)), // 0: le zarci
        Argument::Tagged((2, 0)),                         // 1: fi le zarci
        Argument::Pronoun(Pronoun::You),                  // 2: do (untagged)
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![1, 2],
        x1_present: false,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    let x4 = get_pred_args(&form, "goes_x4", &compiler).expect("goes_x4 present");
    assert_eq!(
        const_str(&compiler, &x4[1]),
        "you",
        "untagged `do` must fill x4 after fi"
    );
    let x1 = get_pred_args(&form, "goes_x1", &compiler).expect("goes_x1 present");
    assert!(
        !matches!(&x1[1], IrTerm::Constant(c) if resolve(&compiler, c) == "you"),
        "do must NOT land in x1 (pre-fix bug), got {:?}",
        x1[1]
    );
    let x3 = get_pred_args(&form, "goes_x3", &compiler).expect("goes_x3 present");
    assert!(
        matches!(&x3[1], IrTerm::Description(_)),
        "fi `le zarci` must fill x3, got {:?}",
        x3[1]
    );
}

#[test]
fn test_untagged_before_tag_still_fills_x1() {
    // Regression: `mi klama fe do` — untagged `mi` fills x1, `fe do` fills x2.
    let predicates = vec![Predicate::Root("goes".into())];
    let arguments = vec![
        Argument::Pronoun(Pronoun::Me),  // 0
        Argument::Pronoun(Pronoun::You), // 1
        Argument::Tagged((1, 1)),        // 2: fe do
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0, 2],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
    let x1 = get_pred_args(&form, "goes_x1", &compiler).expect("goes_x1");
    let x2 = get_pred_args(&form, "goes_x2", &compiler).expect("goes_x2");
    assert_eq!(const_str(&compiler, &x1[1]), "me");
    assert_eq!(const_str(&compiler, &x2[1]), "you");
}
