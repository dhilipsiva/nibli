//! The identity flat-lowering and place-placement *shape* tests migrated to
//! `nibli-kr/src/shape_tests/lowering.rs`. What stays here are the two
//! defense-in-depth cases with no KR surface: n-ary identity (surface `=` is
//! strictly binary) and the CLL place-counter resume (positional-after-named
//! is parse-rejected, so an untagged term after a tagged one is a buffer shape
//! the emitter never produces).

use super::*;

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
