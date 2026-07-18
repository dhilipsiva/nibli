//! The flat `via`-modal *shape* test migrated to
//! `nibli-kr/src/shape_tests/lowering.rs`. What stays here is the
//! defense-in-depth guard the KR emitter rejects first: an arity-1 `via`
//! predicate (every curated `via` modal is arity >= 2, so the buffer with a
//! 1-place modal is only hand-buildable).

use super::*;

#[test]
fn test_via_modal_arity_one_predicate_errors() {
    // `big(me) via person(you)` — `person` is a 1-place predicate, so the
    // modal has no x2 slot to carry the main proposition's x1 (`me`). A
    // 1-place modal that silently drops that link loses meaning, so it
    // must fail closed (every curated `via` modal is arity >= 2).
    let predicates = vec![
        Predicate::Root("big".into()),    // 0
        Predicate::Root("person".into()), // 1 (arity 1)
    ];
    let arguments = vec![
        Argument::Pronoun(Pronoun::Me),          // 0
        Argument::Pronoun(Pronoun::You),         // 1
        Argument::ModalTagged((ModalTag(1), 1)), // 2: fi'o prenu, inner=do
    ];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0, 2],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };
    let (_form, compiler) = compile_one(predicates, arguments, proposition);
    assert!(
        !compiler.errors.is_empty(),
        "a 1-place fi'o modal must fail closed"
    );
    assert!(
        compiler.errors.iter().any(|e| e.contains("Modal tag")),
        "error should name the modal-arity limitation, got: {:?}",
        compiler.errors
    );
}
