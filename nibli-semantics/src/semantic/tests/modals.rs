use super::*;

// ─── BAI modal tag tests ──────────────────────────────────────

#[test]
fn test_via_modal_produces_custom_modal() {
    // mi klama fi'o zbasu do → And(klama(mi,...), zbasu(do, mi,...))
    // Buffer:
    //   arguments: [0: mi, 1: do, 2: ModalTagged(Fio(1), 1)]
    //   predicates: [0: klama, 1: zbasu]
    let predicates = vec![
        Predicate::Root("goes".into()),  // 0
        Predicate::Root("makes".into()), // 1
    ];
    let arguments = vec![
        Argument::Pronoun(Pronoun::Me),          // 0
        Argument::Pronoun(Pronoun::You),         // 1
        Argument::ModalTagged((ModalTag(1), 1)), // 2
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

    // klama is event-decomposed, zbasu is a flat modal Predicate
    assert!(
        has_pred(&form, "goes", &compiler),
        "expected klama type predicate"
    );
    assert!(
        has_pred(&form, "makes", &compiler),
        "expected zbasu modal predicate"
    );
    // zbasu is flat: zbasu(do, mi, ...)
    let zbasu_args = get_pred_args(&form, "makes", &compiler).unwrap();
    assert_eq!(
        zbasu_args[0],
        IrTerm::Constant(compiler.interner.get("you").unwrap())
    );
    assert_eq!(
        zbasu_args[1],
        IrTerm::Constant(compiler.interner.get("me").unwrap())
    );
}

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
