//! The place-routing and rel-clause-on-name *shape* tests migrated to
//! `nibli-kr/src/shape_tests/regressions.rs`. What stays here is the set with
//! no KR surface: the place-tag/overflow/collision guards the emitter rejects
//! first, the unknown-word arity default, the ambiguous-`it` firewall on a
//! name, and the compound-in-restrictor case (a hand-built empty-head body;
//! the shape_tests KR twin pins the observable).

use super::*;

// ─── Panel-finding regressions: meaning loss (fail-closed guards) ────

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
