use super::*;

// ─── Abstraction type tests ──────────────────────────────────

/// Helper: build a buffer with abstraction and compile.
fn compile_abstraction(
    kind: AbstractionKind,
    inner_predicate: &str,
    inner_arguments: Vec<Argument>,
) -> (IrForm, SemanticCompiler) {
    // Build: lo <kind> <inner_arguments> <inner_predicate> kei cu barda
    // Buffer layout:
    //   predicates: [0: inner_predicate, 1: Abstraction(kind, sentence_idx=1), 2: barda]
    //   arguments: [0..N: inner arguments, N: Description(Lo, 1)]
    //   sentences: [0: top-level proposition, 1: inner proposition]
    let inner_argument_ids: Vec<u32> = (0..inner_arguments.len() as u32).collect();
    let desc_argument_idx = inner_arguments.len() as u32;

    let mut all_arguments = inner_arguments;
    all_arguments.push(Argument::Description((Determiner::Indefinite, 1))); // desc_argument_idx

    let predicates = vec![
        Predicate::Root(inner_predicate.into()), // 0
        Predicate::Abstraction((kind, 1)),       // 1 → sentences[1]
        Predicate::Root("big".into()),           // 2
    ];

    let inner_x1_present = !inner_argument_ids.is_empty();
    let inner_proposition = Proposition {
        relation: 0,
        terms: inner_argument_ids,
        x1_present: inner_x1_present,
        negated: false,
        tense: None,
        deontic: None,
    };
    let outer_proposition = Proposition {
        relation: 2,
        terms: vec![desc_argument_idx],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };

    let sentences = vec![
        Sentence::Simple(outer_proposition),
        Sentence::Simple(inner_proposition),
    ];

    let mut compiler = SemanticCompiler::new();
    let form = compiler.compile_proposition(
        match &sentences[0] {
            Sentence::Simple(b) => b,
            _ => unreachable!(),
        },
        &predicates,
        &all_arguments,
        &sentences,
    );
    (form, compiler)
}

#[test]
fn test_fact_abstraction_produces_fact_predicate() {
    // lo du'u mi klama kei cu barda
    // → Exists(_v0, And(duhu(_v0), And(klama(mi, ...), barda(_v0, ...))))
    let (form, compiler) = compile_abstraction(
        AbstractionKind::Fact,
        "goes",
        vec![Argument::Atom("me".into())],
    );

    // Should be Exists(_v0, And(duhu(_v0), And(klama_event, barda_event)))
    // With event decomposition, klama and barda are wrapped in Exists
    match &form {
        IrForm::Exists(var, _body) => {
            assert!(resolve(&compiler, var).starts_with("_v"));
            // Use the recursive helpers that descend into Exists
            assert!(
                has_pred(&form, "fact", &compiler),
                "expected 'duhu' predicate"
            );
            assert!(
                has_pred(&form, "goes", &compiler),
                "expected 'klama' type predicate"
            );
        }
        other => panic!("expected Exists, got {:?}", other),
    }
}

#[test]
fn test_property_with_slot_binds_open_variable() {
    // lo ka ce'u melbi kei cu barda
    // ce'u should resolve to the same variable as the quantified entity
    let (form, compiler) = compile_abstraction(
        AbstractionKind::Property,
        "beautiful",
        vec![Argument::Atom("slot".into())],
    );

    // Should be Exists(_v0, And(ka(_v0), And(melbi_event, barda_event)))
    // The key: ce'u resolves to _v0, which is the same as the description variable
    // With events, melbi_x1 role pred has (ev, _v0) — the bound var
    match &form {
        IrForm::Exists(var, _body) => {
            let var_name = resolve(&compiler, var);
            // ka type pred should reference the description variable
            let ka_args = get_pred_args(&form, "property", &compiler).unwrap();
            let ka_arg0 = match &ka_args[0] {
                IrTerm::Variable(v) => resolve(&compiler, v),
                other => panic!("expected Variable for ka arg, got {:?}", other),
            };
            assert_eq!(
                ka_arg0, var_name,
                "ka predicate arg should be the quantified variable"
            );
            // melbi_x1 role pred should have the same variable as its entity arg
            let melbi_x1_args = get_pred_args(&form, "beautiful_x1", &compiler).unwrap();
            let melbi_entity = match &melbi_x1_args[1] {
                IrTerm::Variable(v) => resolve(&compiler, v),
                other => panic!("expected Variable for melbi_x1 entity, got {:?}", other),
            };
            assert_eq!(
                melbi_entity, var_name,
                "ce'u should resolve to the same variable as ka's entity"
            );
        }
        other => panic!("expected Exists, got {:?}", other),
    }
}

#[test]
fn test_amount_abstraction_produces_amount_predicate() {
    let (form, compiler) = compile_abstraction(
        AbstractionKind::Amount,
        "happy",
        vec![Argument::Atom("me".into())],
    );

    match &form {
        IrForm::Exists(_, _) => {
            // Use the recursive helpers that descend into Exists
            assert!(
                has_pred(&form, "amount", &compiler),
                "expected 'ni' predicate"
            );
            assert!(
                has_pred(&form, "happy", &compiler),
                "expected 'gleki' type predicate"
            );
        }
        other => panic!("expected Exists, got {:?}", other),
    }
}

#[test]
fn test_concept_abstraction_produces_concept_predicate() {
    let (form, compiler) = compile_abstraction(
        AbstractionKind::Concept,
        "goes",
        vec![Argument::Atom("me".into())],
    );

    match &form {
        IrForm::Exists(_, _) => {
            // Use the recursive helpers that descend into Exists
            assert!(
                has_pred(&form, "concept", &compiler),
                "expected 'siho' predicate"
            );
            assert!(
                has_pred(&form, "goes", &compiler),
                "expected 'klama' type predicate"
            );
        }
        other => panic!("expected Exists, got {:?}", other),
    }
}

#[test]
fn test_event_abstraction_still_works() {
    let (form, compiler) = compile_abstraction(
        AbstractionKind::Event,
        "goes",
        vec![Argument::Atom("me".into())],
    );

    match &form {
        IrForm::Exists(_, _) => {
            // Use the recursive helpers that descend into Exists
            assert!(
                has_pred(&form, "event", &compiler),
                "expected 'nu' predicate"
            );
            assert!(
                has_pred(&form, "goes", &compiler),
                "expected 'klama' type predicate"
            );
        }
        other => panic!("expected Exists, got {:?}", other),
    }
}

#[test]
fn test_slot_outside_property_is_rejected() {
    // `ce'u` outside a `ka` abstraction has no binder. The old behavior minted a
    // fresh variable that stayed FREE through compilation (the da/de/di safety net
    // does not close `_v` fresh vars) — a non-ground form leaking toward the store.
    // Fail closed: a semantic error is accumulated (NibliError::Semantic downstream),
    // and no free variable escapes.
    let predicates = vec![Predicate::Root("beautiful".into())];
    let arguments = vec![Argument::Atom("slot".into())];
    let proposition = Proposition {
        relation: 0,
        terms: vec![0],
        x1_present: true,
        negated: false,
        tense: None,
        deontic: None,
    };

    let (form, compiler) = compile_one(predicates, arguments, proposition);

    assert!(
        compiler
            .errors
            .iter()
            .any(|e| e.contains("`slot` outside a `property")),
        "bare slot must accumulate a semantic error, got: {:?}",
        compiler.errors
    );
    // The placeholder term is the rigid Unspecified, never a free variable.
    let x1_args =
        get_pred_args(&form, "beautiful_x1", &compiler).expect("expected melbi_x1 role predicate");
    assert!(
        matches!(&x1_args[1], IrTerm::Unspecified),
        "rejected ce'u compiles to Unspecified (no free variable), got {:?}",
        x1_args[1]
    );
}
