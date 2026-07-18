//! The term-form *shape* tests (names, numbers, quoted literals, descriptions,
//! opaque-vs-veridical restrictors, no-arg, `&`/`ge…gi`, known-arity) migrated
//! to `nibli-kr/src/shape_tests/terms.rs`. What stays here is the set with no
//! KR surface: the unknown-word arity default (unknown predicates don't
//! resolve through the emitter) and the two internal-static white-box units
//! (`fresh_var`, `inject_variable`).

use super::*;

#[test]
fn test_unknown_gismu_defaults_to_arity_2() {
    // An unrecognized word (only reachable programmatically — the KR emitter
    // rejects unknown predicates) defaults to arity 2 → 2 role predicates.
    let predicates = vec![Predicate::Root("xyzzy".into())];
    let arguments = vec![Argument::Pronoun(Pronoun::Me)];
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
        matches!(&form, IrForm::Exists(_, _)),
        "expected Exists, got {:?}",
        form
    );
    assert!(
        has_pred(&form, "xyzzy", &compiler),
        "expected xyzzy type predicate"
    );
    assert!(
        has_pred(&form, "xyzzy_x1", &compiler),
        "expected xyzzy_x1 role"
    );
    assert!(
        has_pred(&form, "xyzzy_x2", &compiler),
        "expected xyzzy_x2 role"
    );
    assert!(
        !has_pred(&form, "xyzzy_x3", &compiler),
        "unknown word should default to arity 2, but found xyzzy_x3"
    );
}

#[test]
fn test_fresh_vars_are_unique() {
    let mut compiler = SemanticCompiler::new();
    let v1 = compiler.fresh_var();
    let v2 = compiler.fresh_var();
    let v3 = compiler.fresh_var();
    assert_ne!(v1, v2);
    assert_ne!(v2, v3);
    assert_ne!(v1, v3);
    assert_eq!(compiler.interner.resolve(&v1), "_v0");
    assert_eq!(compiler.interner.resolve(&v2), "_v1");
    assert_eq!(compiler.interner.resolve(&v3), "_v2");
}

#[test]
fn test_inject_variable_into_and() {
    let mut compiler = SemanticCompiler::new();
    let rel1 = compiler.interner.get_or_intern("dog");
    let rel2 = compiler.interner.get_or_intern("big");
    let var = compiler.interner.get_or_intern("_v0");
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
    let injected = SemanticCompiler::inject_variable(form, var, &compiler.interner);
    match injected {
        IrForm::And(left, right) => {
            // inject_variable fills the FIRST unspecified in the first predicate found
            match left.as_ref() {
                IrForm::Predicate { args, .. } => {
                    assert!(matches!(args[0], IrTerm::Variable(_)));
                }
                other => panic!("expected Predicate, got {:?}", other),
            }
            match right.as_ref() {
                IrForm::Predicate { args, .. } => {
                    assert!(matches!(args[0], IrTerm::Variable(_)));
                }
                other => panic!("expected Predicate, got {:?}", other),
            }
        }
        other => panic!("expected And, got {:?}", other),
    }
}
