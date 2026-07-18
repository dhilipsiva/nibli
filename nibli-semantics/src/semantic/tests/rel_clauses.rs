//! The restrictive/incidental placement and abstraction-body-`da` *shape*
//! tests migrated to `nibli-kr/src/shape_tests/rel_clauses.rs`. What stays
//! here is the one case with no KR surface: a `da` inside a `WithArgs`
//! (be/linked-args) at proposition level — the emitter only produces
//! `WithArgs` inside restrictor descriptions, never as a bridi relation.

use super::*;

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
