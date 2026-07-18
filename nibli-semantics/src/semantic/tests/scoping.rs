//! The position-aware scope *shape* tests migrated to
//! `nibli-kr/src/shape_tests/scoping.rs`. What stays here is the one case with
//! no KR surface: a `da` in a `WithArgs` (be/linked-args) with a universal —
//! the be-arg has no proposition-level surface position, so it is closed
//! innermost, and `WithArgs` at bridi level is only hand-buildable.

use super::*;

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
