//! Count / Exists / connective / binder-nesting shapes.

use super::*;

#[test]
fn exactly_n_produces_count() {
    // `exactly N dog` → a CountNode with the literal N; the body carries both
    // the restrictor (`dog`) and the matrix (`big`).
    let b = lb("big(exactly 2 dog).");
    let (count, body) = match root(&b) {
        LogicNode::CountNode((_, n, body)) => (*n, *body),
        other => panic!("root not Count: {other:?}"),
    };
    assert_eq!(count, 2);
    assert!(has_pred_from(&b, body, "dog"));
    assert!(has_pred_from(&b, body, "big"));
}

#[test]
fn no_determiner_is_count_zero() {
    // `no dog` is exactly `exactly 0 dog` — a CountNode with count 0.
    let b = lb("big(no dog).");
    assert!(matches!(root(&b), LogicNode::CountNode((_, 0, _))));
}

#[test]
fn exactly_one_is_count_one() {
    let b = lb("big(exactly 1 dog).");
    assert!(matches!(root(&b), LogicNode::CountNode((_, 1, _))));
}

#[test]
fn some_still_produces_exists_not_count() {
    // Regression: `some dog` stays an existential, never degrades to a Count.
    let b = lb("big(some dog).");
    assert!(matches!(root(&b), LogicNode::ExistsNode(_)));
}

#[test]
fn afterthought_and_root() {
    // `&` (and the folded ge…gi form) roots an AndNode.
    let b = lb("goes(me) & loves(you).");
    assert!(matches!(root(&b), LogicNode::AndNode(_)));
}

#[test]
fn afterthought_or_root() {
    let b = lb("goes(me) | loves(you).");
    assert!(matches!(root(&b), LogicNode::OrNode(_)));
}

#[test]
fn biconditional_expands_to_and_of_ors() {
    // `<->` has no LogicNode variant — the flattener expands it to
    // (¬a ∨ b) ∧ (¬b ∨ a): root And, both children Or, each Or's first arm a
    // Not.
    let b = lb("goes(me) <-> loves(you).");
    let (l, r) = match root(&b) {
        LogicNode::AndNode((l, r)) => (*l, *r),
        other => panic!("root not And: {other:?}"),
    };
    for side in [l, r] {
        let arm = match node(&b, side) {
            LogicNode::OrNode((a, _)) => *a,
            other => panic!("And child not Or: {other:?}"),
        };
        assert!(
            matches!(node(&b, arm), LogicNode::NotNode(_)),
            "Or arm not Not"
        );
    }
}

#[test]
fn free_var_closes_existentially() {
    // `loves($da, me).` — a free `$da` auto-closes under an outermost
    // existential binding the SIGILED name; x1 is the variable, x2 the const.
    let b = lb("loves($da, me).");
    assert!(matches!(root(&b), LogicNode::ExistsNode((v, _)) if v == "$da"));
    assert!(matches!(role_filler(&b, "loves_x1"), Some(LogicalTerm::Variable(v)) if v == "$da"));
    assert!(role_is_const(&b, "loves_x2", "me"));
    assert!(free_vars(&b).is_empty());
}

#[test]
fn two_free_vars_nest_two_exists() {
    let b = lb("loves($da, $de).");
    assert_eq!(count_exists_binding(&b, "$da"), 1);
    assert_eq!(count_exists_binding(&b, "$de"), 1);
    assert!(free_vars(&b).is_empty());
}

#[test]
fn repeated_free_var_binds_once() {
    // `loves($da, $da).` — the same variable in two places binds exactly once.
    let b = lb("loves($da, $da).");
    assert_eq!(count_exists_binding(&b, "$da"), 1);
    assert!(free_vars(&b).is_empty());
}

#[test]
fn single_free_var_di() {
    let b = lb("big($di).");
    assert!(matches!(root(&b), LogicNode::ExistsNode((v, _)) if v == "$di"));
    assert!(free_vars(&b).is_empty());
}

#[test]
fn negation_is_outside_the_existential() {
    // `~loves($da, me).` — the Not wraps the whole existential (¬∃), not the
    // inner predicate.
    let b = lb("~loves($da, me).");
    let inner = match root(&b) {
        LogicNode::NotNode(i) => *i,
        other => panic!("root not Not: {other:?}"),
    };
    assert!(matches!(node(&b, inner), LogicNode::ExistsNode(_)));
    assert!(free_vars(&b).is_empty());
}

#[test]
fn witness_binds_a_fresh_existential() {
    // `goes(?).` — the `?` witness closes under a fresh existential and fills
    // x1 with that fresh variable.
    let b = lb("goes(?).");
    let bound = match root(&b) {
        LogicNode::ExistsNode((v, _)) => v.clone(),
        other => panic!("root not Exists: {other:?}"),
    };
    assert!(matches!(role_filler(&b, "goes_x1"), Some(LogicalTerm::Variable(v)) if v == bound));
    assert!(free_vars(&b).is_empty());
}

#[test]
fn two_witnesses_are_independent() {
    // `likes(?, ?).` — two `?` produce two DISTINCT fresh existentials.
    let b = lb("likes(?, ?).");
    let x1 = role_filler(&b, "likes_x1").unwrap();
    let x2 = role_filler(&b, "likes_x2").unwrap();
    assert!(matches!(x1, LogicalTerm::Variable(_)));
    assert!(matches!(x2, LogicalTerm::Variable(_)));
    assert_ne!(x1, x2, "the two witnesses must be distinct vars");
    assert!(free_vars(&b).is_empty());
}

#[test]
fn witness_not_stolen_by_nested_rel_clause() {
    // `loves(?, some dog where big).` — the outer `?` stays bound at the outer
    // matrix and is not drained into the nested relative-clause compile; the
    // whole form is closed.
    let b = lb("loves(?, some dog where big).");
    assert!(free_vars(&b).is_empty());
}
