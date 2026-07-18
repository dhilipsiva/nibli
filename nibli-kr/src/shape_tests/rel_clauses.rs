//! Relative-clause placement: restrictive (antecedent) vs incidental
//! (consequent), and abstraction-body variable closure.

use super::*;

#[test]
fn incidental_clause_lands_in_consequent() {
    // `every dog also big` — the incidental `big` is an asserted property of
    // the domain members, so it sits in the universal's CONSEQUENT, not the
    // domain-narrowing antecedent.
    let b = lb("goes(every dog also big).");
    let (antecedent, consequent) = forall_or_split(&b);
    assert!(has_pred_from(&b, consequent, "big"));
    assert!(!has_pred_from(&b, antecedent, "big"));
}

#[test]
fn restrictive_clause_lands_in_antecedent() {
    // `every dog where big` — the restrictive `big` narrows the domain, so it
    // sits in the ANTECEDENT.
    let b = lb("goes(every dog where big).");
    let (antecedent, consequent) = forall_or_split(&b);
    assert!(has_pred_from(&b, antecedent, "big"));
    assert!(!has_pred_from(&b, consequent, "big"));
}

#[test]
fn incidental_under_exact_count_folds_into_body() {
    // `exactly 3 dog also big` — under an exact-count quantifier the incidental
    // is folded into the counted body (a documented residual: it reads
    // restrictive there).
    let b = lb("goes(exactly 3 dog also big).");
    let body = match root(&b) {
        LogicNode::CountNode((_, 3, body)) => *body,
        other => panic!("root not Count(3): {other:?}"),
    };
    assert!(has_pred_from(&b, body, "big"));
}

#[test]
fn abstraction_body_free_var_wrapped_once() {
    // `knows(me, event { runs($da) }).` — the `$da` inside the abstraction body
    // is bound exactly once, and the whole form is closed.
    let b = lb("knows(me, event { runs($da) }).");
    assert_eq!(count_exists_binding(&b, "$da"), 1);
    assert!(free_vars(&b).is_empty());
}
