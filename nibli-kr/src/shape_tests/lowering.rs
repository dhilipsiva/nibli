//! Flat identity, raw place labels, and the `via` modal lowering.

use super::*;

#[test]
fn identity_lowers_flat_not_decomposed() {
    // `me = you.` — the identity predicate is FLAT (a single 2-arg `equals`),
    // NOT event-decomposed: no `equals_x1` role predicate, both args ground.
    let b = lb("me = you.");
    let args = pred_args(&b, "equals").unwrap();
    assert_eq!(args.len(), 2, "identity is a flat binary predicate");
    assert!(!has_pred(&b, "equals_x1"), "identity must not decompose");
    assert!(matches!(root(&b), LogicNode::Predicate(_)));
}

#[test]
fn raw_place_label_routes_to_named_place() {
    // `goes(me, x2: you).` — the untagged `me` fills x1, the raw `x2:` label
    // routes `you` to x2.
    let b = lb("goes(me, x2: you).");
    assert!(role_is_const(&b, "goes_x1", "me"));
    assert!(role_is_const(&b, "goes_x2", "you"));
}

#[test]
fn via_modal_is_flat_with_threaded_subject() {
    // `goes(me) via makes(you).` — the main clause decomposes; the `via` modal
    // is a FLAT predicate whose first arg is its own subject (`you`) and whose
    // second is the main clause's x1 threaded in (`me`).
    let b = lb("goes(me) via makes(you).");
    assert!(has_pred(&b, "goes"), "main clause decomposes");
    let makes = pred_args(&b, "makes").unwrap();
    assert_eq!(makes[0], LogicalTerm::Constant("you".into()));
    assert_eq!(makes[1], LogicalTerm::Constant("me".into()));
}
