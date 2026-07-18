//! Named-place routing, compound restrictor bodies, and rel-clauses on names.

use super::*;

#[test]
fn place_tag_within_arity_routes() {
    // `dog(x2: you).` — a raw place label within arity routes to x2; x1 stays
    // Unspecified (no untagged x1 supplied).
    let b = lb("dog(x2: you).");
    assert!(role_is_const(&b, "dog_x2", "you"));
    assert_eq!(role_filler(&b, "dog_x1"), Some(LogicalTerm::Unspecified));
}

#[test]
fn compound_restrictor_body_not_falsely_rejected() {
    // `some dog where fast runs` — a juxtaposition (tanru) in a restrictor
    // body: both `fast` and `runs` bind the domain entity and share the event
    // var (they are NOT falsely rejected as an unmarked bound place).
    let b = lb("goes(some dog where fast runs).");
    let dog = role_filler(&b, "dog_x1").unwrap();
    assert_eq!(role_filler(&b, "runs_x1"), Some(dog.clone()));
    assert_eq!(role_filler(&b, "fast_x1"), Some(dog));
    let runs_x1 = pred_args(&b, "runs_x1").unwrap();
    let fast_x1 = pred_args(&b, "fast_x1").unwrap();
    assert_eq!(runs_x1[0], fast_x1[0], "tanru units share the event var");
}

#[test]
fn rel_clause_on_name_is_conjoined() {
    // `goes(Adam where dog).` — a restrictive clause on a NAME is conjoined
    // (not dropped): both `goes` and `dog` predicate the same constant.
    let b = lb("goes(Adam where dog).");
    assert!(role_is_const(&b, "goes_x1", "adam"));
    assert!(role_is_const(&b, "dog_x1", "adam"));
}
