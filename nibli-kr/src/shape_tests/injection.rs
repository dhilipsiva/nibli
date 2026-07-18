//! Implicit-`it` (ke'a) injection into relative-clause bodies.

use super::*;

#[test]
fn single_predicate_injects_head_into_subject() {
    // `some dog where big` — the bare-body sugar binds the clause's subject to
    // the description entity: `big`'s x1 filler equals `dog`'s x1 filler (and
    // `goes`'s x1 too). The KR twin of the (staying) hand-built inject-fill
    // test — via KR the emitter marks x1 explicitly, but the observable
    // (shared entity var) is identical.
    let b = lb("goes(some dog where big).");
    let big = role_filler(&b, "big_x1").unwrap();
    let dog = role_filler(&b, "dog_x1").unwrap();
    let goes = role_filler(&b, "goes_x1").unwrap();
    assert!(matches!(big, LogicalTerm::Variable(_)));
    assert_eq!(big, dog, "clause subject binds the description var");
    assert_eq!(dog, goes, "matrix subject binds the same var");
}

#[test]
fn named_x1_const_x2_it_routes_both() {
    // `loves(lover: Alis, loved: it)` — x1 is the constant, x2 is the injected
    // clause var (equal to the domain `dog`'s var).
    let b = lb("animal(every dog where loves(lover: Alis, loved: it)).");
    assert!(role_is_const(&b, "loves_x1", "alis"));
    assert_eq!(role_filler(&b, "loves_x2"), role_filler(&b, "dog_x1"));
}

#[test]
fn named_x1_it_x2_const_routes_both() {
    // Mirror: x1 is the injected clause var, x2 the constant.
    let b = lb("animal(every dog where loves(lover: it, loved: Alis)).");
    assert_eq!(role_filler(&b, "loves_x1"), role_filler(&b, "dog_x1"));
    assert!(role_is_const(&b, "loves_x2", "alis"));
}

#[test]
fn lone_named_it_leaves_x1_unspecified() {
    // `loves(loved: it)` — only x2 is the clause var; x1 is NOT double-filled,
    // it stays Unspecified.
    let b = lb("animal(every dog where loves(loved: it)).");
    assert_eq!(role_filler(&b, "loves_x1"), Some(LogicalTerm::Unspecified));
    assert_eq!(role_filler(&b, "loves_x2"), role_filler(&b, "dog_x1"));
}
