//! The abstraction-decomposition *shape* tests migrated to
//! `nibli-kr/src/shape_tests/abstractions.rs`. What stays here is the
//! defense-in-depth guard the KR emitter rejects first (a bare `slot` outside
//! a `property { … }` block): only a hand-built buffer can reach the
//! nibli-semantics-layer check.

use super::*;

#[test]
fn test_slot_outside_property_is_rejected() {
    // `slot` outside a `property` abstraction has no binder. The old behavior
    // minted a fresh variable that stayed FREE through compilation (the safety
    // net does not close `_v` fresh vars) — a non-ground form leaking toward
    // the store. Fail closed: a semantic error is accumulated, and no free
    // variable escapes. (Via KR, the emitter rejects `slot` here first; this
    // pins the semantics-layer guard independently.)
    let predicates = vec![Predicate::Root("beautiful".into())];
    let arguments = vec![Argument::Marker(Marker::Slot)];
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
    let x1_args = get_pred_args(&form, "beautiful_x1", &compiler)
        .expect("expected beautiful_x1 role predicate");
    assert!(
        matches!(&x1_args[1], IrTerm::Unspecified),
        "rejected slot compiles to Unspecified (no free variable), got {:?}",
        x1_args[1]
    );
}
