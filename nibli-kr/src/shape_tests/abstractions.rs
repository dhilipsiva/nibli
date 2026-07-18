//! Abstraction (`event`/`fact`/`property`/`amount`/`concept`) decomposition.

use super::*;

#[test]
fn fact_abstraction_emits_fact_predicate() {
    // `big(fact { goes(me) }).` — the abstraction contributes a `fact` type
    // predicate alongside the inner body's `goes`.
    let b = lb("big(fact { goes(me) }).");
    assert!(has_pred(&b, "fact"));
    assert!(has_pred(&b, "goes"));
}

#[test]
fn amount_abstraction_emits_amount_predicate() {
    let b = lb("big(amount { happy(me) }).");
    assert!(has_pred(&b, "amount"));
    assert!(has_pred(&b, "happy"));
}

#[test]
fn concept_abstraction_emits_concept_predicate() {
    let b = lb("big(concept { goes(me) }).");
    assert!(has_pred(&b, "concept"));
    assert!(has_pred(&b, "goes"));
}

#[test]
fn event_abstraction_emits_event_predicate() {
    let b = lb("big(event { goes(me) }).");
    assert!(has_pred(&b, "event"));
    assert!(has_pred(&b, "goes"));
}

#[test]
fn property_slot_binds_the_description_var() {
    // `big(property { beautiful(slot) }).` — the open `slot` inside a property
    // abstraction binds to the abstraction's description variable: the
    // `property` predicate's argument equals `beautiful`'s x1 filler.
    let b = lb("big(property { beautiful(slot) }).");
    let prop_var = pred_args(&b, "property").unwrap()[0].clone();
    let slot_filler = role_filler(&b, "beautiful_x1").unwrap();
    assert!(matches!(prop_var, LogicalTerm::Variable(_)));
    assert_eq!(
        prop_var, slot_filler,
        "slot must bind the property description var"
    );
}
