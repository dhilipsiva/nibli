//! Term forms: names, numbers, quoted literals, empty args, descriptions, and
//! the opaque `the`-domain vs veridical restrictor discriminator.

use super::*;

#[test]
fn name_compiles_to_constant() {
    let b = lb("goes(Alis).");
    assert!(role_is_const(&b, "goes_x1", "alis"));
}

#[test]
fn number_compiles_to_number_term() {
    let b = lb("number(42).");
    assert_eq!(
        role_filler(&b, "number_x1"),
        Some(LogicalTerm::Number(42.0))
    );
}

#[test]
fn quoted_literal_compiles_to_constant() {
    let b = lb("word(\"coi\").");
    assert!(role_is_const(&b, "word_x1", "coi"));
}

#[test]
fn no_explicit_args_fill_unspecified() {
    // `goes().` — every place is Unspecified.
    let b = lb("goes().");
    for r in ["goes_x1", "goes_x2", "goes_x3", "goes_x4", "goes_x5"] {
        assert_eq!(role_filler(&b, r), Some(LogicalTerm::Unspecified), "{r}");
    }
}

#[test]
fn the_description_stays_a_description_term() {
    // `big(the dog).` — `the` is the opaque designator, so x1 is a Description
    // term, not a decomposed existential.
    let b = lb("big(the dog).");
    assert_eq!(
        role_filler(&b, "big_x1"),
        Some(LogicalTerm::Description("dog".into()))
    );
}

#[test]
fn every_the_uses_opaque_domain_restrictor() {
    // `every the dog` — the universal ranges over the OPAQUE domain
    // (`the_domain_dog`), and the veridical `dog` type predicate is absent.
    let b = lb("fast(every the dog).");
    assert!(matches!(root(&b), LogicNode::ForAllNode(_)));
    assert!(has_pred(&b, "the_domain_dog"));
    assert!(!has_pred(&b, "dog"));
}

#[test]
fn every_uses_veridical_restrictor() {
    // `every dog` — veridical: the `dog` type predicate is present, the opaque
    // domain restrictor absent.
    let b = lb("fast(every dog).");
    assert!(has_pred(&b, "dog"));
    assert!(!has_pred(&b, "the_domain_dog"));
}

#[test]
fn exactly_the_uses_opaque_domain_restrictor() {
    let b = lb("fast(exactly 2 the dog).");
    assert!(matches!(root(&b), LogicNode::CountNode((_, 2, _))));
    assert!(has_pred(&b, "the_domain_dog"));
}

#[test]
fn exactly_uses_veridical_restrictor() {
    let b = lb("fast(exactly 2 dog).");
    assert!(matches!(root(&b), LogicNode::CountNode((_, 2, _))));
    assert!(has_pred(&b, "dog"));
    assert!(!has_pred(&b, "the_domain_dog"));
}
