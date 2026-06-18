//! Output register for the back-translation: how readable vs. how structural.

/// Controls how structure-exposing the rendered English is.
///
/// `Spec` is the default and the safe choice for a zero-hallucination prover:
/// it keeps quantifier scope and logical structure explicit ("For every X: if X
/// is a dog, then X is an animal"), so a reader verifying the encoding can see
/// the binder order. `Fluent` is an optional enhancement that smooths the prose
/// where it can do so *without* reordering binders or dropping a negation; it
/// must never make a scope error harder to spot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Register {
    /// Structure-exposing logical-specification English (default).
    #[default]
    Spec,
    /// Smoothed readable English (must preserve binder order and negation).
    Fluent,
}
