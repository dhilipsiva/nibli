//! Tense / deontic / negation / unspecified wrappers at the root.

use super::*;

#[test]
fn tense_past() {
    assert!(matches!(
        root(&lb("past goes(me).")),
        LogicNode::PastNode(_)
    ));
}

#[test]
fn tense_now() {
    assert!(matches!(
        root(&lb("now goes(me).")),
        LogicNode::PresentNode(_)
    ));
}

#[test]
fn tense_future() {
    assert!(matches!(
        root(&lb("future goes(me).")),
        LogicNode::FutureNode(_)
    ));
}

#[test]
fn deontic_must() {
    assert!(matches!(
        root(&lb("must goes(me).")),
        LogicNode::ObligatoryNode(_)
    ));
}

#[test]
fn deontic_may() {
    assert!(matches!(
        root(&lb("may goes(me).")),
        LogicNode::PermittedNode(_)
    ));
}

#[test]
fn predication_negation() {
    assert!(matches!(root(&lb("~goes(me).")), LogicNode::NotNode(_)));
}

#[test]
fn something_is_unspecified() {
    // `goes(_).` — the explicit `_` fills x1 with Unspecified.
    let b = lb("goes(_).");
    assert_eq!(role_filler(&b, "goes_x1"), Some(LogicalTerm::Unspecified));
}
