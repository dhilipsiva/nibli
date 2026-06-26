//! Shared human-readable rendering for Nibli.
//!
//! ONE place that turns the engine's internal representations into English for
//! the two surfaces humans read to *verify* the engine:
//!
//! - [`render_logic_buffer`] — the Transparency Triad back-translation: compiles
//!   a `LogicBuffer` (the FOL IR) into structure-exposing English.
//! - [`humanize_fact`] / [`render_proof`] / [`render_proof_text`] — readable proof
//!   traces, sharing the same fact humanizer and term rendering.
//!
//! Rendering is pure: it reads `LogicBuffer`/`ProofTrace` and never mutates a
//! verdict or a proof's tree shape. Unknown predicates fall back to a generic
//! `relation(args)` / gloss-based frame — never invented English.

mod collapse;
mod fact;
mod frame;
mod logic;
mod proof;
mod register;
mod summary;
mod term;

pub use collapse::{collapse_proof, render_node_text};
pub use fact::humanize_fact;
pub use logic::{render_logic_buffer, render_logic_tree};
pub use proof::{
    RenderedNode, css_class, icon, label, render_proof, render_proof_text,
    render_proof_text_indented, trace_display,
};
pub use register::Register;
pub use summary::{fact_to_english, summarize_proof};

#[cfg(test)]
mod tests {
    use super::*;
    use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

    /// Hand-build the compiled IR for `ro lo gerku cu danlu` ("every dog is an
    /// animal"): `∀v0. (∃ev0. gerku(ev0) ∧ gerku_x1(ev0,v0) ∧ gerku_x2(ev0,zo'e))
    /// → (∃ev1. danlu(ev1) ∧ danlu_x1(ev1,v0) ∧ danlu_x2(ev1,zo'e))`.
    fn syllogism_buffer() -> LogicBuffer {
        let v0 = || LogicalTerm::Variable("_v0".to_string());
        let ev0 = || LogicalTerm::Variable("_ev0".to_string());
        let ev1 = || LogicalTerm::Variable("_ev1".to_string());
        let nodes = vec![
            LogicNode::Predicate(("gerku".into(), vec![ev0()])), // 0
            LogicNode::Predicate(("gerku_x1".into(), vec![ev0(), v0()])), // 1
            LogicNode::Predicate(("gerku_x2".into(), vec![ev0(), LogicalTerm::Unspecified])), // 2
            LogicNode::AndNode((0, 1)),                          // 3
            LogicNode::AndNode((3, 2)),                          // 4
            LogicNode::ExistsNode(("_ev0".into(), 4)),           // 5
            LogicNode::NotNode(5),                               // 6
            LogicNode::Predicate(("danlu".into(), vec![ev1()])), // 7
            LogicNode::Predicate(("danlu_x1".into(), vec![ev1(), v0()])), // 8
            LogicNode::Predicate(("danlu_x2".into(), vec![ev1(), LogicalTerm::Unspecified])), // 9
            LogicNode::AndNode((7, 8)),                          // 10
            LogicNode::AndNode((10, 9)),                         // 11
            LogicNode::ExistsNode(("_ev1".into(), 11)),          // 12
            LogicNode::OrNode((6, 12)),                          // 13
            LogicNode::ForAllNode(("_v0".into(), 13)),           // 14
        ];
        LogicBuffer {
            nodes,
            roots: vec![14],
        }
    }

    #[test]
    fn syllogism_back_translation_is_readable_and_scope_exposing() {
        let out = render_logic_buffer(&syllogism_buffer(), Register::Spec);
        assert_eq!(out, "For every X, if X is a dog, then X is an animal.");
        // The whole point: not the old word-salad gloss.
        assert_ne!(out, "all the dog animal");
    }

    #[test]
    fn back_translation_exposes_scope() {
        let out = render_logic_buffer(&syllogism_buffer(), Register::Spec);
        assert!(
            out.to_lowercase().contains("for every"),
            "scope hidden: {out}"
        );
        assert!(
            out.contains("if") && out.contains("then"),
            "implication hidden: {out}"
        );
        assert!(out.contains("dog") && out.contains("animal"));
    }

    #[test]
    fn spec_and_fluent_share_binder_order() {
        let buf = syllogism_buffer();
        let spec = render_logic_buffer(&buf, Register::Spec);
        let fluent = render_logic_buffer(&buf, Register::Fluent);
        // Whatever smoothing Fluent applies, the restrictor must precede the
        // matrix in both — a scope/binder-order invariant.
        let dog_before_animal = |s: &str| {
            s.find("dog")
                .zip(s.find("animal"))
                .is_some_and(|(d, a)| d < a)
        };
        assert!(dog_before_animal(&spec), "spec: {spec}");
        assert!(dog_before_animal(&fluent), "fluent: {fluent}");
    }

    #[test]
    fn flat_fact_back_translation() {
        // A directly-asserted flat fact danlu(adam) -> "adam is an animal."
        let buf = LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                "danlu".into(),
                vec![LogicalTerm::Constant("adam".into())],
            ))],
            roots: vec![0],
        };
        assert_eq!(
            render_logic_buffer(&buf, Register::Spec),
            "Adam is an animal."
        );
    }

    #[test]
    fn interior_unspecified_place_is_not_dropped() {
        // `klama fi le zarci` — x1 is unspecified (zo'e) but x3 is filled (le zarci).
        // The English gloss must NOT collapse to empty (the pre-fix `:debug` bug);
        // the interior/leading x1 renders the generic "something".
        let ev0 = || LogicalTerm::Variable("_ev0".to_string());
        let buf = LogicBuffer {
            nodes: vec![
                LogicNode::Predicate(("klama".into(), vec![ev0()])), // 0
                LogicNode::Predicate(("klama_x1".into(), vec![ev0(), LogicalTerm::Unspecified])), // 1
                LogicNode::Predicate((
                    "klama_x3".into(),
                    vec![ev0(), LogicalTerm::Description("zarci".into())],
                )), // 2
                LogicNode::AndNode((0, 1)),                // 3
                LogicNode::AndNode((3, 2)),                // 4
                LogicNode::ExistsNode(("_ev0".into(), 4)), // 5
            ],
            roots: vec![5],
        };
        let out = render_logic_buffer(&buf, Register::Spec);
        assert!(
            !out.is_empty(),
            "an interior-unspecified frame must not render an empty gloss"
        );
        assert!(
            out.to_lowercase().contains("something"),
            "the unspecified x1 should render a generic filler, got: {out}"
        );
    }

    #[test]
    fn logic_tree_exposes_every_node_with_indentation() {
        let tree = render_logic_tree(&syllogism_buffer(), Register::Spec);
        // The structural tree shows the raw compiled FOL, NOT the regrouped English:
        // every quantifier / connective / event binder is its own indented line.
        assert!(tree.starts_with("\u{2200} _v0:\n"), "tree:\n{tree}");
        assert!(tree.contains("\n  Or:\n"), "tree:\n{tree}");
        assert!(tree.contains("\n    \u{00ac}:\n"), "tree:\n{tree}");
        assert!(tree.contains("\n      \u{2203} _ev0:\n"), "tree:\n{tree}");
        // Functional term notation (never LISP S-expr).
        assert!(tree.contains("gerku(_ev0)\n"), "tree:\n{tree}");
        assert!(tree.contains("gerku_x1(_ev0, _v0)\n"), "tree:\n{tree}");
        assert!(tree.contains("gerku_x2(_ev0, zo'e)\n"), "tree:\n{tree}");
        assert!(!tree.contains("(Pred"), "S-expr leaked: {tree}");
        assert!(!tree.contains("(Cons"), "S-expr leaked: {tree}");
    }

    #[test]
    fn logic_tree_renders_compute_and_integers() {
        // A hand-built ComputeNode — the shape `tenfa` takes once it is registered
        // for compute dispatch (as in the Ch 18 `:debug` after `:compute tenfa`);
        // a bare `:debug li … tenfa …` in a default session compiles `tenfa` to a
        // plain Predicate. Exercises the `[compute]` marker + integer term rendering.
        let ev0 = || LogicalTerm::Variable("_ev0".to_string());
        let buf = LogicBuffer {
            nodes: vec![
                LogicNode::ComputeNode(("tenfa".into(), vec![ev0()])), // 0
                LogicNode::Predicate(("tenfa_x1".into(), vec![ev0(), LogicalTerm::Number(1024.0)])), // 1
                LogicNode::AndNode((0, 1)), // 2
                LogicNode::Predicate(("tenfa_x2".into(), vec![ev0(), LogicalTerm::Number(2.0)])), // 3
                LogicNode::AndNode((2, 3)), // 4
                LogicNode::Predicate(("tenfa_x3".into(), vec![ev0(), LogicalTerm::Number(10.0)])), // 5
                LogicNode::AndNode((4, 5)),                // 6
                LogicNode::ExistsNode(("_ev0".into(), 6)), // 7
            ],
            roots: vec![7],
        };
        let expected = "\u{2203} _ev0:\n  And:\n    And:\n      And:\n        tenfa(_ev0) [compute]\n        tenfa_x1(_ev0, 1024)\n      tenfa_x2(_ev0, 2)\n    tenfa_x3(_ev0, 10)\n";
        assert_eq!(render_logic_tree(&buf, Register::Spec), expected);
    }

    #[test]
    fn logic_tree_flat_fact() {
        let buf = LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                "danlu".into(),
                vec![LogicalTerm::Constant("adam".into())],
            ))],
            roots: vec![0],
        };
        assert_eq!(render_logic_tree(&buf, Register::Spec), "danlu(adam)\n");
    }

    #[test]
    fn logic_tree_invalid_root_is_reported() {
        let buf = LogicBuffer {
            nodes: vec![],
            roots: vec![5],
        };
        assert_eq!(
            render_logic_tree(&buf, Register::Spec),
            "[invalid node 5]\n"
        );
    }
}
