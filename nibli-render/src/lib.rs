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
mod corpus_overlay;
mod fact;
mod frame;
mod logic;
mod overlay;
mod proof;
mod register;
mod summary;
mod term;

pub use collapse::{
    collapse_proof, collapse_proof_with, render_collapsed_text, render_collapsed_text_with,
    render_node_text,
};
pub use corpus_overlay::{DRUG_INTERACTIONS_OVERLAY, GDPR_OVERLAY, UTOPIA_OVERLAY};
pub use fact::humanize_fact;
pub use logic::{render_logic_buffer, render_logic_tree};
pub use overlay::DomainGloss;
pub use proof::{
    RenderedNode, css_class, icon, label, render_proof, render_proof_text,
    render_proof_text_indented, trace_display,
};
pub use register::Register;
pub use summary::{
    VerdictKind, fact_to_english, summarize_proof, summarize_proof_with, summarize_verdict,
    verdict_kind,
};

/// True for relations that are internal reasoning artifacts, not surface content —
/// currently the opaque abstraction marker (`__abs_<id>`) nibli-semantics emits for
/// `nu`/`du'u`/`ka`/`ni`/`si'o`. The renderer drops these everywhere so they never
/// appear in back-translation, proof summaries, or fact listings.
pub(crate) fn is_internal_relation(rel: &str) -> bool {
    rel.starts_with("__abs_")
}

#[cfg(test)]
mod tests {
    use super::*;
    use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

    fn compile_kr(text: &str) -> LogicBuffer {
        nibli_semantics::compile_from_ast(nibli_kr::parse_checked(text).expect("KR parse"))
            .expect("KR compile")
    }

    #[test]
    fn existential_scope_is_visible_in_both_registers() {
        let shared = compile_kr("likes($y, every dog).");
        let dependent = compile_kr("all $x: dog($x) -> likes($y, $x).");
        // Independent IR checks: this is a real scope distinction at the public
        // KR seam, not two hand-made trees assigned different expected prose.
        assert!(
            matches!(&shared.nodes[shared.roots[0] as usize], LogicNode::ExistsNode((_, body)) if matches!(shared.nodes[*body as usize], LogicNode::ForAllNode(_)))
        );
        assert!(matches!(
            &dependent.nodes[dependent.roots[0] as usize],
            LogicNode::ForAllNode(_)
        ));
        let renamed = compile_kr("likes($companion, every dog).");
        for register in [Register::Spec, Register::Fluent] {
            let one = render_logic_buffer(&shared, register);
            let per_dog = render_logic_buffer(&dependent, register);
            assert_eq!(
                one,
                "There exists X such that (for every Y, if Y is a dog, then X likes Y)."
            );
            assert_eq!(
                per_dog,
                "For every X, if X is a dog, then there exists Y such that (Y likes X)."
            );
            assert_ne!(one, per_dog);
            assert_eq!(one, render_logic_buffer(&renamed, register));
        }
    }

    #[test]
    fn existential_restriction_stays_outside_its_duty_description() {
        let buf = compile_kr("obliged(some person, event { message() }).");
        let tree = render_logic_tree(&buf, Register::Spec);
        assert!(tree.contains("person_x1("), "{tree}");
        assert!(
            tree.contains("__abs_"),
            "compiler must retain opaque packaging: {tree}"
        );
        for register in [Register::Spec, Register::Fluent] {
            let out = render_logic_buffer(&buf, register);
            assert_eq!(
                out,
                "There exists X such that (X is a person and (X is obligated to notify))."
            );
            assert!(!out.contains("obligated to person"));
        }
    }

    #[test]
    fn opaque_duty_bodies_keep_arguments_negation_and_local_binders() {
        for (text, content) in [
            ("obliged(Alis, event { message(Bob) }).", "Bob"),
            (
                "obliged(Alis, event { ~message() }).",
                "it is not the case that",
            ),
            (
                "obliged(Alis, event { message(some person) }).",
                "there exists",
            ),
            (
                "obliged(Alis, event { message(every person) }).",
                "for every",
            ),
        ] {
            let buf = compile_kr(text);
            for register in [Register::Spec, Register::Fluent] {
                let out = render_logic_buffer(&buf, register);
                assert!(
                    out.starts_with("Alis is obligated to an event described by ("),
                    "{text}: {out}"
                );
                assert!(
                    out.contains(content),
                    "duty content disappeared for {text}: {out}"
                );
                assert!(!out.contains("__abs_"), "internal marker leaked: {out}");
            }
        }
    }

    #[test]
    fn negation_keeps_its_existential_scope() {
        let buf = compile_kr("~likes(some person, every dog).");
        let tree = render_logic_tree(&buf, Register::Spec);
        assert!(
            matches!(&buf.nodes[buf.roots[0] as usize], LogicNode::NotNode(body) if matches!(buf.nodes[*body as usize], LogicNode::ExistsNode(_)))
        );
        for register in [Register::Spec, Register::Fluent] {
            let out = render_logic_buffer(&buf, register);
            assert!(
                out.contains("there exists") || out.contains("There exists"),
                "{tree}\n{out}"
            );
            assert!(out.contains("for every"), "{tree}\n{out}");
            assert!(
                out.to_lowercase().contains("it is not the case that ("),
                "{tree}\n{out}"
            );
        }
    }

    #[test]
    fn non_duty_abstractions_never_assert_the_quoted_body() {
        let buf = compile_kr("entitled(some person, event { message(Bob) }).");
        let out = render_logic_buffer(&buf, Register::Spec);
        assert!(out.contains("is a person"), "{out}");
        assert!(out.contains("is entitled to"), "{out}");
        assert!(out.contains("is an event described by (Bob"), "{out}");
        assert!(!out.contains("__abs_"), "{out}");
    }

    #[test]
    fn neighboring_duties_do_not_merge_their_quoted_content() {
        let buf =
            compile_kr("obliged(Alis, event { message() }) & obliged(Bob, event { secure() }).");
        let out = render_logic_buffer(&buf, Register::Spec);
        assert!(out.contains("Alis is obligated to notify"), "{out}");
        assert!(out.contains("Bob is obligated to be secure"), "{out}");
        assert!(!out.contains("notify and be secure"), "{out}");
    }

    #[test]
    fn duty_keeps_the_removed_witness_in_the_removed_place() {
        let buf = compile_kr("obliged(every permitted, event { removes(removed: some data) }).");
        // The compiled x2 must share the data witness, regardless of the
        // unrelated event variables and the surrounding duty-holder binder.
        let removed = buf
            .nodes
            .iter()
            .find_map(|node| match node {
                LogicNode::Predicate((rel, args)) if rel == "removes_x2" => args.get(1),
                _ => None,
            })
            .unwrap();
        assert!(buf.nodes.iter().any(|node| matches!(node, LogicNode::Predicate((rel, args)) if rel == "data_x1" && args.get(1) == Some(removed))));
        let out = render_logic_buffer(&buf, Register::Spec);
        assert_eq!(
            out,
            "For every X, if something permits X, then X is obligated to an event described by (there exists Y such that (Y is data and something removes Y))."
        );
    }

    /// Hand-build the compiled IR for `ro lo dog cu animal` ("every dog is an
    /// animal"): `∀v0. (∃ev0. dog(ev0) ∧ gerku_x1(ev0,v0) ∧ gerku_x2(ev0,zo'e))
    /// → (∃ev1. animal(ev1) ∧ danlu_x1(ev1,v0) ∧ danlu_x2(ev1,zo'e))`.
    fn syllogism_buffer() -> LogicBuffer {
        let v0 = || LogicalTerm::Variable("_v0".to_string());
        let ev0 = || LogicalTerm::Variable("_ev0".to_string());
        let ev1 = || LogicalTerm::Variable("_ev1".to_string());
        let nodes = vec![
            LogicNode::Predicate(("dog".into(), vec![ev0()])), // 0
            LogicNode::Predicate(("dog_x1".into(), vec![ev0(), v0()])), // 1
            LogicNode::Predicate(("dog_x2".into(), vec![ev0(), LogicalTerm::Unspecified])), // 2
            LogicNode::AndNode((0, 1)),                        // 3
            LogicNode::AndNode((3, 2)),                        // 4
            LogicNode::ExistsNode(("_ev0".into(), 4)),         // 5
            LogicNode::NotNode(5),                             // 6
            LogicNode::Predicate(("animal".into(), vec![ev1()])), // 7
            LogicNode::Predicate(("animal_x1".into(), vec![ev1(), v0()])), // 8
            LogicNode::Predicate(("animal_x2".into(), vec![ev1(), LogicalTerm::Unspecified])), // 9
            LogicNode::AndNode((7, 8)),                        // 10
            LogicNode::AndNode((10, 9)),                       // 11
            LogicNode::ExistsNode(("_ev1".into(), 11)),        // 12
            LogicNode::OrNode((6, 12)),                        // 13
            LogicNode::ForAllNode(("_v0".into(), 13)),         // 14
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
    fn utopia_floor_obligation_is_not_event_word_salad() {
        // obliged(every person, event { secure() }) must NOT read
        // "Y is event and Y is obligated to X".
        let ast =
            nibli_kr::parse_checked("obliged(every person, event { secure() }).").expect("parse");
        let buf = nibli_semantics::compile_from_ast(ast).expect("compile");
        let out = render_logic_buffer(&buf, Register::Spec);
        assert!(
            out.to_lowercase().contains("obligated to be secure")
                || out.to_lowercase().contains("obligated to be safe"),
            "expected deontic+content collapse, got: {out}"
        );
        assert!(
            !out.to_lowercase().contains("is event"),
            "scaffolding 'event' leaked: {out}"
        );
    }

    /// `entitled` is the claim-right predicate: x1 = holder, x2 = entitlement,
    /// x3 = standard. Two properties matter for reader-facing honesty and are
    /// pinned here.
    #[test]
    fn entitled_keeps_the_holder_in_subject_position_and_hides_the_standard() {
        let render = |t: &str| {
            let ast = nibli_kr::parse_checked(t).expect("parse");
            let buf = nibli_semantics::compile_from_ast(ast).expect("compile");
            render_logic_buffer(&buf, Register::Spec)
        };

        // (1) The x3 `standard` place NEVER reaches the English — the corpus
        // template is 2-placeholder, so a filled OR unfilled standard is
        // invisible. An unconditional floor therefore cannot read as though it
        // carried a condition (the reason this entry exists rather than reusing
        // `deserve`, whose x2/x3 are "wage"/"work").
        assert_eq!(
            render("entitled(Adam, Bread)."),
            "Adam is entitled to Bread."
        );
        assert_eq!(
            render("entitled(Adam, Bread, Law)."),
            "Adam is entitled to Bread.",
            "the `standard` place must not leak into the back-translation"
        );

        // (2) In the rights-floor form the HOLDER stays the grammatical subject.
        // Contrast `permitted`, whose x1<->x2 swap surfaces as "Y permits X" —
        // exactly the inversion a floor right must not have.
        let floor = render("entitled(every person, event { eats() }).");
        assert!(
            floor.contains("X is entitled to"),
            "the holder must stay in subject position, got: {floor}"
        );
        assert!(
            !floor.contains("entitles"),
            "the floor must not invert into an entitle-the-party reading: {floor}"
        );
        // Non-duty abstractions retain an explicit referent and quoted body;
        // they must never render the body as a separate assertion of actuality.
        assert!(floor.contains("is an event described by ("), "{floor}");
    }

    /// THE OBLIGATED PARTY IS x1, in every spelling and at every arity.
    ///
    /// `obliged`'s corpus places are `[bound, duty, standard]`, so the party bound by
    /// the duty is place 1. Two defects used to sit on top of that, and fixing either
    /// alone left the other:
    ///
    /// (a) the renderer took place 2 as the duty-holder — right only for the CONVERTED
    ///     argument order — so a plain-spelled duty named the wrong party, and in the
    ///     deontic form it named a variable bound to nothing ("then Y is obligated
    ///     to notify");
    /// (b) a `TEMPLATE_OVERRIDES` row written in that same converted order
    ///     ("{x2} is obligated that {x1}") beat the correct corpus template. At arity 1
    ///     its leading `{x2}` tripped `fill_template`'s trailing-elision cut and the
    ///     whole line rendered as the EMPTY STRING — which is how `gdpr.nibli`'s
    ///     Article 6(1)(c) restrictor came out as "For every X, if , then …", with the
    ///     antecedent silently gone from a corpus the Transparency Triad asks
    ///     reviewers to check.
    #[test]
    fn a_duty_names_the_bound_party_at_every_arity() {
        let render = |t: &str| {
            let ast = nibli_kr::parse_checked(t).expect("parse");
            let buf = nibli_semantics::compile_from_ast(ast).expect("compile");
            render_logic_buffer(&buf, Register::Spec)
        };

        // (a) x1 is the bound party.
        assert_eq!(render("obliged(Adam, Bel)."), "Adam is obligated to Bel.");
        // The converse alias exchanges the arguments — so it names the OTHER one, and
        // that is the whole point of `_by`. Both readings come from one place contract.
        assert_eq!(
            render("obligated_by(Adam, Bel)."),
            "Bel is obligated to Adam.",
            "the converse alias must still invert, and visibly"
        );

        // (b) arity 1 must render, not vanish.
        assert_eq!(render("obliged(Adam)."), "Adam is obligated.");
        // The shipped GDPR Article 6(1)(c) shape: the antecedent must survive.
        let art6c = render("permitted(every person where obliged).");
        assert!(
            art6c.contains("if X is obligated, then"),
            "the restrictor must not be elided into 'if , then': {art6c}"
        );
        assert!(
            !art6c.contains("if , then"),
            "empty antecedent regressed: {art6c}"
        );

        // The deontic collapse names the party, not the event scaffold.
        let duty = render("obliged(every data governs, event { message() }).");
        assert_eq!(
            duty,
            "For every X, if X governs and X is data, then X is obligated to notify.",
            "{}",
            render_logic_tree(
                &compile_kr("obliged(every data governs, event { message() })."),
                Register::Spec
            )
        );
    }

    #[test]
    fn lose_and_building_place_order_read_naturally() {
        let lose = {
            let ast = nibli_kr::parse_checked("lose(Points, Bela).").unwrap();
            let buf = nibli_semantics::compile_from_ast(ast).unwrap();
            render_logic_buffer(&buf, Register::Spec)
        };
        assert!(
            lose.to_lowercase().contains("bela loses points"),
            "got: {lose}"
        );
        let bld = {
            let ast = nibli_kr::parse_checked("building(HighSec, Lalo).").unwrap();
            let buf = nibli_semantics::compile_from_ast(ast).unwrap();
            render_logic_buffer(&buf, Register::Spec)
        };
        assert!(
            bld.to_lowercase().contains("lalo") && bld.to_lowercase().contains("highsec"),
            "got: {bld}"
        );
        assert!(
            bld.to_lowercase().contains("placed") || bld.to_lowercase().contains("housed"),
            "got: {bld}"
        );
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
        // A directly-asserted flat fact animal(adam) -> "adam is an animal."
        let buf = LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                "animal".into(),
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
        // `goes fi le market` — x1 is unspecified (zo'e) but x3 is filled (le market).
        // The English gloss must NOT collapse to empty (the pre-fix `:debug` bug);
        // the interior/leading x1 renders the generic "something".
        let ev0 = || LogicalTerm::Variable("_ev0".to_string());
        let buf = LogicBuffer {
            nodes: vec![
                LogicNode::Predicate(("goes".into(), vec![ev0()])), // 0
                LogicNode::Predicate(("goes_x1".into(), vec![ev0(), LogicalTerm::Unspecified])), // 1
                LogicNode::Predicate((
                    "goes_x3".into(),
                    vec![ev0(), LogicalTerm::Description("market".into())],
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
        assert!(tree.contains("dog(_ev0)\n"), "tree:\n{tree}");
        assert!(tree.contains("dog_x1(_ev0, _v0)\n"), "tree:\n{tree}");
        assert!(tree.contains("dog_x2(_ev0, something)\n"), "tree:\n{tree}");
        assert!(!tree.contains("(Pred"), "S-expr leaked: {tree}");
        assert!(!tree.contains("(Cons"), "S-expr leaked: {tree}");
    }

    #[test]
    fn logic_tree_renders_compute_and_integers() {
        // A hand-built ComputeNode — the shape `exponential` takes once it is registered
        // for compute dispatch (as in the Ch 18 `:debug` after `:compute exponential`);
        // a bare `:debug li … exponential …` in a default session compiles `exponential` to a
        // plain Predicate. Exercises the `[compute]` marker + integer term rendering.
        let ev0 = || LogicalTerm::Variable("_ev0".to_string());
        let buf = LogicBuffer {
            nodes: vec![
                LogicNode::ComputeNode(("exponential".into(), vec![ev0()])), // 0
                LogicNode::Predicate((
                    "exponential_x1".into(),
                    vec![ev0(), LogicalTerm::Number(1024.0)],
                )), // 1
                LogicNode::AndNode((0, 1)),                                  // 2
                LogicNode::Predicate((
                    "exponential_x2".into(),
                    vec![ev0(), LogicalTerm::Number(2.0)],
                )), // 3
                LogicNode::AndNode((2, 3)),                                  // 4
                LogicNode::Predicate((
                    "exponential_x3".into(),
                    vec![ev0(), LogicalTerm::Number(10.0)],
                )), // 5
                LogicNode::AndNode((4, 5)),                                  // 6
                LogicNode::ExistsNode(("_ev0".into(), 6)),                   // 7
            ],
            roots: vec![7],
        };
        let expected = "\u{2203} _ev0:\n  And:\n    And:\n      And:\n        exponential(_ev0) [compute]\n        exponential_x1(_ev0, 1024)\n      exponential_x2(_ev0, 2)\n    exponential_x3(_ev0, 10)\n";
        assert_eq!(render_logic_tree(&buf, Register::Spec), expected);
    }

    #[test]
    fn logic_tree_flat_fact() {
        let buf = LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                "animal".into(),
                vec![LogicalTerm::Constant("adam".into())],
            ))],
            roots: vec![0],
        };
        assert_eq!(render_logic_tree(&buf, Register::Spec), "animal(adam)\n");
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
