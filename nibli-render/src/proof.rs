//! Proof-trace rendering: ONE walker producing both indented text (CLI/REPL) and
//! a structured [`RenderedNode`] tree (the Dioxus component path). Keyed on the
//! wire `nibli_protocol::ProofTrace`, so every host/UI consumer shares it.
//!
//! Ported from nibli-protocol's former `trace_display`/`icon`/`label`/`css_class`
//! family; the only behavioral change is that fact payloads now route through the
//! fixed flat-form [`crate::fact::humanize_fact`] (the old S-expr humanizer dropped
//! arguments when fed the `relation(args)` form the trace actually carries).

#[cfg(test)]
use nibli_protocol::LogicalTerm;
use nibli_protocol::{AssertionCitation, ProofRule, ProofTrace, RuleCitation, WitnessOrigin};

use crate::fact::humanize_fact;
use crate::register::Register;

/// The closed-world honesty caveat prepended to a proof whose TRUE verdict rests
/// on negation-as-failure. One definition shared by the verbose and collapsed
/// text renderers.
pub(crate) const NAF_NOTE: &str =
    "[Note: result depends on negation-as-failure (closed-world assumption)]";

/// The closed-world honesty caveat prepended to a proof whose FALSE verdict rests on
/// the closed-world assumption ("not derivable from the KB"), as opposed to a
/// compute-decided FALSE from local arithmetic or a trusted external backend.
/// The dual of [`NAF_NOTE`].
pub(crate) const CWA_FALSE_NOTE: &str =
    "[Note: FALSE is closed-world — not derivable from the KB, not a proof of the negation]";

/// A rendered proof node: everything the text and component renderers need,
/// computed once. Children are rendered recursively.
#[derive(Clone, Debug, PartialEq)]
pub struct RenderedNode {
    pub icon: &'static str,
    pub label: String,
    pub css_class: &'static str,
    pub holds: bool,
    pub is_leaf: bool,
    /// A memoized back-reference (`ProofRef`): the UI renders it inline without
    /// expanding the already-shown subtree (so its `children` are left empty).
    pub inline: bool,
    pub children: Vec<RenderedNode>,
}

/// Build the structured rendered proof tree from a wire proof trace.
pub fn render_proof(trace: &ProofTrace, _register: Register) -> RenderedNode {
    build_node(trace, trace.root)
}

pub(crate) fn build_node(trace: &ProofTrace, idx: u32) -> RenderedNode {
    let Some(step) = trace.steps.get(idx as usize) else {
        return RenderedNode {
            icon: "?",
            label: format!("[invalid step index {idx}]"),
            css_class: "proof-failed",
            holds: false,
            is_leaf: true,
            inline: false,
            children: Vec::new(),
        };
    };
    // A ProofRef is a back-reference to an already-rendered subtree; render it
    // inline and do not re-expand the cached children in the UI tree.
    let is_ref = matches!(step.rule, ProofRule::ProofRef { .. });
    RenderedNode {
        icon: icon(&step.rule),
        label: label(&step.rule),
        css_class: css_class(&step.rule),
        holds: step.holds,
        is_leaf: step.children.is_empty(),
        inline: is_ref,
        children: if is_ref {
            Vec::new()
        } else {
            step.children
                .iter()
                .map(|&c| build_node(trace, c))
                .collect()
        },
    }
}

/// Render the proof tree as indented text (REPL/CLI), with the NAF note header.
pub fn render_proof_text(trace: &ProofTrace, register: Register) -> String {
    render_proof_text_indented(trace, register, 0)
}

/// As [`render_proof_text`], with a base indentation (nibli-host indents by one).
pub fn render_proof_text_indented(
    trace: &ProofTrace,
    _register: Register,
    base_indent: usize,
) -> String {
    let mut out = String::new();
    if trace.naf_dependent {
        out.push_str(NAF_NOTE);
        out.push('\n');
    }
    if trace.cwa_false {
        out.push_str(CWA_FALSE_NOTE);
        out.push('\n');
    }
    format_step(trace, trace.root, base_indent, &mut out);
    out
}

fn format_step(trace: &ProofTrace, idx: u32, indent: usize, out: &mut String) {
    let Some(step) = trace.steps.get(idx as usize) else {
        for _ in 0..indent {
            out.push_str("  ");
        }
        out.push_str(&format!("[invalid step index {idx}]\n"));
        return;
    };
    for _ in 0..indent {
        out.push_str("  ");
    }
    out.push_str(&trace_display(&step.rule, step.holds));
    out.push('\n');
    for &child in &step.children {
        format_step(trace, child, indent + 1, out);
    }
}

// ── Per-rule rendering (ported from nibli-protocol) ──

/// Unicode icon for a proof rule type.
pub fn icon(rule: &ProofRule) -> &'static str {
    match rule {
        ProofRule::Conjunction => "∧",
        ProofRule::DisjunctionCheck { .. } | ProofRule::DisjunctionIntro { .. } => "∨",
        ProofRule::Negation => "¬",
        ProofRule::ModalPassthrough { .. } => "◷",
        ProofRule::ExistsWitness { .. } | ProofRule::ExistsFailed => "∃",
        ProofRule::ForallVacuous
        | ProofRule::ForallVerified { .. }
        | ProofRule::ForallCounterexample { .. } => "∀",
        ProofRule::CountResult { .. } => "#",
        ProofRule::PredicateCheck { .. } | ProofRule::ComputeCheck { .. } => "⊢",
        ProofRule::Asserted { .. } => "▣",
        ProofRule::Derived { .. } => "⊢",
        ProofRule::Presupposed { .. } => "∃",
        ProofRule::ProofRef { .. } => "↑",
        ProofRule::EqualitySubstitution { .. } => "≡",
        ProofRule::RuleAttemptFailed { .. } => "✗",
        ProofRule::PredicateNotFound { .. } => "?",
    }
}

/// CSS class for color-coding in the UI proof tree.
pub fn css_class(rule: &ProofRule) -> &'static str {
    match rule {
        ProofRule::Asserted { .. } => "proof-asserted",
        ProofRule::Derived { .. } => "proof-derived",
        ProofRule::Presupposed { .. } => "proof-exists",
        ProofRule::ProofRef { .. } => "proof-ref",
        ProofRule::ExistsWitness { .. } | ProofRule::ModalPassthrough { .. } => "proof-exists",
        ProofRule::ExistsFailed | ProofRule::ForallCounterexample { .. } => "proof-failed",
        ProofRule::Negation => "proof-negation",
        ProofRule::PredicateCheck { .. } | ProofRule::ComputeCheck { .. } => "proof-check",
        ProofRule::Conjunction => "proof-conjunction",
        ProofRule::DisjunctionCheck { .. } | ProofRule::DisjunctionIntro { .. } => "proof-derived",
        ProofRule::ForallVacuous | ProofRule::ForallVerified { .. } => "proof-exists",
        ProofRule::CountResult { .. } => "proof-check",
        ProofRule::EqualitySubstitution { .. } => "proof-derived",
        ProofRule::RuleAttemptFailed { .. } | ProofRule::PredicateNotFound { .. } => "proof-failed",
    }
}

fn witness_origin_suffix(origin: WitnessOrigin) -> &'static str {
    match origin {
        WitnessOrigin::KnowledgeBase => "",
        WitnessOrigin::GeneratedWitness => " [generated-witness]",
        WitnessOrigin::ExistentialImport => " [existential-import]",
    }
}

fn one_line_source_label(label: &str) -> String {
    label.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn assertion_sources_suffix(sources: &[AssertionCitation]) -> String {
    if sources.is_empty() {
        return String::new();
    }
    let citations: Vec<String> = sources
        .iter()
        .map(|source| format!("#{} {}", source.id, one_line_source_label(&source.label)))
        .collect();
    format!(" [assertions: {}]", citations.join("; "))
}

fn rule_sources_suffix(sources: &[RuleCitation]) -> String {
    if sources.is_empty() {
        return String::new();
    }
    let citations: Vec<String> = sources
        .iter()
        .map(|source| {
            format!(
                "#{}/{} {}",
                source.assertion_id,
                source.rule_ordinal,
                one_line_source_label(&source.assertion_label)
            )
        })
        .collect();
    format!(" [rule sources: {}]", citations.join("; "))
}

/// Human-readable label describing the proof step (UI component form).
pub fn label(rule: &ProofRule) -> String {
    match rule {
        ProofRule::Conjunction => "Conjunction".to_string(),
        ProofRule::DisjunctionCheck { detail } => format!("Disjunction Check: {detail}"),
        ProofRule::DisjunctionIntro { side } => format!("Disjunction Intro: {side}"),
        ProofRule::Negation => "Negation".to_string(),
        ProofRule::ModalPassthrough { kind } => kind.to_string(),
        ProofRule::ExistsWitness { var, term, origin } => {
            let suffix = witness_origin_suffix(*origin);
            format!("Witness: {} = {}{}", var, term.display(), suffix)
        }
        ProofRule::ExistsFailed => "No witness found".to_string(),
        ProofRule::ForallVacuous => "Vacuously true".to_string(),
        ProofRule::ForallVerified { entities } => {
            let names: Vec<String> = entities
                .iter()
                .map(|binding| {
                    format!(
                        "{}{}",
                        binding.term.display(),
                        witness_origin_suffix(binding.origin)
                    )
                })
                .collect();
            format!("Verified: [{}]", names.join(", "))
        }
        ProofRule::ForallCounterexample { entity } => {
            format!(
                "Counterexample: {}{}",
                entity.term.display(),
                witness_origin_suffix(entity.origin)
            )
        }
        ProofRule::CountResult {
            expected,
            actual,
            existential_imported,
        } => {
            let suffix = if *existential_imported > 0 {
                format!(" ({existential_imported} existential-imported)")
            } else {
                String::new()
            };
            format!("Count: expected {expected}, got {actual}{suffix}")
        }
        ProofRule::PredicateCheck { method, detail } => {
            format!("Predicate ({method}): {}", humanize_fact(detail))
        }
        ProofRule::ComputeCheck { method, detail } => {
            format!("Compute ({method}): {}", humanize_fact(detail))
        }
        ProofRule::Asserted { fact, sources } => format!(
            "Asserted: {}{}",
            humanize_fact(fact),
            assertion_sources_suffix(sources)
        ),
        ProofRule::Derived {
            label,
            fact,
            sources,
        } => {
            format!(
                "Derived ({}): {}{}",
                humanize_rule_label(label),
                humanize_fact(fact),
                rule_sources_suffix(sources)
            )
        }
        ProofRule::Presupposed {
            label,
            fact,
            sources,
        } => format!(
            "Presupposed (legacy existential import; {}): {}{}",
            humanize_rule_label(label),
            humanize_fact(fact),
            rule_sources_suffix(sources)
        ),
        ProofRule::ProofRef { fact } => format!("(proved above): {}", humanize_fact(fact)),
        ProofRule::EqualitySubstitution {
            original,
            equality_facts,
            substituted,
        } => format!(
            "Equality: {} via {} → {}",
            humanize_fact(original),
            equality_facts,
            humanize_fact(substituted)
        ),
        ProofRule::RuleAttemptFailed {
            rule_label,
            failed_condition,
        } => format!(
            "Rule failed ({}): condition {} not satisfied",
            humanize_rule_label(rule_label),
            humanize_fact(failed_condition)
        ),
        ProofRule::PredicateNotFound { predicate } => {
            format!("Not found: {}", not_found_text(predicate))
        }
    }
}

/// Compact textual rendering used in CLI proof traces (`… -> TRUE`).
pub fn trace_display(rule: &ProofRule, result: bool) -> String {
    let tag = if result { "TRUE" } else { "FALSE" };
    match rule {
        ProofRule::Conjunction => format!("Conjunction -> {tag}"),
        ProofRule::DisjunctionCheck { detail } => format!("Disjunction (check: {detail}) -> {tag}"),
        ProofRule::DisjunctionIntro { side } => format!("Disjunction ({side}) -> {tag}"),
        ProofRule::Negation => {
            if result {
                format!("Negation [NAF] -> {tag}")
            } else {
                format!("Negation -> {tag}")
            }
        }
        ProofRule::ModalPassthrough { kind } => format!("Modal ({kind}) -> {tag}"),
        ProofRule::ExistsWitness { var, term, origin } => {
            let suffix = witness_origin_suffix(*origin);
            format!(
                "Exists: {} = {}{} -> {}",
                var,
                term.trace_display(),
                suffix,
                tag
            )
        }
        ProofRule::ExistsFailed => format!("Exists: no witness -> {tag}"),
        ProofRule::ForallVacuous => format!("ForAll: vacuous (empty domain) -> {tag}"),
        ProofRule::ForallVerified { entities } => {
            let names: Vec<String> = entities
                .iter()
                .map(|binding| {
                    format!(
                        "{}{}",
                        binding.term.trace_display(),
                        witness_origin_suffix(binding.origin)
                    )
                })
                .collect();
            format!("ForAll: verified [{}] -> {}", names.join(", "), tag)
        }
        ProofRule::ForallCounterexample { entity } => {
            format!(
                "ForAll: counterexample {}{} -> {}",
                entity.term.trace_display(),
                witness_origin_suffix(entity.origin),
                tag
            )
        }
        ProofRule::CountResult {
            expected,
            actual,
            existential_imported,
        } => {
            format!(
                "Count: expected={expected}, actual={actual}, existential_imported={existential_imported} -> {tag}"
            )
        }
        ProofRule::PredicateCheck { method, detail } => {
            format!("{}: {} -> {}", method, humanize_fact(detail), tag)
        }
        ProofRule::ComputeCheck { method, detail } => {
            format!("Compute ({}): {} -> {}", method, humanize_fact(detail), tag)
        }
        ProofRule::Asserted { fact, sources } => format!(
            "Fact: {}{} -> {}",
            humanize_fact(fact),
            assertion_sources_suffix(sources),
            tag
        ),
        ProofRule::Derived {
            label,
            fact,
            sources,
        } => {
            format!(
                "Rule ({}): {}{} -> {}",
                humanize_rule_label(label),
                humanize_fact(fact),
                rule_sources_suffix(sources),
                tag
            )
        }
        ProofRule::Presupposed {
            label,
            fact,
            sources,
        } => format!(
            "Presupposition (legacy existential import; {}): {}{} -> {}",
            humanize_rule_label(label),
            humanize_fact(fact),
            rule_sources_suffix(sources),
            tag
        ),
        ProofRule::ProofRef { fact } => format!("(see above): {} -> {}", humanize_fact(fact), tag),
        ProofRule::EqualitySubstitution {
            original,
            equality_facts,
            substituted,
        } => format!(
            "Equality: {} via {} → {} -> {}",
            humanize_fact(original),
            equality_facts,
            humanize_fact(substituted),
            tag
        ),
        ProofRule::RuleAttemptFailed {
            rule_label,
            failed_condition,
        } => format!(
            "Rule failed ({}): {} not satisfied -> {}",
            humanize_rule_label(rule_label),
            humanize_fact(failed_condition),
            tag
        ),
        ProofRule::PredicateNotFound { predicate } => {
            format!("Not found: {} -> {}", not_found_text(predicate), tag)
        }
    }
}

// ── Rule-label humanization (ported verbatim) ──

/// Collapse event decomposition predicates in a rule label.
/// "dog ∧ gerku_x1 ∧ gerku_x2 → animal ∧ danlu_x1 ∧ danlu_x2" → "dog → animal".
pub(crate) fn humanize_rule_label(label: &str) -> String {
    crate::abstraction::fold_markers(&collapse_rule_roles(label))
}

/// The rule label with its role predicates collapsed to their relations (`dog ∧ dog_x1` is
/// `dog`), markers kept: the form the English reading decodes.
pub(crate) fn collapse_rule_roles(label: &str) -> String {
    if let Some((lhs, rhs)) = label.split_once(" → ") {
        format!(
            "{} → {}",
            collapse_role_predicates(lhs),
            collapse_role_predicates(rhs)
        )
    } else {
        label.to_string()
    }
}

/// Given "dog ∧ gerku_x1 ∧ gerku_x2", return just "dog".
fn collapse_role_predicates(s: &str) -> String {
    let parts: Vec<&str> = s.split(" ∧ ").collect();
    let bases: Vec<&str> = parts
        .iter()
        .filter(|p| !p.contains("_x"))
        .copied()
        .collect();
    if bases.is_empty() {
        if let Some(first) = parts.first()
            && let Some(underscore) = first.rfind('_')
        {
            return first[..underscore].to_string();
        }
        s.to_string()
    } else {
        bases.join(" ∧ ")
    }
}

// Term rendering (`display` / `trace_display`) lives as inherent methods on the
// canonical `LogicalTerm` enum (re-exported via `nibli_protocol`); the per-rule
// renderers above call them directly.

/// A missing predicate as English when the frames can phrase it, else its functional form.
fn not_found_text(predicate: &str) -> String {
    crate::summary::fact_to_english(predicate, crate::Register::Spec)
        .unwrap_or_else(|| humanize_fact(predicate))
}

#[cfg(test)]
mod tests {
    use super::*;
    use nibli_protocol::ProofStep;

    fn trace(rule: ProofRule, holds: bool) -> ProofTrace {
        ProofTrace {
            steps: vec![ProofStep {
                rule,
                holds,
                children: vec![],
            }],
            root: 0,
            naf_dependent: false,
            cwa_false: false,
        }
    }

    #[test]
    fn asserted_flat_fact_renders_args() {
        // The bug this whole change fixes: args must survive.
        let t = trace(
            ProofRule::Asserted {
                fact: "dog_x1(sk_2, adam)".to_string(),
                sources: vec![],
            },
            true,
        );
        assert_eq!(
            render_proof_text(&t, Register::Spec),
            "Fact: dog.dog(adam) -> TRUE\n"
        );
    }

    #[test]
    fn rendered_node_carries_metadata() {
        let t = trace(
            ProofRule::Derived {
                label: "dog ∧ gerku_x1 → animal ∧ danlu_x1".to_string(),
                fact: "animal(adam)".to_string(),
                sources: vec![],
            },
            true,
        );
        let node = render_proof(&t, Register::Spec);
        assert_eq!(node.icon, "⊢");
        assert_eq!(node.css_class, "proof-derived");
        assert!(node.holds);
        assert!(node.is_leaf);
        assert_eq!(node.label, "Derived (dog → animal): animal(adam)");
    }

    #[test]
    fn naf_note_prefixes_text() {
        let mut t = trace(ProofRule::Negation, true);
        t.naf_dependent = true;
        let out = render_proof_text(&t, Register::Spec);
        assert!(out.starts_with("[Note: result depends on negation-as-failure"));
        assert!(out.contains("Negation [NAF] -> TRUE"));
    }

    #[test]
    fn generated_witness_origin_is_visible_in_both_renderers() {
        let rule = ProofRule::ExistsWitness {
            var: "$x".to_string(),
            term: LogicalTerm::Constant("sk_0".to_string()),
            origin: WitnessOrigin::GeneratedWitness,
        };
        assert_eq!(label(&rule), "Witness: $x = sk_0 [generated-witness]");
        assert_eq!(
            trace_display(&rule, true),
            "Exists: $x = sk_0 [generated-witness] -> TRUE"
        );
    }

    #[test]
    fn assertion_citations_are_visible_and_keep_duplicates_distinct() {
        let rule = ProofRule::Asserted {
            fact: "animal(adam)".to_string(),
            sources: vec![
                AssertionCitation {
                    id: 3,
                    label: "animal(Adam).".to_string(),
                },
                AssertionCitation {
                    id: 8,
                    label: "animal(Adam).".to_string(),
                },
            ],
        };
        let rendered = label(&rule);
        assert!(rendered.contains("#3 animal(Adam)."), "{rendered}");
        assert!(rendered.contains("#8 animal(Adam)."), "{rendered}");
    }

    #[test]
    fn presupposed_fact_is_never_rendered_as_asserted() {
        let rule = ProofRule::Presupposed {
            label: "dog → animal".to_string(),
            fact: "dog(sk_import_0)".to_string(),
            sources: vec![RuleCitation {
                assertion_id: 11,
                rule_ordinal: 2,
                assertion_label: "Every dog is an animal.".to_string(),
            }],
        };
        let rendered = label(&rule);
        assert!(rendered.starts_with("Presupposed (legacy existential import;"));
        assert!(rendered.contains("#11/2 Every dog is an animal."));
        assert!(!rendered.contains("Asserted:"));
        assert!(trace_display(&rule, true).starts_with("Presupposition "));
    }
}
