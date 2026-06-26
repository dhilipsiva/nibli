//! Macro-logical DAG collapse: a render-only transform from the verbose
//! Neo-Davidsonian [`ProofTrace`] into a compressed [`RenderedNode`] tree of
//! surface-level inference steps ("adam is an animal — by the rule: every dog is
//! an animal — └ adam is a dog (given)"), with the low-level role/event
//! scaffolding folded into expandable `proof-role-detail` clusters.
//!
//! DRY by construction: it emits the SAME [`RenderedNode`] the verbose renderer
//! and the Dioxus UI already consume (so the UI reuses `RenderedNodeView`
//! unchanged and only a tiny [`render_node_text`] is added for the text
//! surfaces), and it reuses the `[Why]`-summary regroup + English helpers
//! ([`regroup_event_leaves`], [`render_group`], [`rule_to_english`]) — one place
//! that turns role predicates back into surface facts.
//!
//! The transform is TOTAL: anything it cannot cleanly collapse degrades to the
//! verbose [`build_node`] rendering. It never panics and never fabricates
//! English (an un-renderable surface falls back to the functional form).

use std::collections::BTreeMap;

use nibli_protocol::{ProofRule, ProofTrace};

use crate::fact::humanize_fact;
use crate::proof::{RenderedNode, build_node, humanize_rule_label};
use crate::register::Register;
use crate::summary::{
    LeafKey, fact_to_english, parse_raw_fact, regroup_event_leaves, render_group, rule_to_english,
};
use crate::term::{is_event_skolem_arg, role_base, role_index};

/// Recursion backstop (proofs are depth-limited at ~10; this only guards a
/// malformed trace from unbounded recursion).
const MAX_DEPTH: usize = 64;

/// Collapse a verbose proof trace into a macro-logical DAG (a [`RenderedNode`]
/// tree). Render-only; the trace is unchanged.
pub fn collapse_proof(trace: &ProofTrace, register: Register) -> RenderedNode {
    if trace.steps.is_empty() {
        return build_node(trace, trace.root);
    }
    let mut seen: Vec<String> = Vec::new();
    let leaves = collect_goal_leaves(trace, trace.root, 0);
    let mut nodes = collapse_goals(trace, &leaves, register, &mut seen, 0);
    match nodes.len() {
        1 => nodes.pop().unwrap(),
        0 => build_node(trace, trace.root),
        _ => {
            let holds = nodes.iter().all(|n| n.holds);
            RenderedNode {
                icon: "∧",
                label: "all of the following hold".to_string(),
                css_class: "proof-conjunction",
                holds,
                is_leaf: false,
                inline: false,
                children: nodes,
            }
        }
    }
}

/// Render any [`RenderedNode`] tree as indented text (the collapsed view for the
/// REPL / book). With `include_detail = false`, `proof-role-detail` clusters are
/// skipped (the clean macro view); with `true`, they render too.
pub fn render_node_text(node: &RenderedNode, base_indent: usize, include_detail: bool) -> String {
    let mut out = String::new();
    write_node_text(node, base_indent, include_detail, &mut out);
    out
}

fn write_node_text(node: &RenderedNode, indent: usize, include_detail: bool, out: &mut String) {
    if !include_detail && node.css_class == "proof-role-detail" {
        return;
    }
    for _ in 0..indent {
        out.push_str("  ");
    }
    if node.inline {
        out.push_str(&format!("{} {}\n", node.icon, node.label));
    } else {
        let tag = if node.holds { "TRUE" } else { "FALSE" };
        out.push_str(&format!("{} {} -> {}\n", node.icon, node.label, tag));
    }
    for child in &node.children {
        write_node_text(child, indent + 1, include_detail, out);
    }
}

// ── the collapse recursion ──

/// Descend the event-decomposition scaffolding (`ExistsWitness` / `Conjunction`
/// / `ModalPassthrough`) to the role-goal leaves; everything else is a leaf.
fn collect_goal_leaves(trace: &ProofTrace, idx: u32, depth: usize) -> Vec<u32> {
    if depth > MAX_DEPTH {
        return vec![idx];
    }
    match trace.steps.get(idx as usize).map(|s| &s.rule) {
        Some(
            ProofRule::ExistsWitness { .. }
            | ProofRule::Conjunction
            | ProofRule::ModalPassthrough { .. },
        ) => {
            let mut out = Vec::new();
            for &c in &trace.steps[idx as usize].children {
                out.extend(collect_goal_leaves(trace, c, depth + 1));
            }
            out
        }
        _ => vec![idx],
    }
}

/// Group goal leaves by event into surface-fact macro nodes (one node per
/// distinct surface fact, first-seen order).
fn collapse_goals(
    trace: &ProofTrace,
    goals: &[u32],
    register: Register,
    seen: &mut Vec<String>,
    depth: usize,
) -> Vec<RenderedNode> {
    if depth > MAX_DEPTH {
        return goals.iter().map(|&g| build_node(trace, g)).collect();
    }
    let mut order: Vec<LeafKey> = Vec::new();
    let mut buckets: BTreeMap<LeafKey, Vec<u32>> = BTreeMap::new();
    let mut singles: Vec<u32> = Vec::new();
    for &g in goals {
        if let Some(key) = goal_event_key(trace, g) {
            if !buckets.contains_key(&key) {
                order.push(key.clone());
            }
            buckets.entry(key).or_default().push(g);
        } else {
            singles.push(g);
        }
    }
    let mut out = Vec::new();
    for key in &order {
        out.push(build_macro_node(
            trace,
            &buckets[key],
            register,
            seen,
            depth,
        ));
    }
    for &g in &singles {
        out.push(build_single_node(trace, g, register, seen, depth));
    }
    out
}

/// The (wrapper, base, event) key of a role/event-type goal, or `None` for a
/// flat / non-event goal (handled as a single).
fn goal_event_key(trace: &ProofTrace, g: u32) -> Option<LeafKey> {
    let rule = &trace.steps.get(g as usize)?.rule;
    let fact = goal_fact(rule)?;
    let (wrapper, relation, args) = parse_raw_fact(&fact)?;
    if let (Some(base), Some(_)) = (role_base(&relation), role_index(&relation))
        && args.len() >= 2
        && is_event_skolem_arg(&args[0])
    {
        return Some((wrapper, base.to_string(), args[0].clone()));
    }
    if args.len() == 1 && is_event_skolem_arg(&args[0]) {
        return Some((wrapper, relation, args[0].clone()));
    }
    None
}

/// The surface fact string a goal step is about, if any.
fn goal_fact(rule: &ProofRule) -> Option<String> {
    match rule {
        ProofRule::Asserted { fact }
        | ProofRule::Derived { fact, .. }
        | ProofRule::ProofRef { fact } => Some(fact.clone()),
        ProofRule::PredicateCheck { detail, .. } | ProofRule::ComputeCheck { detail, .. } => {
            Some(detail.clone())
        }
        ProofRule::PredicateNotFound { predicate } => Some(predicate.clone()),
        _ => None,
    }
}

/// How a surface fact was established (drives the macro label + premises).
enum GroupKind {
    Given,
    Derived(String),
    Computed,
    Checked,
    NotDerivable,
    Reference,
}

fn classify_group(trace: &ProofTrace, steps: &[u32]) -> GroupKind {
    let mut derived: Option<String> = None;
    let (mut given, mut computed, mut checked, mut notfound, mut nonref) =
        (false, false, false, false, false);
    for &g in steps {
        match &trace.steps[g as usize].rule {
            ProofRule::Derived { label, .. } => {
                derived = Some(label.clone());
                nonref = true;
            }
            ProofRule::Asserted { .. } => {
                given = true;
                nonref = true;
            }
            ProofRule::ComputeCheck { .. } => {
                computed = true;
                nonref = true;
            }
            ProofRule::PredicateCheck { .. } => {
                checked = true;
                nonref = true;
            }
            ProofRule::PredicateNotFound { .. }
            | ProofRule::RuleAttemptFailed { .. }
            | ProofRule::ExistsFailed => {
                notfound = true;
                nonref = true;
            }
            ProofRule::ProofRef { .. } => {}
            _ => nonref = true,
        }
    }
    if let Some(l) = derived {
        GroupKind::Derived(l)
    } else if given {
        GroupKind::Given
    } else if computed {
        GroupKind::Computed
    } else if checked {
        GroupKind::Checked
    } else if notfound {
        GroupKind::NotDerivable
    } else if !nonref {
        GroupKind::Reference
    } else {
        GroupKind::Given
    }
}

/// Build the macro node for one surface fact (a bucket of its role goals).
fn build_macro_node(
    trace: &ProofTrace,
    steps: &[u32],
    register: Register,
    seen: &mut Vec<String>,
    depth: usize,
) -> RenderedNode {
    let facts: Vec<String> = steps
        .iter()
        .filter_map(|&g| goal_fact(&trace.steps[g as usize].rule))
        .collect();
    let holds = steps.iter().all(|&g| trace.steps[g as usize].holds);
    let Some(statement) = surface_statement(&facts, register) else {
        return verbose_group(trace, steps, holds); // degrade, never fabricate
    };
    if seen.contains(&statement) {
        return reference_node(statement);
    }
    seen.push(statement.clone());

    match classify_group(trace, steps) {
        GroupKind::Reference => reference_node(statement),
        GroupKind::NotDerivable => macro_leaf(
            &statement,
            "not derivable",
            "✗",
            "proof-failed",
            false,
            role_detail(trace, steps),
        ),
        GroupKind::Given => macro_leaf(
            &statement,
            "given",
            "▣",
            "proof-asserted",
            holds,
            role_detail(trace, steps),
        ),
        GroupKind::Computed => macro_leaf(
            &statement,
            "computed",
            "⊢",
            "proof-check",
            holds,
            role_detail(trace, steps),
        ),
        GroupKind::Checked => macro_leaf(
            &statement,
            "checked",
            "⊢",
            "proof-check",
            holds,
            role_detail(trace, steps),
        ),
        GroupKind::Derived(label) => {
            let just = rule_justification(&label);
            let mut cond_leaves: Vec<u32> = Vec::new();
            for &g in steps {
                if matches!(trace.steps[g as usize].rule, ProofRule::Derived { .. }) {
                    for &c in &trace.steps[g as usize].children {
                        cond_leaves.extend(collect_goal_leaves(trace, c, depth + 1));
                    }
                }
            }
            let mut children = collapse_goals(trace, &cond_leaves, register, seen, depth + 1);
            if let Some(rd) = role_detail(trace, steps) {
                children.push(rd);
            }
            RenderedNode {
                icon: "⊢",
                label: format!("{statement}  [{just}]"),
                css_class: "proof-derived",
                holds,
                is_leaf: children.is_empty(),
                inline: false,
                children,
            }
        }
    }
}

/// Build a node for a non-event ("flat") goal (a directly-asserted flat fact, a
/// not-found leaf, a compute check, …). Degrades to [`build_node`] for anything
/// it cannot phrase.
fn build_single_node(
    trace: &ProofTrace,
    g: u32,
    register: Register,
    seen: &mut Vec<String>,
    depth: usize,
) -> RenderedNode {
    let rule = &trace.steps[g as usize].rule;
    let holds = trace.steps[g as usize].holds;
    match rule {
        ProofRule::Asserted { fact } => {
            let stmt = flat_statement(fact, register);
            if seen.contains(&stmt) {
                return reference_node(stmt);
            }
            seen.push(stmt.clone());
            macro_leaf(&stmt, "given", "▣", "proof-asserted", holds, None)
        }
        ProofRule::ProofRef { fact } => reference_node(flat_statement(fact, register)),
        ProofRule::PredicateNotFound { predicate } => macro_leaf(
            &flat_statement(predicate, register),
            "not derivable",
            "✗",
            "proof-failed",
            false,
            None,
        ),
        ProofRule::ComputeCheck { detail, .. } => macro_leaf(
            &flat_statement(detail, register),
            "computed",
            "⊢",
            "proof-check",
            holds,
            None,
        ),
        ProofRule::PredicateCheck { detail, .. } => macro_leaf(
            &flat_statement(detail, register),
            "checked",
            "⊢",
            "proof-check",
            holds,
            None,
        ),
        ProofRule::Derived { label, fact } => {
            let stmt = flat_statement(fact, register);
            if seen.contains(&stmt) {
                return reference_node(stmt);
            }
            seen.push(stmt.clone());
            let just = rule_justification(label);
            let mut cond_leaves: Vec<u32> = Vec::new();
            for &c in &trace.steps[g as usize].children {
                cond_leaves.extend(collect_goal_leaves(trace, c, depth + 1));
            }
            let children = collapse_goals(trace, &cond_leaves, register, seen, depth + 1);
            RenderedNode {
                icon: "⊢",
                label: format!("{stmt}  [{just}]"),
                css_class: "proof-derived",
                holds,
                is_leaf: children.is_empty(),
                inline: false,
                children,
            }
        }
        // Negation / ForallCounterexample / CountResult / … : keep the honest
        // functional rendering rather than invent English.
        _ => build_node(trace, g),
    }
}

// ── helpers ──

/// Regroup an event's role facts back to one surface English clause.
fn surface_statement(facts: &[String], register: Register) -> Option<String> {
    let (groups, flat) = regroup_event_leaves(facts, register);
    if let Some((key, pm)) = groups.first() {
        render_group(key.0.as_deref(), &key.1, pm)
    } else {
        flat.first().cloned()
    }
}

/// A flat (non-event) fact rendered to English, falling back to the functional
/// `relation(args)` form.
fn flat_statement(fact: &str, register: Register) -> String {
    fact_to_english(fact, register).unwrap_or_else(|| humanize_fact(fact))
}

/// "by the rule: every dog is an animal" (or the functional label when the rule
/// has no clean English form, e.g. an abstraction conclusion).
fn rule_justification(label: &str) -> String {
    let humanized = humanize_rule_label(label);
    match rule_to_english(&humanized) {
        Some(e) => format!("by the rule: {e}"),
        None => format!("by rule: {humanized}"),
    }
}

fn macro_leaf(
    statement: &str,
    just: &str,
    icon: &'static str,
    css_class: &'static str,
    holds: bool,
    detail: Option<RenderedNode>,
) -> RenderedNode {
    let mut children = Vec::new();
    if let Some(d) = detail {
        children.push(d);
    }
    RenderedNode {
        icon,
        label: format!("{statement}  [{just}]"),
        css_class,
        holds,
        is_leaf: children.is_empty(),
        inline: false,
        children,
    }
}

fn reference_node(statement: String) -> RenderedNode {
    RenderedNode {
        icon: "↑",
        label: format!("{statement}  (shown above)"),
        css_class: "proof-ref",
        holds: true,
        is_leaf: true,
        inline: true,
        children: Vec::new(),
    }
}

/// The folded low-level scaffolding for a surface fact: a `proof-role-detail`
/// cluster wrapping the verbose per-role sub-trees (an expandable `<details>` in
/// the UI; skipped in the clean collapsed text). Only emitted when role
/// decomposition actually happened (more than one role step).
fn role_detail(trace: &ProofTrace, steps: &[u32]) -> Option<RenderedNode> {
    if steps.len() <= 1 {
        return None;
    }
    let children: Vec<RenderedNode> = steps.iter().map(|&g| build_node(trace, g)).collect();
    Some(RenderedNode {
        icon: "▸",
        label: "role-level detail".to_string(),
        css_class: "proof-role-detail",
        holds: true,
        is_leaf: false,
        inline: false,
        children,
    })
}

/// Last-resort degradation: keep the verbose sub-tree(s) for a group we cannot
/// phrase as a surface clause.
fn verbose_group(trace: &ProofTrace, steps: &[u32], holds: bool) -> RenderedNode {
    if steps.len() == 1 {
        return build_node(trace, steps[0]);
    }
    RenderedNode {
        icon: "∧",
        label: "(detail)".to_string(),
        css_class: "proof-conjunction",
        holds,
        is_leaf: false,
        inline: false,
        children: steps.iter().map(|&g| build_node(trace, g)).collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nibli_protocol::ProofStep;

    fn step(rule: ProofRule, holds: bool, children: Vec<u32>) -> ProofStep {
        ProofStep {
            rule,
            holds,
            children,
        }
    }

    fn asserted(fact: &str) -> ProofRule {
        ProofRule::Asserted {
            fact: fact.to_string(),
        }
    }

    fn proofref(fact: &str) -> ProofRule {
        ProofRule::ProofRef {
            fact: fact.to_string(),
        }
    }

    fn derived(fact: &str) -> ProofRule {
        ProofRule::Derived {
            label: "gerku ∧ gerku_x1 ∧ gerku_x2 → danlu ∧ danlu_x1 ∧ danlu_x2".to_string(),
            fact: fact.to_string(),
        }
    }

    /// The exact ~15-step shape gasnu captures for `? la .adam. cu danlu` over
    /// `gerku(adam)` + `ro lo gerku cu danlu`: an ExistsWitness over a left-leaning
    /// Conjunction spine of three per-role `Derived(danlu*)` steps, each re-tracing
    /// the same `gerku*` conditions (deduped to ProofRefs after the first). The
    /// asserted dog event is a BARE Skolem (`sk_2`); the derived animal event is a
    /// DEPENDENT Skolem (`sk_3(adam)`) — a universal rule's conclusion event
    /// depends on the quantified individual, exactly as the engine emits.
    fn syllogism_trace() -> ProofTrace {
        ProofTrace {
            steps: vec![
                step(asserted("gerku(sk_2)"), true, vec![]),          // 0
                step(asserted("gerku_x1(sk_2, adam)"), true, vec![]), // 1
                step(asserted("gerku_x2(sk_2, zo'e)"), true, vec![]), // 2
                step(derived("danlu(sk_3(adam))"), true, vec![0, 1, 2]), // 3
                step(proofref("gerku(sk_2)"), true, vec![]),          // 4
                step(proofref("gerku_x1(sk_2, adam)"), true, vec![]), // 5
                step(proofref("gerku_x2(sk_2, zo'e)"), true, vec![]), // 6
                step(derived("danlu_x1(sk_3(adam), adam)"), true, vec![4, 5, 6]), // 7
                step(proofref("gerku(sk_2)"), true, vec![]),          // 8
                step(proofref("gerku_x1(sk_2, adam)"), true, vec![]), // 9
                step(proofref("gerku_x2(sk_2, zo'e)"), true, vec![]), // 10
                step(derived("danlu_x2(sk_3(adam), zo'e)"), true, vec![8, 9, 10]), // 11
                step(ProofRule::Conjunction, true, vec![3, 7]),       // 12
                step(ProofRule::Conjunction, true, vec![12, 11]),     // 13
                step(
                    ProofRule::ExistsWitness {
                        var: "_ev0".to_string(),
                        term: nibli_protocol::LogicalTerm::Constant("sk_3(adam)".to_string()),
                    },
                    true,
                    vec![13],
                ), // 14
            ],
            root: 14,
            naf_dependent: false,
        }
    }

    #[test]
    fn syllogism_collapses_to_conclusion_then_one_given_premise() {
        let trace = syllogism_trace();
        let node = collapse_proof(&trace, Register::Spec);
        // The conclusion is the macro root: a Derived (rule) step.
        assert_eq!(node.css_class, "proof-derived");
        assert!(node.holds);
        assert!(node.label.contains("animal"), "label: {}", node.label);
        assert!(
            node.label.contains("by the rule") && node.label.contains("dog"),
            "label: {}",
            node.label
        );
        // Exactly ONE surface premise (the 3 gerku facts + their 6 ProofRef
        // repeats collapse to a single "is a dog" given), plus the role-detail
        // cluster.
        let premises: Vec<&RenderedNode> = node
            .children
            .iter()
            .filter(|c| c.css_class != "proof-role-detail")
            .collect();
        assert_eq!(premises.len(), 1, "premises: {:?}", node.children);
        assert!(premises[0].label.contains("dog"));
        assert!(premises[0].label.contains("given"));
    }

    #[test]
    fn syllogism_text_is_clean_two_lines() {
        let trace = syllogism_trace();
        let node = collapse_proof(&trace, Register::Spec);
        let text = render_node_text(&node, 0, false);
        // No role-level scaffolding leaks into the clean text view.
        assert!(!text.contains("role-level detail"), "text:\n{text}");
        assert!(!text.contains("gerku.x1"), "text:\n{text}");
        assert!(!text.contains("Conjunction"), "text:\n{text}");
        assert!(!text.contains("(see above)"), "text:\n{text}");
        // Two macro lines: the conclusion, then the given premise.
        assert!(text.contains("animal"), "text:\n{text}");
        assert!(text.contains("by the rule"), "text:\n{text}");
        assert!(text.contains("dog"), "text:\n{text}");
        assert!(text.contains("given"), "text:\n{text}");
        assert_eq!(text.lines().count(), 2, "text:\n{text}");
    }

    #[test]
    fn role_detail_is_present_but_only_shown_with_include_detail() {
        let trace = syllogism_trace();
        let node = collapse_proof(&trace, Register::Spec);
        // The cluster exists on the node (UI expandable).
        assert!(
            node.children
                .iter()
                .any(|c| c.css_class == "proof-role-detail"),
            "no role-detail cluster: {:?}",
            node.children
        );
        // …and shows up only when detail is requested.
        let with = render_node_text(&node, 0, true);
        assert!(with.contains("role-level detail"), "with:\n{with}");
        // The verbose role predicates surface under the cluster.
        assert!(
            with.contains("danlu") || with.contains("gerku"),
            "with:\n{with}"
        );
    }

    #[test]
    fn false_query_is_not_derivable() {
        let trace = ProofTrace {
            steps: vec![step(
                ProofRule::PredicateNotFound {
                    predicate: "danlu(adam)".to_string(),
                },
                false,
                vec![],
            )],
            root: 0,
            naf_dependent: false,
        };
        let node = collapse_proof(&trace, Register::Spec);
        assert!(!node.holds);
        assert_eq!(node.css_class, "proof-failed");
        assert!(
            node.label.contains("not derivable"),
            "label: {}",
            node.label
        );
        assert!(node.label.contains("animal"), "label: {}", node.label);
    }

    #[test]
    fn flat_given_fact_renders() {
        let trace = ProofTrace {
            steps: vec![step(asserted("danlu(adam)"), true, vec![])],
            root: 0,
            naf_dependent: false,
        };
        let node = collapse_proof(&trace, Register::Spec);
        assert_eq!(node.css_class, "proof-asserted");
        assert!(node.label.contains("given"), "label: {}", node.label);
        assert!(node.label.contains("animal"), "label: {}", node.label);
    }

    #[test]
    fn multi_hop_nests_two_rule_steps() {
        // jmive(adam) <- danlu(adam) <- gerku(adam), each a single-role event for
        // a compact fixture. Exercises premise-of-premise recursion.
        let dl = |lhs_base: &str, rhs: &str, fact: &str| ProofRule::Derived {
            label: format!("{lhs_base} ∧ {lhs_base}_x1 → {rhs} ∧ {rhs}_x1"),
            fact: fact.to_string(),
        };
        let trace = ProofTrace {
            steps: vec![
                step(asserted("gerku(sk_1)"), true, vec![]),          // 0
                step(asserted("gerku_x1(sk_1, adam)"), true, vec![]), // 1
                step(ProofRule::Conjunction, true, vec![0, 1]),       // 2
                step(
                    ProofRule::ExistsWitness {
                        var: "_e".into(),
                        term: nibli_protocol::LogicalTerm::Constant("sk_1".into()),
                    },
                    true,
                    vec![2],
                ), // 3 (gerku event)
                step(dl("gerku", "danlu", "danlu(sk_2)"), true, vec![3]), // 4
                step(dl("gerku", "danlu", "danlu_x1(sk_2, adam)"), true, vec![3]), // 5
                step(ProofRule::Conjunction, true, vec![4, 5]),       // 6
                step(
                    ProofRule::ExistsWitness {
                        var: "_e".into(),
                        term: nibli_protocol::LogicalTerm::Constant("sk_2".into()),
                    },
                    true,
                    vec![6],
                ), // 7 (danlu event)
                step(dl("danlu", "jmive", "jmive(sk_3)"), true, vec![7]), // 8
                step(dl("danlu", "jmive", "jmive_x1(sk_3, adam)"), true, vec![7]), // 9
                step(ProofRule::Conjunction, true, vec![8, 9]),       // 10
                step(
                    ProofRule::ExistsWitness {
                        var: "_e".into(),
                        term: nibli_protocol::LogicalTerm::Constant("sk_3".into()),
                    },
                    true,
                    vec![10],
                ), // 11 (jmive event) ROOT
            ],
            root: 11,
            naf_dependent: false,
        };
        let node = collapse_proof(&trace, Register::Spec);
        let text = render_node_text(&node, 0, false);
        // Three nesting levels: jmive <- danlu <- gerku.
        assert_eq!(node.css_class, "proof-derived"); // jmive by rule
        let mid: Vec<&RenderedNode> = node
            .children
            .iter()
            .filter(|c| c.css_class != "proof-role-detail")
            .collect();
        assert_eq!(mid.len(), 1, "text:\n{text}");
        assert_eq!(mid[0].css_class, "proof-derived"); // danlu by rule
        let leaf: Vec<&RenderedNode> = mid[0]
            .children
            .iter()
            .filter(|c| c.css_class != "proof-role-detail")
            .collect();
        assert_eq!(leaf.len(), 1, "text:\n{text}");
        assert_eq!(leaf[0].css_class, "proof-asserted"); // gerku given
        // No verbose scaffolding in the clean text.
        assert!(!text.contains("Conjunction"), "text:\n{text}");
        assert_eq!(text.lines().count(), 3, "text:\n{text}");
    }

    #[test]
    fn degrades_without_panic_on_unrecognized_shape() {
        // A bare Negation root (no event scaffolding) must not panic and must
        // produce SOME node (the honest functional form).
        let trace = ProofTrace {
            steps: vec![step(ProofRule::Negation, true, vec![])],
            root: 0,
            naf_dependent: false,
        };
        let node = collapse_proof(&trace, Register::Spec);
        let _ = render_node_text(&node, 0, false); // no panic
        assert!(!node.label.is_empty());
    }

    #[test]
    fn empty_trace_does_not_panic() {
        let trace = ProofTrace {
            steps: vec![],
            root: 0,
            naf_dependent: false,
        };
        let node = collapse_proof(&trace, Register::Spec);
        let _ = render_node_text(&node, 0, false);
    }
}
