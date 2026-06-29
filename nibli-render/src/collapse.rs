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
use crate::overlay::DomainGloss;
use crate::proof::{CWA_FALSE_NOTE, NAF_NOTE, RenderedNode, build_node, humanize_rule_label};
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
    let mut steps = collapse_to_macrosteps(trace, register);
    match steps.len() {
        1 => step_to_rendered(&steps.pop().unwrap()),
        0 => build_node(trace, trace.root),
        _ => {
            let nodes: Vec<RenderedNode> = steps.iter().map(step_to_rendered).collect();
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

/// One structured step of the collapsed macro-logical derivation: an already
/// INSTANTIATED surface statement (real entities — `varfarin is in danger`), how
/// it was established, and its immediate premises. This is the single source of
/// truth both the [`RenderedNode`] tree ([`step_to_rendered`]) and the
/// plain-English [`crate::summary`] narrative are built from — so the two never
/// drift, and neither has to re-parse the other's display strings.
#[derive(Clone)]
pub(crate) struct MacroStep {
    pub statement: String,
    pub kind: MacroKind,
    pub holds: bool,
    pub premises: Vec<MacroStep>,
    /// Foldable role-level scaffolding cluster (UI-only); carried verbatim.
    pub role_detail: Option<RenderedNode>,
}

/// How a [`MacroStep`]'s surface statement was established.
#[derive(Clone)]
pub(crate) enum MacroKind {
    Given,
    /// Derived by a rule; the string is the (relation-only) rule label.
    Derived(String),
    /// A computed leaf; the string is the `ComputeCheck` source method, so the
    /// rendered label can distinguish a LOCAL computation (built-in arithmetic /
    /// numeric comparison) from a value TRUSTED from the external backend (an
    /// oracle, not a derivation).
    Computed(String),
    Checked,
    NotDerivable,
    /// A back-reference to a statement already shown (deduped).
    Reference,
    /// A shape the collapse could not phrase: keep the verbose rendering verbatim
    /// (never fabricate English). The narrative skips these.
    Raw(Box<RenderedNode>),
}

/// Build the structured macro-step forest for a whole trace (shared by the
/// collapsed tree and the `[Why]` summary).
pub(crate) fn collapse_to_macrosteps(trace: &ProofTrace, register: Register) -> Vec<MacroStep> {
    if trace.steps.is_empty() {
        return Vec::new();
    }
    let mut seen: Vec<String> = Vec::new();
    let leaves = collect_goal_leaves(trace, trace.root, 0);
    collapse_goal_steps(trace, &leaves, register, &mut seen, 0)
}

/// Collapsed-view label for a computed leaf, by its `ComputeCheck` method.
/// Surfaces the honesty distinction: a LOCAL computation (built-in arithmetic
/// `pilji`/`sumji`/`dilcu`, or a `zmadu`/`mleca`/`dunli` numeric comparison) vs a
/// value TRUSTED from the external backend (an axiom from an oracle, not derived).
/// Only a SUCCESSFUL backend reply (`backend`) earns the trusted label — an
/// unavailable backend (`backend_unavailable`) computed nothing, and the edge
/// methods (`indeterminate`/`build_failed`) keep the bare "computed".
fn computed_label(method: &str) -> &'static str {
    match method {
        "backend" => "computed (trusted backend)",
        "arithmetic" | "numeric" => "computed (local)",
        _ => "computed",
    }
}

/// Render a structured [`MacroStep`] to the display [`RenderedNode`] — the
/// labels/icons/classes are byte-for-byte what the old direct builders produced.
fn step_to_rendered(step: &MacroStep) -> RenderedNode {
    match &step.kind {
        MacroKind::Raw(node) => (**node).clone(),
        MacroKind::Reference => reference_node(step.statement.clone()),
        MacroKind::Given => macro_leaf(
            &step.statement,
            "given",
            "▣",
            "proof-asserted",
            step.holds,
            step.role_detail.clone(),
        ),
        MacroKind::Computed(method) => macro_leaf(
            &step.statement,
            computed_label(method),
            "⊢",
            "proof-check",
            step.holds,
            step.role_detail.clone(),
        ),
        MacroKind::Checked => macro_leaf(
            &step.statement,
            "checked",
            "⊢",
            "proof-check",
            step.holds,
            step.role_detail.clone(),
        ),
        MacroKind::NotDerivable => macro_leaf(
            &step.statement,
            "not derivable",
            "✗",
            "proof-failed",
            false,
            step.role_detail.clone(),
        ),
        MacroKind::Derived(label) => {
            let just = rule_justification(label);
            let mut children: Vec<RenderedNode> =
                step.premises.iter().map(step_to_rendered).collect();
            if let Some(rd) = &step.role_detail {
                children.push(rd.clone());
            }
            RenderedNode {
                icon: "⊢",
                label: format!("{}  [{just}]", step.statement),
                css_class: "proof-derived",
                holds: step.holds,
                is_leaf: children.is_empty(),
                inline: false,
                children,
            }
        }
    }
}

/// As [`collapse_proof`], rendering under a domain-gloss `overlay` (`None` = the
/// dictionary-fallback default).
pub fn collapse_proof_with(
    trace: &ProofTrace,
    register: Register,
    overlay: Option<&'static DomainGloss>,
) -> RenderedNode {
    crate::overlay::with_overlay(overlay, || collapse_proof(trace, register))
}

/// The collapsed macro-logical-DAG proof of a whole trace as indented text (the
/// REPL / server / book view): the closed-world NAF caveat (when the verdict
/// rests on it), then the collapsed tree. With `include_detail = false` the
/// role-level clusters are omitted (the clean macro view). One call every text
/// surface shares — gasnu, nibli-server, nibli-wasm.
pub fn render_collapsed_text(
    trace: &ProofTrace,
    register: Register,
    base_indent: usize,
    include_detail: bool,
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
    let node = collapse_proof(trace, register);
    out.push_str(&render_node_text(&node, base_indent, include_detail));
    out
}

/// As [`render_collapsed_text`], rendering under a domain-gloss `overlay`
/// (`None` = the dictionary-fallback default).
pub fn render_collapsed_text_with(
    trace: &ProofTrace,
    register: Register,
    base_indent: usize,
    include_detail: bool,
    overlay: Option<&'static DomainGloss>,
) -> String {
    crate::overlay::with_overlay(overlay, || {
        render_collapsed_text(trace, register, base_indent, include_detail)
    })
}

/// Render any [`RenderedNode`] tree as indented text (the building block of
/// [`render_collapsed_text`]). With `include_detail = false`, `proof-role-detail`
/// clusters are skipped (the clean macro view); with `true`, they render too.
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

/// Group goal leaves by event into surface-fact macro STEPS (one per distinct
/// surface fact, first-seen order).
fn collapse_goal_steps(
    trace: &ProofTrace,
    goals: &[u32],
    register: Register,
    seen: &mut Vec<String>,
    depth: usize,
) -> Vec<MacroStep> {
    if depth > MAX_DEPTH {
        return goals
            .iter()
            .map(|&g| raw_step(build_node(trace, g)))
            .collect();
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
        out.push(build_macro_step(
            trace,
            &buckets[key],
            register,
            seen,
            depth,
        ));
    }
    for &g in &singles {
        out.push(build_single_step(trace, g, register, seen, depth));
    }
    out
}

/// A leaf macro-step (no premises).
fn leaf_step(
    statement: String,
    kind: MacroKind,
    holds: bool,
    role_detail: Option<RenderedNode>,
) -> MacroStep {
    MacroStep {
        statement,
        kind,
        holds,
        premises: Vec::new(),
        role_detail,
    }
}

/// Wrap a pre-rendered (un-phraseable) node as an opaque macro-step.
fn raw_step(node: RenderedNode) -> MacroStep {
    let statement = node.label.clone();
    let holds = node.holds;
    MacroStep {
        statement,
        kind: MacroKind::Raw(Box::new(node)),
        holds,
        premises: Vec::new(),
        role_detail: None,
    }
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
    /// String is the `ComputeCheck` source method (see [`computed_label`]).
    Computed(String),
    Checked,
    NotDerivable,
    Reference,
}

fn classify_group(trace: &ProofTrace, steps: &[u32]) -> GroupKind {
    let mut derived: Option<String> = None;
    let mut computed_method: Option<String> = None;
    let (mut given, mut checked, mut notfound, mut nonref) = (false, false, false, false);
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
            ProofRule::ComputeCheck { method, .. } => {
                computed_method = Some(method.clone());
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
    } else if let Some(m) = computed_method {
        GroupKind::Computed(m)
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

/// Build the macro step for one surface fact (a bucket of its role goals).
fn build_macro_step(
    trace: &ProofTrace,
    steps: &[u32],
    register: Register,
    seen: &mut Vec<String>,
    depth: usize,
) -> MacroStep {
    let facts: Vec<String> = steps
        .iter()
        .filter_map(|&g| goal_fact(&trace.steps[g as usize].rule))
        .collect();
    let holds = steps.iter().all(|&g| trace.steps[g as usize].holds);
    let Some(statement) = surface_statement(&facts, register) else {
        return raw_step(verbose_group(trace, steps, holds)); // degrade, never fabricate
    };
    if seen.contains(&statement) {
        return leaf_step(statement, MacroKind::Reference, true, None);
    }
    seen.push(statement.clone());

    match classify_group(trace, steps) {
        GroupKind::Reference => leaf_step(statement, MacroKind::Reference, true, None),
        GroupKind::NotDerivable => leaf_step(
            statement,
            MacroKind::NotDerivable,
            false,
            role_detail(trace, steps),
        ),
        GroupKind::Given => leaf_step(
            statement,
            MacroKind::Given,
            holds,
            role_detail(trace, steps),
        ),
        GroupKind::Computed(method) => leaf_step(
            statement,
            MacroKind::Computed(method),
            holds,
            role_detail(trace, steps),
        ),
        GroupKind::Checked => leaf_step(
            statement,
            MacroKind::Checked,
            holds,
            role_detail(trace, steps),
        ),
        GroupKind::Derived(label) => {
            let mut cond_leaves: Vec<u32> = Vec::new();
            for &g in steps {
                if matches!(trace.steps[g as usize].rule, ProofRule::Derived { .. }) {
                    for &c in &trace.steps[g as usize].children {
                        cond_leaves.extend(collect_goal_leaves(trace, c, depth + 1));
                    }
                }
            }
            let premises = collapse_goal_steps(trace, &cond_leaves, register, seen, depth + 1);
            MacroStep {
                statement,
                kind: MacroKind::Derived(label),
                holds,
                premises,
                role_detail: role_detail(trace, steps),
            }
        }
    }
}

/// Build a step for a non-event ("flat") goal (a directly-asserted flat fact, a
/// not-found leaf, a compute check, …). Degrades to a [`build_node`] raw step for
/// anything it cannot phrase.
fn build_single_step(
    trace: &ProofTrace,
    g: u32,
    register: Register,
    seen: &mut Vec<String>,
    depth: usize,
) -> MacroStep {
    let rule = &trace.steps[g as usize].rule;
    let holds = trace.steps[g as usize].holds;
    match rule {
        ProofRule::Asserted { fact } => {
            let stmt = flat_statement(fact, register);
            if seen.contains(&stmt) {
                return leaf_step(stmt, MacroKind::Reference, true, None);
            }
            seen.push(stmt.clone());
            leaf_step(stmt, MacroKind::Given, holds, None)
        }
        ProofRule::ProofRef { fact } => leaf_step(
            flat_statement(fact, register),
            MacroKind::Reference,
            true,
            None,
        ),
        ProofRule::PredicateNotFound { predicate } => leaf_step(
            flat_statement(predicate, register),
            MacroKind::NotDerivable,
            false,
            None,
        ),
        ProofRule::ComputeCheck { detail, method } => leaf_step(
            flat_statement(detail, register),
            MacroKind::Computed(method.clone()),
            holds,
            None,
        ),
        ProofRule::PredicateCheck { detail, .. } => leaf_step(
            flat_statement(detail, register),
            MacroKind::Checked,
            holds,
            None,
        ),
        ProofRule::Derived { label, fact } => {
            let stmt = flat_statement(fact, register);
            if seen.contains(&stmt) {
                return leaf_step(stmt, MacroKind::Reference, true, None);
            }
            seen.push(stmt.clone());
            let mut cond_leaves: Vec<u32> = Vec::new();
            for &c in &trace.steps[g as usize].children {
                cond_leaves.extend(collect_goal_leaves(trace, c, depth + 1));
            }
            let premises = collapse_goal_steps(trace, &cond_leaves, register, seen, depth + 1);
            MacroStep {
                statement: stmt,
                kind: MacroKind::Derived(label.clone()),
                holds,
                premises,
                role_detail: None,
            }
        }
        // Negation / ForallCounterexample / CountResult / … : keep the honest
        // functional rendering rather than invent English.
        _ => raw_step(build_node(trace, g)),
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
            cwa_false: false,
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
            cwa_false: false,
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
            cwa_false: false,
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
            cwa_false: false,
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
            cwa_false: false,
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
            cwa_false: false,
        };
        let node = collapse_proof(&trace, Register::Spec);
        let _ = render_node_text(&node, 0, false);
    }
}
