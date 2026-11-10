//! Plain-English "Why" summary of a proof trace (render-only).
//!
//! The technical proof trace ([`crate::proof`]) is exhaustive but cryptic — it
//! shows functional notation (`dog.dog(adam)`) and the Neo-Davidsonian
//! decomposition explodes each fact into role-predicate lines. This produces a
//! short, plain-English explanation of WHY a query holds (or fails), reusing the
//! same place-frame machinery as the back-translation: it walks the flat
//! `ProofTrace`, regroups the role predicates back to surface facts, and fills
//! the curated English templates (`dog` -> `"{x1} is a dog"`).
//!
//! Best-effort and total: anything that does not parse or has no frame falls
//! back to the functional [`crate::fact::humanize_fact`] string — it never
//! invents English. The `ProofTrace` data is unchanged; this is pure rendering,
//! layered ABOVE the detailed trace (which stays for experts).

use std::collections::BTreeMap;

use nibli_protocol::{ProofRule, ProofTrace};

use crate::collapse::{MacroKind, MacroStep, collapse_to_macrosteps};
use crate::fact::humanize_fact;
use crate::frame::{fill_template, frame_template, gloss_for};
use crate::overlay::DomainGloss;
use crate::register::Register;
use crate::term::{humanize_skolem, is_event_skolem, is_event_skolem_arg, role_base, role_index};

/// The verdict class driving the `[Why]` sentence. The trace alone cannot
/// distinguish an UNKNOWN or RESOURCE_EXCEEDED query from an ordinary FALSE
/// (its root simply fails to hold), so verdict-bearing surfaces pass the class
/// in via [`summarize_verdict`] — otherwise a resource cutoff reads as the
/// closed-world "could not be derived" sentence, which is false: no verdict
/// about the facts was reached at all.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerdictKind {
    True,
    False,
    /// UNKNOWN, with the engine's reason label when one exists
    /// (`"backend-unavailable"`, `"non-finite"`, `"cycle-cut"`, …).
    Unknown(Option<&'static str>),
    /// RESOURCE_EXCEEDED, with the kind label (`"depth"`, `"fuel"`, `"memory"`).
    ResourceExceeded(Option<&'static str>),
}

/// Map the engine's typed verdict onto a [`VerdictKind`] (native surfaces;
/// the WIT host maps its bindings enum itself).
pub fn verdict_kind(result: &nibli_types::logic::QueryResult) -> VerdictKind {
    use nibli_types::logic::QueryResult as Q;
    match result {
        Q::True => VerdictKind::True,
        Q::False => VerdictKind::False,
        Q::Unknown(_) => VerdictKind::Unknown(result.detail_label()),
        Q::ResourceExceeded(_) => VerdictKind::ResourceExceeded(result.detail_label()),
    }
}

/// Build a one-block plain-English "why" explanation of the trace, or `None` if
/// there is nothing summarizable (callers then print nothing extra).
///
/// Verdict-less compatibility surface: the class is inferred from the root
/// step (`holds` → TRUE, else FALSE). A caller that knows the verdict should
/// use [`summarize_verdict`], which renders UNKNOWN and RESOURCE_EXCEEDED
/// honestly instead of letting them fall into the FALSE arms.
pub fn summarize_proof(trace: &ProofTrace, register: Register) -> Option<String> {
    crate::tables::with_trace_tables(trace, None, || summarize_proof_inner(trace, register))
}

fn summarize_proof_inner(trace: &ProofTrace, register: Register) -> Option<String> {
    let root = trace.steps.get(trace.root as usize)?;
    if root.holds {
        summarize_true(trace, register)
    } else {
        summarize_false(trace, register)
    }
}

/// As [`summarize_proof`], but driven by the VERDICT: a computed FALSE renders
/// as a decision, an UNKNOWN as the reason no verdict exists, and a
/// RESOURCE_EXCEEDED as a budget cutoff — never the closed-world
/// non-derivability sentence, which is only true of ordinary CWA FALSE.
pub fn summarize_verdict(
    kind: &VerdictKind,
    trace: &ProofTrace,
    register: Register,
) -> Option<String> {
    summarize_verdict_with_source(kind, trace, register, None)
}

/// As [`summarize_verdict`], with the query's KR when the caller has it: constants then keep
/// the author's spelling even when no citation in the trace carries them (a FALSE verdict's
/// query, for one). The trace's own citations always contribute.
pub fn summarize_verdict_with_source(
    kind: &VerdictKind,
    trace: &ProofTrace,
    register: Register,
    source: Option<&str>,
) -> Option<String> {
    crate::tables::with_trace_tables(trace, source, || {
        summarize_verdict_inner(kind, trace, register)
    })
}

fn summarize_verdict_inner(
    kind: &VerdictKind,
    trace: &ProofTrace,
    register: Register,
) -> Option<String> {
    match kind {
        VerdictKind::True => {
            trace.steps.get(trace.root as usize)?;
            summarize_true(trace, register)
        }
        VerdictKind::False => {
            trace.steps.get(trace.root as usize)?;
            summarize_false(trace, register)
        }
        VerdictKind::Unknown(reason) => Some(match *reason {
            Some("backend-unavailable") => "No verdict: the external compute backend was \
                 unavailable, so a required computation could not be evaluated."
                .to_string(),
            Some("non-finite") => "No verdict: a computation produced a non-finite value, \
                 so the comparison could not be decided."
                .to_string(),
            Some(r) => format!("No verdict: the search could not decide this ({r})."),
            None => "No verdict: the search could not decide this.".to_string(),
        }),
        VerdictKind::ResourceExceeded(kind) => Some(match *kind {
            Some(k) => format!(
                "No verdict: the search exhausted its {k} budget before reaching a \
                 decision — a resource limit, not a statement about the facts."
            ),
            None => "No verdict: the search exhausted a resource budget before reaching \
                 a decision — a resource limit, not a statement about the facts."
                .to_string(),
        }),
    }
}

/// As [`summarize_proof`], but renders under a domain-gloss `overlay` (curated
/// examples read in real domain terms; `None` = the dictionary-fallback default).
pub fn summarize_proof_with(
    trace: &ProofTrace,
    register: Register,
    overlay: Option<&'static DomainGloss>,
) -> Option<String> {
    crate::overlay::with_overlay(overlay, || summarize_proof(trace, register))
}

/// Translate one humanized/raw fact string to an English clause via the place
/// frames. `None` when it cannot be rendered (caller falls back to functional).
pub fn fact_to_english(raw: &str, _register: Register) -> Option<String> {
    let (wrapper, relation, args) = parse_raw_fact(raw)?;
    let clause = if role_base(&relation).is_some() {
        // A role alone does not establish its base predicate. It might be a
        // modifier sharing a different head's event; keep its exact atom.
        return None;
    } else if args.len() == 1 && is_event_skolem(&args[0]) {
        // An event-type predicate `base(event)` -> existence.
        format!("there is {}", a_noun(&relation))
    } else {
        // A flat fact -> fill the frame with all args directly; an unspecified place (`_`)
        // stays unfilled, so a trailing one is elided and an interior one reads "something".
        let slots: Vec<Option<String>> = args.iter().map(|a| filler_text(a)).collect();
        fill_template(&frame_template(&relation), &slots)
    };
    if clause.trim().is_empty() {
        None
    } else {
        Some(prefix_wrapper(wrapper.as_deref(), clause))
    }
}

fn summarize_true(trace: &ProofTrace, register: Register) -> Option<String> {
    // Narrate the INSTANTIATED derivation the collapse already computes (real
    // entities — `varfarin is in danger` — never a bare `X`): one "<premises>,
    // <conclusion>" clause per derived step, deepest first (a bottom-up reading).
    let steps = collapse_to_macrosteps(trace, register);
    let mut clauses: Vec<String> = Vec::new();
    narrate_steps(&steps, &mut clauses);
    // Compute results + equality substitutions live outside the collapsed tree.
    clauses.extend(collect_extras(trace));
    if clauses.is_empty() {
        // Fallback for a root the collapse cannot phrase as a derivation (e.g. a
        // negation-as-failure root): list direct assertions and explicitly
        // identified legacy-import presuppositions. Never call the latter givens.
        clauses = asserted_givens(trace, register);
        clauses.extend(presupposed_assumptions(trace, register));
    }
    if clauses.is_empty() {
        return None;
    }
    let mut s = format!("Because {}.", join_clauses(&clauses));
    if trace.naf_dependent {
        s.push_str(" (Under the closed-world assumption — nothing known contradicts it.)");
    }
    Some(s)
}

/// Append narrative clauses describing how the proof's derived conclusions follow
/// from their premises (deepest derivation first). A proof with no rule firing —
/// the conclusion is a directly known fact — lists the given statement(s).
fn narrate_steps(steps: &[MacroStep], out: &mut Vec<String>) {
    let mut any_derived = false;
    for s in steps {
        collect_derived_clauses(s, out, &mut any_derived);
    }
    for s in steps {
        // A raw restriction still supports a mixed natural/structural proof.
        // Never omit it just because a neighboring conclusion has good prose.
        if matches!(s.kind, MacroKind::Raw(_))
            || (!any_derived && matches!(s.kind, MacroKind::Given | MacroKind::Presupposed(_)))
        {
            let stmt = narrative_statement(s);
            if !stmt.is_empty() && !out.contains(&stmt) {
                out.push(stmt);
            }
        }
    }
}

/// Depth-first emit: a derived step contributes "<premises>, <conclusion>" after
/// its premises' own derivations (so the chain reads bottom-up).
fn collect_derived_clauses(step: &MacroStep, out: &mut Vec<String>, any_derived: &mut bool) {
    for p in &step.premises {
        collect_derived_clauses(p, out, any_derived);
    }
    if matches!(step.kind, MacroKind::Derived(_)) {
        *any_derived = true;
        let prem: Vec<String> = step
            .premises
            .iter()
            .map(narrative_statement)
            .filter(|s| !s.is_empty())
            .collect();
        let concl = step.statement.trim();
        let clause = if prem.is_empty() {
            concl.to_string()
        } else {
            format!("{}, {concl}", join_and(&prem))
        };
        if !out.contains(&clause) {
            out.push(clause);
        }
    }
}

fn narrative_statement(step: &MacroStep) -> String {
    if let MacroKind::Raw(node) = &step.kind {
        let text = crate::collapse::render_node_text(node, 0, true);
        return format!("structural proof:\n{}", text.trim());
    }
    let statement = step.statement.trim();
    match &step.kind {
        MacroKind::Presupposed(_) => {
            format!("{statement} (presupposed by legacy existential import)")
        }
        _ => statement.to_string(),
    }
}

/// Chain the narrative clauses: `Because <c1>; and because <c2>; …`.
fn join_clauses(items: &[String]) -> String {
    let mut s = String::new();
    for (i, c) in items.iter().enumerate() {
        if i == 0 {
            s.push_str(c);
        } else {
            s.push_str("; and because ");
            s.push_str(c);
        }
    }
    s
}

/// The asserted (given) facts, regrouped from role predicates back to surface
/// facts and translated to English. Distinct, first-seen order. The fallback
/// narrative when the collapse cannot phrase the root as a derivation.
fn asserted_givens(trace: &ProofTrace, register: Register) -> Vec<String> {
    let facts: Vec<String> = trace
        .steps
        .iter()
        .filter_map(|s| match &s.rule {
            ProofRule::Asserted { fact, .. } => Some(fact.clone()),
            _ => None,
        })
        .collect();
    render_origin_facts(&facts, register)
}

/// Legacy existential-import facts, kept separate from direct assertions so a
/// summary can never present a profile-minted witness as a user-provided given.
fn presupposed_assumptions(trace: &ProofTrace, register: Register) -> Vec<String> {
    let facts: Vec<String> = trace
        .steps
        .iter()
        .filter_map(|s| match &s.rule {
            ProofRule::Presupposed { fact, .. } => Some(fact.clone()),
            _ => None,
        })
        .collect();
    render_origin_facts(&facts, register)
        .into_iter()
        .map(|fact| format!("{fact} (presupposed by legacy existential import)"))
        .collect()
}

fn render_origin_facts(facts: &[String], register: Register) -> Vec<String> {
    let (groups, flat) = regroup_event_leaves(facts, register);
    let mut out: Vec<String> = Vec::new();
    for (key, pm) in &groups {
        if let Some(e) = render_group(key.0.as_deref(), &key.1, pm)
            && !out.contains(&e)
        {
            out.push(e);
        }
    }
    for f in flat {
        if !out.contains(&f) {
            out.push(f);
        }
    }
    out
}

fn summarize_false(trace: &ProofTrace, register: Register) -> Option<String> {
    // A FAILING compute check is a DECISION about the values, not closed-world
    // non-derivability — render it first, without the CWA sentence. (The
    // discriminator `trace.cwa_false` agrees: a numeric-decided FALSE carries
    // `cwa_false: false`.)
    for step in &trace.steps {
        if let ProofRule::ComputeCheck { detail, method } = &step.rule
            && !step.holds
        {
            return Some(format!(
                "Decided by computation: {} is false ({}). This is a decision about \
                 the values, not closed-world non-derivability.",
                humanize_fact(detail),
                computed_extra_label(method)
            ));
        }
    }
    for step in &trace.steps {
        match &step.rule {
            ProofRule::PredicateNotFound { predicate } => {
                let what = not_found_event(trace, predicate, register)
                    .or_else(|| fact_to_english(predicate, register))
                    .unwrap_or_else(|| humanize_fact(predicate));
                return Some(format!("Nothing known establishes that {what}."));
            }
            ProofRule::ForallCounterexample { entity } => {
                let origin = match entity.origin {
                    nibli_protocol::WitnessOrigin::KnowledgeBase => String::new(),
                    other => format!(" [{}]", other.label()),
                };
                let shown = entity.term.display();
                return Some(format!(
                    "It is not true for every case — counterexample: {}{}.",
                    crate::spelling::restore(&shown).unwrap_or(shown),
                    origin
                ));
            }
            ProofRule::ExistsFailed => {
                return Some("No example could be found that satisfies the query.".to_string());
            }
            _ => {}
        }
    }
    if trace.cwa_false {
        Some("This could not be derived from the known facts and rules.".to_string())
    } else {
        // A decided FALSE with no compute leaf and no counterexample arm —
        // genuinely false, not an absence of derivation.
        Some("This is false as a decided matter — not closed-world non-derivability.".to_string())
    }
}

/// A place's filler as English, or `None` for the unspecified placeholder `_`.
fn filler_text(arg: &str) -> Option<String> {
    (arg != "_").then(|| humanize_skolem(arg))
}

/// A missing role of an event the trace otherwise describes, read as the whole event with the
/// missing role's filler in its place. Opaque event referents remain structural;
/// only a complete, reachable proof package may substitute their content.
fn not_found_event(trace: &ProofTrace, predicate: &str, register: Register) -> Option<String> {
    let (_, relation, args) = parse_raw_fact(predicate)?;
    let base = role_base(&relation)?;
    role_index(&relation)?;
    if args.len() < 2 || !is_event_skolem_arg(&args[0]) {
        return None;
    }
    let event = &args[0];
    let mut facts: Vec<String> = Vec::new();
    for step in &trace.steps {
        let fact = match &step.rule {
            ProofRule::Asserted { fact, .. }
            | ProofRule::Derived { fact, .. }
            | ProofRule::Presupposed { fact, .. }
            | ProofRule::ProofRef { fact } => fact,
            _ => continue,
        };
        if let Some((_, r, a)) = parse_raw_fact(fact)
            && role_base(&r) == Some(base)
            && a.first() == Some(event)
            && !facts.contains(fact)
        {
            facts.push(fact.clone());
        }
    }
    facts.push(predicate.to_string());
    let (groups, _) = regroup_event_leaves(&facts, register);
    let (key, pm) = groups.first()?;
    render_group(key.0.as_deref(), &key.1, pm)
}

/// Key for an event group: (tense/deontic wrapper, base relation, event Skolem).
pub(crate) type LeafKey = (Option<String>, String, String);

/// One regrouped event: its key + a `{place -> filler}` map.
pub(crate) type EventGroup = (LeafKey, BTreeMap<usize, String>);

/// Regroup raw fact strings (Neo-Davidsonian role + event-type predicates) back
/// to surface facts: bucket `base_xN(event, filler)` / `base(event)` by
/// `(wrapper, base, event Skolem)` into `{place -> filler}` maps (first-seen
/// order), returning non-event "flat" facts (rendered to English directly) on the
/// side. The shared DRY core of the `[Why]` summary and the macro-DAG collapse.
pub(crate) fn regroup_event_leaves(
    facts: &[String],
    register: Register,
) -> (Vec<EventGroup>, Vec<String>) {
    let mut order: Vec<LeafKey> = Vec::new();
    let mut places: BTreeMap<LeafKey, BTreeMap<usize, String>> = BTreeMap::new();
    let mut flat: Vec<String> = Vec::new();

    for fact in facts {
        let Some((wrapper, relation, args)) = parse_raw_fact(fact) else {
            flat.push(humanize_fact(fact));
            continue;
        };
        // Role predicate `base_xN(event, filler)` — the arg0 event may be a bare
        // (`sk_N`) OR a dependent (`sk_N(rex)`, a universal rule's conclusion
        // event) Skolem, hence the loose check.
        if let (Some(base), Some(idx)) = (role_base(&relation), role_index(&relation))
            && args.len() >= 2
            && is_event_skolem_arg(&args[0])
        {
            let key = (wrapper.clone(), base.to_string(), args[0].clone());
            if !places.contains_key(&key) {
                order.push(key.clone());
            }
            let slots = places.entry(key).or_default();
            if let Some(text) = filler_text(&args[1]) {
                slots.insert(idx, text);
            }
            continue;
        }
        // Event-type predicate `base(event)` — registers the group (no place).
        if args.len() == 1 && is_event_skolem_arg(&args[0]) {
            let key = (wrapper.clone(), relation.clone(), args[0].clone());
            if !places.contains_key(&key) {
                order.push(key.clone());
            }
            places.entry(key).or_default();
            continue;
        }
        // A flat fact (no event Skolem) — render directly.
        if let Some(e) = fact_to_english(fact, register) {
            flat.push(e);
        } else {
            flat.push(humanize_fact(fact));
        }
    }

    let groups = order
        .into_iter()
        .map(|k| {
            let pm = places.remove(&k).unwrap_or_default();
            (k, pm)
        })
        .collect();
    (groups, flat)
}

/// Render a regrouped event's place-map via the frame template.
pub(crate) fn render_group(
    wrapper: Option<&str>,
    base: &str,
    place_map: &BTreeMap<usize, String>,
) -> Option<String> {
    let max = *place_map.keys().max()?; // empty (event-type only) -> None, skip
    // Skip a group whose SUBJECT (x1) is an internal witness Skolem (`#N`): these
    // are presupposition / existential witnesses (e.g. the witness an existential
    // query found), not user-given facts — listing them as "(given)" is noise.
    if place_map.get(&1).is_some_and(|s| s.starts_with('#')) {
        return None;
    }
    let mut slots: Vec<Option<String>> = vec![None; max];
    for (&p, filler) in place_map {
        if (1..=max).contains(&p) {
            slots[p - 1] = Some(filler.clone());
        }
    }
    let filled = fill_template(&frame_template(base), &slots);
    if filled.trim().is_empty() {
        None
    } else {
        Some(prefix_wrapper(wrapper, filled))
    }
}

/// `[Why]` supporting-clause phrasing for a computed result, distinguishing a
/// LOCAL computation from a value TRUSTED from the external backend (an oracle,
/// not a derivation) — the same honesty distinction the collapsed proof label makes.
fn computed_extra_label(method: &str) -> &'static str {
    match method {
        "backend" => "computed by the trusted backend",
        "arithmetic" | "numeric" => "computed locally",
        _ => "computed",
    }
}

/// Compute results + equality substitutions, as supporting clauses.
fn collect_extras(trace: &ProofTrace) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for step in &trace.steps {
        let clause = match &step.rule {
            ProofRule::ComputeCheck { detail, method } => {
                format!(
                    "{} ({})",
                    humanize_fact(detail),
                    computed_extra_label(method)
                )
            }
            ProofRule::EqualitySubstitution {
                original,
                substituted,
                ..
            } => format!(
                "{} is the same as {}",
                humanize_fact(original),
                humanize_fact(substituted)
            ),
            _ => continue,
        };
        if !out.contains(&clause) {
            out.push(clause);
        }
    }
    out
}

// ── small text helpers ──

/// `["a"]` -> "a"; `["a","b"]` -> "a and b"; `["a","b","c"]` -> "a, b, and c".
fn join_and(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [a] => a.clone(),
        [a, b] => format!("{a} and {b}"),
        [rest @ .., last] => format!("{}, and {}", rest.join(", "), last),
    }
}

pub(crate) fn prefix_wrapper(wrapper: Option<&str>, clause: String) -> String {
    match wrapper {
        Some("past") => format!("in the past, {clause}"),
        Some("present") => format!("currently, {clause}"),
        Some("future") => format!("in the future, {clause}"),
        Some("obligatory") => format!("it must be that {clause}"),
        Some("permitted") => format!("it is permitted that {clause}"),
        _ => clause,
    }
}

/// "a dog" / "an animal" from a relation's gloss (best-effort indefinite
/// article), via the overlay -> dictionary -> bare resolution chain.
fn a_noun(relation: &str) -> String {
    let gloss = gloss_for(relation);
    let article = match gloss.chars().next() {
        Some(c) if "aeiou".contains(c.to_ascii_lowercase()) => "an",
        _ => "a",
    };
    format!("{article} {gloss}")
}

fn wrapper_label(name: &str) -> Option<&'static str> {
    match name {
        "Past" => Some("past"),
        "Present" => Some("present"),
        "Future" => Some("future"),
        "Obligatory" => Some("obligatory"),
        "Permitted" => Some("permitted"),
        _ => None,
    }
}

/// Parse a raw nibli-reason fact string into `(wrapper, relation, args)`. `None` for
/// anything that is not the `relation(args)` / `Wrapper(relation(args))` form.
pub(crate) fn parse_raw_fact(raw: &str) -> Option<(Option<String>, String, Vec<String>)> {
    let s = raw.trim();
    if s.is_empty() || s.starts_with('(') {
        return None;
    }
    let Some(open) = s.find('(') else {
        // Bare relation, no args.
        return Some((None, s.to_string(), Vec::new()));
    };
    if !s.ends_with(')') {
        return None;
    }
    let name = &s[..open];
    let inner = &s[open + 1..s.len() - 1];
    if let Some(label) = wrapper_label(name) {
        let (_, rel, args) = parse_raw_fact(inner)?;
        return Some((Some(label.to_string()), rel, args));
    }
    Some((None, name.to_string(), split_top_level_commas(inner)))
}

/// Split on commas that are not nested inside parentheses.
fn split_top_level_commas(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '(' => {
                depth += 1;
                cur.push(c);
            }
            ')' => {
                depth -= 1;
                cur.push(c);
            }
            ',' if depth == 0 => {
                let t = cur.trim();
                if !t.is_empty() {
                    out.push(t.to_string());
                }
                cur.clear();
            }
            _ => cur.push(c),
        }
    }
    let t = cur.trim();
    if !t.is_empty() {
        out.push(t.to_string());
    }
    out
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

    #[test]
    fn isolated_roles_do_not_claim_independent_predicates() {
        for fact in [
            "dog_x1(sk_2, adam)",
            "fast_x1(sk_3, rex)",
            "frobnicatezzzz_x1(sk_9, adam)",
        ] {
            assert!(fact_to_english(fact, Register::Spec).is_none(), "{fact}");
        }
        assert!(fact_to_english("frobnicatezzzz(adam)", Register::Spec).is_some());
    }

    #[test]
    fn summarize_syllogism_true() {
        // The Ch 11 syllogism shape: a `animal` event derived from `dog` facts
        // via the rule `dog → animal`. Root holds.
        let trace = ProofTrace {
            steps: vec![
                step(
                    ProofRule::Asserted {
                        fact: "dog_x1(sk_2, adam)".to_string(),
                        sources: vec![],
                    },
                    true,
                    vec![],
                ),
                step(
                    ProofRule::Derived {
                        label: "dog ∧ gerku_x1 → animal ∧ danlu_x1".to_string(),
                        fact: "animal_x1(sk_3, adam)".to_string(),
                        sources: vec![],
                    },
                    true,
                    vec![0],
                ),
            ],
            root: 1,
            naf_dependent: false,
            cwa_false: false,
        };
        let s = summarize_proof(&trace, Register::Spec).unwrap();
        // The instantiated narrative: "Because adam is a dog, adam is an animal."
        // Structure-robust across XML / no-XML builds (article/phrasing differ).
        assert!(s.starts_with("Because "), "got: {s}");
        assert!(s.ends_with('.'), "got: {s}");
        // The given premise and the derived conclusion, both with the real entity.
        assert!(
            s.contains("adam") && s.contains("dog"),
            "premise missing: {s}"
        );
        assert!(s.contains("animal"), "conclusion missing: {s}");
        // No bare algebra variable leaks into the explanation.
        assert!(!s.contains('X'), "bare variable leaked: {s}");
    }

    #[test]
    fn summarize_naf_appends_note() {
        let trace = ProofTrace {
            steps: vec![
                step(
                    ProofRule::Asserted {
                        fact: "dog_x1(sk_2, adam)".to_string(),
                        sources: vec![],
                    },
                    true,
                    vec![],
                ),
                step(ProofRule::Negation, true, vec![0]),
            ],
            root: 1,
            naf_dependent: true,
            cwa_false: false,
        };
        let s = summarize_proof(&trace, Register::Spec).unwrap();
        // The negation root is unphraseable as a derivation, so the fallback lists
        // the asserted given; the NAF caveat is still appended.
        assert!(s.contains("dog_x1(sk_2, adam)"), "given missing: {s}");
        assert!(
            s.contains("closed-world assumption"),
            "naf note missing: {s}"
        );
    }

    #[test]
    fn summarize_presupposition_never_calls_it_a_given() {
        let trace = ProofTrace {
            steps: vec![step(
                ProofRule::Presupposed {
                    label: "dog → animal".to_string(),
                    fact: "animal(adam)".to_string(),
                    sources: vec![],
                },
                true,
                vec![],
            )],
            root: 0,
            naf_dependent: false,
            cwa_false: false,
        };
        let s = summarize_proof(&trace, Register::Spec).expect("presupposition is narratable");
        assert!(
            s.contains("presupposed by legacy existential import"),
            "{s}"
        );
        assert!(!s.contains("given"), "{s}");
    }

    #[test]
    fn summarize_false_predicate_not_found() {
        let trace = ProofTrace {
            steps: vec![step(
                ProofRule::PredicateNotFound {
                    predicate: "animal_x1(sk_3, adam)".to_string(),
                },
                false,
                vec![],
            )],
            root: 0,
            naf_dependent: false,
            cwa_false: false,
        };
        let s = summarize_proof(&trace, Register::Spec).unwrap();
        assert!(s.starts_with("Nothing known establishes that"), "got: {s}");
        assert!(s.contains("adam") && s.contains("animal"), "got: {s}");
    }

    #[test]
    fn summarize_compute_extra() {
        let trace = ProofTrace {
            steps: vec![step(
                ProofRule::ComputeCheck {
                    method: "arithmetic".to_string(),
                    detail: "sumji(adam)".to_string(),
                },
                true,
                vec![],
            )],
            root: 0,
            naf_dependent: false,
            cwa_false: false,
        };
        // No givens/rules, but a compute extra -> still summarized. A local
        // arithmetic method is labelled "computed locally" (distinct from a
        // trusted-backend result).
        let s = summarize_proof(&trace, Register::Spec).unwrap();
        assert!(s.contains("(computed locally)"), "got: {s}");
    }

    #[test]
    fn rule_skips_abstraction_operators_no_broken_output() {
        // `person → nu ∧ animal`: the abstraction `nu` is dropped (no surface
        // frame); the conclusion never leaks a raw `∧` or a dangling subject.
        let trace = ProofTrace {
            steps: vec![step(
                ProofRule::Derived {
                    label: "person → nu ∧ animal".to_string(),
                    fact: "animal_x1(sk_3, adam)".to_string(),
                    sources: vec![],
                },
                true,
                vec![],
            )],
            root: 0,
            naf_dependent: false,
            cwa_false: false,
        };
        let s = summarize_proof(&trace, Register::Spec).expect("renders the animal conclusion");
        assert!(!s.contains('∧'), "abstraction/raw-conjunction leaked: {s}");
        assert!(!s.contains(" X and X"), "broken output: {s}");
        assert!(s.contains("animal"), "animal conclusion missing: {s}"); // nu skipped, animal kept
    }

    #[test]
    fn deontic_wrapper_is_preserved_on_the_statement() {
        // A conclusion fact carrying an `Obligatory(…)` wrapper keeps its mood
        // ("it must be that …") — render-only, no code change (the guard).
        let e = fact_to_english("Obligatory(person(adam))", Register::Spec)
            .expect("deontic flat fact renders");
        assert!(e.contains("it must be that"), "mood dropped: {e}");
        assert!(e.contains("person"), "predicate dropped: {e}");
        // Permitted likewise.
        let p = fact_to_english("Permitted(person(adam))", Register::Spec).unwrap();
        assert!(p.contains("it is permitted that"), "mood dropped: {p}");
    }

    #[test]
    fn an_unspecified_place_is_elided_not_printed() {
        assert_eq!(
            fact_to_english("makes(dhilipsiva, nibli, _)", Register::Spec).as_deref(),
            Some("dhilipsiva makes nibli")
        );
        assert_eq!(
            fact_to_english("writes(oda, onepiece, _, _, _)", Register::Spec).as_deref(),
            Some("oda writes onepiece")
        );
        let (groups, _) = regroup_event_leaves(
            &[
                "entitled_x1(sk_36(lucy), lucy)".into(),
                "entitled_x3(sk_36(lucy), _)".into(),
            ],
            Register::Spec,
        );
        let (key, pm) = &groups[0];
        assert_eq!(
            pm.len(),
            1,
            "the unspecified standard leaves no place: {pm:?}"
        );
        assert_eq!(
            render_group(key.0.as_deref(), &key.1, pm).as_deref(),
            Some("lucy is entitled")
        );
    }

    #[test]
    fn a_noun_gloss_reads_nominally() {
        assert_eq!(
            fact_to_english("member(luffy, strawhatcrew)", Register::Spec).as_deref(),
            Some("luffy is a member of strawhatcrew")
        );
        assert_eq!(
            fact_to_english("fiction(onepiece, oda)", Register::Spec).as_deref(),
            Some("onepiece is a fiction by oda")
        );
    }

    #[test]
    fn a_rule_with_an_abstraction_reads_its_taker_with_the_content() {
        for (source, query, reading) in [
            (
                "entitled(every person, event { protest() }).",
                "entitled(Lucy, event { protest() }).",
                "Lucy is entitled to protest",
            ),
            (
                "decide(every person, event { obey() }).",
                "decide(Lucy, event { obey() }).",
                "Lucy decides to obey",
            ),
        ] {
            let session = nibli_session::CoreSession::new();
            session.assert_text("person(Lucy).").unwrap();
            session.assert_text(source).unwrap();
            let (verdict, trace) = session.query_text_with_proof(query).unwrap();
            assert_eq!(verdict, nibli_types::logic::QueryResult::True);
            let why = summarize_proof(&trace, Register::Spec).unwrap();
            assert!(why.contains(reading), "{why}");
            let proof = crate::render_collapsed_text(&trace, Register::Spec, 0, false);
            assert!(proof.contains(reading), "{proof}");
            assert!(
                proof.contains(&format!("recorded source #1/0: {source}")),
                "{proof}"
            );
            assert!(!proof.contains("__abs_"), "{proof}");
        }
    }

    #[test]
    fn join_and_variants() {
        assert_eq!(join_and(&["a".into()]), "a");
        assert_eq!(join_and(&["a".into(), "b".into()]), "a and b");
        assert_eq!(
            join_and(&["a".into(), "b".into(), "c".into()]),
            "a, b, and c"
        );
    }
}

#[cfg(test)]
mod verdict_tests {
    use super::*;
    use nibli_protocol::{ProofStep, ProofTrace};

    fn false_trace(rule: ProofRule, cwa_false: bool) -> ProofTrace {
        ProofTrace {
            steps: vec![ProofStep {
                rule,
                holds: false,
                children: vec![],
            }],
            root: 0,
            naf_dependent: false,
            cwa_false,
        }
    }

    /// A failing compute check renders as a DECISION — no closed-world caveat —
    /// with the local/backend method distinguished; a passing one inside a
    /// FALSE trace does not trigger the arm.
    #[test]
    fn computed_false_is_a_decision_not_cwa() {
        for (method, label) in [
            ("arithmetic", "computed locally"),
            ("numeric", "computed locally"),
            ("backend", "computed by the trusted backend"),
        ] {
            let trace = false_trace(
                ProofRule::ComputeCheck {
                    detail: "greater(3, 5)".to_string(),
                    method: method.to_string(),
                },
                false,
            );
            let why = summarize_proof(&trace, Register::Spec).unwrap();
            assert!(
                why.starts_with("Decided by computation:"),
                "{method}: {why}"
            );
            assert!(why.contains(label), "{method}: {why}");
            assert!(
                !why.contains("could not be derived"),
                "a computed FALSE must not carry the CWA sentence: {why}"
            );
        }
        // Control: a TRUE compute check inside a FALSE trace is not the decider.
        let mut trace = false_trace(
            ProofRule::ComputeCheck {
                detail: "greater(5, 3)".to_string(),
                method: "arithmetic".to_string(),
            },
            true,
        );
        trace.steps[0].holds = true;
        trace.steps.push(ProofStep {
            rule: ProofRule::PredicateNotFound {
                predicate: "dog_x1(sk_2, adam)".to_string(),
            },
            holds: false,
            children: vec![],
        });
        trace.root = 1;
        let why = summarize_proof(&trace, Register::Spec).unwrap();
        assert!(
            why.starts_with("Nothing known establishes"),
            "a passing check must not hijack the FALSE summary: {why}"
        );
    }

    /// Ordinary closed-world FALSE keeps the non-derivability sentence; a
    /// decided FALSE with no arm and cwa_false = false gets the decided
    /// sentence instead.
    #[test]
    fn cwa_flag_selects_the_false_fallback() {
        let cwa = false_trace(ProofRule::Negation, true);
        assert_eq!(
            summarize_proof(&cwa, Register::Spec).unwrap(),
            "This could not be derived from the known facts and rules."
        );
        let decided = false_trace(ProofRule::Negation, false);
        assert_eq!(
            summarize_proof(&decided, Register::Spec).unwrap(),
            "This is false as a decided matter — not closed-world non-derivability."
        );
    }

    /// The verdict-driven surface: UNKNOWN and RESOURCE_EXCEEDED never fall
    /// into the FALSE arms — each class gets its own honest sentence.
    #[test]
    fn unknown_and_resource_verdicts_never_read_as_cwa() {
        let trace = false_trace(ProofRule::Negation, true);
        let cases: Vec<(VerdictKind, &str)> = vec![
            (
                VerdictKind::Unknown(Some("backend-unavailable")),
                "external compute backend was",
            ),
            (VerdictKind::Unknown(Some("non-finite")), "non-finite value"),
            (
                VerdictKind::Unknown(Some("cycle-cut")),
                "could not decide this (cycle-cut)",
            ),
            (VerdictKind::Unknown(None), "could not decide this."),
            (
                VerdictKind::ResourceExceeded(Some("depth")),
                "exhausted its depth budget",
            ),
            (
                VerdictKind::ResourceExceeded(Some("fuel")),
                "exhausted its fuel budget",
            ),
        ];
        for (kind, needle) in cases {
            let why = summarize_verdict(&kind, &trace, Register::Spec).unwrap();
            assert!(
                why.starts_with("No verdict:"),
                "{kind:?} must be a no-verdict sentence: {why}"
            );
            assert!(why.contains(needle), "{kind:?}: {why}");
            assert!(
                !why.contains("could not be derived"),
                "{kind:?} must never read as CWA non-derivability: {why}"
            );
        }
    }

    /// The typed-verdict mapping feeds the same classes.
    #[test]
    fn verdict_kind_maps_the_typed_result() {
        use nibli_types::logic::{QueryResult, ResourceKind, UnknownReason};
        assert_eq!(verdict_kind(&QueryResult::True), VerdictKind::True);
        assert_eq!(verdict_kind(&QueryResult::False), VerdictKind::False);
        assert_eq!(
            verdict_kind(&QueryResult::Unknown(UnknownReason::BackendUnavailable)),
            VerdictKind::Unknown(Some("backend-unavailable"))
        );
        assert_eq!(
            verdict_kind(&QueryResult::Unknown(UnknownReason::NonFinite)),
            VerdictKind::Unknown(Some("non-finite"))
        );
        assert_eq!(
            verdict_kind(&QueryResult::ResourceExceeded(ResourceKind::Depth)),
            VerdictKind::ResourceExceeded(Some("depth"))
        );
    }
}
