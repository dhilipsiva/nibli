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

use crate::abstraction::{
    content_for, content_phrase, content_relations, is_marker, is_type_predicate,
};
use crate::collapse::{MacroKind, MacroStep, collapse_to_macrosteps};
use crate::fact::humanize_fact;
use crate::frame::{
    fill_template, frame_template, gloss_for, strip_trailing_particle, template_max_place,
};
use crate::overlay::DomainGloss;
use crate::register::Register;
use crate::takers::taker_of;
use crate::term::{humanize_skolem, is_event_skolem_arg, role_base, role_index};

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
    let clause = if let (Some(base), Some(idx)) = (role_base(&relation), role_index(&relation)) {
        // A single role predicate `base_xN(event, filler)` -> fill place N only.
        if args.len() < 2 || !is_event_skolem_arg(&args[0]) {
            return None;
        }
        let mut slots: Vec<Option<String>> = vec![None; idx];
        slots[idx - 1] = filler_text(&args[1]);
        fill_template(&frame_template(base), &slots)
    } else if args.len() == 1 && is_event_skolem_arg(&args[0]) {
        // An event-type predicate `base(event)` -> existence.
        format!("there is {}", a_noun(&relation))
    } else {
        // A flat fact -> fill the frame with all args directly; an unspecified place (`_`)
        // stays unfilled, so a trailing one is elided and an interior one reads "something".
        let slots: Vec<Option<String>> = args.iter().map(|a| filler_text(a)).collect();
        let place_map: BTreeMap<usize, String> = slots
            .iter()
            .enumerate()
            .filter_map(|(i, s)| s.clone().map(|s| (i + 1, s)))
            .collect();
        match taker_statement(&relation, &place_map) {
            Some(s) => s,
            None => fill_template(&frame_template(&relation), &slots),
        }
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
    if !any_derived {
        for s in steps {
            if matches!(s.kind, MacroKind::Given | MacroKind::Presupposed(_)) {
                let stmt = narrative_statement(s);
                if !stmt.is_empty() && !out.contains(&stmt) {
                    out.push(stmt);
                }
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
/// missing role's filler in its place: `entitled_x1(sk_10(lucy), hostwsl)` beside
/// `entitled_x2(sk_10(lucy), <protest>)` reads "HostWsl is entitled to protest".
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
        // An event's marker and type predicate only carry the event; its content is read
        // into the taker's place (`is entitled to protest`), so they are folded away.
        if args.len() == 1
            && content_for(&args[0]).is_some()
            && (is_marker(&relation) || is_type_predicate(&relation))
        {
            continue;
        }
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
    if let Some(s) = taker_statement(base, place_map) {
        return Some(prefix_wrapper(wrapper, s));
    }
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

/// A taker whose event place holds a described event reads with the taker's own phrase
/// ("Lucy decides to obey"), the one every rendering path shares, not its corpus frame.
fn taker_statement(base: &str, place_map: &BTreeMap<usize, String>) -> Option<String> {
    let taker = taker_of(base)?;
    let content = place_map.get(&taker.event_place)?;
    if !crate::abstraction::is_content(content) {
        return None;
    }
    let party = place_map
        .get(&taker.party_place)
        .cloned()
        .unwrap_or_else(|| "something".to_string());
    Some(format!("{party} {} {content}", taker.phrase))
}

/// `dog → animal` -> "every dog is an animal"; `increases ∧ cinla ∧ chemical → dangerous`
/// -> "every chemical that increases and is thin is in danger". When the rule's
/// conditions carry a class restrictor ("{x1} is a &lt;noun&gt;") it heads the
/// reading ("every &lt;noun&gt; …"); otherwise it falls back to "anything that …".
/// Either way the bare algebra variable `X` is gone. Each side may carry several
/// base predicates; abstraction operators (`nu`/`du'u`/…) are dropped.
///
/// HONEST LIMIT: the rule LABEL has lost variable identity, so the reading treats
/// the rule as a single-variable universal. For the common case (`ro lo X cu Y`,
/// `ganai P gi Q`) that is correct; a multi-variable prenex join is an
/// approximation — `:proof-verbose` is the authoritative view.
pub(crate) fn rule_to_english(label: &str) -> Option<String> {
    let (lhs, rhs) = label.split_once(" → ")?;
    let conds: Vec<&str> = lhs.split(" ∧ ").map(str::trim).collect();
    let concls = conclusion_phrases(rhs);
    if concls.is_empty() {
        return None;
    }
    // A class restrictor ("{x1} is a <noun>") among the conditions heads the
    // universal as "every <noun> that …"; the rest become subject-elided phrases.
    let mut head: Option<String> = None;
    let mut cond_phrases: Vec<String> = Vec::new();
    for &c in &conds {
        if head.is_none()
            && let Some(noun) = class_noun(c)
        {
            head = Some(noun);
            continue;
        }
        if let Some(p) = relation_predicate(c) {
            cond_phrases.push(p);
        }
    }
    let subject_clause = match head {
        Some(noun) if cond_phrases.is_empty() => format!("every {noun}"),
        Some(noun) => format!("every {noun} that {}", join_and(&cond_phrases)),
        None if cond_phrases.is_empty() => return None,
        None => format!("anything that {}", join_and(&cond_phrases)),
    };
    Some(format!("{subject_clause} {}", join_and(&concls)))
}

/// The conclusion phrases of a rule label. A conclusion that packages an event abstraction
/// (`event ∧ __abs_… ∧ protest ∧ entitled`) reads as its taker with the content in the event's
/// place ("is entitled to protest"): the marker, the type predicate and the content's own
/// relations are folded into that one phrase rather than read as separate conclusions.
fn conclusion_phrases(rhs: &str) -> Vec<String> {
    let tokens: Vec<&str> = rhs.split(" ∧ ").map(str::trim).collect();
    let marker = tokens.iter().copied().find(|t| is_marker(t));
    let content = marker.and_then(content_phrase);
    let content_bases: Vec<String> = marker.map(content_relations).unwrap_or_default();
    let base_of = |t: &str| -> String {
        match (role_base(t), role_index(t)) {
            (Some(b), Some(_)) => b.to_string(),
            _ => t.to_string(),
        }
    };
    let mut out: Vec<String> = Vec::new();
    let mut taker_done = false;
    for t in tokens {
        if is_marker(t) {
            continue;
        }
        let base = base_of(t);
        if let Some(c) = &content {
            if is_type_predicate(&base) || content_bases.contains(&base) {
                continue;
            }
            if let Some(taker) = taker_of(&base) {
                if !taker_done {
                    out.push(format!("{} {c}", taker.phrase));
                    taker_done = true;
                }
                continue;
            }
        }
        if let Some(p) = relation_predicate(t)
            && !out.contains(&p)
        {
            out.push(p);
        }
    }
    out
}

/// The subject-stripped predicate phrase of a rule clause ("increases", "permits
/// something") — the universal reading elides the shared subject. `None` for an
/// abstraction operator or an empty fill.
///
/// A `se`-converted overlay template ("{x2} is metabolized by {x1}") puts the
/// subject in x2, so eliding x1 leaves a spurious leading "something" and a now-
/// dangling trailing particle ("something is metabolized by"); both are trimmed so
/// the phrase reads "is metabolized".
fn relation_predicate(relation: &str) -> Option<String> {
    let phrase = relation_clause(relation, "")?;
    let phrase = phrase.trim();
    let phrase = phrase.strip_prefix("something ").unwrap_or(phrase);
    let phrase = strip_trailing_particle(phrase).trim();
    if phrase.is_empty() {
        None
    } else {
        Some(phrase.to_string())
    }
}

/// If `relation`'s frame is a class predicate ("{x1} is a/an &lt;noun&gt;"),
/// return the bare noun ("dog", "chemical"); otherwise `None`. Drives the
/// "every &lt;noun&gt; …" universal heading.
fn class_noun(relation: &str) -> Option<String> {
    if is_abstraction(relation) {
        return None;
    }
    let phrase = relation_predicate(relation)?;
    for prefix in ["is a ", "is an "] {
        if let Some(noun) = phrase.strip_prefix(prefix) {
            return Some(noun.to_string());
        }
    }
    None
}

/// Render a single rule-clause predicate with `subject` in x1 and a generic
/// "something" in every other place of its frame, so a multi-place predicate
/// reads "permits something" / "is a rule about something" instead of collapsing
/// to the bare subject. Called with an empty `subject` by [`relation_predicate`]
/// to get the subject-elided phrase for the universal "every …/anything that …"
/// reading. `None` for an abstraction operator (no surface frame) or an empty fill.
fn relation_clause(relation: &str, subject: &str) -> Option<String> {
    if is_abstraction(relation) {
        return None;
    }
    let tmpl = frame_template(relation);
    let n = template_max_place(&tmpl).max(1);
    let mut places = vec![Some("something".to_string()); n];
    places[0] = Some(subject.to_string());
    let filled = fill_template(&tmpl, &places);
    let trimmed = filled.trim();
    // Reject a degenerate fill that is just the bare subject (the relation had no
    // usable gloss/frame text) — dropping the clause beats emitting "X".
    if trimmed.is_empty() || trimmed == subject {
        None
    } else {
        Some(trimmed.to_string())
    }
}

/// Abstraction type predicates (the `AbstractionKind` set — `event`/`fact`/
/// `property`/`amount`/`concept`): they wrap an event/property and have no
/// surface place-frame, so they are skipped when glossing a rule.
fn is_abstraction(relation: &str) -> bool {
    crate::is_internal_relation(relation)
        || matches!(
            relation,
            "event" | "fact" | "property" | "amount" | "concept"
        )
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

fn prefix_wrapper(wrapper: Option<&str>, clause: String) -> String {
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
    fn fact_to_english_role_predicate() {
        // Robust across XML (curated "adam is a dog") and no-XML fallback
        // ("adam is dog") builds — assert the subject + the gloss noun.
        let dog = fact_to_english("dog_x1(sk_2, adam)", Register::Spec).unwrap();
        assert!(dog.starts_with("adam"), "got: {dog}");
        assert!(dog.contains("dog"), "got: {dog}");
        let animal = fact_to_english("animal_x1(sk_3, adam)", Register::Spec).unwrap();
        assert!(animal.starts_with("adam"), "got: {animal}");
        assert!(animal.contains("animal"), "got: {animal}");
    }

    #[test]
    fn fact_to_english_unknown_relation_returns_none_or_generic() {
        // An uncurated relation falls back to its generic gloss frame, never an
        // S-expr or panic. (`frobnicatezzzz` has no gloss -> "X is frobnicatezzzz".)
        let out = fact_to_english("frobnicatezzzz_x1(sk_9, adam)", Register::Spec);
        assert!(out.is_some(), "should produce a generic frame");
        assert!(out.unwrap().starts_with("adam"));
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
        assert!(s.contains("adam is a dog"), "given missing: {s}");
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
    fn rule_multi_predicate_conclusion_renders_each() {
        // `dog → animal ∧ alive`: the universal rule reading renders both
        // conclusion predicates, joined. (The "why" narrative shows the
        // instantiated fact; the multi-conclusion lives in the rule justification.)
        let e = rule_to_english("dog → animal ∧ alive").expect("renders");
        assert!(e.starts_with("every dog"), "type head missing: {e}");
        assert!(e.contains("animal"), "animal missing: {e}");
        assert!(e.contains("alive"), "alive missing: {e}");
        assert!(e.contains(" and "), "multi-conclusion not joined: {e}");
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
    fn rule_multi_place_predicate_keeps_its_object() {
        // A 2-place rule (`permits → rule`) with no class restrictor reads as
        // "anything that …"; multi-place predicates keep a generic object rather
        // than collapsing to a dangling verb.
        let e = rule_to_english("permits → rule").expect("multi-place rule now renders");
        assert!(e.starts_with("anything that "), "got: {e}");
        assert!(e.contains("permits something"), "permits truncated: {e}");
        assert!(
            e.contains("is a rule about something"),
            "javni truncated: {e}"
        );
        // No bare variable, and no dangling multi-place verb with no object.
        assert!(!e.contains('X'), "bare variable leaked: {e}");
        assert!(!e.ends_with("permits"), "dangling: {e}");
    }

    #[test]
    fn rule_single_place_reads_as_every_type() {
        // A class restrictor heads the universal: "every dog is an animal" — no
        // bare `X`, no spurious "something" filler.
        assert_eq!(
            rule_to_english("dog → animal").as_deref(),
            Some("every dog is an animal")
        );
        let e = rule_to_english("dog → animal").unwrap();
        assert!(!e.contains("something"), "1-place leaked a filler: {e}");
        assert!(!e.contains('X'), "bare variable leaked: {e}");
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
        let m = crate::abstraction::tests::marker_in("entitled(Lucy, event { protest() }).");
        let label = format!("person → event ∧ {m} ∧ protest ∧ entitled");
        assert_eq!(
            rule_to_english(&label).as_deref(),
            Some("every person is entitled to protest")
        );
        let m = crate::abstraction::tests::marker_in("decide(Lucy, event { obey() }).");
        let label = format!("person → event ∧ {m} ∧ obey ∧ decide");
        assert_eq!(
            rule_to_english(&label).as_deref(),
            Some("every person decides to obey")
        );
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
