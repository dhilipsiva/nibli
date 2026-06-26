//! Plain-English "Why" summary of a proof trace (render-only).
//!
//! The technical proof trace ([`crate::proof`]) is exhaustive but cryptic — it
//! shows functional notation (`gerku.x1(adam)`) and the Neo-Davidsonian
//! decomposition explodes each fact into role-predicate lines. This produces a
//! short, plain-English explanation of WHY a query holds (or fails), reusing the
//! same place-frame machinery as the back-translation: it walks the flat
//! `ProofTrace`, regroups the role predicates back to surface facts, and fills
//! the curated English templates (`gerku` -> `"{x1} is a dog"`).
//!
//! Best-effort and total: anything that does not parse or has no frame falls
//! back to the functional [`crate::fact::humanize_fact`] string — it never
//! invents English. The `ProofTrace` data is unchanged; this is pure rendering,
//! layered ABOVE the detailed trace (which stays for experts).

use std::collections::BTreeMap;

use nibli_protocol::{ProofRule, ProofTrace};

use crate::fact::humanize_fact;
use crate::frame::{fill_template, frame_template, template_max_place};
use crate::proof::humanize_rule_label;
use crate::register::Register;
use crate::term::{humanize_skolem, is_event_skolem, is_event_skolem_arg, role_base, role_index};

/// Build a one-block plain-English "why" explanation of the trace, or `None` if
/// there is nothing summarizable (callers then print nothing extra).
pub fn summarize_proof(trace: &ProofTrace, register: Register) -> Option<String> {
    let root = trace.steps.get(trace.root as usize)?;
    if root.holds {
        summarize_true(trace, register)
    } else {
        summarize_false(trace, register)
    }
}

/// Translate one humanized/raw fact string to an English clause via the place
/// frames. `None` when it cannot be rendered (caller falls back to functional).
pub fn fact_to_english(raw: &str, _register: Register) -> Option<String> {
    let (wrapper, relation, args) = parse_raw_fact(raw)?;
    let clause = if let (Some(base), Some(idx)) = (role_base(&relation), role_index(&relation)) {
        // A single role predicate `base_xN(event, filler)` -> fill place N only.
        if args.len() < 2 || !is_event_skolem(&args[0]) {
            return None;
        }
        let mut slots: Vec<Option<String>> = vec![None; idx];
        slots[idx - 1] = Some(humanize_skolem(&args[1]));
        fill_template(&frame_template(base), &slots)
    } else if args.len() == 1 && is_event_skolem(&args[0]) {
        // An event-type predicate `base(event)` -> existence.
        format!("there is {}", a_noun(&relation))
    } else {
        // A flat fact -> fill the frame with all args directly.
        let slots: Vec<Option<String>> = args.iter().map(|a| Some(humanize_skolem(a))).collect();
        fill_template(&frame_template(&relation), &slots)
    };
    if clause.trim().is_empty() {
        None
    } else {
        Some(prefix_wrapper(wrapper.as_deref(), clause))
    }
}

fn summarize_true(trace: &ProofTrace, register: Register) -> Option<String> {
    let mut clauses: Vec<String> = Vec::new();
    for g in collect_givens(trace, register) {
        clauses.push(format!("{g} (given)"));
    }
    for r in collect_rules(trace) {
        clauses.push(format!("{r} (rule)"));
    }
    clauses.extend(collect_extras(trace));
    if clauses.is_empty() {
        return None;
    }
    let mut s = format!("Because {}.", join_and(&clauses));
    if trace.naf_dependent {
        s.push_str(" (Under the closed-world assumption — nothing known contradicts it.)");
    }
    Some(s)
}

fn summarize_false(trace: &ProofTrace, register: Register) -> Option<String> {
    for step in &trace.steps {
        match &step.rule {
            ProofRule::PredicateNotFound { predicate } => {
                let what = fact_to_english(predicate, register)
                    .unwrap_or_else(|| humanize_fact(predicate));
                return Some(format!("Nothing known establishes that {what}."));
            }
            ProofRule::ForallCounterexample { entity } => {
                return Some(format!(
                    "It is not true for every case — counterexample: {}.",
                    entity.display()
                ));
            }
            ProofRule::ExistsFailed => {
                return Some("No example could be found that satisfies the query.".to_string());
            }
            _ => {}
        }
    }
    Some("This could not be derived from the known facts and rules.".to_string())
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
            places
                .entry(key)
                .or_default()
                .insert(idx, humanize_skolem(&args[1]));
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

/// Collect the asserted (given) facts, regrouped from role predicates back to
/// surface facts and translated to English. Distinct, first-seen order.
fn collect_givens(trace: &ProofTrace, register: Register) -> Vec<String> {
    let facts: Vec<String> = trace
        .steps
        .iter()
        .filter_map(|s| match &s.rule {
            ProofRule::Asserted { fact } => Some(fact.clone()),
            _ => None,
        })
        .collect();
    let (groups, flat) = regroup_event_leaves(&facts, register);

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

/// Collect the distinct rules applied, translated to English ("if X is a dog
/// then X is an animal").
fn collect_rules(trace: &ProofTrace) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for step in &trace.steps {
        if let ProofRule::Derived { label, .. } = &step.rule
            && let Some(e) = rule_to_english(&humanize_rule_label(label))
            && !out.contains(&e)
        {
            out.push(e);
        }
    }
    out
}

/// `gerku → danlu` -> "if X is a dog then X is an animal". Each side may carry
/// several base predicates (`nu ∧ curmi ∧ bilga`); abstraction operators
/// (`nu`/`du'u`/…) have no surface frame and are dropped.
pub(crate) fn rule_to_english(label: &str) -> Option<String> {
    let (lhs, rhs) = label.split_once(" → ")?;
    let conds: Vec<String> = lhs
        .split(" ∧ ")
        .filter_map(|c| relation_clause(c.trim(), "X"))
        .collect();
    let concls: Vec<String> = rhs
        .split(" ∧ ")
        .filter_map(|c| relation_clause(c.trim(), "X"))
        .collect();
    if conds.is_empty() || concls.is_empty() {
        return None;
    }
    Some(format!(
        "if {} then {}",
        join_and(&conds),
        join_and(&concls)
    ))
}

/// Render a single rule-clause predicate with `subject` in x1 and a generic
/// "something" in every other place of its frame, so a multi-place predicate
/// reads "X permits something" / "X is a rule about something" instead of
/// collapsing to the bare subject (which `fill_template` would truncate to "X",
/// triggering the degenerate-fill `None` below and the `[by rule: …]` fallback).
/// `None` for an abstraction operator (no surface frame) or an empty fill.
///
/// HONEST LIMIT: the rule LABEL this is rendered from has lost variable identity,
/// so every clause shares the subject `X`. For a SINGLE-variable rule (the common
/// case — `ro lo X cu Y`, `ganai P gi Q`) that is correct; for a MULTI-variable
/// join (a prenex `ro da ro de …` rule, where the clauses are about distinct
/// entities) the shared `X` is an approximation — `:proof-verbose` is the
/// authoritative view. The renderer cannot distinguish the two from the label.
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

/// Lojban abstraction operators (NU-class): they wrap an event/property and have
/// no surface place-frame, so they are skipped when glossing a rule.
fn is_abstraction(relation: &str) -> bool {
    matches!(
        relation,
        "nu" | "du'u"
            | "ka"
            | "ni"
            | "si'o"
            | "jei"
            | "su'u"
            | "li'i"
            | "mu'e"
            | "zu'o"
            | "za'i"
            | "pu'u"
    )
}

/// Compute results + equality substitutions, as supporting clauses.
fn collect_extras(trace: &ProofTrace) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for step in &trace.steps {
        let clause = match &step.rule {
            ProofRule::ComputeCheck { detail, .. } => {
                format!("{} (computed)", humanize_fact(detail))
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

/// "a dog" / "an animal" from a relation's gloss (best-effort indefinite article).
fn a_noun(relation: &str) -> String {
    let gloss = smuni_dictionary::get_gloss(relation).unwrap_or(relation);
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

/// Parse a raw logji fact string into `(wrapper, relation, args)`. `None` for
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
        let dog = fact_to_english("gerku_x1(sk_2, adam)", Register::Spec).unwrap();
        assert!(dog.starts_with("adam"), "got: {dog}");
        assert!(dog.contains("dog"), "got: {dog}");
        let animal = fact_to_english("danlu_x1(sk_3, adam)", Register::Spec).unwrap();
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
        // The Ch 11 syllogism shape: a `danlu` event derived from `gerku` facts
        // via the rule `gerku → danlu`. Root holds.
        let trace = ProofTrace {
            steps: vec![
                step(
                    ProofRule::Asserted {
                        fact: "gerku_x1(sk_2, adam)".to_string(),
                    },
                    true,
                    vec![],
                ),
                step(
                    ProofRule::Derived {
                        label: "gerku ∧ gerku_x1 → danlu ∧ danlu_x1".to_string(),
                        fact: "danlu_x1(sk_3, adam)".to_string(),
                    },
                    true,
                    vec![0],
                ),
            ],
            root: 1,
            naf_dependent: false,
        };
        let s = summarize_proof(&trace, Register::Spec).unwrap();
        // Structure-robust across XML / no-XML builds (article/phrasing differ).
        assert!(s.starts_with("Because "), "got: {s}");
        assert!(s.ends_with('.'), "got: {s}");
        assert!(
            s.contains("adam") && s.contains("dog"),
            "given missing: {s}"
        );
        assert!(s.contains("(given)"), "got: {s}");
        assert!(
            s.contains("if ") && s.contains(" then ") && s.contains("animal"),
            "rule missing: {s}"
        );
        assert!(s.contains("(rule)"), "got: {s}");
    }

    #[test]
    fn summarize_naf_appends_note() {
        let trace = ProofTrace {
            steps: vec![
                step(
                    ProofRule::Asserted {
                        fact: "gerku_x1(sk_2, adam)".to_string(),
                    },
                    true,
                    vec![],
                ),
                step(ProofRule::Negation, true, vec![0]),
            ],
            root: 1,
            naf_dependent: true,
        };
        let s = summarize_proof(&trace, Register::Spec).unwrap();
        assert!(s.contains("adam is a dog (given)"));
        assert!(s.contains("closed-world assumption"));
    }

    #[test]
    fn summarize_false_predicate_not_found() {
        let trace = ProofTrace {
            steps: vec![step(
                ProofRule::PredicateNotFound {
                    predicate: "danlu_x1(sk_3, adam)".to_string(),
                },
                false,
                vec![],
            )],
            root: 0,
            naf_dependent: false,
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
        };
        // No givens/rules, but a compute extra -> still summarized.
        let s = summarize_proof(&trace, Register::Spec).unwrap();
        assert!(s.contains("(computed)"));
    }

    #[test]
    fn rule_multi_predicate_conclusion_renders_each() {
        // `gerku → danlu ∧ jmive`: both conclusion predicates render, joined.
        let trace = ProofTrace {
            steps: vec![step(
                ProofRule::Derived {
                    label: "gerku → danlu ∧ jmive".to_string(),
                    fact: "danlu_x1(sk_3, adam)".to_string(),
                },
                true,
                vec![],
            )],
            root: 0,
            naf_dependent: false,
        };
        let s = summarize_proof(&trace, Register::Spec).unwrap();
        assert!(s.contains("if ") && s.contains(" then "), "got: {s}");
        assert!(s.contains("animal"), "danlu missing: {s}"); // danlu
        assert!(s.contains(" and "), "multi-conclusion not joined: {s}");
    }

    #[test]
    fn rule_skips_abstraction_operators_no_broken_output() {
        // `prenu → nu ∧ danlu`: the abstraction `nu` is dropped (no surface
        // frame); the conclusion never leaks a raw `∧` or a dangling subject.
        let trace = ProofTrace {
            steps: vec![step(
                ProofRule::Derived {
                    label: "prenu → nu ∧ danlu".to_string(),
                    fact: "danlu_x1(sk_3, adam)".to_string(),
                },
                true,
                vec![],
            )],
            root: 0,
            naf_dependent: false,
        };
        let s = summarize_proof(&trace, Register::Spec).expect("renders the danlu conclusion");
        assert!(!s.contains('∧'), "abstraction/raw-conjunction leaked: {s}");
        assert!(!s.contains(" X and X"), "broken output: {s}");
        assert!(s.contains("animal"), "danlu conclusion missing: {s}"); // nu skipped, danlu kept
    }

    #[test]
    fn rule_clause_pads_multi_place_instead_of_falling_back() {
        // A 2-place rule (`curmi → javni`) used to collapse to the bare subject
        // (the connective before the trailing place is dropped → "X" → None →
        // `[by rule: …]`). Padding the other places with "something" renders it.
        let e = rule_to_english("curmi → javni").expect("multi-place rule now renders");
        assert!(e.starts_with("if ") && e.contains(" then "), "got: {e}");
        assert!(e.contains("permits something"), "curmi truncated: {e}");
        assert!(
            e.contains("is a rule about something"),
            "javni truncated: {e}"
        );
        // No dangling clause (a multi-place verb with no object).
        assert!(!e.ends_with("permits"), "dangling: {e}");
    }

    #[test]
    fn rule_clause_single_place_is_byte_identical() {
        // 1-place predicates have no trailing place, so padding is a no-op — the
        // common syllogism rule must read exactly as before.
        assert_eq!(
            rule_to_english("gerku → danlu").as_deref(),
            Some("if X is a dog then X is an animal")
        );
        // …and no spurious "something" leaks into a 1-place clause.
        let e = rule_to_english("gerku → danlu").unwrap();
        assert!(!e.contains("something"), "1-place leaked a filler: {e}");
    }

    #[test]
    fn deontic_wrapper_is_preserved_on_the_statement() {
        // A conclusion fact carrying an `Obligatory(…)` wrapper keeps its mood
        // ("it must be that …") — render-only, no code change (the guard).
        let e = fact_to_english("Obligatory(prenu(adam))", Register::Spec)
            .expect("deontic flat fact renders");
        assert!(e.contains("it must be that"), "mood dropped: {e}");
        assert!(e.contains("person"), "predicate dropped: {e}");
        // Permitted likewise.
        let p = fact_to_english("Permitted(prenu(adam))", Register::Spec).unwrap();
        assert!(p.contains("it is permitted that"), "mood dropped: {p}");
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
