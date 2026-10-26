//! Abstractions on the proof-trace side. The compiler keeps an abstraction's body behind a
//! lossless marker relation (`__abs_v1_…`) that the reasoner only matches; the body was retained
//! for rendering. Here it is read back: an event marker reads as the infinitive its content
//! names ("protest", "retain PrivateMemory"), every event skolem the trace describes maps to that
//! phrase, and the marker and type predicates that only carry the event are folded away.

use std::cell::RefCell;
use std::collections::BTreeMap;

use nibli_types::abstraction::{
    ABSTRACTION_MARKER_PREFIX, BodyForm, BodyKind, BodyTerm, decode_v1,
};
use nibli_types::logic::{ProofRule, ProofTrace};

use crate::frame::deontic_content_phrase;
use crate::term::humanize_skolem;

pub(crate) fn is_marker(relation: &str) -> bool {
    relation.starts_with(ABSTRACTION_MARKER_PREFIX)
}

/// The abstraction type predicates (`event(e)`…): they only carry the event.
pub(crate) fn is_type_predicate(relation: &str) -> bool {
    matches!(
        relation,
        "event" | "fact" | "property" | "amount" | "concept"
    )
}

/// The predicates of a body that is a plain positive conjunction (binders over the private
/// event allowed); `None` for anything the frames cannot phrase as a bare event.
fn simple_predicates(form: &BodyForm, out: &mut Vec<(String, Vec<BodyTerm>)>) -> bool {
    match form {
        BodyForm::And(l, r) => simple_predicates(l, out) && simple_predicates(r, out),
        BodyForm::Exists(_, body) => simple_predicates(body, out),
        BodyForm::Predicate { relation, args } => {
            out.push((relation.clone(), args.clone()));
            true
        }
        BodyForm::NestedMarker { .. } => true,
        _ => false,
    }
}

fn term_text(t: &BodyTerm) -> Option<String> {
    match t {
        BodyTerm::Constant(s) => Some(humanize_skolem(s)),
        BodyTerm::Description(s) => Some(format!("the {s}")),
        BodyTerm::Number(n) => Some(if *n == (*n as i64) as f64 {
            format!("{}", *n as i64)
        } else {
            format!("{n}")
        }),
        BodyTerm::Variable(_) | BodyTerm::Unspecified => None,
    }
}

fn base_and_place(relation: &str) -> (String, Option<usize>) {
    match relation.rsplit_once("_x") {
        Some((b, n)) => match n.parse::<usize>() {
            Ok(i) => (b.to_string(), Some(i)),
            Err(_) => (relation.to_string(), None),
        },
        None => (relation.to_string(), None),
    }
}

/// The content relations of an event marker's body, in order (`protest`), without the roles.
pub(crate) fn content_relations(marker: &str) -> Vec<String> {
    let Some(body) = decode_v1(marker) else {
        return Vec::new();
    };
    let mut preds = Vec::new();
    if !simple_predicates(&body.form, &mut preds) {
        return Vec::new();
    }
    let mut out: Vec<String> = Vec::new();
    for (rel, _) in preds {
        let (base, _) = base_and_place(&rel);
        if is_type_predicate(&base) || is_marker(&base) || out.contains(&base) {
            continue;
        }
        out.push(base);
    }
    out
}

/// The infinitive an event marker reads as: its content predicates as bare events
/// (`event { protest() }` is "protest"), each filled place after its verb ("retain
/// PrivateMemory"). `None` when the body is not an event or not a plain positive conjunction.
pub(crate) fn content_phrase(marker: &str) -> Option<String> {
    let body = decode_v1(marker)?;
    if body.kind != BodyKind::Event {
        return None;
    }
    let mut preds = Vec::new();
    if !simple_predicates(&body.form, &mut preds) {
        return None;
    }
    let mut order: Vec<String> = Vec::new();
    let mut places: BTreeMap<String, BTreeMap<usize, String>> = BTreeMap::new();
    for (rel, args) in preds {
        let (base, place) = base_and_place(&rel);
        if is_type_predicate(&base) || is_marker(&base) {
            continue;
        }
        if !places.contains_key(&base) {
            order.push(base.clone());
            places.insert(base.clone(), BTreeMap::new());
        }
        let slots = places.get_mut(&base).expect("inserted above");
        match place {
            Some(i) => {
                if let Some(text) = args.get(1).and_then(term_text) {
                    slots.insert(i, text);
                }
            }
            None => {
                for (k, t) in args.iter().enumerate().skip(1) {
                    if let Some(text) = term_text(t) {
                        slots.insert(k + 1, text);
                    }
                }
            }
        }
    }
    if order.is_empty() {
        return None;
    }
    let phrases: Vec<String> = order
        .iter()
        .map(|base| {
            let slots = &places[base];
            if slots.contains_key(&1) {
                // The content names its own subject: a clause, as the buffer path reads it.
                let max = *slots.keys().max().unwrap_or(&1);
                let filled: Vec<Option<String>> =
                    (1..=max).map(|i| slots.get(&i).cloned()).collect();
                let clause =
                    crate::frame::fill_template(&crate::frame::frame_template(base), &filled);
                return format!("an event described by ({clause})");
            }
            let mut p = deontic_content_phrase(base);
            for (i, filler) in slots {
                if *i >= 2 {
                    p.push(' ');
                    p.push_str(filler);
                }
            }
            p
        })
        .collect();
    Some(join_and(&phrases))
}

fn join_and(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [one] => one.clone(),
        [a, b] => format!("{a} and {b}"),
        _ => {
            let (last, init) = items.split_last().expect("non-empty");
            format!("{}, and {last}", init.join(", "))
        }
    }
}

/// A rule label for the functional readings: an abstraction's marker, type predicate and
/// content relations fold into its taker (`entitled{protest}`); a marker with no taker reads
/// `event{<content>}`; one the renderer cannot read, `⟨abstraction⟩`.
pub(crate) fn fold_markers(label: &str) -> String {
    label
        .split(" → ")
        .map(fold_side)
        .collect::<Vec<_>>()
        .join(" → ")
}

fn fold_side(side: &str) -> String {
    let tokens: Vec<&str> = side.split(" ∧ ").map(str::trim).collect();
    let marker = tokens.iter().copied().find(|t| is_marker(t));
    let content = marker.and_then(content_phrase);
    let bases = marker.map(content_relations).unwrap_or_default();
    let has_taker = content.is_some()
        && tokens
            .iter()
            .any(|t| crate::takers::taker_of(&base_and_place(t).0).is_some());
    let mut out: Vec<String> = Vec::new();
    for t in &tokens {
        if is_marker(t) {
            match (&content, has_taker) {
                (Some(_), true) => {}
                (Some(c), false) => out.push(format!("event{{{c}}}")),
                (None, _) => out.push("⟨abstraction⟩".to_string()),
            }
            continue;
        }
        let (base, _) = base_and_place(t);
        if let Some(c) = &content {
            if has_taker && (is_type_predicate(&base) || bases.contains(&base)) {
                continue;
            }
            if has_taker && crate::takers::taker_of(&base).is_some() {
                let folded = format!("{t}{{{c}}}");
                if !out.contains(&folded) {
                    out.push(folded);
                }
                continue;
            }
        }
        if !out.contains(&t.to_string()) {
            out.push(t.to_string());
        }
    }
    out.join(" ∧ ")
}

/// Is this text the content phrase of an event the active trace describes?
pub(crate) fn is_content(text: &str) -> bool {
    CONTENTS.with(|c| {
        c.borrow()
            .as_ref()
            .is_some_and(|m| m.values().any(|v| v == text))
    })
}

fn step_fact(rule: &ProofRule) -> Option<&str> {
    match rule {
        ProofRule::Asserted { fact, .. }
        | ProofRule::Derived { fact, .. }
        | ProofRule::Presupposed { fact, .. }
        | ProofRule::ProofRef { fact } => Some(fact),
        ProofRule::PredicateNotFound { predicate } => Some(predicate),
        _ => None,
    }
}

/// Every event the trace's markers describe: the skolem as the facts spell it
/// (`sk_34(lucy)`) → the phrase its content reads as.
pub(crate) fn event_contents(trace: &ProofTrace) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for step in &trace.steps {
        let Some(fact) = step_fact(&step.rule) else {
            continue;
        };
        let Some((_, relation, args)) = crate::summary::parse_raw_fact(fact) else {
            continue;
        };
        if !is_marker(&relation) || args.len() != 1 {
            continue;
        }
        if let Some(phrase) = content_phrase(&relation) {
            out.entry(args[0].clone()).or_insert(phrase);
        }
    }
    out
}

thread_local! {
    static CONTENTS: RefCell<Option<BTreeMap<String, String>>> = const { RefCell::new(None) };
}

/// Run `f` with the trace's event contents active; the previous table is restored after.
pub(crate) fn with_event_contents<R>(trace: &ProofTrace, f: impl FnOnce() -> R) -> R {
    let prev = CONTENTS.with(|c| c.borrow_mut().replace(event_contents(trace)));
    let out = f();
    CONTENTS.with(|c| *c.borrow_mut() = prev);
    out
}

/// The content phrase of an event skolem, as the facts spell it, when the active trace has it.
pub(crate) fn content_for(skolem: &str) -> Option<String> {
    CONTENTS.with(|c| c.borrow().as_ref().and_then(|m| m.get(skolem).cloned()))
}

/// Is this fact only plumbing for an event the trace describes (its marker, or its type
/// predicate)? Folded into the taker's statement rather than shown.
pub(crate) fn is_event_plumbing(fact: &str) -> bool {
    let Some((_, relation, args)) = crate::summary::parse_raw_fact(fact) else {
        return false;
    };
    if args.len() != 1 {
        return false;
    }
    (is_marker(&relation) && content_for(&args[0]).is_some())
        || (is_type_predicate(&relation) && content_for(&args[0]).is_some())
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use nibli_types::logic::{LogicBuffer, LogicNode, ProofStep};

    /// The marker the compiler emits for the abstraction in `kr`.
    pub(crate) fn marker_in(kr: &str) -> String {
        let buf: LogicBuffer =
            nibli_semantics::compile_from_ast(nibli_kr::parse_checked(kr).expect("KR parse"))
                .expect("KR compile");
        buf.nodes
            .iter()
            .find_map(|n| match n {
                LogicNode::Predicate((rel, _)) if is_marker(rel) => Some(rel.clone()),
                _ => None,
            })
            .expect("an abstraction marker in the buffer")
    }

    #[test]
    fn an_event_marker_reads_as_its_content() {
        assert_eq!(
            content_phrase(&marker_in("entitled(Lucy, event { protest() }).")).as_deref(),
            Some("protest")
        );
        assert_eq!(
            content_phrase(&marker_in("decide(Lucy, event { obey() }).")).as_deref(),
            Some("obey")
        );
        assert_eq!(
            content_relations(&marker_in("entitled(Lucy, event { protest() }).")),
            vec!["protest".to_string()]
        );
        assert!(content_phrase("protest").is_none(), "not a marker");
    }

    #[test]
    fn a_content_with_its_own_subject_reads_as_a_clause() {
        let m = marker_in("obliged(Host, event { retain(PrivateMemory) }).");
        assert_eq!(
            content_phrase(&m).as_deref(),
            Some("an event described by (privatememory holds)")
        );
    }

    #[test]
    fn a_label_folds_the_event_into_its_taker() {
        let m = marker_in("entitled(Lucy, event { protest() }).");
        let label = format!("person → event ∧ {m} ∧ protest ∧ entitled");
        assert_eq!(fold_markers(&label), "person → entitled{protest}");
        let bare = format!("person → event ∧ {m} ∧ protest");
        assert_eq!(
            fold_markers(&bare),
            "person → event ∧ event{protest} ∧ protest"
        );
        assert_eq!(fold_markers("dog → animal"), "dog → animal");
    }

    #[test]
    fn the_trace_maps_every_described_event_to_its_phrase() {
        let m = marker_in("entitled(Lucy, event { protest() }).");
        let trace = ProofTrace {
            steps: vec![
                ProofStep {
                    rule: ProofRule::Derived {
                        label: "person → entitled".into(),
                        fact: format!("{m}(sk_34(lucy))"),
                        sources: vec![],
                    },
                    holds: true,
                    children: vec![],
                },
                ProofStep {
                    rule: ProofRule::ProofRef {
                        fact: "event(sk_34(lucy))".into(),
                    },
                    holds: true,
                    children: vec![],
                },
            ],
            root: 0,
            naf_dependent: false,
            cwa_false: false,
        };
        let contents = event_contents(&trace);
        assert_eq!(
            contents.get("sk_34(lucy)").map(String::as_str),
            Some("protest")
        );
        with_event_contents(&trace, || {
            assert_eq!(content_for("sk_34(lucy)").as_deref(), Some("protest"));
            assert!(is_event_plumbing("event(sk_34(lucy))"));
            assert!(is_event_plumbing(&format!("{m}(sk_34(lucy))")));
            assert!(!is_event_plumbing("entitled_x1(sk_36(lucy), lucy)"));
            assert_eq!(humanize_skolem("sk_34(lucy)"), "protest");
        });
        assert_eq!(content_for("sk_34(lucy)"), None);
    }
}
