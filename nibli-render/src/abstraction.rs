//! Abstraction labels on the proof-trace side. The compiler keeps an abstraction's body behind a
//! lossless marker relation (`__abs_v1_…`) that the reasoner only matches; the body was retained
//! for rendering. These helpers decode closed bodies for compact rule labels. Proof prose
//! joins event content with its holder only through the checked, reachable packages in
//! `collapse`; a marker elsewhere in the trace must never relabel an unrelated event.

use nibli_types::abstraction::{ABSTRACTION_MARKER_PREFIX, BodyForm, BodyTerm, decode_v1};

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

/// Reuse the complete, closed-body decoder used by proven event packages.
/// Shared modifiers, external variables and unsupported shapes retain fallback.
pub(crate) fn content_phrase(marker: &str) -> Option<String> {
    crate::logic::proof_event_content(marker, crate::Register::Spec)
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

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use nibli_types::logic::{LogicBuffer, LogicNode};

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
            Some("an event described by (Privatememory holds)")
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
    fn incomplete_or_modified_event_bodies_keep_structural_fallback() {
        let modified = marker_in("entitled(Lucy, event { fast dog(Rex) }).");
        assert!(content_phrase(&modified).is_none());
        let open = marker_in("all $x: person($x) -> entitled($x, event { message($x) }).");
        assert!(content_phrase(&open).is_none());
    }
}
