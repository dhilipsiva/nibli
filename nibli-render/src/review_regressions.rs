//! End-to-end display regressions through the real compiler and proof search.
use crate::*;
use nibli_session::CoreSession;
use nibli_types::logic::QueryResult;

#[test]
fn event_content_proof_keeps_opaque_content_inside_its_entitlement() {
    let session = CoreSession::new();
    session.assert_text("person(Lucy).").unwrap();
    session
        .assert_text("entitled(every person, event { survive() }).")
        .unwrap();
    let (verdict, trace) = session
        .query_text_with_proof("entitled(Lucy, event { survive() }).")
        .unwrap();
    assert_eq!(verdict, QueryResult::True);
    let before = format!("{trace:?}");
    let why = summarize_proof(&trace, Register::Spec).unwrap();
    assert_eq!(
        why,
        "Because Lucy is a person, Lucy is entitled to survive."
    );
    let proof = render_collapsed_text(&trace, Register::Spec, 0, false);
    assert!(proof.contains("Lucy is entitled to survive"), "{proof}");
    assert!(proof.contains("Lucy is a person"), "{proof}");
    assert!(
        proof.contains("recorded source #1/0: entitled(every person, event { survive() })."),
        "{proof}"
    );
    assert!(!proof.contains("__abs_"), "{proof}");
    assert!(!proof.contains("#2(lucy)"), "{proof}");
    assert_eq!(before, format!("{trace:?}"));
    assert_eq!(
        session.query_text("survive().").unwrap(),
        QueryResult::False
    );
    println!("EVENT CONTENT\n[Why] {why}\n[Proof]\n{proof}");
}

#[test]
fn event_content_proofs_preserve_filled_places_negation_and_local_scope() {
    for (source, query, expected) in [
        (
            "obliged(every person, event { message() }).",
            "obliged(Lucy, event { message() }).",
            "Lucy is obligated to notify",
        ),
        (
            "permitted(every person, event { cease() }).",
            "permitted(Lucy, event { cease() }).",
            "Lucy is permitted to cease",
        ),
        (
            "decide(every person, event { obey() }).",
            "decide(Lucy, event { obey() }).",
            "Lucy decides to obey",
        ),
        (
            "entitled(every person, event { message(Bob) }).",
            "entitled(Lucy, event { message(Bob) }).",
            "an event described by (Bob",
        ),
        (
            "entitled(Lucy, event { ~message() }).",
            "entitled(Lucy, event { ~message() }).",
            "it is not the case that",
        ),
        (
            "entitled(Lucy, event { message(some person) }).",
            "entitled(Lucy, event { message(some person) }).",
            "there exists",
        ),
        (
            "entitled(Lucy, event { message(every person) }).",
            "entitled(Lucy, event { message(every person) }).",
            "for every",
        ),
    ] {
        let session = CoreSession::new();
        session.assert_text("person(Lucy).").unwrap();
        session
            .assert_text(source)
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        let (verdict, trace) = session.query_text_with_proof(query).unwrap();
        assert_eq!(verdict, QueryResult::True, "{source}");
        for register in [Register::Spec, Register::Fluent] {
            let why = summarize_proof(&trace, register).unwrap();
            assert!(why.contains(expected), "{source}: {why}");
            assert!(!why.contains("__abs_"), "{source}: {why}");
            if !source.starts_with("entitled(Lucy") {
                assert!(why.contains("Lucy is a person"), "{source}: {why}");
            }
        }
        assert_eq!(
            session.query_text("message(Bob).").unwrap(),
            QueryResult::False
        );
    }
}

#[test]
fn event_content_keeps_each_dependent_referent_with_its_holder() {
    let session = CoreSession::new();
    session.assert_text("person(Lucy).").unwrap();
    session.assert_text("person(Bob).").unwrap();
    session
        .assert_text("entitled(every person, event { survive() }).")
        .unwrap();
    let (_, trace) = session
        .query_text_with_proof(
            "entitled(Lucy, event { survive() }) & entitled(Bob, event { survive() }).",
        )
        .unwrap();
    let why = summarize_proof(&trace, Register::Spec).unwrap();
    assert!(
        why.contains("Lucy is a person, Lucy is entitled to survive"),
        "{why}"
    );
    assert!(
        why.contains("Bob is a person, Bob is entitled to survive"),
        "{why}"
    );
    assert!(!why.contains("__abs_"), "{why}");

    // An external variable inside the opaque key has no substitution record
    // available to this renderer. Preserve its exact structural evidence.
    let open = session
        .compile_text("all $x: person($x) -> entitled($x, event { message($x) }).")
        .unwrap();
    let marker = open
        .nodes
        .iter()
        .find_map(|node| match node {
            nibli_types::logic::LogicNode::Predicate((rel, _)) if rel.starts_with("__abs_") => {
                Some(rel)
            }
            _ => None,
        })
        .unwrap();
    assert!(crate::logic::proof_event_content(marker, Register::Spec).is_none());
}

#[test]
fn event_content_fallback_preserves_malformed_missing_and_unreachable_evidence() {
    use nibli_protocol::ProofRule;
    let session = CoreSession::new();
    session.assert_text("person(Lucy).").unwrap();
    session
        .assert_text("entitled(every person, event { survive() }).")
        .unwrap();
    let (_, trace) = session
        .query_text_with_proof("entitled(Lucy, event { survive() }).")
        .unwrap();
    let marker_step = trace.steps.iter().position(|step| matches!(&step.rule, ProofRule::Derived { fact, .. } if fact.starts_with("__abs_"))).unwrap();
    let mut malformed = trace.clone();
    if let ProofRule::Derived { fact, .. } = &mut malformed.steps[marker_step].rule {
        *fact = "__abs_v1_malformed(sk_2(lucy))".into();
    }
    let fallback = render_collapsed_text(&malformed, Register::Spec, 0, false);
    assert!(
        fallback.contains("__abs_v1_malformed(sk_2(lucy))"),
        "{fallback}"
    );
    assert!(
        fallback.contains("entitled(every person, event { survive() })."),
        "{fallback}"
    );
    assert!(
        !fallback.contains("Lucy is entitled to survive"),
        "{fallback}"
    );

    let mut missing = trace.clone();
    if let ProofRule::Derived { fact, .. } = &mut missing.steps[marker_step].rule {
        *fact = fact.replace("sk_2(lucy)", "sk_999(lucy)");
    }
    let fallback = render_collapsed_text(&missing, Register::Spec, 0, false);
    assert!(fallback.contains("__abs_"), "{fallback}");
    assert!(
        !fallback.contains("Lucy is entitled to survive"),
        "{fallback}"
    );

    let mut extra = trace.clone();
    extra.steps.push(malformed.steps[marker_step].clone());
    assert_eq!(
        render_collapsed_text(&extra, Register::Spec, 0, false),
        render_collapsed_text(&trace, Register::Spec, 0, false)
    );

    // A valid marker outside the reachable proof cannot repair a missing
    // event package, even when its generated referent matches the consumer.
    let mut unreachable = missing.clone();
    unreachable.steps.push(trace.steps[marker_step].clone());
    assert_eq!(
        render_collapsed_text(&unreachable, Register::Spec, 0, false),
        render_collapsed_text(&missing, Register::Spec, 0, false)
    );

    let modified = CoreSession::new();
    modified
        .assert_text("entitled(Lucy, event { fast dog(Rex) }).")
        .unwrap();
    let (_, trace) = modified
        .query_text_with_proof("entitled(Lucy, event { fast dog(Rex) }).")
        .unwrap();
    let fallback = summarize_proof(&trace, Register::Spec).unwrap();
    assert!(fallback.contains("fast dog(Rex)"), "{fallback}");
    assert!(
        !fallback.to_lowercase().contains("rex is fast"),
        "{fallback}"
    );
}

#[test]
fn shared_modifier_reading_preserves_all_atoms_and_scope() {
    let session = CoreSession::new();
    for source in [
        "fast dog(Rex).",
        "big fast dog(Rex).",
        "blue big fast dog(Rex).",
        "[big fast] dog(Rex).",
        "fast likes(Rex, Bel).",
        "fast likes(Bel, Rex).",
        "past fast dog(Rex).",
        "fast dog(some person).",
    ] {
        let Ok(buf) = session.compile_text(source) else {
            panic!("invalid fixture {source}");
        };
        let structure = render_logic_tree(&buf, Register::Spec);
        for register in [Register::Spec, Register::Fluent] {
            let reading = render_logic_buffer(&buf, register);
            assert!(reading.contains(structure.trim()), "{source}: {reading}");
            assert!(!reading.to_lowercase().contains("rex is fast"), "{reading}");
        }
    }
    let ordinary = session.compile_text("dog(Rex). fast(Rex).").unwrap();
    let reading = render_logic_buffer(&ordinary, Register::Spec);
    assert!(!reading.contains("Structural reading"), "{reading}");
    assert!(reading.contains("Rex is fast"), "{reading}");
}

#[test]
fn modifier_proof_never_promotes_role_to_independent_predicate() {
    let session = CoreSession::new();
    session.assert_text("fast dog(Rex).").unwrap();
    assert_eq!(session.query_text("dog(Rex).").unwrap(), QueryResult::True);
    assert_eq!(
        session.query_text("fast(Rex).").unwrap(),
        QueryResult::False
    );
    let (verdict, trace) = session.query_text_with_proof("fast dog(Rex).").unwrap();
    assert_eq!(verdict, QueryResult::True);
    let collapsed = render_collapsed_text(&trace, Register::Spec, 0, false);
    let why = summarize_proof(&trace, Register::Spec).unwrap();
    for text in [&collapsed, &why] {
        assert!(text.contains("fast_x1("), "missing modifier role: {text}");
        assert!(text.contains("dog("), "missing head: {text}");
        assert!(
            !text.to_lowercase().contains("rex is fast"),
            "invented standalone predicate: {text}"
        );
    }
    println!(
        "SOURCE: fast dog(Rex).\nQUERY: fast dog(Rex).\nVERDICT: TRUE\n[English]\n{}\n[Why]\n{why}\n[Proof]\n{collapsed}",
        render_logic_buffer(
            &session.compile_text("fast dog(Rex).").unwrap(),
            Register::Spec
        )
    );
}

#[test]
fn dependent_witness_caption_quotes_recorded_source_without_changing_subject() {
    for (source, query) in [
        ("likes(every dog, some cat).", "likes(Rex, some cat)."),
        ("loves(every dog, some person).", "loves(Rex, some person)."),
    ] {
        let session = CoreSession::new();
        session.assert_text("dog(Rex).").unwrap();
        session.assert_text(source).unwrap();
        let (verdict, trace) = session.query_text_with_proof(query).unwrap();
        assert_eq!(verdict, QueryResult::True);
        let why = summarize_proof(&trace, Register::Spec).unwrap();
        let witness_type = if source.starts_with("likes") {
            "cat("
        } else {
            "person("
        };
        assert!(
            why.contains(witness_type),
            "witness restriction must survive mixed natural/structural Why: {why}"
        );
        let before = trace.clone();
        let proof = render_collapsed_text(&trace, Register::Spec, 0, false);
        assert!(proof.contains(source), "recorded source missing: {proof}");
        assert!(
            proof.contains("recorded source #1/"),
            "citation identity missing: {proof}"
        );
        assert!(!proof.contains("every dog is a cat"), "{proof}");
        assert!(!proof.contains("every dog is a person"), "{proof}");
        assert_eq!(
            format!("{trace:?}"),
            format!("{before:?}"),
            "display cannot mutate proof evidence"
        );
        println!(
            "SOURCE: dog(Rex).\nSOURCE: {source}\nQUERY: {query}\nVERDICT: TRUE\n[Why]\n{why}\n[Proof]\n{proof}"
        );
    }
}

#[test]
fn duplicate_rule_sources_remain_distinct_in_collapsed_captions() {
    let session = CoreSession::new();
    session.assert_text("dog(Rex).").unwrap();
    session.assert_text("animal(every dog).").unwrap();
    session.assert_text("animal(every dog).").unwrap();
    let (verdict, trace) = session.query_text_with_proof("animal(Rex).").unwrap();
    assert_eq!(verdict, QueryResult::True);
    let text = render_collapsed_text(&trace, Register::Spec, 0, false);
    assert!(
        text.contains("recorded source #1/0: animal(every dog)."),
        "{text}"
    );
    assert!(
        text.contains("recorded source #2/0: animal(every dog)."),
        "{text}"
    );
    assert!(
        !text.contains("every dog is an animal"),
        "source label must not be reinterpreted: {text}"
    );
}
