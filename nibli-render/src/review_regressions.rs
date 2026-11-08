//! End-to-end display regressions through the real compiler and proof search.
use crate::*;
use nibli_session::CoreSession;
use nibli_types::logic::QueryResult;

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
