// SPDX-License-Identifier: MIT OR Apache-2.0

use nibli_session::CoreSession;
use nibli_types::logic::QueryResult;
use std::sync::{Arc, atomic::AtomicBool};

#[test]
fn batch_preserves_root_ids_labels_verdicts_and_retraction() {
    let lines = [
        "person(Ara). person(Bel).",
        "all $x: person($x) & ~rotten($x) -> fit($x).",
        "rotten(Bel).",
    ];
    let sequential = CoreSession::new();
    let expected_ids: Vec<Vec<_>> = lines
        .iter()
        .map(|line| {
            sequential
                .assert_text(line)
                .unwrap()
                .into_iter()
                .map(|(id, _)| id)
                .collect()
        })
        .collect();
    let (batch, ids) = CoreSession::from_text_batch(&lines).unwrap();
    assert_eq!(ids, expected_ids);
    assert_eq!(
        format!("{:?}", batch.list_facts().unwrap()),
        format!("{:?}", sequential.list_facts().unwrap())
    );
    for query in ["fit(Ara).", "fit(Bel).", "person(Ara)."] {
        assert_eq!(
            batch.query_text(query).unwrap(),
            sequential.query_text(query).unwrap()
        );
    }
    batch.retract_fact(ids[2][0]).unwrap();
    assert_eq!(batch.query_text("fit(Bel).").unwrap(), QueryResult::True);
    // The bulk-only deferral cannot escape into ordinary mutation.
    assert!(batch.assert_text("all $x: fit($x) -> rotten($x).").is_err());
    assert_eq!(batch.query_text("fit(Bel).").unwrap(), QueryResult::True);
}

#[test]
fn batch_refuses_invalid_final_graph_and_preserves_declaration_order() {
    for lines in [
        vec![
            "all $x: person($x) & ~rotten($x) -> fit($x).",
            "all $x: fit($x) -> rotten($x).",
        ],
        vec!["derived_only(\"fit\").", "fit(Ara)."],
        vec!["fit(Ara).", "derived_only(\"fit\")."],
        vec!["admits(\"person\").", "animal(Ara)."],
        vec!["person(Ara).", "big(exactly 1 dog)."],
    ] {
        assert!(
            CoreSession::from_text_batch(&lines).is_err(),
            "accepted {lines:?}"
        );
    }
    let (session, _) = CoreSession::from_text_batch(&[
        "admits(\"person\").",
        "person(Ara).",
        "derived_only(\"fit\").",
        "all $x: person($x) -> fit($x).",
    ])
    .unwrap();
    assert_eq!(session.query_text("fit(Ara).").unwrap(), QueryResult::True);
}

#[test]
fn cancelled_fixture_is_never_returned() {
    let cancellation = Arc::new(AtomicBool::new(true));
    assert!(CoreSession::from_text_batch_with_cancel(&["person(Ara)."], cancellation).is_err());
}

#[test]
fn append_batch_matches_sequential_and_rolls_back_late_failure() {
    let initial = ["person(Ara).", "derived_only(\"fit\")."];
    let (batch, _) = CoreSession::from_text_batch(&initial).unwrap();
    let (sequential, _) = CoreSession::from_text_batch(&initial).unwrap();
    let lines = [
        "person(Bel). person(Cia).",
        "all $x: person($x) & ~rotten($x) -> fit($x).",
        "rotten(Bel).",
    ];
    let compiled = lines
        .iter()
        .map(|line| (batch.compile_text(line).unwrap(), (*line).to_owned()))
        .collect();
    let ids = batch.kb().assert_compiled_batch(compiled).unwrap();
    let expected: Vec<Vec<_>> = lines
        .iter()
        .map(|line| {
            sequential
                .assert_text(line)
                .unwrap()
                .into_iter()
                .map(|(id, _)| id)
                .collect()
        })
        .collect();
    assert_eq!(ids, expected);
    for query in ["fit(Ara).", "fit(Bel).", "fit(Cia)."] {
        assert_eq!(
            batch.query_text(query).unwrap(),
            sequential.query_text(query).unwrap()
        );
    }
    let before = format!("{:?}", batch.list_facts().unwrap());
    let invalid = ["person(Dee).", "fit(Dee)."];
    assert!(
        batch
            .kb()
            .assert_compiled_batch(
                invalid
                    .iter()
                    .map(|line| { (batch.compile_text(line).unwrap(), (*line).to_owned()) })
                    .collect()
            )
            .is_err()
    );
    assert_eq!(format!("{:?}", batch.list_facts().unwrap()), before);
    assert_eq!(
        batch.query_text("person(Dee).").unwrap(),
        QueryResult::False
    );
    let batch_next = batch.assert_text("person(Eve).").unwrap()[0].0;
    let sequential_next = sequential.assert_text("person(Eve).").unwrap()[0].0;
    assert_eq!(batch_next, sequential_next);
}

#[test]
fn append_batch_cancellation_preserves_the_live_registry() {
    let (session, _) = CoreSession::from_text_batch(&["person(Ara)."]).unwrap();
    let before = format!("{:?}", session.list_facts().unwrap());
    let flag = Arc::new(AtomicBool::new(true));
    session.kb().set_cancel_flag(Arc::clone(&flag));
    assert!(
        session
            .kb()
            .assert_compiled_batch(vec![(
                session.compile_text("person(Bel).").unwrap(),
                "person(Bel).".into()
            ),])
            .is_err()
    );
    flag.store(false, std::sync::atomic::Ordering::Relaxed);
    assert_eq!(format!("{:?}", session.list_facts().unwrap()), before);
    assert_eq!(
        session.query_text("person(Bel).").unwrap(),
        QueryResult::False
    );
}
