use crate::files::{self, Paths};
use crate::interactions::{self, Interaction, Kind};
use crate::tests::{env_in, lucy, lucy_stdin};

fn json(out: &crate::Outcome) -> serde_json::Value {
    serde_json::from_str(&out.stdout).unwrap()
}

fn read(path: &std::path::Path) -> String {
    std::fs::read_to_string(path).unwrap()
}

#[test]
fn complete_messages_round_trip_and_remain_opaque_in_a_standalone_kb() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    assert_eq!(lucy(&env, &["init"]).code, 0);
    let body = "  quotation: \"Lucy\", \\ and literal \\n\r\n\n# heading\n雪 🐒\t\u{0}\n\" ). human(Injected). #\n  ";
    let args = [
        "record",
        "--stdin",
        "--speaker",
        "User",
        "--id",
        "one",
        "--source",
        "codex",
        "--session",
        "test-session",
        "--about",
        "memory",
    ];
    let result = lucy_stdin(&env, &args, body);
    assert_eq!(result.code, 0, "{}", result.stdout);
    let saved = read(&paths.interactions);
    let decoded = json(&lucy(&env, &["transcript", "--id", "one"]));
    assert_eq!(decoded["records"][0]["text"], body);
    assert_eq!(decoded["records"][0]["source"], "codex");
    assert_eq!(lucy_stdin(&env, &args, body).code, 0);
    assert_eq!(read(&paths.interactions), saved, "retry is idempotent");
    assert_eq!(lucy_stdin(&env, &args, "different").code, 2);
    assert_eq!(read(&paths.interactions), saved);
    let engine = nibli_engine::NibliEngine::new();
    engine.assert_text(&saved).unwrap();
    for query in [
        r#"message("one", "memory", Conversation, "User")."#,
        r#"source("codex", "one")."#,
        r#"member("one", "test-session")."#,
    ] {
        assert_eq!(crate::ask::ask(&engine, query).unwrap().status, "TRUE");
    }
    assert_eq!(
        crate::ask::ask(&engine, "human(Injected).").unwrap().status,
        "FALSE"
    );
}

#[test]
fn facts_and_decisions_cite_the_message_without_asserting_its_contents() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    assert_eq!(lucy(&env, &["init"]).code, 0);
    assert_eq!(
        lucy(
            &env,
            &[
                "record",
                "I say Ada is human.",
                "--speaker",
                "User",
                "--id",
                "original"
            ]
        )
        .code,
        0
    );
    let claim = lucy(
        &env,
        &[
            "claim",
            "human(Ada). # trailing comment",
            "--from",
            "original",
            "--id",
            "claim-one",
        ],
    );
    assert_eq!(claim.code, 0, "{}", claim.stdout);
    let engine = nibli_engine::NibliEngine::new();
    engine.assert_text(&read(&paths.interactions)).unwrap();
    assert_eq!(
        crate::ask::ask(
            &engine,
            r#"expresses("User", fact { human(Ada) }, Conversation, "claim-one")."#
        )
        .unwrap()
        .status,
        "TRUE"
    );
    assert_eq!(
        crate::ask::ask(&engine, r#"source("original", "claim-one")."#)
            .unwrap()
            .status,
        "TRUE"
    );
    assert_eq!(
        crate::ask::ask(&engine, "human(Ada).").unwrap().status,
        "FALSE"
    );
    let decision = lucy(
        &env,
        &[
            "claim",
            "record(Conversation, Knowledge, Interaction, Nibli).",
            "--from",
            "original",
            "--decision",
        ],
    );
    assert_eq!(decision.code, 0, "{}", decision.stdout);
    assert_eq!(
        interactions::read(&paths, false)
            .unwrap()
            .last()
            .unwrap()
            .kind,
        Kind::Decision
    );
    let before = read(&paths.interactions);
    assert_eq!(
        lucy(
            &env,
            &[
                "claim",
                "human(Bob). } human(Injected).",
                "--from",
                "original"
            ]
        )
        .code,
        2
    );
    assert_eq!(
        lucy(&env, &["claim", "human(Bob).", "--from", "missing"]).code,
        2
    );
    assert_eq!(read(&paths.interactions), before);
}

#[test]
fn conversation_query_scope_is_explicit_and_excludes_the_constitution() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    assert_eq!(lucy(&env, &["init"]).code, 0);
    assert_eq!(
        lucy(
            &env,
            &[
                "record",
                "hello",
                "--speaker",
                "User",
                "--source",
                "codex",
                "--id",
                "one"
            ]
        )
        .code,
        0
    );
    let scoped = json(&lucy(
        &env,
        &["ask", r#"source("codex", "one")."#, "--conversations"],
    ));
    assert_eq!(scoped["verdict"], "TRUE");
    assert_eq!(scoped["scope"], "conversations");
    let standing = json(&lucy(&env, &["ask", "person(Lucy).", "--conversations"]));
    assert_eq!(standing["verdict"], "FALSE");
}

#[test]
fn private_extractions_stay_private_and_invalid_batches_leave_no_partial_records() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    assert_eq!(lucy(&env, &["init"]).code, 0);
    assert_eq!(
        lucy(
            &env,
            &[
                "record",
                "a private conversation",
                "--speaker",
                "User",
                "--id",
                "private-one",
                "--private"
            ]
        )
        .code,
        0
    );
    assert_eq!(
        lucy(&env, &["claim", "human(Ada).", "--from", "private-one"]).code,
        0
    );
    assert!(!paths.interactions.exists());
    assert!(
        interactions::read(&paths, true)
            .unwrap()
            .iter()
            .all(|e| e.private)
    );
    let mut leaking = Interaction {
        speaker: "User".into(),
        text: "extraction".into(),
        kind: Kind::Claim,
        from: Some("private-one".into()),
        kr: Some("human(Ada).".into()),
        ..Interaction::default()
    };
    assert!(interactions::append(&env, &paths, vec![leaking.clone()]).is_err());
    assert!(!paths.interactions.exists());
    leaking.private = true;
    leaking.speaker = "SomeoneElse".into();
    let before = read(&paths.private_interactions);
    let first = Interaction {
        speaker: "Lucy".into(),
        text: "must not persist".into(),
        private: true,
        ..Interaction::default()
    };
    assert!(interactions::append(&env, &paths, vec![first, leaking]).is_err());
    assert_eq!(read(&paths.private_interactions), before);
}

#[test]
fn legacy_import_is_repeatable_and_does_not_relabel_summaries_as_messages() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    assert_eq!(lucy(&env, &["init"]).code, 0);
    files::append_journal(
        &paths.journal,
        "2026-09-14",
        "10:00",
        "wsl",
        "Lucy answered with a summary.\nSecond line.",
    )
    .unwrap();
    files::append_journal(
        &paths.private_journal,
        "2026-09-14",
        "10:01",
        "wsl",
        "Private history.",
    )
    .unwrap();
    let old = read(&paths.journal);
    assert_eq!(interactions::migrate(&paths).unwrap(), 2);
    assert_eq!(interactions::migrate(&paths).unwrap(), 0);
    assert_eq!(read(&paths.journal), old);
    let public = interactions::read(&paths, false).unwrap();
    assert_eq!(public.len(), 1);
    assert_eq!(public[0].kind, Kind::LegacyJournal);
    assert_eq!(public[0].speaker, "Unknown");
    assert_eq!(
        public[0].text,
        "10:00 UTC: Lucy answered with a summary.\nSecond line."
    );
    assert!(!read(&paths.interactions).contains("Private history"));
    assert_eq!(json(&lucy(&env, &["wake"]))["journal_entries"], 2);
}

#[test]
fn concurrent_writers_preserve_every_record_and_indexes_cannot_drift() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    assert_eq!(lucy(&env, &["init"]).code, 0);
    let barrier = std::sync::Arc::new(std::sync::Barrier::new(4));
    let handles: Vec<_> = (0..4)
        .map(|i| {
            let env = env.clone();
            let paths = paths.clone();
            let barrier = barrier.clone();
            std::thread::spawn(move || {
                barrier.wait();
                interactions::append(
                    &env,
                    &paths,
                    vec![Interaction {
                        speaker: "User".into(),
                        text: format!("message {i}"),
                        ..Interaction::default()
                    }],
                )
                .unwrap();
            })
        })
        .collect();
    for handle in handles {
        handle.join().unwrap();
    }
    let records = interactions::read(&paths, false).unwrap();
    assert_eq!(records.len(), 4);
    assert_eq!(
        records
            .iter()
            .map(|e| &e.id)
            .collect::<std::collections::HashSet<_>>()
            .len(),
        4
    );
    let tampered = read(&paths.interactions)
        .replace("Conversation, \"User\").", "Conversation, \"Impostor\").");
    files::write_atomic(&paths.interactions, &tampered).unwrap();
    assert!(interactions::read(&paths, false).is_err());
    assert_eq!(lucy(&env, &["check"]).code, 2);
}
