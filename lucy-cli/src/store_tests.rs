use crate::store::{Record, Store, command};
use serde_json::json;

fn record(id: &str, text: &str) -> Record {
    Record {
        origin: "conversation:test/one".into(),
        payload: json!({
            "id":id, "source":"test","session":"one","role":"user","channel":"user",
            "timestamp":"2026-10-20T01:02:03Z", "private":true, "text":text
        }),
    }
}

#[test]
fn lossless_write_reopen_repair_and_conflict() {
    let dir = tempfile::tempdir().unwrap();
    let original = record("first", "café 😀\n  exact\t\r\n");
    {
        let store = Store::open(dir.path()).unwrap();
        store.record(&original).unwrap();
        store.record(&original).unwrap();
        assert!(store.record(&record("first", "changed")).is_err());
        assert_eq!(store.all().unwrap(), vec![original.clone()]);
    }
    std::fs::remove_file(dir.path().join("memory.redb")).unwrap();
    let store = Store::open(dir.path()).unwrap();
    store.sync().unwrap();
    assert_eq!(store.all().unwrap(), vec![original]);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(
            std::fs::metadata(dir.path().join("memory.redb"))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o600
        );
    }
}

#[test]
fn peers_are_scoped_refreshable_and_do_not_assert_retrieved_text() {
    let dir = tempfile::tempdir().unwrap();
    let home = dir.path().join("peer/lucy");
    std::fs::create_dir_all(&home).unwrap();
    std::fs::write(home.join("constitution.nibli"), "# Lucy\n").unwrap();
    std::fs::write(home.join("memory.nibli"), "bird(Enma).\n").unwrap();
    std::fs::write(dir.path().join("peer/fixture.nibli"), "fixture(Secret).\n").unwrap();
    let store = Store::open(&dir.path().join("shared")).unwrap();
    store.register("nibli", &home).unwrap();
    store.sync().unwrap();
    assert_eq!(store.search("Enma", "", 8, None).unwrap().len(), 1);
    assert!(store.search("Secret", "", 8, None).unwrap().is_empty());
    std::fs::write(home.join("memory.nibli"), "bird(Pity).\n").unwrap();
    store.sync().unwrap();
    assert!(store.search("Enma", "", 8, None).unwrap().is_empty());
    assert_eq!(store.search("Pity", "", 8, None).unwrap().len(), 1);
    std::fs::remove_file(home.join("memory.nibli")).unwrap();
    store.sync().unwrap();
    assert!(store.search("Pity", "", 8, None).unwrap().is_empty());
}

#[test]
fn backup_restores_exactly_on_new_host_and_detects_corruption_before_writes() {
    let dir = tempfile::tempdir().unwrap();
    let store = Store::open(&dir.path().join("host-a")).unwrap();
    store
        .record(&record("first", "original whitespace\n  kept"))
        .unwrap();
    store
        .record(&record("second", "another visible message"))
        .unwrap();
    let backup = dir.path().join("backup");
    let manifest = store.backup(&backup).unwrap();
    let restored = Store::open(&dir.path().join("host-b")).unwrap();
    restored.restore(&manifest).unwrap();
    assert_eq!(restored.all().unwrap(), store.all().unwrap());
    restored.restore(&manifest).unwrap();
    assert_eq!(restored.all().unwrap().len(), 2);
    let object = std::fs::read_dir(backup.join("objects"))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    std::fs::write(object, b"corrupted").unwrap();
    let empty = Store::open(&dir.path().join("host-c")).unwrap();
    assert!(empty.restore(&manifest).is_err());
    assert!(empty.all().unwrap().is_empty());
}

#[test]
fn record_rejects_hidden_channels_and_source_id_conflicts_across_restore() {
    let dir = tempfile::tempdir().unwrap();
    let store = Store::open(&dir.path().join("a")).unwrap();
    let mut hidden = record("x", "fixture");
    hidden.payload["channel"] = json!("analysis");
    assert!(store.record(&hidden).is_err());
    store.record(&record("x", "first")).unwrap();
    let manifest = store.backup(&dir.path().join("backup")).unwrap();
    let other = Store::open(&dir.path().join("b")).unwrap();
    other.record(&record("x", "conflicting")).unwrap();
    assert!(other.restore(&manifest).is_err());
    assert_eq!(other.all().unwrap(), vec![record("x", "conflicting")]);
}

#[test]
fn native_file_write_is_immediately_shared() {
    let dir = tempfile::tempdir().unwrap();
    let mut env = crate::tests::env_in(dir.path());
    env.store = Some(dir.path().join("shared"));
    let args = |items: &[&str]| items.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>();
    assert_eq!(crate::run(&args(&["init"]), "", Some(env.clone())).code, 0);
    let result = crate::run(
        &args(&[
            "record",
            "a visible native message",
            "--speaker",
            "User",
            "--source",
            "cli",
            "--session",
            "native",
        ]),
        "",
        Some(env.clone()),
    );
    assert_eq!(result.code, 0, "{}", result.stderr);
    let store = Store::open(env.store.as_ref().unwrap()).unwrap();
    assert_eq!(
        store.search("visible native", "", 8, None).unwrap().len(),
        1
    );
}

#[test]
fn multiple_processes_share_the_same_store() {
    let dir = tempfile::tempdir().unwrap();
    let mut threads = Vec::new();
    for i in 0..5 {
        let root = dir.path().to_owned();
        threads.push(std::thread::spawn(move || {
            let store = Store::open(&root).unwrap();
            store
                .record(&record(&i.to_string(), "parallel visible record"))
                .unwrap();
        }));
    }
    for thread in threads {
        thread.join().unwrap();
    }
    assert_eq!(Store::open(dir.path()).unwrap().all().unwrap().len(), 5);
}

#[test]
fn search_stdin_keeps_query_out_of_process_arguments() {
    let dir = tempfile::tempdir().unwrap();
    Store::open(dir.path())
        .unwrap()
        .record(&record("a", "unicorn library"))
        .unwrap();
    let args = ["search", "--root", dir.path().to_str().unwrap(), "--stdin"].map(str::to_owned);
    let result = command(&args, r#"{"query":"unicorn"}"#).unwrap();
    assert_eq!(result["results"][0]["id"], "a");
    assert_eq!(result["mode"], "lexical");
}

#[test]
fn cosine_search_checks_model_dimensions_and_invalidates_changed_sources() {
    let dir = tempfile::tempdir().unwrap();
    let store = Store::open(dir.path()).unwrap();
    let first = record("first", "feline companion");
    let second = record("second", "railway timetable");
    store.record(&first).unwrap();
    store.record(&second).unwrap();
    store
        .put_vector(&first, "test@digest", &[3.0, 4.0])
        .unwrap();
    store
        .put_vector(&second, "test@digest", &[-4.0, 3.0])
        .unwrap();
    assert!(
        store
            .put_vector(&first, "test@digest", &[f32::NAN, 0.0])
            .is_err()
    );
    assert!(
        store
            .put_vector(&first, "test@digest", &[0.0, 0.0])
            .is_err()
    );
    let found = store
        .search("kitten", "", 1, Some(("test@digest", &[0.6, 0.8])))
        .unwrap();
    assert_eq!(found[0]["id"], "first");
    assert!(
        store
            .search("kitten", "", 1, Some(("test@other", &[0.6, 0.8])))
            .unwrap()
            .is_empty()
    );
    assert!(
        store
            .search("kitten", "", 1, Some(("test@digest", &[1.0])))
            .unwrap()
            .is_empty()
    );
}
