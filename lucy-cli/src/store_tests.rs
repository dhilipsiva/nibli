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

#[test]
fn a_bad_file_is_skipped_and_named_never_fatal() {
    let dir = tempfile::tempdir().unwrap();
    let store = Store::open(dir.path()).unwrap();
    store.record(&record("good", "a findable note")).unwrap();
    std::fs::write(dir.path().join("records/broken.json"), b"{\"origin\": ").unwrap();
    let home = dir.path().join("peer/lucy");
    std::fs::create_dir_all(&home).unwrap();
    std::fs::write(home.join("constitution.nibli"), "# Lucy\n").unwrap();
    std::fs::write(home.join("notes.md"), b"caf\xff\n").unwrap();
    std::fs::write(home.join("memory.nibli"), "bird(Enma).\n").unwrap();
    store.register("nibli", &home).unwrap();
    let sync = store.sync().unwrap();
    let skipped = sync["skipped"].to_string();
    assert!(skipped.contains("broken.json"), "{sync}");
    assert!(skipped.contains("notes.md"), "{sync}");
    assert_eq!(store.search("findable", "", 8, None).unwrap().len(), 1);
    assert_eq!(store.search("Enma", "", 8, None).unwrap().len(), 1);
}

#[test]
fn restored_peer_conversations_stay_recallable_until_the_peer_files_arrive() {
    let dir = tempfile::tempdir().unwrap();
    let host_a = Store::open(&dir.path().join("host-a")).unwrap();
    let mut private = record("p1", "a private conversation about herons");
    private.origin = "peer:nibli/private-interactions.nibli".into();
    host_a.record(&private).unwrap();
    let manifest = host_a.backup(&dir.path().join("backup")).unwrap();
    let host_b = Store::open(&dir.path().join("host-b")).unwrap();
    host_b.restore(&manifest).unwrap();
    assert_eq!(host_b.search("herons", "", 8, None).unwrap().len(), 1);
    // STORE.md's order on a new host: restore, then register the peers, whose private
    // archive is not in Git.
    let home = dir.path().join("checkout/lucy");
    std::fs::create_dir_all(&home).unwrap();
    std::fs::write(home.join("constitution.nibli"), "# Lucy\n").unwrap();
    host_b.register("nibli", &home).unwrap();
    host_b.sync().unwrap();
    assert_eq!(host_b.search("herons", "", 8, None).unwrap().len(), 1);
    // Once the peer's own file exists, it wins.
    std::fs::write(home.join("private-interactions.nibli"), "").unwrap();
    host_b.sync().unwrap();
    assert!(host_b.search("herons", "", 8, None).unwrap().is_empty());
}

#[test]
fn restored_copies_stand_in_only_until_a_local_file_has_existed() {
    let dir = tempfile::tempdir().unwrap();
    let host_a = Store::open(&dir.path().join("host-a")).unwrap();
    let mut archive = record("p1", "a private conversation about herons");
    archive.origin = "peer:nibli/private-interactions.nibli".into();
    host_a.record(&archive).unwrap();
    let mut private = record("p2", "a private fact about kingfishers");
    private.origin = "peer:nibli/private.nibli".into();
    host_a.record(&private).unwrap();
    let manifest = host_a.backup(&dir.path().join("backup")).unwrap();
    let host_b = Store::open(&dir.path().join("host-b")).unwrap();
    host_b.restore(&manifest).unwrap();
    let home = dir.path().join("checkout/lucy");
    std::fs::create_dir_all(&home).unwrap();
    std::fs::write(home.join("constitution.nibli"), "# Lucy\n").unwrap();
    host_b.register("nibli", &home).unwrap();
    host_b.sync().unwrap();
    // Every gitignored private file of the peer, not only the archives.
    assert_eq!(host_b.search("herons", "", 8, None).unwrap().len(), 1);
    assert_eq!(host_b.search("kingfishers", "", 8, None).unwrap().len(), 1);
    std::fs::write(home.join("private-interactions.nibli"), "").unwrap();
    host_b.sync().unwrap();
    assert!(host_b.search("herons", "", 8, None).unwrap().is_empty());
    // A local file has existed, so deleting it empties the origin; the snapshot does not return.
    std::fs::remove_file(home.join("private-interactions.nibli")).unwrap();
    host_b.sync().unwrap();
    assert!(host_b.search("herons", "", 8, None).unwrap().is_empty());
    assert_eq!(host_b.search("kingfishers", "", 8, None).unwrap().len(), 1);
}

#[test]
fn invalid_and_symlinked_records_are_skipped_too() {
    let dir = tempfile::tempdir().unwrap();
    let store = Store::open(dir.path()).unwrap();
    store.record(&record("good", "a findable note")).unwrap();
    let records = dir.path().join("records");
    let mut empty = serde_json::to_value(record("empty", "x")).unwrap();
    empty["payload"]["text"] = json!("");
    std::fs::write(records.join("invalid.json"), empty.to_string()).unwrap();
    let mut tool = serde_json::to_value(record("tool", "tool output")).unwrap();
    tool["payload"]["role"] = json!("tool");
    std::fs::write(records.join("tool.json"), tool.to_string()).unwrap();
    std::os::unix::fs::symlink("/etc/hostname", records.join("linked.json")).unwrap();
    let sync = store.sync().unwrap();
    let skipped = sync["skipped"].to_string();
    for name in ["invalid.json", "tool.json", "linked.json"] {
        assert!(skipped.contains(name), "{name}: {sync}");
    }
    assert_eq!(store.search("findable", "", 8, None).unwrap().len(), 1);
}

#[test]
fn restored_copies_whose_files_are_gone_leave_recall_and_conflicts_are_skipped() {
    let dir = tempfile::tempdir().unwrap();
    let host_a = Store::open(&dir.path().join("host-a")).unwrap();
    let mut private = record("p2", "a private fact about kingfishers");
    private.origin = "peer:nibli/private.nibli".into();
    host_a.record(&private).unwrap();
    let manifest = host_a.backup(&dir.path().join("backup")).unwrap();
    let root = dir.path().join("host-b");
    let host_b = Store::open(&root).unwrap();
    host_b.restore(&manifest).unwrap();
    let home = dir.path().join("checkout/lucy");
    std::fs::create_dir_all(&home).unwrap();
    std::fs::write(home.join("constitution.nibli"), "# Lucy\n").unwrap();
    host_b.register("nibli", &home).unwrap();
    host_b.sync().unwrap();
    assert_eq!(host_b.search("kingfishers", "", 8, None).unwrap().len(), 1);
    // The restored record files are removed: their copies leave recall too.
    for entry in std::fs::read_dir(root.join("records")).unwrap() {
        std::fs::remove_file(entry.unwrap().path()).unwrap();
    }
    host_b.sync().unwrap();
    assert!(
        host_b
            .search("kingfishers", "", 8, None)
            .unwrap()
            .is_empty()
    );
    // A record file that conflicts with the index is skipped and named, not fatal.
    host_b.record(&record("same", "the original text")).unwrap();
    let mut changed =
        serde_json::to_value(record("same", "edited behind the store's back")).unwrap();
    changed["payload"]["text"] = json!("edited behind the store's back");
    std::fs::write(root.join("records/edited-copy.json"), changed.to_string()).unwrap();
    let sync = host_b.sync().unwrap();
    assert!(
        sync["skipped"].to_string().contains("edited-copy.json"),
        "{sync}"
    );
}

#[test]
fn restored_copies_whose_files_vanish_before_the_first_sync_leave_recall() {
    let dir = tempfile::tempdir().unwrap();
    let host_a = Store::open(&dir.path().join("host-a")).unwrap();
    let mut private = record("p3", "a private fact about dippers");
    private.origin = "peer:nibli/private.nibli".into();
    host_a.record(&private).unwrap();
    let manifest = host_a.backup(&dir.path().join("backup")).unwrap();
    let root = dir.path().join("host-b");
    let host_b = Store::open(&root).unwrap();
    host_b.restore(&manifest).unwrap();
    for entry in std::fs::read_dir(root.join("records")).unwrap() {
        std::fs::remove_file(entry.unwrap().path()).unwrap();
    }
    let home = dir.path().join("checkout/lucy");
    std::fs::create_dir_all(&home).unwrap();
    std::fs::write(home.join("constitution.nibli"), "# Lucy\n").unwrap();
    host_b.register("nibli", &home).unwrap();
    host_b.sync().unwrap();
    host_b.sync().unwrap();
    assert!(host_b.search("dippers", "", 8, None).unwrap().is_empty());
}
