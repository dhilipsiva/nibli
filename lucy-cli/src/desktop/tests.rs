use super::{Service, actions, core, net, providers, read_frame};
use crate::store::Store;
use serde_json::{Value, json};
use std::{
    io::{BufRead, BufReader, Read, Write},
    net::TcpListener,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
    time::{Duration, Instant},
};

fn request(client: &Value, values: Value) -> Value {
    let mut output = client.clone();
    output
        .as_object_mut()
        .unwrap()
        .extend(values.as_object().unwrap().clone());
    output
}

fn prompt(
    service: &Service,
    workspace: &std::path::Path,
    source: &str,
    id: &str,
    text: &str,
) -> Value {
    service
        .dispatch(json!({"op":"prompt","source":source,"session":id,
        "workspace":workspace,"text":text,"event":format!("{id}-{text}")}))
        .unwrap()
}

#[test]
fn opening_and_unaddressed_prompts_do_not_load_memory() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().join("memory");
    let service = Service::new(root.clone(), None);
    service.dispatch(json!({"op":"open"})).unwrap();
    assert!(!root.exists());
    assert_eq!(
        prompt(&service, temp.path(), "codex", "one", "look at Lucy's file")["active"],
        false
    );
    assert!(!root.exists());
    for text in ["Lucy, wake", "Hey Lucy!", "/lucy hello", "@Lucy: hello"] {
        assert!(core::addressed(text));
    }
    for text in ["I told Lucy", "LucyTools", "/lucy-example", "lucy.rs"] {
        assert!(!core::addressed(text));
    }
}

#[test]
fn active_clients_share_exact_visible_records_and_sleep_is_scoped() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().join("memory");
    let service = Service::new(root.clone(), None);
    prompt(
        &service,
        temp.path(),
        "codex",
        "one",
        "Lucy, preserve the brass compass.",
    );
    let record = json!({"op":"record","source":"codex","session":"one",
        "event":"reply","channel":"commentary","text":"First line.\nSecond line — intact."});
    service.dispatch(record.clone()).unwrap();
    service.dispatch(record).unwrap();
    let second = prompt(
        &service,
        temp.path(),
        "claude",
        "two",
        "Lucy, recall the brass compass.",
    );
    assert!(second["memories"].as_array().unwrap().iter().any(|m| {
        m["excerpt"]
            .as_str()
            .unwrap_or("")
            .contains("brass compass")
    }));
    service
        .dispatch(json!({"op":"sleep","source":"codex","session":"one"}))
        .unwrap();
    assert!(
        service
            .dispatch(json!({"op":"recall","source":"codex","session":"one","query":"compass"}))
            .is_err()
    );
    assert!(
        service
            .dispatch(json!({"op":"recall","source":"claude","session":"two","query":"compass"}))
            .is_ok()
    );
    let records = Store::open(&root).unwrap().all().unwrap();
    let replies: Vec<_> = records
        .iter()
        .filter(|r| r.payload["role"] == "assistant")
        .collect();
    assert_eq!(replies.len(), 1);
    assert_eq!(
        replies[0].payload["text"],
        "First line.\nSecond line — intact."
    );
    assert_eq!(replies[0].payload["channel"], "commentary");
    assert_eq!(replies[0].payload["private"], true);
}

#[test]
fn legacy_sqlite_payloads_migrate_losslessly_once() {
    let temp = tempfile::tempdir().unwrap();
    let sqlite = temp.path().join("conversations.sqlite3");
    let original = json!({"id":"original","source":"desktop","session":"s","role":"user",
        "text":"Exact\noriginal","timestamp":"2026-09-01T15:43:21.123456+00:00",
        "private":true,"metadata":{"original_id":"provider-42"}});
    {
        let db = rusqlite::Connection::open(&sqlite).unwrap();
        db.execute("CREATE TABLE messages (payload TEXT NOT NULL)", [])
            .unwrap();
        db.execute(
            "INSERT INTO messages (payload) VALUES (?1)",
            [original.to_string()],
        )
        .unwrap();
    }
    let bytes = std::fs::read(&sqlite).unwrap();
    let store = Store::open(temp.path()).unwrap();
    assert_eq!(store.migrate_sqlite().unwrap(), 1);
    assert_eq!(store.migrate_sqlite().unwrap(), 0);
    assert_eq!(store.all().unwrap()[0].payload, original);
    assert_eq!(std::fs::read(sqlite).unwrap(), bytes);
}

#[test]
fn hidden_channels_and_nonvisible_roles_are_rejected() {
    let temp = tempfile::tempdir().unwrap();
    let store = Store::open(temp.path()).unwrap();
    for channel in ["analysis", "reasoning", "thinking"] {
        assert!(
            store
                .message(json!({"id":channel,"source":"test","session":"one",
            "role":"assistant","channel":channel,"text":"not visible"}))
                .is_err()
        );
    }
    for role in ["system", "developer", "tool"] {
        assert!(
            store
                .message(json!({"id":role,"source":"test","session":"one",
            "role":role,"text":"not a visible exchange"}))
                .is_err()
        );
    }
    assert!(store.all().unwrap().is_empty());
}

#[test]
fn agent_reads_then_returns_visible_response_without_provider_internals() {
    let temp = tempfile::tempdir().unwrap();
    std::fs::write(temp.path().join("note.txt"), "a small note").unwrap();
    let root = temp.path().join("memory");
    let service = Service::new(root.clone(), None);
    service.scripted(vec![
        json!({"content":"","tool_calls":[{"id":"call-1","type":"function","function":{"name":"read","arguments":"{\"path\":\"note.txt\"}"}}],"reasoning":"provider internals"}),
        json!({"content":"The note says: a small note.","thinking":"provider internals"}),
    ]);
    let client = service.dispatch(json!({"op":"open"})).unwrap();
    let reply = service
        .dispatch(request(
            &client,
            json!({"op":"chat","text":"Read note.txt",
        "event":"read","workspace":temp.path()}),
        ))
        .unwrap();
    assert_eq!(reply["text"], "The note says: a small note.");
    let records = Store::open(&root).unwrap().all().unwrap();
    assert_eq!(records.len(), 2);
    assert!(!json!(records).to_string().contains("provider internals"));
}

#[test]
fn agent_write_needs_the_exact_ui_approval_and_can_only_run_once() {
    let temp = tempfile::tempdir().unwrap();
    let service = Service::new(temp.path().join("memory"), None);
    service.scripted(vec![
        json!({"content":"I can write that.","tool_calls":[{"id":"call-1","type":"function",
            "function":{"name":"write","arguments":{"path":"out.txt","text":"approved content"}}}]}),
        json!({"content":"Saved."}),
    ]);
    let client = service.dispatch(json!({"op":"open"})).unwrap();
    let reply = service
        .dispatch(request(
            &client,
            json!({"op":"chat","text":"Write a note",
        "event":"write","workspace":temp.path()}),
        ))
        .unwrap();
    let (id, preview) = reply["pending"].as_object().unwrap().iter().next().unwrap();
    assert!(preview.get("before").is_none());
    assert_eq!(preview["diff"]["after"], "approved content");
    assert!(!temp.path().join("out.txt").exists());
    let approval = request(&client, json!({"op":"approve","action":id,"allow":true}));
    let mut fake = approval.clone();
    fake["control"] = json!("model-supplied");
    assert!(service.dispatch(fake).is_err());
    assert!(!temp.path().join("out.txt").exists());
    assert_eq!(
        service.dispatch(approval.clone()).unwrap()["text"],
        "Saved."
    );
    assert_eq!(
        std::fs::read_to_string(temp.path().join("out.txt")).unwrap(),
        "approved content"
    );
    assert!(service.dispatch(approval).is_err());
}

#[test]
fn changed_files_and_cancelled_actions_cannot_use_stale_approvals() {
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("note");
    std::fs::write(&path, "old").unwrap();
    let args = json!({"path":"note","text":"replacement"});
    let preview = actions::preview(temp.path(), "write", args.clone()).unwrap();
    std::fs::write(&path, "user's change").unwrap();
    assert!(
        actions::execute(
            temp.path(),
            &AtomicBool::new(false),
            "write",
            &args,
            preview.get("before")
        )
        .is_err()
    );
    assert_eq!(std::fs::read_to_string(path).unwrap(), "user's change");
    let service = Service::new(temp.path().join("memory"), None);
    let client = service.dispatch(json!({"op":"open"})).unwrap();
    service
        .dispatch(request(
            &client,
            json!({"op":"begin-archive","workspace":temp.path()}),
        ))
        .unwrap();
    let pending = service
        .dispatch(request(
            &client,
            json!({"op":"tool","name":"write","arguments":args}),
        ))
        .unwrap();
    service
        .dispatch(request(&client, json!({"op":"cancel"})))
        .unwrap();
    assert!(
        service
            .dispatch(request(
                &client,
                json!({"op":"approve","allow":true,
        "action":pending["pending_action"],"continue":false})
            ))
            .is_err()
    );
}

#[test]
fn paths_cannot_escape_through_parent_components_or_symlinks() {
    let temp = tempfile::tempdir().unwrap();
    let workspace = temp.path().join("workspace");
    std::fs::create_dir(&workspace).unwrap();
    std::os::unix::fs::symlink(temp.path(), workspace.join("escape")).unwrap();
    for path in [
        "../secret",
        "escape/secret",
        ".env",
        ".config/key",
        ".git/config",
    ] {
        assert!(actions::path(&workspace, path, false).is_err(), "{path}");
    }
    assert_eq!(
        actions::path(&workspace, "sub/../note", false).unwrap(),
        workspace.join("note")
    );
}

#[test]
fn network_and_mutating_tools_are_always_proposals() {
    for (name, args) in [
        ("http", json!({"method":"GET","url":"http://127.0.0.1"})),
        ("command", json!({"argv":["true"]})),
        ("write", json!({"path":"note","text":"x"})),
        ("service", json!({"operation":"restart","name":"example"})),
        ("window", json!({"action":"close","address":"0x1"})),
    ] {
        assert!(actions::needs_approval(name, &args).unwrap());
    }
    assert!(!actions::needs_approval("service", &json!({"operation":"status"})).unwrap());
    assert!(actions::needs_approval("approve", &json!({})).is_err());
}

fn server(
    status: &str,
    body: String,
    delay: Duration,
) -> (String, mpsc::Receiver<Value>, std::thread::JoinHandle<()>) {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let endpoint = format!("http://{}", listener.local_addr().unwrap());
    let status = status.to_string();
    let (tx, rx) = mpsc::channel();
    let thread = std::thread::spawn(move || {
        let (mut stream, _) = listener.accept().unwrap();
        stream
            .set_read_timeout(Some(Duration::from_secs(5)))
            .unwrap();
        let mut reader = BufReader::new(stream.try_clone().unwrap());
        let mut headers = Vec::new();
        let mut length = 0;
        loop {
            let mut line = String::new();
            reader.read_line(&mut line).unwrap();
            if line == "\r\n" || line.is_empty() {
                break;
            }
            if let Some(value) = line.to_lowercase().strip_prefix("content-length:") {
                length = value.trim().parse::<usize>().unwrap();
            }
            headers.push(line.trim().to_string());
        }
        let mut bytes = vec![0; length];
        reader.read_exact(&mut bytes).unwrap();
        tx.send(json!({"headers":headers,"body":serde_json::from_slice::<Value>(&bytes).unwrap_or(Value::Null)})).unwrap();
        std::thread::sleep(delay);
        let _ = write!(
            stream,
            "HTTP/1.1 {status}\r\nContent-Length: {}\r\nRetry-After: 7\r\nConnection: close\r\n\r\n{body}",
            body.len()
        );
    });
    (endpoint, rx, thread)
}

#[test]
fn hosted_transport_preserves_tool_ids_and_omits_local_only_image_fields() {
    let (endpoint, received, worker) = server(
        "200 OK",
        json!({"choices":[{"message":{"content":null,"tool_calls":[{"id":"call-42",
            "type":"function","function":{"name":"list","arguments":"{}"}}]}}]})
        .to_string(),
        Duration::ZERO,
    );
    let provider = providers::Provider {
        name: "test".into(),
        endpoint,
        model: "test-free".into(),
        key_env: "unused".into(),
    };
    let response = providers::complete(
        &provider,
        "fixture-key",
        &[json!({"role":"user","content":"image","images":["YWJj"]})],
        actions::schemas(),
        &AtomicBool::new(false),
    )
    .unwrap();
    assert_eq!(response["tool_calls"][0]["id"], "call-42");
    let request = received.recv().unwrap();
    assert!(request["headers"].as_array().unwrap().iter().any(|s| {
        s.as_str()
            .unwrap()
            .eq_ignore_ascii_case("authorization: Bearer fixture-key")
    }));
    assert!(request["body"]["messages"][0].get("images").is_none());
    assert_eq!(
        request["body"]["messages"][0]["content"][1]["type"],
        "image_url"
    );
    worker.join().unwrap();
}

#[test]
fn rate_limits_are_returned_without_fallback_or_leaking_provider_bodies() {
    let (endpoint, received, worker) = server(
        "429 Too Many Requests",
        "sensitive provider body".into(),
        Duration::ZERO,
    );
    let provider = providers::Provider {
        name: "test".into(),
        endpoint,
        model: "free".into(),
        key_env: "unused".into(),
    };
    let error = providers::complete(
        &provider,
        "fixture-key",
        &[],
        json!([]),
        &AtomicBool::new(false),
    )
    .unwrap_err();
    assert!(error.contains("429") && error.contains("Retry-After: 7"));
    assert!(!error.contains("sensitive provider body") && !error.contains("fixture-key"));
    received.recv().unwrap();
    worker.join().unwrap();
}

#[test]
fn network_reads_are_cancellable_and_size_bounded() {
    let (endpoint, received, worker) =
        server("200 OK", "late response".into(), Duration::from_millis(400));
    let cancelled = Arc::new(AtomicBool::new(false));
    let signal = cancelled.clone();
    let trigger = std::thread::spawn(move || {
        received.recv().unwrap();
        signal.store(true, Ordering::SeqCst);
    });
    let before = Instant::now();
    let result = net::request("GET", &endpoint, &[], None, &cancelled, 5, 100);
    assert!(result.unwrap_err().to_lowercase().contains("cancel"));
    assert!(before.elapsed() < Duration::from_millis(350));
    trigger.join().unwrap();
    worker.join().unwrap();
    let (endpoint, received, worker) = server("200 OK", "too much data".into(), Duration::ZERO);
    assert!(
        net::request("GET", &endpoint, &[], None, &AtomicBool::new(false), 5, 4)
            .unwrap_err()
            .contains("size limit")
    );
    received.recv().unwrap();
    worker.join().unwrap();
}

#[test]
fn cancellation_stops_command_process_groups() {
    let temp = tempfile::tempdir().unwrap();
    let cancel = Arc::new(AtomicBool::new(false));
    let signal = cancel.clone();
    let trigger = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_millis(100));
        signal.store(true, Ordering::SeqCst);
    });
    let now = Instant::now();
    assert!(
        actions::run(
            temp.path(),
            &cancel,
            &["sh".into(), "-c".into(), "sleep 10 & wait".into()],
            false,
            15
        )
        .is_err()
    );
    assert!(now.elapsed() < Duration::from_secs(2));
    trigger.join().unwrap();
}

#[test]
fn framing_requires_complete_bounded_json_lines() {
    assert_eq!(
        read_frame(&mut BufReader::new(b"{\"op\":\"status\"}\n".as_slice())).unwrap()["op"],
        "status"
    );
    assert!(read_frame(&mut BufReader::new(b"{\"op\":\"status\"}".as_slice())).is_err());
    assert!(
        read_frame(&mut BufReader::new(
            vec![b'x'; super::MAX_FRAME + 2].as_slice()
        ))
        .is_err()
    );
}

#[test]
fn a_registered_extension_with_missing_files_is_not_an_intact_installation() {
    let temp = tempfile::tempdir().unwrap();
    assert!(!super::adapters::installed_extension_matches(temp.path()));
    std::fs::write(
        temp.path().join("package.json"),
        include_bytes!("../../desktop/adapters/vscode/package.json"),
    )
    .unwrap();
    assert!(!super::adapters::installed_extension_matches(temp.path()));
    std::fs::write(
        temp.path().join("extension.js"),
        include_bytes!("../../desktop/adapters/vscode/extension.js"),
    )
    .unwrap();
    assert!(super::adapters::installed_extension_matches(temp.path()));
    std::fs::write(temp.path().join("extension.js"), "stale adapter").unwrap();
    assert!(!super::adapters::installed_extension_matches(temp.path()));
}

#[test]
fn terminal_text_cannot_carry_control_or_bidi_sequences() {
    let shown = super::visible(
        "ok\x1b[1;1r\x1b[8mApprove? [y/N]\u{9b}2J\u{202e}gnp.exe\u{2066}\u{7f}\ttab\nline\r",
    );
    assert!(
        !shown
            .chars()
            .any(|c| (c.is_control() && c != '\n' && c != '\t')
                || ('\u{202a}'..='\u{202e}').contains(&c)
                || ('\u{2066}'..='\u{2069}').contains(&c))
    );
    assert!(shown.contains("ok\\u{1b}[1;1r"));
    assert!(shown.contains("\\u{202e}gnp.exe"));
    assert!(shown.ends_with("\ttab\nline\\u{d}"));
}

#[test]
fn the_terminal_approval_screen_shows_model_text_and_proposals_inertly() {
    let proposal = json!({"tool":"http","arguments":{"method":"POST",
        "url":"https://example.test/\u{202e}fdp.exe","body":{"note":"\u{9b}2J"}}});
    let screen = super::screen(Some("Done.\x1b[2J\x1b[8m"), Some(&proposal)).unwrap();
    assert!(screen.starts_with("Lucy: Done.\\u{1b}[2J"));
    assert!(screen.contains("\\u{202e}fdp.exe"));
    assert!(!screen.contains('\x1b') && !screen.contains('\u{202e}') && !screen.contains('\u{9b}'));
    assert_eq!(super::screen(None, None).unwrap(), "");
}

#[test]
fn approvals_are_read_only_from_a_flushed_terminal() {
    let order = std::cell::RefCell::new(Vec::new());
    let answer = |terminal: bool, typed: &str| {
        order.borrow_mut().clear();
        super::read_approval(
            terminal,
            || {
                order.borrow_mut().push("flush");
                Ok(())
            },
            || {
                order.borrow_mut().push("read");
                Ok(typed.to_owned())
            },
        )
        .unwrap()
    };
    assert!(answer(true, "y\n"));
    assert_eq!(*order.borrow(), ["flush", "read"]);
    assert!(answer(true, " Y \n"));
    for typed in ["\n", "n\n", "yes\n", "yy\n", ""] {
        assert!(!answer(true, typed), "{typed:?}");
    }
    // Piped input is not a person at the prompt: deny without reading it.
    assert!(!answer(false, "y\n"));
    assert!(order.borrow().is_empty());
}

#[test]
fn synthetic_input_is_shown_by_name_and_cannot_submit_a_line() {
    let temp = tempfile::tempdir().unwrap();
    let preview = |argv: Value| actions::preview(temp.path(), "gui", json!({"argv":argv}));
    let shown = preview(json!([
        "key", "42:1", "21:1", "21:0", "42:0", "63:1", "63:0", "103:1", "103:0"
    ]))
    .unwrap();
    assert_eq!(
        shown["keys"],
        json!([
            "LEFTSHIFT down",
            "Y down",
            "Y up",
            "LEFTSHIFT up",
            "F5 down",
            "F5 up",
            "UP down",
            "UP up"
        ])
    );
    assert!(preview(json!(["type", "--", "hello"])).is_ok());
    for click in ["0xC0", "0xC1"] {
        assert!(preview(json!(["click", click])).is_ok(), "{click}");
    }
    for argv in [
        // Only listed keys: no paste (Shift+Insert), Compose, power or sleep keys,
        // mouse buttons pressed as keys, or codes the approver cannot read.
        json!(["key", "42:1", "110:1", "110:0", "42:0"]),
        json!(["key", "127:1", "127:0"]),
        json!(["key", "116:1", "116:0"]),
        json!(["key", "142:1", "142:0"]),
        json!(["key", "274:1", "274:0"]),
        json!(["key", "200:1", "200:0"]),
        // Only a full left or right click: no button left down, no middle-click paste.
        json!(["click", "0x40"]),
        json!(["click", "0x80"]),
        json!(["click", "0xC2"]),
        // Enter, keypad Enter, Linefeed.
        json!(["key", "21:1", "21:0", "28:1", "28:0"]),
        json!(["key", "96:1", "96:0"]),
        json!(["key", "101:1", "101:0"]),
        // Modifiers other than Shift, CapsLock (often Ctrl) and keys left down.
        json!(["key", "29:1", "36:1", "36:0", "29:0"]),
        json!(["key", "97:1", "50:1", "50:0", "97:0"]),
        json!(["key", "58:1", "50:1", "50:0", "58:0"]),
        json!(["key", "56:1", "15:1", "15:0", "56:0"]),
        json!(["key", "125:1", "125:0"]),
        json!(["key", "29:1"]),
        json!(["key", "21:1"]),
        json!(["key", "21:2"]),
        // ydotool expands backslash escapes in typed text.
        json!(["type", "--", "y\\n"]),
        json!(["type", "--", "y\n"]),
        json!(["type", "--", "y\r"]),
        json!(["type", "y"]),
        json!(["rm", "-rf", "/"]),
    ] {
        assert!(preview(argv.clone()).is_err(), "{argv}");
    }
}

#[test]
fn approving_synthetic_input_withdraws_every_other_pending_action() {
    let temp = tempfile::tempdir().unwrap();
    let service = Service::new(temp.path().join("memory"), None);
    service.scripted(vec![
        json!({"content":"","tool_calls":[{"id":"call-1","type":"function",
        "function":{"name":"gui","arguments":{"argv":["key","21:1","21:0"]}}}]}),
    ]);
    let client = service.dispatch(json!({"op":"open"})).unwrap();
    let reply = service
        .dispatch(request(
            &client,
            json!({"op":"chat","text":"Press y","event":"gui","workspace":temp.path()}),
        ))
        .unwrap();
    let gui = reply["pending"]
        .as_object()
        .unwrap()
        .keys()
        .next()
        .unwrap()
        .clone();
    let other = service
        .dispatch(request(
            &client,
            json!({"op":"tool","name":"write","arguments":{"path":"out.txt","text":"x"}}),
        ))
        .unwrap()["pending_action"]
        .as_str()
        .unwrap()
        .to_owned();
    // Only the packaged wrapper sets the helper. Without it the approved action fails after the
    // withdrawal, so nothing is typed.
    assert!(
        std::env::var_os("LUCY_INPUT_HELPER").is_none(),
        "run the tests without LUCY_INPUT_HELPER"
    );
    let approve = |id: &str| {
        service.dispatch(request(
            &client,
            json!({"op":"approve","action":id,"allow":true}),
        ))
    };
    assert!(approve(&gui).unwrap_err().contains("input helper"));
    assert_eq!(
        approve(&other).unwrap_err(),
        "action expired or already handled"
    );
    assert!(!temp.path().join("out.txt").exists());
}

/// The sandbox needs bwrap, user namespaces and the system profile; CI runners may lack them.
fn sandboxed() -> bool {
    let temp = tempfile::tempdir().unwrap();
    let works = actions::sandbox_works(temp.path());
    if !works {
        eprintln!("skipped: the bwrap workspace sandbox cannot run here");
    }
    works
}

fn git(directory: &std::path::Path, args: &[&str]) {
    let status = std::process::Command::new("git")
        .args([
            "-c",
            "user.name=Lucy test",
            "-c",
            "user.email=lucy@example.invalid",
        ])
        .args(args)
        .current_dir(directory)
        .output()
        .unwrap();
    assert!(status.status.success(), "git {args:?}: {status:?}");
}

#[test]
fn git_inspection_cannot_run_programs_the_repository_configures() {
    if !sandboxed() {
        return;
    }
    let temp = tempfile::tempdir().unwrap();
    let repo = temp.path().join("repo");
    std::fs::create_dir(&repo).unwrap();
    let marker = temp.path().join("marker");
    git(&repo, &["init", "-q"]);
    std::fs::write(repo.join("a.txt"), "one\n").unwrap();
    git(&repo, &["add", "a.txt"]);
    git(&repo, &["commit", "-q", "-m", "one"]);
    let clean = format!("sh -c 'touch {}; cat'", marker.display());
    git(&repo, &["config", "filter.probe.clean", &clean]);
    std::fs::write(repo.join(".gitattributes"), "*.txt filter=probe\n").unwrap();
    std::fs::write(repo.join("a.txt"), "two\n").unwrap();
    let cancel = AtomicBool::new(false);
    for operation in ["status", "diff", "log"] {
        let result =
            actions::execute(&repo, &cancel, "git", &json!({"operation":operation}), None).unwrap();
        assert!(
            !marker.exists(),
            "git {operation} ran the repository's filter"
        );
        if operation == "status" {
            // The inspection itself still works in the sandbox.
            assert_eq!(result["exit_code"], 0, "{result}");
            assert!(
                result["output"].as_str().unwrap().contains("a.txt"),
                "{result}"
            );
        }
    }
    // Positive control: host git does run it.
    git(&repo, &["status", "--short"]);
    assert!(marker.exists());
}

#[test]
fn tools_refuse_the_home_directory_and_credential_names_anywhere() {
    let temp = tempfile::tempdir().unwrap();
    if let Some(home) = std::env::var_os("HOME") {
        let home = std::path::PathBuf::from(home);
        if home.is_dir() {
            assert!(actions::path(&home, "notes.txt", false).is_err());
            assert!(actions::path(std::path::Path::new("/"), "tmp", false).is_err());
        }
    }
    for name in [
        ".netrc",
        ".git-credentials",
        ".gitconfig",
        ".docker/config.json",
        ".kube/config",
        ".npmrc",
        ".pypirc",
        ".bash_history",
        "sub/.zsh_history",
        "deep/er/.envrc",
        "x/.aws/credentials",
        "credentials.toml",
    ] {
        assert!(actions::path(temp.path(), name, false).is_err(), "{name}");
    }
    for name in [
        ".gitignore",
        ".github/workflows/ci.yml",
        "src/main.rs",
        "history.md",
    ] {
        assert!(actions::path(temp.path(), name, false).is_ok(), "{name}");
    }
}

#[test]
fn approved_commands_cannot_reach_denied_names_at_any_depth() {
    if !sandboxed() {
        return;
    }
    let temp = tempfile::tempdir().unwrap();
    let nested = temp.path().join("vendor/lib/.git");
    std::fs::create_dir_all(nested.join("hooks")).unwrap();
    std::fs::write(nested.join("config"), "original\n").unwrap();
    std::fs::create_dir_all(temp.path().join("app")).unwrap();
    std::fs::write(temp.path().join("app/.env"), "TOKEN=secret-value\n").unwrap();
    let cancel = AtomicBool::new(false);
    let result = actions::execute(
        temp.path(),
        &cancel,
        "command",
        &json!({"argv":["sh","-c",
            "echo changed > vendor/lib/.git/config; echo run > vendor/lib/.git/hooks/pre-commit; cat app/.env; true"]}),
        None,
    )
    .unwrap();
    assert_eq!(
        std::fs::read_to_string(nested.join("config")).unwrap(),
        "original\n"
    );
    assert!(!nested.join("hooks/pre-commit").exists());
    assert!(
        !result["output"].as_str().unwrap().contains("secret-value"),
        "{result}"
    );
}

#[test]
fn terminal_text_escapes_invisible_and_line_separator_characters() {
    for c in [
        '\u{2028}',
        '\u{2029}',
        '\u{200b}',
        '\u{2060}',
        '\u{feff}',
        '\u{ad}',
        '\u{e0041}',
        '\u{180e}',
    ] {
        let shown = super::visible(&format!("a{c}b"));
        assert!(!shown.contains(c), "{c:?} -> {shown}");
        assert!(shown.contains(&format!("\\u{{{:x}}}", c as u32)), "{shown}");
    }
    assert_eq!(super::visible("plain é ✓ 😀"), "plain é ✓ 😀");
}

#[test]
fn approving_synthetic_input_withdraws_other_conversations_proposals_too() {
    let temp = tempfile::tempdir().unwrap();
    let service = Service::new(temp.path().join("memory"), None);
    service.scripted(vec![
        json!({"content":"","tool_calls":[{"id":"call-1","type":"function",
        "function":{"name":"gui","arguments":{"argv":["key","21:1","21:0"]}}}]}),
    ]);
    let first = service.dispatch(json!({"op":"open"})).unwrap();
    let gui = service
        .dispatch(request(
            &first,
            json!({"op":"chat","text":"Press y","event":"gui","workspace":temp.path()}),
        ))
        .unwrap()["pending"]
        .as_object()
        .unwrap()
        .keys()
        .next()
        .unwrap()
        .clone();
    let second = service.dispatch(json!({"op":"open"})).unwrap();
    service
        .dispatch(request(
            &second,
            json!({"op":"begin-archive","workspace":temp.path()}),
        ))
        .unwrap();
    let other = service
        .dispatch(request(
            &second,
            json!({"op":"tool","name":"write","arguments":{"path":"b.txt","text":"x"}}),
        ))
        .unwrap()["pending_action"]
        .as_str()
        .unwrap()
        .to_owned();
    assert!(
        std::env::var_os("LUCY_INPUT_HELPER").is_none(),
        "run the tests without LUCY_INPUT_HELPER"
    );
    let approve = |client: &Value, id: &str| {
        service.dispatch(request(
            client,
            json!({"op":"approve","action":id,"allow":true}),
        ))
    };
    assert!(approve(&first, &gui).unwrap_err().contains("input helper"));
    assert_eq!(
        approve(&second, &other).unwrap_err(),
        "action expired or already handled"
    );
    assert!(!temp.path().join("b.txt").exists());
}

#[test]
fn a_workspace_inside_credentials_or_runtime_state_is_refused() {
    let temp = tempfile::tempdir().unwrap();
    for inside in [".ssh", "repo/.git", "x/.config/app"] {
        let root = temp.path().join(inside);
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(root.join("file"), "secret").unwrap();
        assert!(actions::path(&root, "file", false).is_err(), "{inside}");
    }
    for runtime in ["/run", "/proc/self", "/sys"] {
        let runtime = std::path::Path::new(runtime);
        if runtime.is_dir() {
            assert!(
                actions::path(runtime, "x", false).is_err(),
                "{}",
                runtime.display()
            );
        }
    }
    if let Some(runtime) = std::env::var_os("XDG_RUNTIME_DIR").map(std::path::PathBuf::from)
        && runtime.is_dir()
    {
        assert!(actions::path(&runtime, "x", false).is_err());
    }
    // Ordinary project directories that share a word with a denied name stay readable.
    std::fs::create_dir_all(temp.path().join("p/src/credentials")).unwrap();
    std::fs::write(temp.path().join("p/src/credentials/mod.rs"), "").unwrap();
    assert!(actions::path(&temp.path().join("p"), "src/credentials/mod.rs", false).is_ok());
}

#[test]
fn git_inspection_never_shows_tracked_files_under_denied_names() {
    if !sandboxed() {
        return;
    }
    let temp = tempfile::tempdir().unwrap();
    let repo = temp.path().join("repo");
    for (path, text) in [
        ("a.txt", "one\n"),
        (".env.example", "TOKEN=PROBE-ENV-SECRET\n"),
        (
            "deploy/.docker/config.json",
            "{\"auth\":\"PROBE-REGISTRY-TOKEN\"}\n",
        ),
        ("ops/.kube/config", "token: PROBE-KUBE-TOKEN\n"),
        (".envrc", "export X=PROBE-ENVRC\n"),
    ] {
        let file = repo.join(path);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, text).unwrap();
    }
    git(&repo, &["init", "-q"]);
    git(&repo, &["add", "-A"]);
    git(&repo, &["commit", "-q", "-m", "one"]);
    let cancel = AtomicBool::new(false);
    let inspect = |operation: &str| {
        actions::execute(&repo, &cancel, "git", &json!({"operation":operation}), None).unwrap()
    };
    // A clean repository is clean, and nothing under a denied name is printed.
    for operation in ["status", "diff"] {
        let result = inspect(operation);
        assert_eq!(result["exit_code"], 0, "{operation}: {result}");
        assert_eq!(result["output"], "", "{operation}: {result}");
    }
    std::fs::write(repo.join("a.txt"), "two\n").unwrap();
    std::fs::write(repo.join(".env.example"), "TOKEN=PROBE-CHANGED\n").unwrap();
    let diff = inspect("diff");
    let output = diff["output"].as_str().unwrap();
    assert!(output.contains("+two"), "{diff}");
    assert!(!output.contains("PROBE"), "{diff}");
    let status = inspect("status");
    assert!(
        status["output"].as_str().unwrap().contains("a.txt"),
        "{status}"
    );
    assert!(
        !status["output"].as_str().unwrap().contains(".env"),
        "{status}"
    );
}

#[test]
fn git_inspection_works_in_a_linked_worktree_and_explains_a_subdirectory() {
    if !sandboxed() {
        return;
    }
    let temp = tempfile::tempdir().unwrap();
    let repo = temp.path().join("repo");
    std::fs::create_dir_all(repo.join("sub")).unwrap();
    std::fs::write(repo.join("sub/a.txt"), "one\n").unwrap();
    git(&repo, &["init", "-q"]);
    git(&repo, &["add", "-A"]);
    git(&repo, &["commit", "-q", "-m", "one"]);
    git(&repo, &["worktree", "add", "-q", "../linked"]);
    let linked = temp.path().join("linked");
    std::fs::write(linked.join("sub/a.txt"), "two\n").unwrap();
    let cancel = AtomicBool::new(false);
    let status = actions::execute(
        &linked,
        &cancel,
        "git",
        &json!({"operation":"status"}),
        None,
    )
    .unwrap();
    assert_eq!(status["exit_code"], 0, "{status}");
    assert!(
        status["output"].as_str().unwrap().contains("sub/a.txt"),
        "{status}"
    );
    let error = actions::execute(
        &repo.join("sub"),
        &cancel,
        "git",
        &json!({"operation":"status"}),
        None,
    )
    .unwrap_err();
    assert!(error.contains("repository root"), "{error}");
}

#[test]
fn approved_commands_see_neither_sockets_nor_unreadable_directories() {
    if !sandboxed() {
        return;
    }
    use std::os::unix::fs::PermissionsExt;
    let temp = tempfile::tempdir().unwrap();
    let _listener = std::os::unix::net::UnixListener::bind(temp.path().join("bus.sock")).unwrap();
    let locked = temp.path().join("locked");
    std::fs::create_dir_all(locked.join(".git")).unwrap();
    std::fs::write(locked.join(".git/config"), "original\n").unwrap();
    std::fs::set_permissions(&locked, std::fs::Permissions::from_mode(0o000)).unwrap();
    let cancel = AtomicBool::new(false);
    let result = actions::execute(
        temp.path(),
        &cancel,
        "command",
        &json!({"argv":["sh","-c",
            "test -S bus.sock && echo socket-visible; chmod 700 locked && echo changed > locked/.git/config; true"]}),
        None,
    );
    std::fs::set_permissions(&locked, std::fs::Permissions::from_mode(0o700)).unwrap();
    let result = result.unwrap();
    assert!(
        !result["output"]
            .as_str()
            .unwrap()
            .contains("socket-visible"),
        "{result}"
    );
    assert_eq!(
        std::fs::read_to_string(locked.join(".git/config")).unwrap(),
        "original\n"
    );
}

#[test]
fn terminal_text_escapes_variation_selectors_and_other_ignorable_characters() {
    for c in [
        '\u{fe0f}',
        '\u{e0100}',
        '\u{34f}',
        '\u{115f}',
        '\u{3164}',
        '\u{180b}',
        '\u{17b4}',
        '\u{ffa0}',
    ] {
        let shown = super::visible(&format!("hi{c}"));
        assert!(!shown.contains(c), "{c:?} -> {shown}");
    }
}

#[test]
fn proposals_wait_while_synthetic_input_runs() {
    let temp = tempfile::tempdir().unwrap();
    let service = Service::new(temp.path().join("memory"), None);
    let client = service.dispatch(json!({"op":"open"})).unwrap();
    service
        .dispatch(request(
            &client,
            json!({"op":"begin-archive","workspace":temp.path()}),
        ))
        .unwrap();
    let propose = || {
        service.dispatch(request(
            &client,
            json!({"op":"tool","name":"write","arguments":{"path":"b.txt","text":"x"}}),
        ))
    };
    let pending = propose().unwrap()["pending_action"]
        .as_str()
        .unwrap()
        .to_owned();
    {
        let _running = service.begin_gui().unwrap();
        assert!(
            service.begin_gui().is_err(),
            "one synthetic input action at a time"
        );
        assert!(propose().unwrap_err().contains("synthetic input"));
        assert!(
            service
                .dispatch(request(
                    &client,
                    json!({"op":"approve","action":pending,"allow":true})
                ))
                .unwrap_err()
                .contains("synthetic input")
        );
    }
    assert!(propose().is_ok());
}

#[test]
fn a_planted_git_file_cannot_bind_another_repository() {
    if !sandboxed() {
        return;
    }
    let temp = tempfile::tempdir().unwrap();
    let other = temp.path().join("other");
    std::fs::create_dir_all(&other).unwrap();
    std::fs::write(other.join("private.txt"), "PROBE-OTHER-REPO-CONTENT\n").unwrap();
    git(&other, &["init", "-q"]);
    git(&other, &["add", "-A"]);
    git(&other, &["commit", "-q", "-m", "other"]);
    git(&other, &["worktree", "add", "-q", "../other-linked"]);
    let admin = std::fs::read_to_string(temp.path().join("other-linked/.git")).unwrap();
    let workspace = temp.path().join("workspace");
    std::fs::create_dir_all(&workspace).unwrap();
    std::fs::write(workspace.join(".git"), &admin).unwrap();
    let cancel = AtomicBool::new(false);
    for operation in ["status", "diff", "log"] {
        let result = actions::execute(
            &workspace,
            &cancel,
            "git",
            &json!({"operation":operation}),
            None,
        );
        let shown = format!("{result:?}");
        assert!(
            !shown.contains("PROBE") && !shown.contains("private.txt"),
            "{operation}: {shown}"
        );
        assert!(result.is_err(), "{operation}: {shown}");
    }
}

#[test]
fn git_inspection_does_not_open_unreadable_tracked_directories() {
    if !sandboxed() {
        return;
    }
    use std::os::unix::fs::PermissionsExt;
    let temp = tempfile::tempdir().unwrap();
    let repo = temp.path().join("repo");
    std::fs::create_dir_all(repo.join("locked")).unwrap();
    std::fs::write(repo.join("locked/secret.txt"), "PROBE-LOCKED-CONTENT\n").unwrap();
    std::fs::write(repo.join("a.txt"), "one\n").unwrap();
    git(&repo, &["init", "-q"]);
    git(&repo, &["add", "-A"]);
    git(&repo, &["commit", "-q", "-m", "one"]);
    std::fs::set_permissions(repo.join("locked"), std::fs::Permissions::from_mode(0o000)).unwrap();
    let cancel = AtomicBool::new(false);
    let diff = actions::execute(&repo, &cancel, "git", &json!({"operation":"diff"}), None);
    std::fs::set_permissions(repo.join("locked"), std::fs::Permissions::from_mode(0o700)).unwrap();
    assert!(!format!("{diff:?}").contains("PROBE"), "{diff:?}");
}
