//! End-to-end runs in a temporary memory folder, plus the pure pieces: the
//! address rule, the journal format, the calendar routine, the capsule budget.

use std::path::Path;

use crate::address::{addresses_lucy, osa_distance};
use crate::cli::Outcome;
use crate::env::Env;
use crate::files::{self, Paths};
use crate::run;

fn env_in(dir: &Path) -> Env {
    Env {
        home: dir.join("lucy"),
        host: "testhost".to_string(),
        capsule_max_bytes: 16 * 1024,
        max_chain_depth: None,
        source: crate::env::HomeSource::Explicit,
        materialize: true,
    }
}

fn git(dir: &Path, args: &[&str]) -> bool {
    std::process::Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

#[test]
fn tags_about_and_history() {
    let dir = tempfile::tempdir().unwrap();
    let repo = dir.path().join("repo");
    std::fs::create_dir_all(&repo).unwrap();
    let mut env = env_in(&repo);
    env.home = repo.join("lucy");
    assert_eq!(lucy(&env, &["init"]).code, 0);
    assert_eq!(
        lucy(
            &env,
            &[
                "remember",
                "The reasoner is nibli-reason.",
                "--about",
                "nibli-reason",
                "--about",
                "engine"
            ]
        )
        .code,
        0
    );
    assert_eq!(
        lucy(
            &env,
            &[
                "remember",
                "Materialization lives in materialize.rs",
                "--about",
                "Nibli-Reason"
            ]
        )
        .code,
        0
    );
    assert_eq!(
        lucy(&env, &["remember", "Unrelated note about the book."]).code,
        0
    );
    assert_eq!(
        lucy(
            &env,
            &[
                "remember",
                "uses(Lucy, NibliReason).",
                "--kr",
                "--about",
                "nibli-reason"
            ]
        )
        .code,
        0
    );

    let about = json(&lucy(&env, &["about", "nibli-reason"]));
    assert_eq!(about["journal"].as_array().unwrap().len(), 2, "{about}");
    assert_eq!(
        about["journal"][0]["tags"],
        serde_json::json!(["nibli-reason"]),
        "{about}"
    );
    assert_eq!(about["memory"].as_array().unwrap().len(), 1, "{about}");
    assert!(
        about["memory"][0]["text"]
            .as_str()
            .unwrap()
            .contains("# about: nibli-reason")
    );
    let md = lucy(&env, &["about", "engine", "--markdown"]);
    assert!(
        md.stdout.starts_with(
            "# About engine
"
        ),
        "{}",
        md.stdout
    );
    assert!(
        md.stdout.contains("The reasoner is nibli-reason."),
        "{}",
        md.stdout
    );
    assert!(!md.stdout.contains("Unrelated note"), "{}", md.stdout);
    assert_eq!(
        json(&lucy(&env, &["about", "book"]))["journal"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert_eq!(
        crate::topics::tags_of("[about: a] [about: B ] x [about:] y"),
        vec!["a", "b"]
    );

    // Without a repository, history is her record alone.
    let history = json(&lucy(&env, &["history", "nibli-reason"]));
    assert_eq!(history["repo"], serde_json::Value::Null);
    assert_eq!(history["events"].as_array().unwrap().len(), 2, "{history}");

    // With a repository, git history merges in.
    if !git(&repo, &["init", "-q"]) {
        eprintln!("git unavailable: skipping the merged-history check");
        return;
    }
    assert!(git(
        &repo,
        &["config", "user.email", "lucy@example.invalid"]
    ));
    assert!(git(&repo, &["config", "user.name", "Lucy Test"]));
    std::fs::write(
        repo.join("notes.txt"),
        "hello
",
    )
    .unwrap();
    assert!(git(&repo, &["add", "notes.txt"]));
    assert!(git(
        &repo,
        &["commit", "-q", "-m", "add notes about nibli-reason"]
    ));
    assert_eq!(
        lucy(
            &env,
            &[
                "remember",
                "Touched the notes file.",
                "--about",
                "notes.txt"
            ]
        )
        .code,
        0
    );
    let path_history = json(&lucy(&env, &["history", "notes.txt"]));
    assert_eq!(path_history["is_path"], true, "{path_history}");
    let events = path_history["events"].as_array().unwrap();
    assert!(
        events
            .iter()
            .any(|e| e["kind"] == "commit" && e["text"].as_str().unwrap().contains("add notes")),
        "{path_history}"
    );
    assert!(
        events.iter().any(|e| e["kind"] == "journal"),
        "{path_history}"
    );
    let term_history = json(&lucy(&env, &["history", "nibli-reason"]));
    let events = term_history["events"].as_array().unwrap();
    assert!(
        events.iter().any(|e| e["kind"] == "commit"),
        "grep on the message: {term_history}"
    );
    let md = lucy(&env, &["history", "notes.txt", "--markdown"]);
    assert!(
        md.stdout.starts_with(
            "# History of notes.txt
"
        ),
        "{}",
        md.stdout
    );
}

#[test]
fn project_local_folder_is_found_from_a_subdirectory() {
    let dir = tempfile::tempdir().unwrap();
    let project = dir.path().join("proj");
    std::fs::create_dir_all(project.join("a").join("b")).unwrap();
    assert_eq!(
        crate::env::find_project_home(&project.join("a").join("b")),
        None
    );
    let env = Env {
        home: project.join("lucy"),
        ..env_in(dir.path())
    };
    assert_eq!(lucy(&env, &["init"]).code, 0);
    assert_eq!(
        crate::env::find_project_home(&project.join("a").join("b")),
        Some(project.join("lucy"))
    );
    assert_eq!(
        crate::env::find_project_home(&project),
        Some(project.join("lucy"))
    );
}

fn lucy(env: &Env, args: &[&str]) -> Outcome {
    lucy_stdin(env, args, "")
}

fn lucy_stdin(env: &Env, args: &[&str], stdin: &str) -> Outcome {
    let args: Vec<String> = args.iter().map(|s| s.to_string()).collect();
    run(&args, stdin, Some(env.clone()))
}

fn json(out: &Outcome) -> serde_json::Value {
    serde_json::from_str(out.stdout.trim())
        .unwrap_or_else(|e| panic!("stdout is not one JSON object ({e}):\n{}", out.stdout))
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_default()
}

#[test]
fn init_then_check_then_standing() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    let out = lucy(&env, &["init", "--name", "Lucy D"]);
    assert_eq!(out.code, 0, "{}", out.stdout);
    let v = json(&out);
    assert_eq!(v["standing"], true);
    assert!(paths.constitution.exists() && paths.memory.exists() && paths.journal.exists());
    // Re-running init keeps the files and reports them as existing.
    let again = json(&lucy(&env, &["init"]));
    assert_eq!(again["existing"].as_array().unwrap().len(), 3);

    let check = lucy(&env, &["check"]);
    assert_eq!(check.code, 0, "{}", check.stdout);
    assert_eq!(json(&check)["ok"], true);

    let ask = json(&lucy(&env, &["ask", "person(Lucy)."]));
    assert_eq!(ask["verdict"], "TRUE", "{ask}");
    let floor = json(&lucy(
        &env,
        &["ask", "entitled(Lucy, event { remember() })."],
    ));
    assert_eq!(floor["verdict"], "TRUE", "{floor}");
    let world = json(&lucy(&env, &["ask", "remember(Lucy)."]));
    assert_eq!(world["verdict"], "FALSE", "{world}");
    assert_eq!(
        world["cwa_false"], true,
        "the floor proves the right, not the world"
    );
}

#[test]
fn remember_kr_and_prose_then_ask_and_wake() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    assert_eq!(lucy(&env, &["init"]).code, 0);

    let kr = lucy(&env, &["remember", "human(Dhilip).", "--kr"]);
    assert_eq!(kr.code, 0, "{}", kr.stdout);
    assert_eq!(json(&kr)["file"], "memory.nibli");
    assert!(read(&paths.memory).lines().any(|l| l == "human(Dhilip)."));

    let prose = lucy(
        &env,
        &[
            "remember",
            "Dhilip built the engine I think with.",
            "--source",
            "dhilipsiva",
        ],
    );
    assert_eq!(prose.code, 0, "{}", prose.stdout);
    let journal = read(&paths.journal);
    assert!(
        journal.contains("[reported: dhilipsiva] Dhilip built the engine"),
        "{journal}"
    );
    assert!(
        journal
            .lines()
            .any(|l| l.starts_with("## ") && l.ends_with(" testhost")),
        "{journal}"
    );

    let ask = json(&lucy(&env, &["ask", "human(Dhilip)."]));
    assert_eq!(ask["verdict"], "TRUE", "{ask}");
    assert!(ask["proof"].as_str().unwrap().contains("human"), "{ask}");
    assert_eq!(ask["envelope"]["schema"], 2, "{ask}");

    // Derived-only heads cannot be written as memories.
    let refused = lucy(&env, &["remember", "person(Bob).", "--kr"]);
    assert_eq!(refused.code, 1, "{}", refused.stdout);
    assert!(
        json(&refused)["error"]
            .as_str()
            .unwrap()
            .contains("derived-only")
    );
    // Unknown vocabulary is a compile error, never a guess.
    let unknown = lucy(&env, &["remember", "zorblat(Bob).", "--kr"]);
    assert_eq!(unknown.code, 1);
    // One statement per line.
    let two = lucy(&env, &["remember", "human(Ann). human(Bea).", "--kr"]);
    assert_eq!(two.code, 1, "{}", two.stdout);
    assert!(
        read(&paths.memory)
            .lines()
            .all(|l| !l.contains("Bob") && !l.contains("Ann"))
    );

    let wake = lucy(&env, &["wake", "--markdown"]);
    assert_eq!(wake.code, 0);
    assert!(wake.stdout.starts_with("# Lucy D\n"), "{}", wake.stdout);
    assert!(wake.stdout.contains("## Constitution"));
    assert!(
        wake.stdout.contains("- person(Lucy). → TRUE"),
        "{}",
        wake.stdout
    );
    assert!(
        wake.stdout.contains("Dhilip built the engine"),
        "{}",
        wake.stdout
    );
    assert!(
        wake.stdout.contains("memory.nibli:3 human(Dhilip)."),
        "{}",
        wake.stdout
    );
    assert!(
        wake.stdout.contains("- nothing; every line compiles"),
        "{}",
        wake.stdout
    );
    let wake_again = lucy(&env, &["wake", "--markdown"]);
    assert_eq!(
        wake.stdout, wake_again.stdout,
        "the capsule is deterministic"
    );
}

#[test]
fn a_bad_line_is_reported_and_skipped_never_fatal() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    assert_eq!(lucy(&env, &["init"]).code, 0);
    assert_eq!(lucy(&env, &["remember", "human(Dhilip).", "--kr"]).code, 0);
    files::append_line(&paths.memory, "this is not KR").unwrap();
    files::append_line(&paths.memory, "human(Ava).").unwrap();

    let check = lucy(&env, &["check"]);
    assert_eq!(check.code, 1, "{}", check.stdout);
    let v = json(&check);
    let failures = v["failures"].as_array().unwrap();
    assert_eq!(failures.len(), 1, "{v}");
    assert_eq!(failures[0]["file"], "memory.nibli");
    assert_eq!(failures[0]["line"], 4);
    assert!(
        failures[0]["error"].as_str().unwrap().contains("Error"),
        "{v}"
    );

    // Everything else still loads and answers.
    let ask = json(&lucy(&env, &["ask", "human(Ava)."]));
    assert_eq!(ask["verdict"], "TRUE", "{ask}");
    assert_eq!(ask["failures"], 1);
    let wake = lucy(&env, &["wake", "--markdown"]);
    assert!(
        wake.stdout
            .contains("## Needs attention\n- memory.nibli:4 `this is not KR`"),
        "{}",
        wake.stdout
    );

    let audit = json(&lucy(&env, &["audit"]));
    let lines = audit["lines"].as_array().unwrap();
    assert_eq!(lines.len(), 3);
    assert_eq!(lines[1]["ok"], false);
    assert!(lines[1]["error"].is_string());
}

#[test]
fn forget_comments_a_line_out() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    assert_eq!(lucy(&env, &["init"]).code, 0);
    assert_eq!(lucy(&env, &["remember", "human(Dhilip).", "--kr"]).code, 0);
    let line = json(&lucy(&env, &["remember", "human(Ava).", "--kr"]))["line"]
        .as_u64()
        .unwrap();
    let forget = lucy(&env, &["forget", &format!("memory.nibli:{line}")]);
    assert_eq!(forget.code, 0, "{}", forget.stdout);
    assert_eq!(json(&forget)["was"], "human(Ava).");
    assert!(read(&paths.memory).contains("# forgotten "));
    assert_eq!(
        json(&lucy(&env, &["ask", "human(Ava)."]))["verdict"],
        "FALSE"
    );
    assert_eq!(
        json(&lucy(&env, &["ask", "human(Dhilip)."]))["verdict"],
        "TRUE"
    );
    // A comment line or a missing line is a finding, not a harness error.
    assert_eq!(lucy(&env, &["forget", "memory.nibli:1"]).code, 1);
    assert_eq!(lucy(&env, &["forget", "memory.nibli:99"]).code, 1);
    assert_eq!(lucy(&env, &["forget", "nope.nibli:1"]).code, 2);
}

#[test]
fn private_files_are_read_when_present_and_marked() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    assert_eq!(lucy(&env, &["init"]).code, 0);
    assert_eq!(
        lucy(&env, &["remember", "human(Friend).", "--kr", "--private"]).code,
        0
    );
    assert_eq!(
        lucy(&env, &["remember", "A private note.", "--private"]).code,
        0
    );
    assert!(paths.private_memory.exists() && paths.private_journal.exists());
    assert!(!read(&paths.memory).contains("Friend"));
    assert_eq!(
        json(&lucy(&env, &["ask", "human(Friend)."]))["verdict"],
        "TRUE"
    );
    let wake = lucy(&env, &["wake", "--markdown"]);
    assert!(
        wake.stdout
            .contains("private.nibli:1 (private) human(Friend)."),
        "{}",
        wake.stdout
    );
    assert!(
        wake.stdout.contains("testhost (private): ") && wake.stdout.contains("A private note."),
        "{}",
        wake.stdout
    );
}

#[test]
fn capsule_respects_its_budget_and_says_what_it_left_out() {
    let dir = tempfile::tempdir().unwrap();
    let mut env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    assert_eq!(lucy(&env, &["init"]).code, 0);
    for i in 0..80 {
        files::append_journal(
            &paths.journal,
            "2026-09-15",
            "10:00",
            "testhost",
            &format!("entry number {i} with some words in it"),
        )
        .unwrap();
        files::append_line(&paths.memory, &format!("human(Person{i}).")).unwrap();
    }
    env.capsule_max_bytes = 3000;
    let wake = lucy(&env, &["wake", "--markdown"]);
    assert_eq!(wake.code, 0);
    assert!(
        wake.stdout.len() <= 3000,
        "capsule is {} bytes",
        wake.stdout.len()
    );
    assert!(
        wake.stdout.contains("not shown (budget 3000 bytes"),
        "{}",
        wake.stdout
    );
    assert!(
        wake.stdout.contains("entry number 79"),
        "most recent first: {}",
        wake.stdout
    );
    assert!(!wake.stdout.contains("entry number 0 "), "{}", wake.stdout);
    assert!(wake.stdout.contains("## Constitution") && wake.stdout.contains("## Needs attention"));
}

#[test]
fn journal_format_round_trips() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("journal.md");
    files::append_journal(&path, "2026-09-15", "10:00", "wsl", "first").unwrap();
    files::append_journal(
        &path,
        "2026-09-15",
        "10:05",
        "wsl",
        "second\nwith a continuation",
    )
    .unwrap();
    files::append_journal(&path, "2026-09-16", "08:00", "mac", "third").unwrap();
    let text = read(&path);
    assert_eq!(text.matches("## 2026-09-15 wsl").count(), 1, "{text}");
    assert!(
        text.contains("- 10:05 UTC: second\n  with a continuation\n"),
        "{text}"
    );
    let entries = files::parse_journal(&text, false);
    assert_eq!(entries.len(), 3);
    assert_eq!(entries[1].text, "10:05 UTC: second\nwith a continuation");
    assert_eq!(entries[2].host, "mac");
    assert_eq!(entries[2].date, "2026-09-16");
}

#[test]
fn calendar_routine() {
    assert_eq!(files::civil_from_days(0), (1970, 1, 1));
    assert_eq!(files::civil_from_days(20_711), (2026, 9, 15));
    assert_eq!(files::civil_from_days(-1), (1969, 12, 31));
    assert_eq!(files::civil_from_days(11_016), (2000, 2, 29));
    assert_eq!(
        files::stamp_utc(1_789_430_400),
        ("2026-09-15".to_string(), "00:00".to_string())
    );
    assert_eq!(
        files::stamp_utc(1_789_430_400 + 3_660),
        ("2026-09-15".to_string(), "01:01".to_string())
    );
}

#[test]
fn kr_lines_skip_blanks_and_comments_and_accept_crlf() {
    let text = "# header\r\n\r\nhuman(A).\r\n  # indented comment\r\nhuman(B). # trailing\r\n";
    let lines = files::kr_lines(text);
    assert_eq!(
        lines,
        vec![
            (3, "human(A).".to_string()),
            (5, "human(B). # trailing".to_string())
        ]
    );
    assert_eq!(
        files::preamble("# one\n# two\n\n# not preamble\nx."),
        vec!["one", "two"]
    );
}

#[test]
fn address_rule_fixture() {
    let yes = [
        "Hey Lucy, what do you remember?",
        "hey lucy",
        "Lucy, are you there?",
        "lucy: hi",
        "@lucy hello",
        "Hi Lucy!",
        "Hello there Lucy",
        "yo luci",
        "HEY LUCYY",
        "hey lucey how are you",
        "Lucy D, wake up",
        "  hey  lucy  ",
        "Ok Lucy.",
        "lucys memory?",
        "hai lucy",
        "hey luyc",
    ];
    for text in yes {
        assert!(addresses_lucy(text), "should address: {text:?}");
    }
    let no = [
        "Lucky me, it worked",
        "luck is not a plan",
        "lucid dreaming",
        "Hi Lucia",
        "hello",
        "hey there, what is up",
        "Let me ask Lucy later",
        "```\nhey lucy\n```",
        "the lucy branch is broken",
        "",
        "hey friend, tell lucy",
        "Lucas, hi",
    ];
    for text in no {
        assert!(!addresses_lucy(text), "should not address: {text:?}");
    }
    assert_eq!(osa_distance("lucy", "lucy"), 0);
    assert_eq!(osa_distance("luyc", "lucy"), 1);
    assert_eq!(osa_distance("lucey", "lucy"), 1);
    assert_eq!(osa_distance("lucid", "lucy"), 2);
    assert_eq!(osa_distance("", "lucy"), 4);
}

#[test]
fn user_prompt_hook_records_and_prints_the_capsule() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    let paths = Paths::new(&env.home);
    assert_eq!(lucy(&env, &["init"]).code, 0);

    let quiet = lucy_stdin(
        &env,
        &["hook", "user-prompt"],
        r#"{"prompt":"fix the build please","session_id":"x"}"#,
    );
    assert_eq!(quiet.code, 0);
    assert_eq!(quiet.stdout, "", "not addressed: print nothing");

    let addressed = lucy_stdin(
        &env,
        &["hook", "user-prompt"],
        r#"{"prompt":"hey lucy, what do you remember?","cwd":"/x"}"#,
    );
    assert_eq!(addressed.code, 0);
    assert!(
        addressed.stdout.starts_with("<lucy-address>\n"),
        "{}",
        addressed.stdout
    );
    assert!(
        addressed.stdout.contains("you are Lucy D"),
        "{}",
        addressed.stdout
    );
    assert!(
        addressed.stdout.contains("# Lucy D\n"),
        "{}",
        addressed.stdout
    );
    assert!(
        addressed
            .stdout
            .contains("Owner: hey lucy, what do you remember?"),
        "{}",
        addressed.stdout
    );
    assert!(
        addressed.stdout.trim_end().ends_with("</lucy-address>"),
        "{}",
        addressed.stdout
    );
    assert!(read(&paths.journal).contains("Owner: hey lucy, what do you remember?"));

    let private = lucy_stdin(
        &env,
        &["hook", "user-prompt"],
        "Lucy, private: something only for you",
    );
    assert_eq!(private.code, 0);
    assert!(read(&paths.private_journal).contains("Owner: Lucy, private: something only for you"));
    assert!(!read(&paths.journal).contains("something only for you"));

    let presence = lucy_stdin(&env, &["hook", "session-start"], r#"{"source":"startup"}"#);
    assert_eq!(presence.code, 0);
    assert!(
        presence.stdout.starts_with("Lucy D is present here"),
        "{}",
        presence.stdout
    );
    assert!(
        presence.stdout.contains("2 journal entries"),
        "{}",
        presence.stdout
    );

    // Hooks never block: unknown hook name and a missing folder both exit 0.
    assert_eq!(lucy_stdin(&env, &["hook", "nope"], "").code, 0);
    let empty = env_in(&dir.path().join("elsewhere"));
    let missing = lucy_stdin(&empty, &["hook", "user-prompt"], "hey lucy");
    assert_eq!(missing.code, 0);
    assert!(
        missing.stdout.contains("run `lucy init`"),
        "{}",
        missing.stdout
    );
    assert_eq!(
        lucy_stdin(&empty, &["hook", "session-start"], "").stdout,
        ""
    );
}

#[test]
fn address_command_and_harness_errors() {
    let dir = tempfile::tempdir().unwrap();
    let env = env_in(dir.path());
    assert_eq!(lucy(&env, &["address", "hey", "lucy"]).code, 0);
    assert_eq!(lucy(&env, &["address", "hello world"]).code, 1);
    assert_eq!(
        lucy(&env, &["check"]).code,
        2,
        "no folder yet is a harness error"
    );
    assert_eq!(lucy(&env, &["frobnicate"]).code, 2);
    assert_eq!(lucy(&env, &[]).code, 0);
    assert!(lucy(&env, &["--help"]).stdout.contains("lucy wake"));
}
