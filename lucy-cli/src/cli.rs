//! Command dispatch and the output contract: one JSON object on stdout for
//! every command except `wake --markdown` and the hooks, prose on stderr,
//! exit 0 ok / 1 finding / 2 harness (missing folder, bad arguments, I/O).

use std::path::PathBuf;

use serde_json::{Value, json};

use crate::env::Env;
use crate::files::{self, Paths, short_name};
use crate::{CONSTITUTION_TEMPLATE, address, ask, capsule, hook, load, topics};

/// What a command produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Outcome {
    /// Process exit code.
    pub code: i32,
    /// Standard output.
    pub stdout: String,
    /// Standard error.
    pub stderr: String,
}

/// The usage text.
pub const USAGE: &str = "lucy — a persistent identity whose memory is nibli text

  lucy init [--name NAME] [--here]   create the memory folder (--here: ./lucy in this directory)
  lucy check                         compile every line; list the ones that fail (exit 1 if any)
  lucy wake [--markdown]             load everything and print the capsule
  lucy remember \"TEXT\" [--kr] [--private] [--source WHO] [--about THING]...
                                     append a prose memory to the journal, or with --kr a
                                     nibli statement to memory.nibli (checked first)
  lucy ask \"KR QUERY\"                answer with verdict, [Why] line, proof and envelope
  lucy about THING [--markdown]      everything she holds about a thing: tagged and matching
                                     journal entries, formal lines, git history
  lucy history THING [--markdown]    the git log of a path or term merged with her record of it
  lucy audit                         list every formal memory line with its compile status
  lucy forget FILE:LINE              comment a line out of memory.nibli or private.nibli
  lucy address \"TEXT\"                exit 0 if TEXT starts by addressing Lucy, else 1
  lucy hook user-prompt              Claude Code UserPromptSubmit hook (JSON on stdin)
  lucy hook session-start            Claude Code SessionStart hook

Memory folder: LUCY_HOME, else a lucy/ folder in this directory or a parent, else ~/.lucy.
Environment: LUCY_HOME, LUCY_HOST, LUCY_CAPSULE_MAX_BYTES, LUCY_MAX_CHAIN_DEPTH.
";

/// Whether the command wants stdin (only the hooks do).
pub fn reads_stdin(args: &[String]) -> bool {
    args.first().map(String::as_str) == Some("hook")
}

/// Runs one command. `env_override` lets tests point at a temporary folder.
pub fn run(args: &[String], stdin: &str, env_override: Option<Env>) -> Outcome {
    let Some(command) = args.first() else {
        return text(0, USAGE);
    };
    match command.as_str() {
        "help" | "--help" | "-h" => return text(0, USAGE),
        "version" | "--version" | "-V" => {
            return text(0, &format!("lucy {}\n", env!("CARGO_PKG_VERSION")));
        }
        _ => {}
    }
    let env = match env_override {
        Some(env) => env,
        None => match Env::from_process() {
            Ok(env) => env,
            Err(e) => return harness(&e),
        },
    };
    let paths = Paths::new(&env.home);
    let rest = &args[1..];
    let mut outcome = match command.as_str() {
        "init" => cmd_init(&env, rest),
        "check" => cmd_check(&env, &paths),
        "wake" => cmd_wake(&env, &paths, rest),
        "remember" => cmd_remember(&env, &paths, rest),
        "ask" => cmd_ask(&env, &paths, rest),
        "about" => cmd_about(&env, &paths, rest, false),
        "history" => cmd_about(&env, &paths, rest, true),
        "audit" => cmd_audit(&env, &paths),
        "forget" => cmd_forget(&paths, rest),
        "address" => cmd_address(rest),
        "hook" => cmd_hook(&env, &paths, rest, stdin),
        other => harness(&format!("unknown command `{other}`\n\n{USAGE}")),
    };
    if command != "hook" {
        outcome.stderr.insert_str(
            0,
            &format!(
                "lucy · home={} ({}) · host={}\n",
                env.home.display(),
                match env.source {
                    crate::env::HomeSource::Env => "LUCY_HOME",
                    crate::env::HomeSource::Project => "project-local",
                    crate::env::HomeSource::Default => "default",
                    crate::env::HomeSource::Explicit => "explicit",
                },
                env.host
            ),
        );
    }
    outcome
}

// ── outcomes ──

fn text(code: i32, body: &str) -> Outcome {
    Outcome {
        code,
        stdout: body.to_string(),
        stderr: String::new(),
    }
}

fn json_out(code: i32, value: Value) -> Outcome {
    Outcome {
        code,
        stdout: format!("{value}\n"),
        stderr: String::new(),
    }
}

fn finding(value: Value) -> Outcome {
    json_out(1, value)
}

fn harness(message: &str) -> Outcome {
    Outcome {
        code: 2,
        stdout: format!("{}\n", json!({ "ok": false, "error": message })),
        stderr: format!("{message}\n"),
    }
}

// ── argument parsing ──

struct Args {
    positional: Vec<String>,
    flags: Vec<(String, Option<String>)>,
}

const VALUE_FLAGS: &[&str] = &["--name", "--source", "--about", "--limit"];

fn parse(rest: &[String]) -> Args {
    let mut positional = Vec::new();
    let mut flags = Vec::new();
    let mut i = 0;
    while i < rest.len() {
        let arg = &rest[i];
        if let Some(flag) = arg.strip_prefix("--") {
            let key = format!("--{flag}");
            if VALUE_FLAGS.contains(&key.as_str()) {
                let value = rest.get(i + 1).cloned();
                flags.push((key, value));
                i += 2;
                continue;
            }
            flags.push((key, None));
        } else {
            positional.push(arg.clone());
        }
        i += 1;
    }
    Args { positional, flags }
}

impl Args {
    fn has(&self, flag: &str) -> bool {
        self.flags.iter().any(|(k, _)| k == flag)
    }
    fn value(&self, flag: &str) -> Option<&str> {
        self.flags
            .iter()
            .find(|(k, _)| k == flag)
            .and_then(|(_, v)| v.as_deref())
    }
    fn values(&self, flag: &str) -> Vec<&str> {
        self.flags
            .iter()
            .filter(|(k, _)| k == flag)
            .filter_map(|(_, v)| v.as_deref())
            .filter(|v| !v.trim().is_empty())
            .collect()
    }
}

// ── commands ──

fn cmd_init(env: &Env, rest: &[String]) -> Outcome {
    let args = parse(rest);
    let name = args.value("--name").unwrap_or("Lucy D");
    let mut env = env.clone();
    if args.has("--here") {
        match std::env::current_dir() {
            Ok(cwd) => {
                env.home = cwd.join("lucy");
                env.source = crate::env::HomeSource::Explicit;
            }
            Err(e) => return harness(&format!("cannot read the working directory: {e}")),
        }
    }
    let env = &env;
    let paths = &Paths::new(&env.home);
    if let Err(e) = std::fs::create_dir_all(&env.home) {
        return harness(&format!("cannot create {}: {e}", env.home.display()));
    }
    let seeds: [(&PathBuf, String); 3] = [
        (&paths.constitution, CONSTITUTION_TEMPLATE.to_string()),
        (
            &paths.memory,
            format!(
                "# {name} — memory\n# One nibli KR statement per line; `#` starts a comment. Edit freely: `lucy check` tells you which lines compile.\n"
            ),
        ),
        (&paths.journal, format!("# {name} — journal\n")),
    ];
    let mut created = Vec::new();
    let mut existing = Vec::new();
    for (path, content) in seeds {
        if path.exists() {
            existing.push(short_name(path));
            continue;
        }
        if let Err(e) = files::write_atomic(path, &content) {
            return harness(&e);
        }
        created.push(short_name(path));
    }
    match load::load(env, paths) {
        Ok(loaded) if loaded.failures.is_empty() && loaded.standing => json_out(
            0,
            json!({ "ok": true, "command": "init", "home": env.home.display().to_string(), "created": created, "existing": existing, "standing": true }),
        ),
        Ok(loaded) => harness(&format!(
            "the constitution does not load cleanly: {}",
            loaded
                .failures
                .iter()
                .map(|f| format!("{}:{} {}", f.file, f.line, f.error))
                .collect::<Vec<_>>()
                .join("; ")
        )),
        Err(e) => harness(&e),
    }
}

fn failures_json(loaded: &load::Loaded) -> Value {
    Value::Array(
        loaded
            .failures
            .iter()
            .map(|f| json!({ "file": f.file, "line": f.line, "text": f.text, "error": f.error }))
            .collect(),
    )
}

fn counts_json(loaded: &load::Loaded) -> Value {
    Value::Array(
        loaded
            .counts
            .iter()
            .map(|c| json!({ "file": c.file, "present": c.present, "asserted": c.asserted, "failed": c.failed }))
            .collect(),
    )
}

fn cmd_check(env: &Env, paths: &Paths) -> Outcome {
    let loaded = match load::load(env, paths) {
        Ok(loaded) => loaded,
        Err(e) => return harness(&e),
    };
    let ok = loaded.failures.is_empty() && loaded.standing;
    let value = json!({
        "ok": ok,
        "command": "check",
        "standing": loaded.standing,
        "files": counts_json(&loaded),
        "journal_entries": loaded.journal.len(),
        "failures": failures_json(&loaded),
    });
    json_out(if ok { 0 } else { 1 }, value)
}

fn cmd_wake(env: &Env, paths: &Paths, rest: &[String]) -> Outcome {
    let args = parse(rest);
    let loaded = match load::load(env, paths) {
        Ok(loaded) => loaded,
        Err(e) => return harness(&e),
    };
    let capsule = capsule::render(&loaded, env);
    if args.has("--markdown") {
        return text(0, &capsule);
    }
    json_out(
        0,
        json!({
            "ok": true,
            "command": "wake",
            "standing": loaded.standing,
            "files": counts_json(&loaded),
            "journal_entries": loaded.journal.len(),
            "failures": loaded.failures.len(),
            "capsule": capsule,
        }),
    )
}

fn cmd_remember(env: &Env, paths: &Paths, rest: &[String]) -> Outcome {
    let args = parse(rest);
    if args.positional.len() != 1 {
        return harness("remember takes exactly one quoted TEXT argument");
    }
    let body = args.positional[0].trim().to_string();
    if body.is_empty() {
        return harness("remember: TEXT is empty");
    }
    let private = args.has("--private");
    let tags = args.values("--about");
    if args.has("--kr") {
        let loaded = match load::load(env, paths) {
            Ok(loaded) => loaded,
            Err(e) => return harness(&e),
        };
        // Tags ride a trailing comment; nibli's lexer ignores it, `lucy about` reads it.
        let body = if tags.is_empty() {
            body
        } else {
            format!("{body} # about: {}", tags.join(", "))
        };
        let ids = match loaded.engine.assert_text(&body) {
            Ok(ids) => ids,
            Err(e) => {
                return finding(
                    json!({ "ok": false, "command": "remember", "kind": "kr", "error": e.to_string() }),
                );
            }
        };
        if ids.len() != 1 {
            return finding(
                json!({ "ok": false, "command": "remember", "kind": "kr", "error": format!("one statement per line: this text compiled to {} statements", ids.len()) }),
            );
        }
        let target = if private {
            &paths.private_memory
        } else {
            &paths.memory
        };
        if let Err(e) = files::append_line(target, &body) {
            return harness(&e);
        }
        let line = files::read_optional(target)
            .ok()
            .flatten()
            .map(|t| t.lines().count())
            .unwrap_or(0);
        return json_out(
            0,
            json!({ "ok": true, "command": "remember", "kind": "kr", "file": short_name(target), "line": line, "text": body }),
        );
    }
    let mut text = String::new();
    for tag in &tags {
        text.push_str(&format!("[about: {}] ", tag.trim()));
    }
    if let Some(source) = args.value("--source")
        && !source.trim().is_empty()
    {
        text.push_str(&format!("[reported: {}] ", source.trim()));
    }
    text.push_str(&body);
    let target = if private {
        &paths.private_journal
    } else {
        &paths.journal
    };
    let (date, hhmm) = files::now_utc();
    if let Err(e) = files::append_journal(target, &date, &hhmm, &env.host, &text) {
        return harness(&e);
    }
    json_out(
        0,
        json!({ "ok": true, "command": "remember", "kind": "journal", "file": short_name(target), "date": date, "time": format!("{hhmm} UTC"), "text": text }),
    )
}

fn cmd_ask(env: &Env, paths: &Paths, rest: &[String]) -> Outcome {
    let args = parse(rest);
    if args.positional.len() != 1 {
        return harness("ask takes exactly one quoted KR QUERY argument");
    }
    let loaded = match load::load(env, paths) {
        Ok(loaded) => loaded,
        Err(e) => return harness(&e),
    };
    match ask::ask(&loaded.engine, &args.positional[0]) {
        Ok(answer) => json_out(
            0,
            json!({
                "ok": true,
                "command": "ask",
                "query": answer.query,
                "verdict": answer.status,
                "detail": answer.detail,
                "why": answer.why,
                "proof": answer.proof,
                "cwa_false": answer.cwa_false,
                "naf_dependent": answer.naf_dependent,
                "envelope": answer.envelope,
                "failures": loaded.failures.len(),
            }),
        ),
        Err(e) => finding(json!({ "ok": false, "command": "ask", "error": e })),
    }
}

fn cmd_about(env: &Env, paths: &Paths, rest: &[String], history_only: bool) -> Outcome {
    let args = parse(rest);
    let command = if history_only { "history" } else { "about" };
    if args.positional.len() != 1 {
        return harness(&format!(
            "{command} takes exactly one THING argument (a topic, a term, or a path)"
        ));
    }
    let thing = args.positional[0].trim().to_string();
    let limit = args
        .value("--limit")
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(40);
    let loaded = match load::load(env, paths) {
        Ok(loaded) => loaded,
        Err(e) => return harness(&e),
    };
    let about = topics::about(&loaded, &env.home, &thing, limit);
    if history_only {
        let mut events: Vec<(String, String, String)> = about
            .commits
            .iter()
            .map(|c| {
                (
                    c.date.clone(),
                    "commit".to_string(),
                    format!("{} {}", c.hash, c.subject),
                )
            })
            .chain(about.journal.iter().map(|e| {
                (
                    e.date.clone(),
                    if e.private {
                        "journal (private)".to_string()
                    } else {
                        "journal".to_string()
                    },
                    e.text.clone(),
                )
            }))
            .collect();
        events.sort_by(|a, b| b.0.cmp(&a.0));
        if args.has("--markdown") {
            let mut out = format!("# History of {thing}\n");
            if events.is_empty() {
                out.push_str("- nothing recorded\n");
            }
            for (date, kind, text) in &events {
                out.push_str(&format!(
                    "- {date} [{kind}] {}\n",
                    text.replace('\n', "\n  ")
                ));
            }
            return text(0, &out);
        }
        let events_json: Vec<Value> = events
            .iter()
            .map(|(date, kind, text)| json!({ "date": date, "kind": kind, "text": text }))
            .collect();
        return json_out(
            0,
            json!({ "ok": true, "command": "history", "thing": thing, "is_path": about.is_path, "repo": about.repo.as_ref().map(|p| p.display().to_string()), "events": events_json }),
        );
    }
    if args.has("--markdown") {
        return text(0, &topics::render_about(&thing, &about));
    }
    json_out(
        0,
        json!({
            "ok": true,
            "command": "about",
            "thing": thing,
            "journal": about.journal.iter().map(|e| json!({ "date": e.date, "host": e.host, "private": e.private, "text": e.text, "tags": topics::tags_of(&e.text) })).collect::<Vec<_>>(),
            "memory": about.memory.iter().map(|m| json!({ "file": m.file, "line": m.line, "text": m.text, "private": m.private })).collect::<Vec<_>>(),
            "is_path": about.is_path,
            "repo": about.repo.as_ref().map(|p| p.display().to_string()),
            "commits": about.commits.iter().map(|c| json!({ "hash": c.hash, "date": c.date, "subject": c.subject })).collect::<Vec<_>>(),
        }),
    )
}

fn cmd_audit(env: &Env, paths: &Paths) -> Outcome {
    let loaded = match load::load(env, paths) {
        Ok(loaded) => loaded,
        Err(e) => return harness(&e),
    };
    let lines: Vec<Value> = loaded
        .memory
        .iter()
        .map(|m| {
            let error = loaded
                .failures
                .iter()
                .find(|f| f.file == m.file && f.line == m.line)
                .map(|f| f.error.clone());
            json!({ "file": m.file, "line": m.line, "text": m.text, "private": m.private, "ok": m.ok, "error": error })
        })
        .collect();
    json_out(
        0,
        json!({ "ok": true, "command": "audit", "lines": lines, "journal_entries": loaded.journal.len() }),
    )
}

fn cmd_forget(paths: &Paths, rest: &[String]) -> Outcome {
    let args = parse(rest);
    let Some(target) = args.positional.first() else {
        return harness("forget takes FILE:LINE, e.g. memory.nibli:12");
    };
    let Some((file, line)) = target.rsplit_once(':') else {
        return harness("forget takes FILE:LINE, e.g. memory.nibli:12");
    };
    let path = match file {
        "memory" | "memory.nibli" => &paths.memory,
        "private" | "private.nibli" => &paths.private_memory,
        other => {
            return harness(&format!(
                "forget: unknown file `{other}` (memory.nibli or private.nibli)"
            ));
        }
    };
    let Ok(line_no) = line.parse::<usize>() else {
        return harness(&format!("forget: `{line}` is not a line number"));
    };
    let Some(content) = files::read_optional(path).ok().flatten() else {
        return finding(
            json!({ "ok": false, "command": "forget", "error": format!("{} does not exist", short_name(path)) }),
        );
    };
    let mut lines: Vec<String> = content
        .lines()
        .map(|l| l.trim_end_matches('\r').to_string())
        .collect();
    if line_no == 0 || line_no > lines.len() {
        return finding(
            json!({ "ok": false, "command": "forget", "error": format!("{}:{} does not exist", short_name(path), line_no) }),
        );
    }
    let was = lines[line_no - 1].clone();
    let trimmed = was.trim();
    if trimmed.is_empty() || trimmed.starts_with('#') {
        return finding(
            json!({ "ok": false, "command": "forget", "error": format!("{}:{} is not a statement", short_name(path), line_no) }),
        );
    }
    let (date, _) = files::now_utc();
    lines[line_no - 1] = format!("# forgotten {date}: {was}");
    let mut text = lines.join("\n");
    text.push('\n');
    if let Err(e) = files::write_atomic(path, &text) {
        return harness(&e);
    }
    json_out(
        0,
        json!({ "ok": true, "command": "forget", "file": short_name(path), "line": line_no, "was": was }),
    )
}

fn cmd_address(rest: &[String]) -> Outcome {
    let text = rest.join(" ");
    let addressed = address::addresses_lucy(&text);
    json_out(
        if addressed { 0 } else { 1 },
        json!({ "ok": true, "command": "address", "addressed": addressed }),
    )
}

fn cmd_hook(env: &Env, paths: &Paths, rest: &[String], stdin: &str) -> Outcome {
    // Hooks never exit 2: in Claude Code that would block the user's prompt.
    match rest.first().map(String::as_str) {
        Some("user-prompt") => text(0, &hook::user_prompt(env, paths, stdin)),
        Some("session-start") => text(0, &hook::session_start(env, paths)),
        other => text(
            0,
            &format!(
                "lucy hook: unknown hook {:?} (user-prompt | session-start)\n",
                other.unwrap_or("")
            ),
        ),
    }
}
