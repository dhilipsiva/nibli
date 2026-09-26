//! Command dispatch and the output contract: one JSON object on stdout for
//! every command except `wake --markdown` and the hooks, prose on stderr,
//! exit 0 ok / 1 finding / 2 harness (missing folder, bad arguments, I/O).

use std::path::PathBuf;

use serde_json::{Value, json};

use crate::env::Env;
use crate::files::{self, Paths, short_name};
use crate::interactions::{Interaction, Kind};
use crate::{CONSTITUTION_TEMPLATE, address, ask, capsule, hook, interactions, load, talk, topics};

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
                                     append a note to the conversation KB, or with --kr a
                                     nibli statement to memory.nibli (checked first)
  lucy record \"TEXT\" --speaker NAME [--source NAME] [--session ID] [--id ID]
                                     save the complete message; --stdin reads exact text
                                     --json reads one record or a batch from stdin
  lucy claim \"KR STATEMENT\" --from ID [--decision] [--text \"INTERPRETATION\"]
                                     save attributed KR, quoting it without asserting it
  lucy transcript [--markdown]       read complete messages, notes and attributed claims
  lucy migrate-journal               import old journals into the KB, once per archive
  lucy ask \"KR QUERY\" [--conversations]
                                     answer with verdict, proof and envelope; the flag
                                     queries the conversation KB without the constitution
  lucy about THING [--markdown]      everything she holds about a thing: tagged and matching
                                     journal entries, formal lines, git history
  lucy history THING [--markdown]    the git log of a path or term merged with her record of it
  lucy talk \"MESSAGE\" [--model M] [--about THING]... [--markdown]
  lucy task WORDS...                 answer as Lucy through a local Ollama model and record it
                                     (task takes the rest of the line unquoted)
  lucy dataset --home DIR --out DIR  export my public memory for fine-tuning: knowledge,
                                     engine-checked probes, system prompt, manifest; refuses
                                     a folder that holds any private file
  lucy audit                         list every formal memory line with its compile status
  lucy forget FILE:LINE              comment a line out of memory.nibli or private.nibli
  lucy address \"TEXT\"                exit 0 if TEXT starts by addressing Lucy, else 1
  lucy hook user-prompt              Claude Code UserPromptSubmit hook (JSON on stdin)
  lucy hook session-start            Claude Code SessionStart hook

Memory folder: LUCY_HOME, else a lucy/ folder in this directory or a parent, else ~/.lucy.
Environment: LUCY_HOME, LUCY_HOST, LUCY_CAPSULE_MAX_BYTES, LUCY_MAX_CHAIN_DEPTH,
             LUCY_OLLAMA_URL (default http://127.0.0.1:11434), LUCY_MODEL, LUCY_TALK_TIMEOUT_SECS.
";

/// Whether the command wants stdin.
pub fn reads_stdin(args: &[String]) -> bool {
    args.first().map(String::as_str) == Some("hook")
        || (args.first().map(String::as_str) == Some("record")
            && args.iter().any(|a| a == "--stdin" || a == "--json"))
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
        // Takes its folder only from --home: the process's own memory folder,
        // which holds private files, is never resolved for an export.
        "dataset" => return cmd_dataset(&args[1..]),
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
        "record" => cmd_record(&env, &paths, rest, stdin),
        "claim" => cmd_claim(&env, &paths, rest),
        "transcript" => cmd_transcript(&paths, rest),
        "migrate-journal" => match interactions::migrate(&paths) {
            Ok(imported) => json_out(
                0,
                json!({"ok": true, "command": "migrate-journal", "imported": imported}),
            ),
            Err(e) => harness(&e),
        },
        "ask" => cmd_ask(&env, &paths, rest),
        "talk" | "task" => cmd_talk(&env, &paths, rest),
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

const VALUE_FLAGS: &[&str] = &[
    "--name",
    "--source",
    "--about",
    "--limit",
    "--model",
    "--speaker",
    "--session",
    "--id",
    "--channel",
    "--kind",
    "--from",
    "--text",
    "--home",
    "--out",
];

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
    let entry = Interaction {
        speaker: "Lucy".into(),
        text: args.positional[0].clone(),
        kind: Kind::Note,
        source: args.value("--source").unwrap_or("").into(),
        about: tags.iter().map(|s| s.to_string()).collect(),
        private,
        ..Interaction::default()
    };
    recorded(env, paths, "remember", vec![entry])
}

fn recorded(env: &Env, paths: &Paths, command: &str, entries: Vec<Interaction>) -> Outcome {
    match interactions::append(env, paths, entries) {
        Ok(records) => json_out(
            0,
            json!({
                "ok": true, "command": command,
                "file": short_name(interactions::archive_path(paths, records[0].private)),
                "records": records,
            }),
        ),
        Err(e) => harness(&e),
    }
}

fn cmd_record(env: &Env, paths: &Paths, rest: &[String], stdin: &str) -> Outcome {
    let args = parse(rest);
    if args.has("--json") {
        if rest.len() != 1 {
            return harness("record --json takes metadata in the JSON, with no other arguments");
        }
        let entries = serde_json::from_str::<Value>(stdin).and_then(|value| {
            if value.is_array() {
                serde_json::from_value::<Vec<Interaction>>(value)
            } else {
                serde_json::from_value::<Interaction>(value).map(|entry| vec![entry])
            }
        });
        return match entries {
            Ok(entries) => recorded(env, paths, "record", entries),
            Err(e) => harness(&format!("record JSON: {e}")),
        };
    }
    let body = if args.has("--stdin") && args.positional.is_empty() {
        stdin.to_string()
    } else if !args.has("--stdin") && args.positional.len() == 1 {
        args.positional[0].clone()
    } else {
        return harness("record takes exactly one TEXT argument, or --stdin");
    };
    let Some(speaker) = args.value("--speaker") else {
        return harness("record requires --speaker NAME");
    };
    let kind = match args.value("--kind").unwrap_or("message") {
        "message" => Kind::Message,
        "summary" => Kind::Summary,
        "note" => Kind::Note,
        _ => {
            return harness(
                "record --kind is message, summary or note; use claim for interpreted KR",
            );
        }
    };
    recorded(
        env,
        paths,
        "record",
        vec![Interaction {
            id: args.value("--id").unwrap_or("").into(),
            speaker: speaker.into(),
            text: body,
            kind,
            source: args.value("--source").unwrap_or("").into(),
            session: args.value("--session").unwrap_or("").into(),
            channel: args.value("--channel").unwrap_or("").into(),
            about: args
                .values("--about")
                .iter()
                .map(|s| s.to_string())
                .collect(),
            private: args.has("--private"),
            ..Interaction::default()
        }],
    )
}

fn cmd_claim(env: &Env, paths: &Paths, rest: &[String]) -> Outcome {
    let args = parse(rest);
    if args.positional.len() != 1 || args.value("--from").is_none() {
        return harness("claim takes one KR statement and --from MESSAGE_ID");
    }
    let from = args.value("--from").unwrap();
    let entries = interactions::read(paths, false).and_then(|mut entries| {
        entries.extend(interactions::read(paths, true)?);
        Ok(entries)
    });
    let entries = match entries {
        Ok(entries) => entries,
        Err(e) => return harness(&e),
    };
    let Some(origin) = entries.iter().find(|e| e.id == from) else {
        return harness(&format!("source interaction {from} does not exist"));
    };
    recorded(
        env,
        paths,
        "claim",
        vec![Interaction {
            id: args.value("--id").unwrap_or("").into(),
            speaker: origin.speaker.clone(),
            text: args.value("--text").unwrap_or(&args.positional[0]).into(),
            kind: if args.has("--decision") {
                Kind::Decision
            } else {
                Kind::Claim
            },
            source: origin.source.clone(),
            session: origin.session.clone(),
            about: origin.about.clone(),
            private: origin.private,
            from: Some(origin.id.clone()),
            kr: Some(args.positional[0].clone()),
            ..Interaction::default()
        }],
    )
}

fn cmd_dataset(rest: &[String]) -> Outcome {
    let args = parse(rest);
    let (Some(home), Some(out)) = (args.value("--home"), args.value("--out")) else {
        return harness("dataset takes --home DIR (a fresh public clone's lucy/) and --out DIR");
    };
    if !args.positional.is_empty() {
        return harness("dataset takes no positional arguments");
    }
    let export = match crate::dataset::build(std::path::Path::new(home)) {
        Ok(export) => export,
        Err(e) => return harness(&e),
    };
    if let Err(e) = crate::dataset::write(&export, std::path::Path::new(out)) {
        return harness(&e);
    }
    json_out(
        0,
        json!({
            "ok": true, "command": "dataset", "out": out,
            "items": export.items.len(), "probes": export.probes.len(),
            "dropped": export.dropped.len(), "manifest": export.manifest,
        }),
    )
}

fn cmd_transcript(paths: &Paths, rest: &[String]) -> Outcome {
    let args = parse(rest);
    let entries = interactions::read(paths, false).and_then(|mut entries| {
        entries.extend(interactions::read(paths, true)?);
        Ok(entries)
    });
    let mut entries = match entries {
        Ok(entries) => entries,
        Err(e) => return harness(&e),
    };
    if let Some(session) = args.value("--session") {
        entries.retain(|e| e.session == session);
    }
    if let Some(id) = args.value("--id") {
        entries.retain(|e| e.id == id);
    }
    entries.sort_by(|a, b| a.timestamp.cmp(&b.timestamp));
    if args.has("--markdown") {
        let mut out = String::from("# Lucy transcript\n");
        for entry in entries {
            out.push_str(&format!(
                "\n## {} · {} · {}{}\n\n{}\n",
                entry.timestamp,
                entry.speaker,
                entry.id,
                if entry.private { " (private)" } else { "" },
                entry.text
            ));
            if let Some(from) = entry.from {
                out.push_str(&format!("\nAttributed to {from}.\n"));
            }
        }
        text(0, &out)
    } else {
        json_out(
            0,
            json!({"ok": true, "command": "transcript", "records": entries}),
        )
    }
}

fn cmd_ask(env: &Env, paths: &Paths, rest: &[String]) -> Outcome {
    let args = parse(rest);
    if args.positional.len() != 1 {
        return harness("ask takes exactly one quoted KR QUERY argument");
    }
    let scope = if args.has("--conversations") {
        "conversations"
    } else {
        "all"
    };
    let (engine, failures) = if args.has("--conversations") {
        let engine = match interactions::query_engine(paths) {
            Ok(engine) => engine,
            Err(e) => return harness(&e),
        };
        if !env.materialize {
            engine.set_materialization(false);
        }
        if let Some(depth) = env.max_chain_depth
            && let Err(e) = engine.set_max_chain_depth(depth)
        {
            return harness(&e.to_string());
        }
        (engine, 0)
    } else {
        match load::load(env, paths) {
            Ok(loaded) => (loaded.engine, loaded.failures.len()),
            Err(e) => return harness(&e),
        }
    };
    match ask::ask(&engine, &args.positional[0]) {
        Ok(answer) => json_out(
            0,
            json!({
                "ok": true,
                "command": "ask",
                "scope": scope,
                "query": answer.query,
                "verdict": answer.status,
                "detail": answer.detail,
                "why": answer.why,
                "proof": answer.proof,
                "cwa_false": answer.cwa_false,
                "naf_dependent": answer.naf_dependent,
                "envelope": answer.envelope,
                "failures": failures,
            }),
        ),
        Err(e) => finding(json!({ "ok": false, "command": "ask", "error": e })),
    }
}

fn cmd_talk(env: &Env, paths: &Paths, rest: &[String]) -> Outcome {
    let args = parse(rest);
    // `lucy task summarize your constitution` works unquoted: the words join.
    let joined = args.positional.join(" ");
    let message = joined.as_str();
    if message.trim().is_empty() {
        return harness("talk takes a MESSAGE (quoted, or the rest of the line)");
    }
    if files::read_optional(&paths.constitution)
        .ok()
        .flatten()
        .is_none()
    {
        return harness(&format!(
            "no memory at {}: run `lucy init`",
            env.home.display()
        ));
    }
    let tags = args.values("--about");
    // Ollama is meant to be local; anything else travels as cleartext HTTP.
    let warning = match talk::parse_url(&env.ollama_url) {
        Ok((host, _, _))
            if !matches!(host.as_str(), "127.0.0.1" | "localhost" | "::1" | "[::1]") =>
        {
            format!(
                "lucy talk: {} is not loopback; the capsule and the reply travel as cleartext HTTP\n",
                env.ollama_url
            )
        }
        _ => String::new(),
    };
    let mut outcome = match talk::talk(env, paths, message, &tags, args.value("--model")) {
        Ok(result) => {
            if args.has("--markdown") {
                text(0, &format!("{}\n", result.reply))
            } else {
                json_out(
                    0,
                    json!({
                        "ok": true,
                        "command": "talk",
                        "model": result.model,
                        "reply": result.reply,
                        "file": result.file,
                        "url": env.ollama_url,
                    }),
                )
            }
        }
        Err(e) => {
            finding(json!({ "ok": false, "command": "talk", "error": e, "url": env.ollama_url }))
        }
    };
    outcome.stderr.push_str(&warning);
    outcome
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
