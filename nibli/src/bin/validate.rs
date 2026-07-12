//! nibli-validate — batch validation via stdin.
//!
//! Reads one sentence per line from stdin (Lojban by default; `--lang klaro`
//! or `NIBLI_LANG=klaro` selects the Klaro front-end — the flag wins over the
//! env var, and the default follows the engine default).
//! For each line, runs the selected front-end and smuni (compile to FOL).
//! Outputs one JSON object per line to stdout:
//!   {"line":"...","valid":true}
//!   {"line":"...","valid":false,"error":"parse error: ..."}
//!
//! Used by python/generate_training_data.py and book/tools/verify_book.py for
//! batch validation (both invoke it with no flags — the default is load-bearing).

use nibli_engine::{Language, NibliEngine};
use std::io::{self, BufRead};
use std::process::ExitCode;

fn main() -> ExitCode {
    // --lang errors are FATAL (an explicit flag must not be silently ignored);
    // a bad NIBLI_LANG only WARNS and falls back (ambient config must not
    // break pipelines that didn't opt in). Flag wins over env.
    let mut lang: Option<Language> = None;
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--lang" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --lang needs a value (klaro|lojban)");
                    return ExitCode::FAILURE;
                };
                match value.parse::<Language>() {
                    Ok(l) => lang = Some(l),
                    Err(e) => {
                        eprintln!("error: --lang: {e}");
                        return ExitCode::FAILURE;
                    }
                }
            }
            other => {
                eprintln!(
                    "error: unexpected argument '{other}' (usage: nibli-validate [--lang klaro|lojban])"
                );
                return ExitCode::FAILURE;
            }
        }
        i += 1;
    }
    if lang.is_none()
        && let Ok(value) = std::env::var("NIBLI_LANG")
    {
        match value.parse::<Language>() {
            Ok(l) => lang = Some(l),
            Err(e) => eprintln!("warning: NIBLI_LANG ignored: {e}"),
        }
    }

    // nibli-engine is quiet by default (verbose off — we never call
    // `set_verbose`), so the engine emits no stdout diagnostics: our JSON result
    // lines are the only thing on stdout. We use `println!` for them (simple,
    // line-atomic); consumers parse the `{…}` lines.
    let engine = NibliEngine::new();
    if let Some(l) = lang {
        // Set once: the language is configuration and survives the per-line
        // `reset()` (pinned by the engine's language tests).
        engine.set_language(l);
    }

    let stdin = io::stdin();

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        // Validate parse + compile in a fresh KB. `reset()` clears all mutable
        // state, so per-line reuse is equivalent to a fresh engine.
        engine.reset();
        match engine.assert_text(trimmed) {
            Ok(_fact_id) => {
                let escaped_line = escape_json(trimmed);
                println!(r#"{{"line":"{}","valid":true}}"#, escaped_line);
            }
            Err(e) => {
                let escaped_line = escape_json(trimmed);
                let escaped_err = escape_json(&e.to_string());
                println!(
                    r#"{{"line":"{}","valid":false,"error":"{}"}}"#,
                    escaped_line, escaped_err
                );
            }
        }
    }

    ExitCode::SUCCESS
}

/// Escape a string for embedding in JSON.
fn escape_json(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str(r#"\""#),
            '\\' => out.push_str(r#"\\"#),
            '\n' => out.push_str(r#"\n"#),
            '\r' => out.push_str(r#"\r"#),
            '\t' => out.push_str(r#"\t"#),
            c => out.push(c),
        }
    }
    out
}
