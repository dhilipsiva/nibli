//! nibli-validate — batch validation via stdin.
//!
//! Reads one KR statement per line from stdin. For each line, runs the KR
//! front-end, nibli-semantics, and engine assertion ingress in a fresh KB.
//! This validates assertable KB input,
//! not every formula that is legal as a query: query-only `exactly N` / `no`
//! formulas and the reference external compute names (`exponential`,
//! `logarithm`) are rejected. Outputs one JSON object per line to stdout:
//!   {"line":"...","valid":true}
//!   {"line":"...","valid":false,"error":"parse error: ..."}

use nibli_engine::NibliEngine;
use std::io::{self, BufRead};
use std::process::ExitCode;

fn main() -> ExitCode {
    // nibli-engine is quiet by default (verbose off — we never call
    // `set_verbose`), so the engine emits no stdout diagnostics: our JSON result
    // lines are the only thing on stdout. We use `println!` for them (simple,
    // line-atomic); consumers parse the `{…}` lines.
    let engine = NibliEngine::new();

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

        match validate_statement(&engine, trimmed) {
            Ok(()) => {
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

/// Validate parse + compile + assertability in a fresh KB. `reset()` clears all
/// mutable state, so per-line reuse is equivalent to a fresh engine.
fn validate_statement(engine: &NibliEngine, statement: &str) -> Result<(), String> {
    engine.reset().map_err(|error| error.to_string())?;
    engine
        .assert_text(statement)
        .map(|_| ())
        .map_err(|error| error.to_string())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reporter_validates_kb_assertability_not_just_formula_compilation() {
        let engine = NibliEngine::new();
        validate_statement(&engine, "dog(Adam).").expect("ordinary fact");

        for statement in ["big(exactly 1 dog).", "big(no dog)."] {
            let error = validate_statement(&engine, statement)
                .expect_err("an outer count is query-only, even though it compiles");
            assert!(error.contains("query-only"), "{statement}: {error}");
            assert!(
                engine.list_facts().unwrap().is_empty(),
                "the rejected candidate must leave the fresh validator KB empty"
            );
        }

        validate_statement(&engine, "believe(me, fact { big(exactly 1 dog) }).")
            .expect("a count in opaque quoted content is assertable");
    }

    #[test]
    fn reporter_rejects_reference_external_compute_names() {
        let engine = NibliEngine::new();
        for statement in ["exponential(8, 2, 3).", "logarithm(3, 8, 2)."] {
            let error = validate_statement(&engine, statement)
                .expect_err("a reference compute name is query-only, registered or not");
            assert!(error.contains("query-only"), "{statement}: {error}");
            assert!(
                engine.list_facts().unwrap().is_empty(),
                "the rejected candidate must leave the fresh validator KB empty"
            );
        }

        validate_statement(&engine, "believe(me, fact { exponential(8, 2, 3) }).")
            .expect("a reference compute name in opaque quoted content is assertable");
    }
}
