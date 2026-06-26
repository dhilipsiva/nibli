//! nibli-validate — batch Lojban validation via stdin.
//!
//! Reads one Lojban sentence per line from stdin.
//! For each line, runs gerna (parse) and smuni (compile to FOL).
//! Outputs one JSON object per line to stdout:
//!   {"line":"...","valid":true}
//!   {"line":"...","valid":false,"error":"parse error: ..."}
//!
//! Used by python/generate_training_data.py for batch validation.

use nibli_engine::NibliEngine;
use std::io::{self, BufRead};

fn main() {
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
