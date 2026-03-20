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
use std::io::{self, BufRead, Write};

fn main() {
    // Suppress engine "Native engine ready" message by redirecting nothing —
    // it prints to stdout which we parse as JSON. We just deal with it in Python.
    let engine = NibliEngine::new();

    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        // Try to assert into a fresh KB to validate parse + compile.
        // Reset KB each time to avoid cross-contamination.
        engine.reset();
        match engine.assert_text(trimmed) {
            Ok(_fact_id) => {
                let escaped_line = escape_json(trimmed);
                let _ = writeln!(
                    out,
                    r#"{{"line":"{}","valid":true}}"#,
                    escaped_line
                );
            }
            Err(e) => {
                let escaped_line = escape_json(trimmed);
                let escaped_err = escape_json(&e);
                let _ = writeln!(
                    out,
                    r#"{{"line":"{}","valid":false,"error":"{}"}}"#,
                    escaped_line, escaped_err
                );
            }
        }
    }

    let _ = out.flush();
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
