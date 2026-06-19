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
    // The engine prints diagnostics ("Native engine ready", "[Skolem] …",
    // "[Rule] …") via `println!` to the global stdout. We MUST emit our JSON
    // results through that same line-atomic writer — `println!` — rather than a
    // separate BufWriter over `stdout.lock()`. Two independent buffers over fd 1
    // interleave: a JSON line straddling the BufWriter's flush boundary gets an
    // engine diagnostic spliced into it, corrupting it (the consumer then drops
    // that line as unparseable). Using `println!` for both, each call takes the
    // stdout lock and flushes a complete line on its newline, so no two lines
    // can ever split each other. Consumers filter the non-`{…}` diagnostic lines.
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
