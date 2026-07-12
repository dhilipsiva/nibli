//! lojban2klaro — mechanical `.lojban` → `.klaro` corpus migration.
//!
//! Usage: lojban2klaro <src.lojban> <dst.klaro>
//!
//! Line-by-line, preserving the file's structure at IDENTICAL line numbers
//! (the twins gate `verify-klaro-twins` pins this):
//! - `#` comments (including `# =>` verdict annotations — they are comments)
//!   and blank lines: copied byte-for-byte.
//! - `:`-prefixed REPL-command lines (e.g. `:retract 0`): copied byte-for-byte.
//! - `? ` query lines: the prefix is kept, the Lojban payload is translated.
//! - everything else: the whole line is a Lojban payload, translated.
//!
//! Translation = `gerna::parse_checked` → `klaro::render::render`, fail-closed:
//! any parse/render error, or a payload rendering to MULTIPLE Klaro statements
//! (a bare-`.i` line would break the line-number correspondence), aborts with
//! the offending file:line. RE-RUNNABLE: the destination is overwritten, so
//! `just migrate-corpora` regenerates the twins while the corpora still change
//! during the dual-front-end phase.

use std::process::ExitCode;

fn translate(payload: &str) -> Result<String, String> {
    let buffer = gerna::parse_checked(payload).map_err(|e| format!("gerna: {e}"))?;
    let rendered = klaro::render::render(&buffer).map_err(|e| format!("render: {e}"))?;
    if rendered.contains('\n') {
        return Err(format!(
            "payload renders to multiple Klaro statements (bare `.i`?), which would \
             break the twins' line-number correspondence: {rendered:?}"
        ));
    }
    Ok(rendered)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [src, dst] = args.as_slice() else {
        eprintln!("usage: lojban2klaro <src.lojban> <dst.klaro>");
        return ExitCode::FAILURE;
    };

    let source = match std::fs::read_to_string(src) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {src}: {e}");
            return ExitCode::FAILURE;
        }
    };

    let mut out: Vec<String> = Vec::new();
    let mut errors = 0u32;
    for (idx, line) in source.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') || trimmed.starts_with(':') {
            out.push(line.to_string());
        } else if let Some(payload) = line.strip_prefix("? ") {
            match translate(payload) {
                Ok(klaro) => out.push(format!("? {klaro}")),
                Err(e) => {
                    eprintln!("{src}:{}: {e}", idx + 1);
                    errors += 1;
                    out.push(line.to_string());
                }
            }
        } else {
            match translate(line) {
                Ok(klaro) => out.push(klaro),
                Err(e) => {
                    eprintln!("{src}:{}: {e}", idx + 1);
                    errors += 1;
                    out.push(line.to_string());
                }
            }
        }
    }

    if errors > 0 {
        eprintln!("error: {errors} line(s) failed to translate — {dst} NOT written");
        return ExitCode::FAILURE;
    }

    let mut text = out.join("\n");
    text.push('\n');
    if let Err(e) = std::fs::write(dst, text) {
        eprintln!("error: cannot write {dst}: {e}");
        return ExitCode::FAILURE;
    }
    println!("[migrate] {src} -> {dst} ({} lines)", out.len());
    ExitCode::SUCCESS
}
