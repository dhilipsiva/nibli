//! The corpora-twins honesty gate (`just verify-klaro-twins`, part of `ci`) —
//! the shipped-corpora leg of SURFACE_SYNTAX §13 obligation 3, making the
//! dual-front-end phase self-policing:
//!
//! 1. Twin existence BOTH directions: every repo-root `.lojban` corpus has a
//!    committed `.klaro` twin and vice versa.
//! 2. Line-structure correspondence at IDENTICAL line numbers: comments,
//!    blanks and `:`-command lines byte-identical; `? ` query prefixes paired.
//! 3. Per-payload-line equality: the Lojban line and its Klaro twin line must
//!    compile to the SAME canonicalized LogicBuffer. DUAL-MODE: a fallback
//!    build lacks the generated long-tail aliases, so twin lines whose Klaro
//!    side hits the fail-closed "unknown predicate" are tallied as
//!    fallback-vocab skips (the translation battery's disclosed degradation);
//!    the full local build checks every line.
//!
//! The Klaro determinism leg (`determinism_corpus_klaro_native`) was RE-HOMED
//! to `tests/kr_seam_gate.rs` (2026-07-12): this whole twins gate dies with
//! the Lojban front-end at THE DROP (TODO.md), and the determinism leg
//! must outlive it.

use nibli_verify::klaro_battery::{canonical, kompile};
use nibli_verify::seam;

const PAIRS: &[(&str, &str, &str)] = &[
    (
        "gdpr",
        include_str!("../../gdpr.lojban"),
        include_str!("../../gdpr.klaro"),
    ),
    (
        "drug-interactions",
        include_str!("../../drug-interactions.lojban"),
        include_str!("../../drug-interactions.klaro"),
    ),
    (
        "readme",
        include_str!("../../readme.lojban"),
        include_str!("../../readme.klaro"),
    ),
    (
        "determinism-corpus",
        include_str!("../../determinism-corpus.lojban"),
        include_str!("../../determinism-corpus.klaro"),
    ),
];

/// Mode read from the artifact under test (the established convention).
fn full_mode() -> bool {
    klaro_dictionary::GISMU_TO_ALIAS.len() >= 1000
}

#[test]
fn twin_files_exist_both_directions() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut lojban: Vec<String> = Vec::new();
    let mut klaro: Vec<String> = Vec::new();
    for entry in std::fs::read_dir(&root).expect("repo root") {
        let path = entry.expect("dir entry").path();
        let (Some(stem), Some(ext)) = (
            path.file_stem().and_then(|s| s.to_str()),
            path.extension().and_then(|e| e.to_str()),
        ) else {
            continue;
        };
        match ext {
            "lojban" => lojban.push(stem.to_string()),
            "klaro" => klaro.push(stem.to_string()),
            _ => {}
        }
    }
    lojban.sort();
    klaro.sort();
    assert_eq!(
        lojban, klaro,
        "every repo-root .lojban corpus needs a .klaro twin and vice versa \
         (run `just migrate-corpora`)"
    );
    assert!(lojban.len() >= 4, "corpus set hollowed out: {lojban:?}");
}

#[test]
fn corpus_twins_line_structure_and_buffer_equality() {
    let full = full_mode();
    let mut checked = 0usize;
    let mut vocab_skipped = 0usize;
    let mut failures: Vec<String> = Vec::new();

    for (name, loj_text, klaro_text) in PAIRS {
        let loj_lines: Vec<&str> = loj_text.lines().collect();
        let klaro_lines: Vec<&str> = klaro_text.lines().collect();
        assert_eq!(
            loj_lines.len(),
            klaro_lines.len(),
            "{name}: twin line counts differ (run `just migrate-corpora`)"
        );

        let mut corpus_checked = 0usize;
        for (idx, (loj, kla)) in loj_lines.iter().zip(&klaro_lines).enumerate() {
            let n = idx + 1;
            let loj_trim = loj.trim();
            // Structure lines: byte-identical in the twin.
            if loj_trim.is_empty() || loj_trim.starts_with('#') || loj_trim.starts_with(':') {
                assert_eq!(
                    loj, kla,
                    "{name}:{n}: comment/blank/command lines must be byte-identical"
                );
                continue;
            }
            // Payload lines: `? ` prefixes must pair; payloads must compile equal.
            let (loj_payload, kla_payload) = match (loj.strip_prefix("? "), kla.strip_prefix("? "))
            {
                (Some(l), Some(k)) => (l, k),
                (None, None) => (*loj, *kla),
                _ => panic!("{name}:{n}: `? ` prefix present on only one twin line"),
            };
            let klaro_buf = match kompile(kla_payload) {
                Ok(buf) => buf,
                Err(e) if !full && e.contains("unknown predicate") => {
                    // Long-tail vocabulary outside the curated fallback core.
                    vocab_skipped += 1;
                    continue;
                }
                Err(e) => {
                    failures.push(format!("{name}:{n}: klaro side failed: {e}"));
                    continue;
                }
            };
            let loj_buf = match seam::compile(loj_payload) {
                Ok(buf) => buf,
                Err(e) => {
                    failures.push(format!("{name}:{n}: lojban side failed: {e}"));
                    continue;
                }
            };
            if canonical(&klaro_buf) != canonical(&loj_buf) {
                failures.push(format!(
                    "{name}:{n}: twin buffers differ\n  lojban: {loj_payload}\n  klaro:  {kla_payload}"
                ));
                continue;
            }
            checked += 1;
            corpus_checked += 1;
        }
        assert!(
            corpus_checked >= 1,
            "{name}: no payload line checked (hollowed out)"
        );
    }

    println!(
        "klaro twins: {checked} payload pairs checked, {vocab_skipped} fallback-vocab-skipped"
    );
    if !full {
        eprintln!(
            "klaro twins: FALLBACK MODE — {vocab_skipped} twin lines use vocabulary beyond \
             the curated core. Full validation needs `just fetch-dict` + rebuild."
        );
    }
    assert!(
        failures.is_empty(),
        "{} twin failure(s):\n{}",
        failures.len(),
        failures.join("\n---\n")
    );
    // First real run: 144 payload pairs across the four corpora (full mode).
    let floor = if full { 120 } else { 25 };
    assert!(
        checked >= floor,
        "twins gate hollowed out: {checked} pairs checked (floor {floor})"
    );
}
