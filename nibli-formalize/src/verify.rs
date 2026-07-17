//! The semantic verification turn — the fourth, non-deterministic check.
//!
//! The deterministic gates (nibli-kr → nibli-semantics → round-trip) prove a candidate is
//! *well-formed*; they cannot prove it *means* what the source says. Models
//! routinely emit syntactically valid KB text with wrong semantics — misresolved anaphora,
//! overflowed bridi places, deontics used as commands (`ei` for "you
//! must"). The int19h Genesis probe made the failure vivid: 8 of Gemini's 15
//! Genesis 1:1–8 lines pass every gate while claiming things like "John is a
//! name-word meaning a sun".
//!
//! So after the gates pass, the agent builds the `nibli_render`
//! back-translation of each KB line — the *engine's own reading* of what the
//! KB line actually claims, overlay-free (`Register::Spec`; the curated
//! `DomainGloss` overlays are UI-example-only and never used here) — and asks
//! a FRESH-context validator to compare it against the source. Fresh context
//! is structural: the Chat seam is stateless, so the validator call carries a
//! single user turn and its own system prompt — it never sees the translation
//! conversation and cannot green-light its own past output.
//!
//! Honest scope: this check is BEST-EFFORT ADVISORY. The deterministic gates
//! remain the hard guarantee; an unparseable validator reply or a validator
//! transport error never blocks a gate-clean translation (fail-open), while a
//! clear MISMATCH verdict drives the same bounded retry machinery as a hard
//! gate failure (`GateError::Verification`).

use crate::gates::{self, GateError};
use nibli_render::{Register, render_logic_buffer};

/// The validator's system prompt: an independent judge of MEANING only.
/// Language-neutral prose (the CLAIMS line is the IR-level `nibli_render`
/// gloss, identical whichever front-end compiled the KB line). The strict
/// first-line verdict format is what `parse_verdict` reads.
pub const VALIDATOR_SYSTEM_PROMPT: &str = "\
You are an independent semantic auditor for the formalization of English into a \
machine-checkable knowledge-base language. You will be given a SOURCE text and, for \
each line of a candidate formalization, the CLAIMS line — a mechanical English \
rendering of what that line actually asserts, produced by a deterministic compiler \
(not by the formalizer). Grammar has already been machine-checked; do NOT comment on \
grammar or style.

Judge ONE thing: does the set of claims match the meaning of the source text? Watch \
especially for: wrong or missing participants (misresolved pronouns/anaphora), arguments \
in the wrong predicate places, words whose claims say something unrelated to the source, \
missing assertions, and invented assertions.

Reply in EXACTLY this format: first line, the single word MATCH or MISMATCH. If \
MISMATCH, follow with a numbered list of concrete discrepancies, each naming the KB line \
number and stating what the line claims versus what the source says. No other text.";

/// Per-line back-translation of a gate-clean KB: `(kb_line, english_claims)`
/// for every non-empty, non-comment line (the same line discipline as
/// `gates::validate_kb`). Recompiles via `gates::local_gates` — cheap, and the
/// buffer was discarded by validation; the rendered gloss is IR-level. Errors
/// are defensively propagated but should be impossible for text that just
/// passed the gates.
pub fn back_translation(kb_text: &str) -> Result<Vec<(String, String)>, GateError> {
    let mut out = Vec::new();
    for raw in kb_text.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let buf = gates::local_gates(line)?;
        out.push((line.to_string(), render_logic_buffer(&buf, Register::Spec)));
    }
    Ok(out)
}

/// Build the validator's single user turn: the source, then each candidate
/// line with the engine's reading of it.
pub fn judge_prompt(source: &str, back: &[(String, String)]) -> String {
    let mut p = format!("SOURCE TEXT:\n{source}\n\nCANDIDATE FORMALIZATION (per KB line):\n");
    for (i, (kb_line, claims)) in back.iter().enumerate() {
        p.push_str(&format!("{}. {kb_line}\n   claims: {claims}\n", i + 1));
    }
    p.push_str("\nVerdict?");
    p
}

/// Read the validator's verdict. `None` = match (proceed); `Some(issues)` =
/// mismatch with the verifier's discrepancy list. FAIL-OPEN: a reply that
/// doesn't follow the format is treated as a match — the verification is
/// best-effort advisory and must never block a gate-clean translation on a
/// malformed judge reply.
pub fn parse_verdict(reply: &str) -> Option<String> {
    let mut lines = reply.trim().lines();
    let first = lines.next().unwrap_or("").trim().to_ascii_uppercase();
    if first.starts_with("MISMATCH") {
        let issues: String = lines.collect::<Vec<_>>().join("\n").trim().to_string();
        let issues = if issues.is_empty() {
            "the verifier judged the meaning does not match the source (no details given)"
                .to_string()
        } else {
            issues
        };
        Some(issues)
    } else {
        None
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    #[test]
    fn back_translation_renders_each_line() {
        let back = back_translation("dog(Adam).\n# comment\n\ncat(Betis).").unwrap();
        assert_eq!(back.len(), 2);
        assert_eq!(back[0].0, "dog(Adam).");
        assert!(
            back[0].1.to_lowercase().contains("adam"),
            "claims must mention the participant: {}",
            back[0].1
        );
    }

    #[test]
    fn judge_prompt_contains_source_lines_and_claims() {
        let back = vec![("dog(Adam).".to_string(), "adam is a dog".to_string())];
        let p = judge_prompt("Adam is a dog.", &back);
        assert!(p.contains("SOURCE TEXT:\nAdam is a dog."));
        assert!(p.contains("1. dog(Adam)."));
        assert!(p.contains("claims: adam is a dog"));
    }

    #[test]
    fn verdict_parsing_match_mismatch_and_fail_open() {
        assert_eq!(parse_verdict("MATCH"), None);
        assert_eq!(parse_verdict("  match  "), None);
        let v = parse_verdict("MISMATCH\n1. line 1 claims X but source says Y").unwrap();
        assert!(v.contains("line 1 claims X"));
        // Bare MISMATCH still carries a usable message.
        assert!(
            parse_verdict("MISMATCH")
                .unwrap()
                .contains("verifier judged")
        );
        // Fail-open: malformed replies never block.
        assert_eq!(parse_verdict("I think it's mostly fine?"), None);
        assert_eq!(parse_verdict(""), None);
    }
}
