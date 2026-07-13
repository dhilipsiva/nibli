//! The validation gates — the "verify" firewall around the LLM's output.
//!
//! KR-only since THE DROP: every candidate runs `klaro::parse_checked` →
//! smuni → the RENDER ROUND-TRIP gate (the drift-catcher: the candidate's
//! canonical re-spelling must compile to the SAME `LogicBuffer` — klaro's
//! pinned fixpoint contract, `klaro/src/render.rs`; AstBuffer equality is
//! deliberately NOT the contract there). The round-trip gate is pure Rust,
//! so it runs on native AND wasm. (The legacy Lojban chain — gerna + the
//! wasm-only camxes gate — retired with the Lojban front-end.)

use nibli_types::error::NibliError;
use nibli_types::logic::LogicBuffer;

/// Which gate rejected a candidate, carrying the compiler's own message. The
/// message is fed back verbatim into the LLM conversation as correction context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GateError {
    /// The front-end rejected the grammar (klaro's parse/resolve errors —
    /// including fail-closed dictionary-unknown aliases).
    Syntax(String),
    /// smuni rejected the semantics/arity (`NibliError::Semantic`).
    Semantic(String),
    /// The render round-trip gate: the candidate compiles, but its canonical
    /// re-spelling (`klaro::render`) fails to re-parse or compiles to a
    /// DIFFERENT `LogicBuffer` — the drift-catcher. *(native + wasm)*
    RoundTrip(String),
    /// The fresh-context semantic verifier judged that the candidate — though
    /// grammatically valid — does not MEAN what the source says (the message is
    /// the verifier's concrete mismatch list). Unlike the deterministic
    /// gates, this verdict comes from an LLM judge reading the `nibli_render`
    /// back-translation; it is best-effort advisory, but a mismatch still
    /// drives the same retry machinery as a hard gate failure.
    Verification(String),
}

impl GateError {
    /// Short human name of the gate that failed — for UI badges and logs.
    pub fn gate(&self) -> &'static str {
        match self {
            GateError::Syntax(_) => "klaro",
            GateError::Semantic(_) => "smuni",
            GateError::RoundTrip(_) => "round-trip",
            GateError::Verification(_) => "semantic verifier",
        }
    }

    /// The underlying compiler message.
    pub fn message(&self) -> &str {
        match self {
            GateError::Syntax(m)
            | GateError::Semantic(m)
            | GateError::RoundTrip(m)
            | GateError::Verification(m) => m,
        }
    }
}

/// Run the local gates in fail-fast order and return the compiled FOL on
/// success. Mirrors `nibli-ui`'s `compile_text` front-end (minus
/// `logji::transform_compute_nodes`, which the translator does not need):
/// klaro grammar (parse + fail-closed resolve) → smuni semantics → the render
/// round-trip gate. Which call fails determines the [`GateError`] variant: a
/// `parse_checked` failure is always a grammar error; a
/// `compile_from_gerna_ast` failure is a semantic one.
pub fn local_gates(candidate: &str) -> Result<LogicBuffer, GateError> {
    let ast = klaro::parse_checked(candidate).map_err(syntax)?;
    let buf = smuni::compile_from_gerna_ast(ast.clone()).map_err(semantic)?;
    klaro_round_trip(&ast, &buf)?;
    Ok(buf)
}

/// The render round-trip gate: render the accepted AST back to canonical
/// KR, re-parse and re-compile it, and demand the SAME `LogicBuffer` —
/// klaro's own fixpoint contract (`parse ∘ render ∘ parse` compiles equal for
/// klaro-originated buffers), enforced per candidate as a drift-catcher. Any
/// leg failing is a [`GateError::RoundTrip`] carrying the canonical
/// re-spelling, so the correction turn can steer the model toward it.
fn klaro_round_trip(ast: &nibli_types::ast::AstBuffer, buf: &LogicBuffer) -> Result<(), GateError> {
    let rendered = klaro::render::render(ast).map_err(|e| {
        GateError::RoundTrip(format!(
            "the canonical renderer could not re-spell the statement: {e}"
        ))
    })?;
    let ast2 = klaro::parse_checked(&rendered).map_err(|e| {
        GateError::RoundTrip(format!(
            "the canonical re-spelling {rendered:?} failed to re-parse: {e}"
        ))
    })?;
    let buf2 = smuni::compile_from_gerna_ast(ast2).map_err(|e| {
        GateError::RoundTrip(format!(
            "the canonical re-spelling {rendered:?} failed to re-compile: {e}"
        ))
    })?;
    if buf2 != *buf {
        return Err(GateError::RoundTrip(format!(
            "the statement compiles, but its canonical re-spelling {rendered:?} compiles to \
             different logic — prefer the canonical spelling"
        )));
    }
    Ok(())
}

/// The full validation gate the agent calls — [`local_gates`]; the round-trip
/// gate inside it is the third gate on every target.
pub fn validate(candidate: &str) -> Result<LogicBuffer, GateError> {
    local_gates(candidate)
}

/// Validate a multi-line KB the way `nibli-ui` uses it: each non-empty,
/// non-comment line must pass the gates on its own. Returns the first failing
/// line's error, tagged with its KB line number so the LLM can locate it. A
/// single-line candidate is simply validated as one statement, so this also
/// covers the single-sentence case.
pub fn validate_kb(text: &str) -> Result<(), GateError> {
    for (i, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        validate(line).map(|_| ()).map_err(|e| tag_line(e, i + 1))?;
    }
    Ok(())
}

/// Prefix a gate error with its KB line number, preserving the variant.
fn tag_line(e: GateError, line_no: usize) -> GateError {
    let msg = format!("(KB line {line_no}) {}", e.message());
    match e {
        GateError::Syntax(_) => GateError::Syntax(msg),
        GateError::Semantic(_) => GateError::Semantic(msg),
        GateError::RoundTrip(_) => GateError::RoundTrip(msg),
        GateError::Verification(_) => GateError::Verification(msg),
    }
}

fn syntax(e: NibliError) -> GateError {
    GateError::Syntax(e.to_string())
}

fn semantic(e: NibliError) -> GateError {
    GateError::Semantic(e.to_string())
}

/// The correction turn appended to the conversation when a gate rejects a
/// candidate: it names the gate, quotes the compiler's message, and asks for a
/// fix in the KB language only. Kept in one place so the phrasing is
/// consistent across gates.
pub fn feedback_for(err: &GateError) -> String {
    if let GateError::Verification(issues) = err {
        return format!(
            "That is grammatically valid but does not MEAN what the source says. An \
             independent reading of what your Klaro actually claims reported these \
             mismatches:\n{issues}\nRevise so the meaning matches the source; output ONLY \
             the corrected Klaro — no explanation."
        );
    }
    let (what, tool) = match err {
        GateError::Syntax(_) => ("is not valid Klaro", "klaro compiler"),
        GateError::Semantic(_) => (
            "parses but failed semantic compilation (e.g. a predicate got the wrong number of arguments)",
            "smuni compiler",
        ),
        GateError::RoundTrip(_) => (
            "compiles but is not canonical Klaro (its canonical re-spelling does not compile to the same logic)",
            "round-trip gate",
        ),
        GateError::Verification(_) => unreachable!("handled above"),
    };
    format!(
        "That {what}. The {tool} reported:\n{}\nFix it and output ONLY the corrected Klaro — no explanation.",
        err.message()
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_klaro_passes_local_gates() {
        // Same shape nibli-ui asserts as its default KB; runs all three
        // gates (klaro, smuni, round-trip).
        local_gates("dog(Adam).").expect("valid Klaro should pass the three local gates");
    }

    #[test]
    fn klaro_garbage_fails_at_the_grammar_gate() {
        let err = local_gates("dog(Adam") // no close paren / period
            .expect_err("malformed Klaro must be rejected");
        assert!(
            matches!(err, GateError::Syntax(_)),
            "expected Syntax, got {err:?}"
        );
        assert_eq!(err.gate(), "klaro");
    }

    #[test]
    fn klaro_unknown_alias_fails_closed_at_the_grammar_gate() {
        // Fail-closed name resolution (SURFACE_SYNTAX): an alias the dictionary
        // does not know is a COMPILE ERROR, not a silent new predicate.
        let err = local_gates("zzyzxq(Adam).").expect_err("unknown alias must fail closed");
        assert!(
            matches!(err, GateError::Syntax(_)),
            "expected Syntax (resolve), got {err:?}"
        );
    }

    #[test]
    fn klaro_round_trip_gate_holds_on_shipped_shapes() {
        // A cross-section of the determinism corpus' construct classes: the
        // canonical fixpoint must hold for anything the front-end accepts.
        for s in [
            "dog(Adam).",
            "animal(every dog).",
            "beautiful(every person where ~cat).",
            "Kim = Adam.",
            "past dog(Dan).",
            "red(exactly 2 red).",
            "~eats(Adam).",
        ] {
            validate(s)
                .unwrap_or_else(|e| panic!("round-trip gate rejected shipped shape {s:?}: {e:?}"));
        }
    }

    #[test]
    fn feedback_names_the_klaro_gates() {
        let fb = feedback_for(&GateError::Syntax("[Syntax Error] line 1:5: nope".into()));
        assert!(fb.contains("klaro compiler"));
        assert!(fb.contains("line 1:5"));
        assert!(fb.contains("corrected Klaro"));
        let fb = feedback_for(&GateError::RoundTrip(
            "canonical re-spelling differs".into(),
        ));
        assert!(fb.contains("round-trip gate"));
        assert!(fb.contains("corrected Klaro"));
        let fb = feedback_for(&GateError::Verification("1. off".into()));
        assert!(fb.contains("your Klaro"));
        assert!(fb.contains("corrected Klaro"));
    }

    #[test]
    fn validate_kb_passes_valid_multiline_and_skips_blanks_and_comments() {
        validate_kb("dog(Adam).\n# a note\n\neats(Adam).")
            .expect("every non-comment line is valid Klaro");
    }

    #[test]
    fn validate_kb_reports_the_failing_line_number() {
        let err = validate_kb("dog(Adam).\ndog(Adam").expect_err("line 2 is malformed Klaro");
        assert!(err.message().contains("KB line 2"), "got {err:?}");
    }
}
