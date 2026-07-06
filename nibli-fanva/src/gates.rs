//! The validation gates — the "verify" firewall around the LLM's output.
//!
//! [`local_gates`] runs the two offline gates (gerna grammar → smuni semantics)
//! and returns the compiled FOL [`LogicBuffer`] on success. The third "official"
//! gate (vendored `camxes.js` via JS-interop) is wasm-only and lands in a later
//! phase; [`GateError::Official`] is already defined so [`feedback_for`] and the
//! agent loop don't change shape when it arrives.

use nibli_types::error::NibliError;
use nibli_types::logic::LogicBuffer;

/// Which gate rejected a candidate, carrying the compiler's own message. The
/// message is fed back verbatim into the LLM conversation as correction context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GateError {
    /// gerna rejected the grammar (`NibliError::Syntax`, e.g. `[Syntax Error] line L:C: …`).
    Syntax(String),
    /// smuni rejected the semantics/arity (`NibliError::Semantic`).
    Semantic(String),
    /// The official grammar (`camxes.js`) rejected it. *(wasm-only gate; later phase)*
    Official(String),
}

impl GateError {
    /// Short human name of the gate that failed — for UI badges and logs.
    pub fn gate(&self) -> &'static str {
        match self {
            GateError::Syntax(_) => "gerna",
            GateError::Semantic(_) => "smuni",
            GateError::Official(_) => "camxes",
        }
    }

    /// The underlying compiler message.
    pub fn message(&self) -> &str {
        match self {
            GateError::Syntax(m) | GateError::Semantic(m) | GateError::Official(m) => m,
        }
    }
}

/// Run the two local gates in fail-fast order (grammar, then semantics) and
/// return the compiled FOL on success. Mirrors `nibli-ui`'s `compile_text`
/// front-end (minus `logji::transform_compute_nodes`, which the translator does
/// not need). Which call fails determines the [`GateError`] variant: a
/// `parse_checked` failure is always a grammar error; a `compile_from_gerna_ast`
/// failure is a semantic one.
pub fn local_gates(candidate: &str) -> Result<LogicBuffer, GateError> {
    let ast = gerna::parse_checked(candidate).map_err(syntax)?;
    smuni::compile_from_gerna_ast(ast).map_err(semantic)
}

/// The full validation gate the agent calls. Today this is exactly
/// [`local_gates`]; the wasm-only official (`camxes.js`) gate joins here in a
/// later phase without changing this signature, so the agent loop is stable.
pub fn validate(candidate: &str) -> Result<LogicBuffer, GateError> {
    local_gates(candidate)
}

fn syntax(e: NibliError) -> GateError {
    GateError::Syntax(e.to_string())
}

fn semantic(e: NibliError) -> GateError {
    GateError::Semantic(e.to_string())
}

/// The correction turn appended to the conversation when a gate rejects a
/// candidate: it names the gate, quotes the compiler's message, and asks for a
/// Lojban-only fix. Kept in one place so the phrasing is consistent across gates.
pub fn feedback_for(err: &GateError) -> String {
    let (what, tool) = match err {
        GateError::Syntax(_) => ("is not grammatically valid Lojban", "gerna parser"),
        GateError::Semantic(_) => (
            "parses but failed semantic compilation (e.g. a predicate got the wrong number of arguments)",
            "smuni compiler",
        ),
        GateError::Official(_) => ("is not valid standard Lojban", "camxes parser"),
    };
    format!(
        "That {what}. The {tool} reported:\n{}\nFix it and output ONLY the corrected Lojban — no explanation.",
        err.message()
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_lojban_passes_local_gates() {
        // Same shape nibli-ui asserts as its default KB; must compile cleanly.
        local_gates("la .adam. cu gerku").expect("valid Lojban should pass both local gates");
    }

    #[test]
    fn syntactic_garbage_fails_at_the_grammar_gate() {
        // Invalid bytes after a valid sentence — gerna fails closed (from gerna's own tests).
        let err = local_gates("la .adam. cu gerku .i \u{ff}\u{ff}\u{ff}")
            .expect_err("ungrammatical input must be rejected");
        assert!(
            matches!(err, GateError::Syntax(_)),
            "expected Syntax, got {err:?}"
        );
    }

    #[test]
    fn feedback_names_the_failing_gate() {
        let fb = feedback_for(&GateError::Syntax("[Syntax Error] line 1:5: nope".into()));
        assert!(fb.contains("gerna parser"));
        assert!(fb.contains("line 1:5"));
    }
}
