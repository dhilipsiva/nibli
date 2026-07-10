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
    /// The fresh-context semantic verifier judged that the candidate — though
    /// grammatically valid — does not MEAN what the source says (the message is
    /// the verifier's concrete mismatch list). Unlike the three deterministic
    /// gates, this verdict comes from an LLM judge reading the `nibli_render`
    /// back-translation; it is best-effort advisory, but a mismatch still
    /// drives the same retry machinery as a hard gate failure.
    Verification(String),
}

impl GateError {
    /// Short human name of the gate that failed — for UI badges and logs.
    pub fn gate(&self) -> &'static str {
        match self {
            GateError::Syntax(_) => "gerna",
            GateError::Semantic(_) => "smuni",
            GateError::Official(_) => "camxes",
            GateError::Verification(_) => "semantic verifier",
        }
    }

    /// The underlying compiler message.
    pub fn message(&self) -> &str {
        match self {
            GateError::Syntax(m)
            | GateError::Semantic(m)
            | GateError::Official(m)
            | GateError::Verification(m) => m,
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
    let buf = local_gates(candidate)?;
    // The third gate is the local (browser) camxes parser — wasm-only.
    #[cfg(target_arch = "wasm32")]
    official_gate(candidate)?;
    Ok(buf)
}

/// The "official" grammar gate: the vendored standard **camxes** parser
/// (ilmentufa), run locally in the browser through the `window.camxes_validate`
/// shim that `nibli-ui` loads. wasm-only and **synchronous** (a plain JS call).
///
/// Degrades to `Ok` when the shim is not present — on native, or if the script
/// failed to load — so `nibli-fanva` stays usable without it and translation is
/// never hard-blocked by a camxes hiccup; the local gerna+smuni gates still gate.
/// When the shim IS loaded, a camxes rejection is a `GateError::Official`, making
/// the success gate `gerna ∧ smuni ∧ camxes`.
#[cfg(target_arch = "wasm32")]
pub fn official_gate(candidate: &str) -> Result<(), GateError> {
    use wasm_bindgen::{JsCast, JsValue};
    let Some(f) = js_sys::Reflect::get(&js_sys::global(), &JsValue::from_str("camxes_validate"))
        .ok()
        .and_then(|v| v.dyn_into::<js_sys::Function>().ok())
    else {
        return Ok(()); // shim not loaded → degrade to the local gates
    };
    match f.call1(&JsValue::NULL, &JsValue::from_str(candidate)) {
        Ok(res) => read_camxes_result(&res),
        Err(_) => Ok(()), // validator threw unexpectedly → degrade, don't block
    }
}

/// Read the shim's `{ ok, message?, line?, column? }` object into a gate result.
/// Split out so it is unit-testable with a synthetic object under
/// `wasm-pack test --node` (no DOM/`window` needed).
#[cfg(target_arch = "wasm32")]
fn read_camxes_result(res: &wasm_bindgen::JsValue) -> Result<(), GateError> {
    use wasm_bindgen::JsValue;
    let get = |k: &str| js_sys::Reflect::get(res, &JsValue::from_str(k)).ok();
    let ok = get("ok").and_then(|v| v.as_bool()).unwrap_or(true);
    if ok {
        return Ok(());
    }
    let msg = get("message")
        .and_then(|v| v.as_string())
        .unwrap_or_else(|| "camxes rejected the parse".to_string());
    let line = get("line").and_then(|v| v.as_f64()).unwrap_or(0.0) as u32;
    let column = get("column").and_then(|v| v.as_f64()).unwrap_or(0.0) as u32;
    Err(GateError::Official(format!("line {line}:{column}: {msg}")))
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
        GateError::Official(_) => GateError::Official(msg),
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
/// Lojban-only fix. Kept in one place so the phrasing is consistent across gates.
pub fn feedback_for(err: &GateError) -> String {
    if let GateError::Verification(issues) = err {
        return format!(
            "That is grammatically valid but does not MEAN what the source says. An \
             independent reading of what your Lojban actually claims reported these \
             mismatches:\n{issues}\nRevise so the meaning matches the source; output ONLY \
             the corrected Lojban — no explanation."
        );
    }
    let (what, tool) = match err {
        GateError::Syntax(_) => ("is not grammatically valid Lojban", "gerna parser"),
        GateError::Semantic(_) => (
            "parses but failed semantic compilation (e.g. a predicate got the wrong number of arguments)",
            "smuni compiler",
        ),
        GateError::Official(_) => ("is not valid standard Lojban", "camxes parser"),
        GateError::Verification(_) => unreachable!("handled above"),
    };
    format!(
        "That {what}. The {tool} reported:\n{}\nFix it and output ONLY the corrected Lojban — no explanation.",
        err.message()
    )
}

#[cfg(all(test, not(target_arch = "wasm32")))]
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

    #[test]
    fn validate_kb_passes_valid_multiline_and_skips_blanks_and_comments() {
        validate_kb("la .adam. cu gerku\n# a note\n\nla .adam. cu citka")
            .expect("every non-comment line is valid Lojban");
    }

    #[test]
    fn validate_kb_reports_the_failing_line_number() {
        let err = validate_kb("la .adam. cu gerku\nbroken \u{ff}\u{ff}")
            .expect_err("line 2 is ungrammatical");
        assert!(err.message().contains("KB line 2"), "got {err:?}");
    }
}

/// Wasm-only tests for the camxes JS marshalling — run with
/// `wasm-pack test --node nibli-fanva`. A synthetic result object exercises
/// `read_camxes_result` (no DOM needed), and `official_gate` is checked on its
/// degrade path (no global). The real camxes engine needs `window` + the loaded
/// shim and is verified manually in the browser.
#[cfg(all(test, target_arch = "wasm32"))]
mod wasm_tests {
    use super::*;
    use wasm_bindgen::JsValue;
    use wasm_bindgen_test::wasm_bindgen_test;

    fn obj(pairs: &[(&str, JsValue)]) -> JsValue {
        let o = js_sys::Object::new();
        for (k, v) in pairs {
            js_sys::Reflect::set(&o, &JsValue::from_str(k), v).unwrap();
        }
        o.into()
    }

    #[wasm_bindgen_test]
    fn ok_result_passes() {
        let res = obj(&[("ok", JsValue::from_bool(true))]);
        assert!(read_camxes_result(&res).is_ok());
    }

    #[wasm_bindgen_test]
    fn error_result_maps_to_official() {
        let res = obj(&[
            ("ok", JsValue::from_bool(false)),
            (
                "message",
                JsValue::from_str("Expected selbri but end of input found."),
            ),
            ("line", JsValue::from_f64(1.0)),
            ("column", JsValue::from_f64(4.0)),
        ]);
        match read_camxes_result(&res) {
            Err(GateError::Official(m)) => {
                assert!(m.contains("Expected selbri"), "{m}");
                assert!(m.contains("1:4"), "{m}");
            }
            other => panic!("expected Official, got {other:?}"),
        }
    }

    #[wasm_bindgen_test]
    fn official_gate_degrades_without_the_shim() {
        // No `camxes_validate` on the node global → the gate is a no-op.
        assert!(official_gate("la .adam. cu gerku").is_ok());
    }
}
