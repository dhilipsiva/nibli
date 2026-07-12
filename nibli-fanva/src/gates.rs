//! The validation gates — the "verify" firewall around the LLM's output.
//!
//! Language-aware since the Klaro retarget: every gate entry point takes the
//! KB [`Language`]. The KLARO arm runs `klaro::parse_checked` → smuni → the
//! RENDER ROUND-TRIP gate (the drift-catcher: the candidate's canonical
//! re-spelling must compile to the SAME `LogicBuffer` — klaro's pinned
//! fixpoint contract, `klaro/src/render.rs`; AstBuffer equality is
//! deliberately NOT the contract there). The LOJBAN arm is the legacy chain:
//! `gerna::parse_checked` → smuni → the wasm-only "official" **camxes** gate
//! (vendored `camxes.js` via JS-interop) — camxes is Lojban-only, so it never
//! runs for Klaro; the round-trip gate is its Klaro replacement and, being
//! pure Rust, runs on native AND wasm.

use nibli_types::error::NibliError;
use nibli_types::lang::Language;
use nibli_types::logic::LogicBuffer;

/// Which gate rejected a candidate, carrying the compiler's own message. The
/// message is fed back verbatim into the LLM conversation as correction context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GateError {
    /// The front-end rejected the grammar (`NibliError::Syntax` from gerna in
    /// Lojban mode, or klaro's parse/resolve errors — including fail-closed
    /// dictionary-unknown aliases — in Klaro mode).
    Syntax(String),
    /// smuni rejected the semantics/arity (`NibliError::Semantic`).
    Semantic(String),
    /// The official grammar (`camxes.js`) rejected it. *(wasm-only, Lojban-only gate)*
    Official(String),
    /// The Klaro render round-trip gate: the candidate compiles, but its
    /// canonical re-spelling (`klaro::render`) fails to re-parse or compiles
    /// to a DIFFERENT `LogicBuffer` — the drift-catcher that replaces camxes
    /// in Klaro mode. *(Klaro-only gate, native + wasm)*
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
    /// Short human name of the gate that failed — for UI badges and logs. The
    /// grammar gate's badge is the front-end that ran, so it takes the language.
    pub fn gate(&self, lang: Language) -> &'static str {
        match self {
            GateError::Syntax(_) => match lang {
                Language::Klaro => "klaro",
                Language::Lojban => "gerna",
            },
            GateError::Semantic(_) => "smuni",
            GateError::Official(_) => "camxes",
            GateError::RoundTrip(_) => "round-trip",
            GateError::Verification(_) => "semantic verifier",
        }
    }

    /// The underlying compiler message.
    pub fn message(&self) -> &str {
        match self {
            GateError::Syntax(m)
            | GateError::Semantic(m)
            | GateError::Official(m)
            | GateError::RoundTrip(m)
            | GateError::Verification(m) => m,
        }
    }
}

/// The display name of the KB language, for feedback prose.
fn lang_name(lang: Language) -> &'static str {
    match lang {
        Language::Klaro => "Klaro",
        Language::Lojban => "Lojban",
    }
}

/// Run the local gates in fail-fast order and return the compiled FOL on
/// success. Mirrors `nibli-ui`'s `compile_text` front-end (minus
/// `logji::transform_compute_nodes`, which the translator does not need).
/// LOJBAN: gerna grammar → smuni semantics. KLARO: klaro grammar (parse +
/// fail-closed resolve) → smuni semantics → the render round-trip gate.
/// Which call fails determines the [`GateError`] variant: a `parse_checked`
/// failure is always a grammar error; a `compile_from_gerna_ast` failure is a
/// semantic one.
pub fn local_gates(lang: Language, candidate: &str) -> Result<LogicBuffer, GateError> {
    match lang {
        Language::Lojban => {
            let ast = gerna::parse_checked(candidate).map_err(syntax)?;
            smuni::compile_from_gerna_ast(ast).map_err(semantic)
        }
        Language::Klaro => {
            let ast = klaro::parse_checked(candidate).map_err(syntax)?;
            let buf = smuni::compile_from_gerna_ast(ast.clone()).map_err(semantic)?;
            klaro_round_trip(&ast, &buf)?;
            Ok(buf)
        }
    }
}

/// The Klaro render round-trip gate: render the accepted AST back to canonical
/// Klaro, re-parse and re-compile it, and demand the SAME `LogicBuffer` —
/// klaro's own fixpoint contract (`parse ∘ render ∘ parse` compiles equal for
/// Klaro-originated buffers), enforced per candidate as a drift-catcher. Any
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

/// The full validation gate the agent calls: [`local_gates`] plus, in LOJBAN
/// mode on wasm, the official (`camxes.js`) grammar gate. In KLARO mode the
/// round-trip gate inside [`local_gates`] is the third gate on every target,
/// so this adds nothing — the signature stays stable across languages.
pub fn validate(lang: Language, candidate: &str) -> Result<LogicBuffer, GateError> {
    let buf = local_gates(lang, candidate)?;
    // The third Lojban gate is the local (browser) camxes parser — wasm-only.
    #[cfg(target_arch = "wasm32")]
    if lang == Language::Lojban {
        official_gate(candidate)?;
    }
    Ok(buf)
}

/// The "official" grammar gate: the vendored standard **camxes** parser
/// (ilmentufa), run locally in the browser through the `window.camxes_validate`
/// shim that `nibli-ui` loads. wasm-only, Lojban-only, and **synchronous** (a
/// plain JS call).
///
/// Degrades to `Ok` when the shim is not present — on native, or if the script
/// failed to load — so `nibli-fanva` stays usable without it and translation is
/// never hard-blocked by a camxes hiccup; the local gerna+smuni gates still gate.
/// When the shim IS loaded, a camxes rejection is a `GateError::Official`, making
/// the Lojban success gate `gerna ∧ smuni ∧ camxes`.
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
pub fn validate_kb(lang: Language, text: &str) -> Result<(), GateError> {
    for (i, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        validate(lang, line)
            .map(|_| ())
            .map_err(|e| tag_line(e, i + 1))?;
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
pub fn feedback_for(lang: Language, err: &GateError) -> String {
    let name = lang_name(lang);
    if let GateError::Verification(issues) = err {
        return format!(
            "That is grammatically valid but does not MEAN what the source says. An \
             independent reading of what your {name} actually claims reported these \
             mismatches:\n{issues}\nRevise so the meaning matches the source; output ONLY \
             the corrected {name} — no explanation."
        );
    }
    let (what, tool) = match (err, lang) {
        (GateError::Syntax(_), Language::Lojban) => {
            ("is not grammatically valid Lojban", "gerna parser")
        }
        (GateError::Syntax(_), Language::Klaro) => ("is not valid Klaro", "klaro compiler"),
        (GateError::Semantic(_), _) => (
            "parses but failed semantic compilation (e.g. a predicate got the wrong number of arguments)",
            "smuni compiler",
        ),
        (GateError::Official(_), _) => ("is not valid standard Lojban", "camxes parser"),
        (GateError::RoundTrip(_), _) => (
            "compiles but is not canonical Klaro (its canonical re-spelling does not compile to the same logic)",
            "round-trip gate",
        ),
        (GateError::Verification(_), _) => unreachable!("handled above"),
    };
    format!(
        "That {what}. The {tool} reported:\n{}\nFix it and output ONLY the corrected {name} — no explanation.",
        err.message()
    )
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    #[test]
    fn valid_lojban_passes_local_gates() {
        // Same shape nibli-ui asserts as its legacy default KB; must compile cleanly.
        local_gates(Language::Lojban, "la .adam. cu gerku")
            .expect("valid Lojban should pass both local gates");
    }

    #[test]
    fn valid_klaro_passes_local_gates() {
        // Same shape nibli-ui asserts as its default KB; runs all three Klaro
        // gates (klaro, smuni, round-trip).
        local_gates(Language::Klaro, "dog(Adam).")
            .expect("valid Klaro should pass the three local gates");
    }

    #[test]
    fn klaro_and_lojban_twins_compile_equal_through_the_gates() {
        // The gates run the same smuni back-end for both front-ends — the twin
        // claims must land on the identical LogicBuffer.
        let k = local_gates(Language::Klaro, "dog(Adam).").unwrap();
        let l = local_gates(Language::Lojban, "la .adam. cu gerku").unwrap();
        assert_eq!(k, l, "twin claims must compile to the same logic");
    }

    #[test]
    fn syntactic_garbage_fails_at_the_grammar_gate() {
        // Invalid bytes after a valid sentence — gerna fails closed (from gerna's own tests).
        let err = local_gates(Language::Lojban, "la .adam. cu gerku .i \u{ff}\u{ff}\u{ff}")
            .expect_err("ungrammatical input must be rejected");
        assert!(
            matches!(err, GateError::Syntax(_)),
            "expected Syntax, got {err:?}"
        );
        assert_eq!(err.gate(Language::Lojban), "gerna");
    }

    #[test]
    fn klaro_garbage_fails_at_the_grammar_gate() {
        let err = local_gates(Language::Klaro, "dog(Adam") // no close paren / period
            .expect_err("malformed Klaro must be rejected");
        assert!(
            matches!(err, GateError::Syntax(_)),
            "expected Syntax, got {err:?}"
        );
        assert_eq!(err.gate(Language::Klaro), "klaro");
    }

    #[test]
    fn klaro_unknown_alias_fails_closed_at_the_grammar_gate() {
        // Fail-closed name resolution (SURFACE_SYNTAX): an alias the dictionary
        // does not know is a COMPILE ERROR, not a silent new predicate.
        let err = local_gates(Language::Klaro, "zzyzxq(Adam).")
            .expect_err("unknown alias must fail closed");
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
            validate(Language::Klaro, s)
                .unwrap_or_else(|e| panic!("round-trip gate rejected shipped shape {s:?}: {e:?}"));
        }
    }

    #[test]
    fn feedback_names_the_failing_gate() {
        let fb = feedback_for(
            Language::Lojban,
            &GateError::Syntax("[Syntax Error] line 1:5: nope".into()),
        );
        assert!(fb.contains("gerna parser"));
        assert!(fb.contains("line 1:5"));
        assert!(fb.contains("corrected Lojban"));
    }

    #[test]
    fn feedback_names_the_klaro_gates() {
        let fb = feedback_for(
            Language::Klaro,
            &GateError::Syntax("[Syntax Error] line 1:5: nope".into()),
        );
        assert!(fb.contains("klaro compiler"));
        assert!(fb.contains("corrected Klaro"));
        let fb = feedback_for(
            Language::Klaro,
            &GateError::RoundTrip("canonical re-spelling differs".into()),
        );
        assert!(fb.contains("round-trip gate"));
        assert!(fb.contains("corrected Klaro"));
        let fb = feedback_for(Language::Klaro, &GateError::Verification("1. off".into()));
        assert!(fb.contains("your Klaro"));
        assert!(fb.contains("corrected Klaro"));
    }

    #[test]
    fn validate_kb_passes_valid_multiline_and_skips_blanks_and_comments() {
        validate_kb(
            Language::Lojban,
            "la .adam. cu gerku\n# a note\n\nla .adam. cu citka",
        )
        .expect("every non-comment line is valid Lojban");
        validate_kb(Language::Klaro, "dog(Adam).\n# a note\n\neats(Adam).")
            .expect("every non-comment line is valid Klaro");
    }

    #[test]
    fn validate_kb_reports_the_failing_line_number() {
        let err = validate_kb(Language::Lojban, "la .adam. cu gerku\nbroken \u{ff}\u{ff}")
            .expect_err("line 2 is ungrammatical");
        assert!(err.message().contains("KB line 2"), "got {err:?}");
        let err = validate_kb(Language::Klaro, "dog(Adam).\ndog(Adam")
            .expect_err("line 2 is malformed Klaro");
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

    #[wasm_bindgen_test]
    fn klaro_validate_skips_camxes_and_passes() {
        // The camxes gate is Lojban-only: a Klaro candidate must validate on
        // wasm through klaro+smuni+round-trip alone (no shim involved).
        assert!(validate(Language::Klaro, "dog(Adam).").is_ok());
    }
}
