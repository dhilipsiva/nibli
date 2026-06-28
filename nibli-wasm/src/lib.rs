//! Browser wasm wrapper for the nibli pipeline: gerna → smuni → logji, plus the
//! smuni-dictionary back-translation. Mirrors nibli-engine's no-store path —
//! no persistence, no compute backend, pure in-memory KnowledgeBase.
//!
//! Powers the live Transparency Triad demo at <https://dhilipsiva.dev/nibli>.

use std::collections::HashSet;

use wasm_bindgen::prelude::*;

use nibli_types::error::NibliError as PipelineError;
use nibli_types::logic as logji_logic;

// The canonical proof types ARE the wire types now; `nibli_protocol` only
// supplies the JSON helper. Readable rendering lives in `nibli-render`.

// ── the session ──────────────────────────────────────────────────────────

/// One in-memory knowledge base. The page creates one per loaded example;
/// "Reset" just builds a fresh Session and re-asserts the .lojban lines.
#[wasm_bindgen]
pub struct Session {
    kb: logji::KnowledgeBase,
    compute_predicates: HashSet<String>,
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

#[wasm_bindgen]
impl Session {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Session {
        Session {
            kb: logji::KnowledgeBase::new(),
            compute_predicates: logji::default_compute_predicates(),
        }
    }

    /// Parse one Lojban assertion, compile to FOL, assert. Returns the fact id.
    pub fn assert_text(&self, text: &str) -> Result<u64, JsError> {
        let buf = self.compile_text(text).map_err(js_err)?;
        self.kb
            .assert_fact(buf, text.to_string())
            .map_err(|e| js_err(e.to_string()))
    }

    /// Run a Lojban query. Returns JSON:
    /// `{ status, detail, naf_dependent, proof_text, proof }`.
    pub fn query_with_proof(&self, text: &str) -> Result<String, JsError> {
        let buf = self.compile_text(text).map_err(js_err)?;
        let (result, trace) = self
            .kb
            .query_entailment_with_proof(buf)
            .map_err(|e| js_err(e.to_string()))?;
        // `trace` IS the wire `ProofTrace` (canonical == wire now) — no conversion.
        let out = serde_json::json!({
            "status": result.status_label(),
            "detail": result.detail_label(),
            "naf_dependent": trace.naf_dependent,
            // The collapsed macro-logical DAG (the full canonical trace is in `proof`).
            "proof_text": nibli_render::render_collapsed_text(&trace, nibli_render::Register::Spec, 0, false),
            "why": nibli_render::summarize_proof(&trace, nibli_render::Register::Spec),
            "proof": serde_json::from_str::<serde_json::Value>(&nibli_protocol::proof_trace_to_json(&trace))
                .unwrap_or(serde_json::Value::Null),
        });
        Ok(out.to_string())
    }

    /// Retract a fact by id and rebuild derived state.
    pub fn retract_fact(&self, id: u64) -> Result<(), JsError> {
        self.kb.retract_fact(id).map_err(|e| js_err(e.to_string()))
    }

    /// All active facts as JSON: `[{ id, label }]`.
    pub fn list_facts(&self) -> Result<String, JsError> {
        let facts = self.kb.list_facts().map_err(|e| js_err(e.to_string()))?;
        let rows: Vec<serde_json::Value> = facts
            .iter()
            .map(|f| serde_json::json!({ "id": f.id, "label": f.label }))
            .collect();
        Ok(serde_json::Value::Array(rows).to_string())
    }

    /// Clear all facts and rules.
    pub fn reset(&self) {
        self.kb.reset().ok();
    }
}

impl Session {
    fn compile_text(&self, input: &str) -> Result<logji_logic::LogicBuffer, String> {
        // Shared parse front-end (fail-closed on any parse error) + smuni compile
        // + compute-node marking. String-error surface preserved via `to_string`.
        let ast = gerna::parse_checked(input).map_err(|e: PipelineError| e.to_string())?;
        let mut buf =
            smuni::compile_from_gerna_ast(ast).map_err(|e: PipelineError| e.to_string())?;
        logji::transform_compute_nodes(&mut buf, &self.compute_predicates);
        Ok(buf)
    }
}

fn js_err(msg: impl std::fmt::Display) -> JsError {
    JsError::new(&msg.to_string())
}

/// Word-by-word robotic back-translation (smuni-dictionary, 10k+ jbovlaste
/// entries). Mechanical by design — the labeled "lexical gloss" fallback for
/// tokens that do not compile.
#[wasm_bindgen]
pub fn back_translate(lojban: &str) -> String {
    smuni_dictionary::back_translate(lojban)
}

/// IR-driven back-translation: parse + compile to FOL, then render structure-
/// exposing English via nibli-render. This is the default Transparency Triad
/// reading; it falls back to the lexical gloss when the input does not compile.
#[wasm_bindgen]
pub fn back_translate_ir(lojban: &str) -> String {
    match compile_for_render(lojban) {
        Ok(buf) => nibli_render::render_logic_buffer(&buf, nibli_render::Register::Spec),
        Err(_) => smuni_dictionary::back_translate(lojban),
    }
}

/// Parse + compile a line to the FOL `LogicBuffer` for rendering (no compute
/// transform, no assertion — display only).
fn compile_for_render(input: &str) -> Result<logji_logic::LogicBuffer, String> {
    let ast = gerna::parse_checked(input).map_err(|e: PipelineError| e.to_string())?;
    smuni::compile_from_gerna_ast(ast).map_err(|e: PipelineError| e.to_string())
}

// ── native tests: the book's headline queries against the real KBs ─────────

#[cfg(test)]
mod tests {
    use super::Session;

    fn load(kb_text: &str) -> Session {
        let session = Session::new();
        for line in kb_text.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            session
                .assert_text(line)
                .unwrap_or_else(|_| panic!("failed to assert: {line}"));
        }
        session
    }

    fn status(session: &Session, query: &str) -> String {
        let json = session.query_with_proof(query).expect("query failed");
        let v: serde_json::Value = serde_json::from_str(&json).unwrap();
        v["status"].as_str().unwrap().to_string()
    }

    #[test]
    fn syllogism_two_hop_proof() {
        // Book Ch 19's minimal worked example — the demo's first tab.
        let session = load("ro lo gerku cu danlu\nro lo danlu cu citka\nla .adam. cu gerku");
        assert_eq!(status(&session, "la .adam. cu citka"), "TRUE");
        assert_eq!(status(&session, "la .adam. cu danlu"), "TRUE");
        assert_eq!(status(&session, "la .adam. cu cipni"), "FALSE");
    }

    // NOTE: the Ch 20 breach-notification queries (`... se bilga lo nu notci`)
    // are deliberately NOT exercised here or in the /nibli demo: against the
    // FULL gdpr.lojban corpus the traced query does not return in bounded time
    // (confirmed >240s in release, 2026-06-11) — matching the suspicion in
    // code-review-panel-2026-06-10.json. Upstream pins that query shape only
    // against smaller inline KBs (nibli-engine/tests/integration.rs).
    #[test]
    fn gdpr_lawful_basis_and_withdrawal() {
        let session = load(include_str!("../../gdpr.lojban"));
        // Book Ch 20: consent gives Adam a lawful basis.
        assert_eq!(status(&session, "la .adam. cu se curmi"), "TRUE");
        assert_eq!(status(&session, "la .adam. na se curmi"), "FALSE");
        // A controller is not a consenting person — a real, exhaustive FALSE.
        assert_eq!(status(&session, "la .gugli. cu se curmi"), "FALSE");
        // Special-category derivation: health record → personal data (Art 4/9).
        assert_eq!(status(&session, "la .kanrek. cu datni"), "TRUE");

        // Withdraw consent (retract `la .adam. cu zanru`) — basis collapses.
        let facts = session.list_facts().unwrap();
        let rows: serde_json::Value = serde_json::from_str(&facts).unwrap();
        let consent_id = rows
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r["label"].as_str().unwrap_or("").contains("zanru"))
            .expect("consent fact present")["id"]
            .as_u64()
            .unwrap();
        session.retract_fact(consent_id).unwrap();
        assert_eq!(status(&session, "la .adam. cu se curmi"), "FALSE");
        assert_eq!(status(&session, "la .adam. na se curmi"), "TRUE");
    }

    #[test]
    fn drug_interaction_chain_and_discontinuation() {
        let session = load(include_str!("../../drug-interactions.lojban"));
        // Book Ch 21: warfarin chain fires end to end.
        assert_eq!(status(&session, "la .varfarin. cu zenba"), "TRUE");
        assert_eq!(status(&session, "la .varfarin. cu ckape"), "TRUE");
        assert_eq!(status(&session, "la .varfarin. cu kajde"), "TRUE");
        // Negative control: apixaban (CYP3A4) does not alert.
        assert_eq!(status(&session, "la .apiksaban. cu kajde"), "FALSE");

        // Discontinue fluconazole (retract the inhibition fact) — chain collapses.
        let facts = session.list_facts().unwrap();
        let rows: serde_json::Value = serde_json::from_str(&facts).unwrap();
        let inhibit_id = rows
            .as_array()
            .unwrap()
            .iter()
            .find(|r| {
                let l = r["label"].as_str().unwrap_or("");
                l.contains("flukonazol") && l.contains("fanta")
            })
            .expect("inhibition fact present")["id"]
            .as_u64()
            .unwrap();
        session.retract_fact(inhibit_id).unwrap();
        assert_eq!(status(&session, "la .varfarin. cu kajde"), "FALSE");
    }

    #[test]
    fn lexical_fallback_gloss_is_word_level() {
        // `back_translate` is the LEXICAL fallback (smuni-dictionary), used only
        // when a line does not compile. It is the word-salad gloss — NOT what the
        // Transparency Triad's Back-translation tab shows for a compiling line
        // (that is `back_translate_ir`, pinned below).
        assert_eq!(
            super::back_translate("ro lo gerku cu danlu"),
            "all the dog animal"
        );
    }

    /// The exact bytes Chapter 19's Syllogism walkthrough reproduces click-for-
    /// click in the playground: the Back-translation tab (`back_translate_ir`),
    /// and the verdict + "why" + collapsed proof panel (`query_with_proof`).
    /// If this breaks, the book's "verbatim" claim is stale — re-capture and
    /// update both the book and these asserts together. Pairs with the verdict
    /// pin `syllogism_two_hop_proof` above.
    #[test]
    fn syllogism_playground_bytes_are_verbatim() {
        // Back-translation tab: structure-exposing IR English (not the fallback).
        assert_eq!(
            super::back_translate_ir("ro lo gerku cu danlu"),
            "For every X, if X is a dog, then X is an animal."
        );
        assert_eq!(
            super::back_translate_ir("ro lo danlu cu citka"),
            "For every X, if X is an animal, then X eats."
        );
        assert_eq!(super::back_translate_ir("la .adam. cu gerku"), "Adam is a dog.");

        let session = load("ro lo gerku cu danlu\nro lo danlu cu citka\nla .adam. cu gerku");
        let q = |query: &str| -> (String, String, String) {
            let json = session.query_with_proof(query).expect("query failed");
            let v: serde_json::Value = serde_json::from_str(&json).unwrap();
            (
                v["status"].as_str().unwrap().to_string(),
                v["why"].as_str().unwrap_or("").to_string(),
                v["proof_text"].as_str().unwrap_or("").trim_end().to_string(),
            )
        };

        // 2-hop: does Adam eat?  (the preset's first/auto-run query)
        let (status, why, proof) = q("la .adam. cu citka");
        assert_eq!(status, "TRUE");
        assert_eq!(
            why,
            "Because adam is a dog, adam is an animal; and because adam is an animal, adam eats _."
        );
        assert_eq!(
            proof,
            "⊢ adam eats _  [by the rule: every animal eats something] -> TRUE\n  \
             ⊢ adam is an animal  [by the rule: every dog is an animal] -> TRUE\n    \
             ▣ adam is a dog  [given] -> TRUE"
        );

        // 1-hop: is Adam an animal?
        let (status, why, proof) = q("la .adam. cu danlu");
        assert_eq!(status, "TRUE");
        assert_eq!(why, "Because adam is a dog, adam is an animal.");
        assert_eq!(
            proof,
            "⊢ adam is an animal  [by the rule: every dog is an animal] -> TRUE\n  \
             ▣ adam is a dog  [given] -> TRUE"
        );

        // A real FALSE: is Adam a bird?
        let (status, why, proof) = q("la .adam. cu cipni");
        assert_eq!(status, "FALSE");
        assert_eq!(why, "No example could be found that satisfies the query.");
        assert_eq!(proof, "∃ No witness found -> FALSE");
    }

    /// The back-translations Chapter 19's two draft-error examples reproduce in
    /// the playground (the Transparency Triad catching an LLM mistake). These are
    /// the structure-exposing IR gloss (`back_translate_ir`), NOT the lexical
    /// `(swap-2)` fallback. If this breaks, C19's quoted glosses are stale.
    #[test]
    fn c19_draft_error_glosses_are_verbatim() {
        // Quantifier swap (GDPR Art 33): `su'o` reads as a flat existential
        // assertion; `ro` reads as a universal "For every X, if … then …" rule.
        assert_eq!(
            super::back_translate_ir("su'o lo datni turni cu bilga lo nu notci"),
            "X govern, X is data, Y is event-of, and X is obligated to Y."
        );
        assert_eq!(
            super::back_translate_ir("ro lo datni turni cu bilga lo nu notci"),
            "For every X, if X govern and X is data, then Y is event-of and X is obligated to Y."
        );
        // Missing negation (GDPR Art 17), single-condition restrictor so the
        // gloss has no spurious person-split — the dropped `na` is isolated in
        // the antecedent.
        assert_eq!(
            super::back_translate_ir("ro lo se curmi cu se bilga lo nu lo datni cu se vimcu"),
            "For every X, if something permits X, then Y is event-of, Z is data, \
             something is removed, and Y is obligated to X."
        );
        assert_eq!(
            super::back_translate_ir("ro lo na se curmi cu se bilga lo nu lo datni cu se vimcu"),
            "For every X, if it is not the case that something permits X, then Y is \
             event-of, Z is data, something is removed, and Y is obligated to X."
        );
        // The corrected negated-restrictor rule compiles and enters the KB — the
        // "engine refuses to compile it" claim C19 used to make is stale.
        let session = Session::new();
        assert!(
            session
                .assert_text("ro lo na se curmi cu se bilga lo nu lo datni cu se vimcu")
                .is_ok(),
            "negated-restrictor universal rule should assert, not be rejected"
        );
    }
}
