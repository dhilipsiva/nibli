//! Browser wasm wrapper for the nibli pipeline: gerna → smuni → logji, plus the
//! nibli-lexicon back-translation. Mirrors nibli-engine's no-store path —
//! no persistence, no compute backend, pure in-memory KnowledgeBase.
//!
//! Powers the live Transparency Triad demo at <https://dhilipsiva.dev/nibli>.

use std::collections::HashSet;

use wasm_bindgen::prelude::*;

use nibli_types::error::NibliError as PipelineError;
use nibli_types::logic;

// The canonical proof types ARE the wire types now; `nibli_protocol` only
// supplies the JSON helper. Readable rendering lives in `nibli-render`.

// ── the session ──────────────────────────────────────────────────────────

/// One in-memory knowledge base. The page creates one per loaded example;
/// "Reset" just builds a fresh Session and re-asserts the KB lines.
#[wasm_bindgen]
pub struct Session {
    kb: nibli_reason::KnowledgeBase,
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
            kb: nibli_reason::KnowledgeBase::new(),
            compute_predicates: nibli_reason::default_compute_predicates(),
        }
    }

    /// DEPRECATED NO-OP compatibility shim: the Lojban front-end retired at
    /// THE DROP, so there is no language to select — every session is KR.
    /// Kept (accepting and ignoring any string) so deployed-site JS written
    /// against the dual-front-end API keeps loading; dies at the "nibli KR"
    /// rename milestone.
    pub fn set_language(&self, _lang: &str) -> Result<(), JsError> {
        Ok(())
    }

    /// Parse one Lojban assertion, compile to FOL, assert. A bare-`.i`
    /// multi-sentence text becomes N INDEPENDENT facts (one per root; connectives
    /// stay whole); returns the minted fact ids in root order.
    pub fn assert_text(&self, text: &str) -> Result<Vec<u64>, JsError> {
        let buf = self.compile_text(text).map_err(js_err)?;
        let mut ids = Vec::new();
        for sub in buf.split_roots() {
            ids.push(
                self.kb
                    .assert_fact(sub, text.to_string())
                    .map_err(|e| js_err(e.to_string()))?,
            );
        }
        Ok(ids)
    }

    /// Run a Lojban query. Returns JSON:
    /// `{ status, detail, naf_dependent, cwa_false, proof_text, why, proof }`.
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
            "cwa_false": trace.cwa_false,
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
    fn compile_text(&self, input: &str) -> Result<logic::LogicBuffer, String> {
        // Fail-closed KR parse + smuni compile + compute-node marking.
        // String-error surface preserved via `to_string`.
        let ast = nibli_kr::parse_checked(input).map_err(|e: PipelineError| e.to_string())?;
        let mut buf =
            nibli_semantics::compile_from_ast(ast).map_err(|e: PipelineError| e.to_string())?;
        nibli_reason::transform_compute_nodes(&mut buf, &self.compute_predicates);
        Ok(buf)
    }
}

fn js_err(msg: impl std::fmt::Display) -> JsError {
    JsError::new(&msg.to_string())
}

/// DEPRECATED compatibility shim — now a pure ECHO no-op: the word-by-word
/// Lojban lexical gloss it once produced died with the cmavo layer at the
/// committed-corpus milestone. Kept only so deployed-site JS written against
/// the dual-front-end API keeps loading; the site-migration bullet owns the
/// deletion of this and `set_language` together.
#[wasm_bindgen]
pub fn back_translate(word: &str) -> String {
    word.to_string()
}

/// IR-driven back-translation: parse + compile to FOL, then render structure-
/// exposing English via nibli-render. This is the default Transparency Triad
/// reading; it falls back to the lexical gloss when the input does not compile.
#[wasm_bindgen]
pub fn back_translate_ir(text: &str) -> String {
    match compile_for_render(text) {
        Ok(buf) => nibli_render::render_logic_buffer(&buf, nibli_render::Register::Spec),
        // A non-compiling line echoes as-is (KR is already readable; the
        // Lojban word-gloss fallback retired with the front-end).
        Err(_) => text.to_string(),
    }
}

/// Parse + compile a line to the FOL `LogicBuffer` for rendering (no compute
/// transform, no assertion — display only).
fn compile_for_render(input: &str) -> Result<logic::LogicBuffer, String> {
    let ast = nibli_kr::parse_checked(input).map_err(|e: PipelineError| e.to_string())?;
    nibli_semantics::compile_from_ast(ast).map_err(|e: PipelineError| e.to_string())
}

// ── native tests: the book's headline queries against the real KBs ─────────

#[cfg(test)]
mod tests {
    use super::Session;

    /// Load a KR KB, vocab-skipping lines the FALLBACK dictionary build
    /// cannot resolve (the corpora carry full-mode generated aliases; the
    /// shipped_examples_compile pattern) — with a non-vacuity floor so the
    /// skip can never hollow a test out.
    fn load(kb_text: &str) -> Session {
        let session = Session::new();
        let (mut asserted, mut skipped) = (0usize, 0usize);
        for line in kb_text.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') || line.starts_with(':') {
                continue;
            }
            let line = line.strip_prefix("? ").unwrap_or(line);
            // Skip-check via the native-safe parse path (a JsError cannot be
            // formatted on non-wasm targets, so probe nibli-kr directly).
            if let Err(e) = nibli_kr::parse_checked(line) {
                if e.to_string().contains("unknown predicate") {
                    skipped += 1;
                    continue;
                }
            }
            match session.assert_text(line) {
                Ok(_) => asserted += 1,
                Err(_) => panic!("failed to assert: {line}"),
            }
        }
        assert!(
            asserted > skipped,
            "vocab-skip hollowed the KB out: {asserted} asserted, {skipped} skipped"
        );
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
        let session = load("animal(every dog).\neats(every animal).\ndog(Adam).");
        assert_eq!(status(&session, "eats(Adam)."), "TRUE");
        assert_eq!(status(&session, "animal(Adam)."), "TRUE");
        assert_eq!(status(&session, "bird(Adam)."), "FALSE");
    }

    #[test]
    fn c02_intro_repl_verdicts() {
        // Chapter 2's three intro REPL sessions (dog/animal, the made-up glorp
        // words, GDPR consent). The captured Show-It/Glorp blocks are byte-gated;
        // the GDPR-consent block is flagged (its long proof is elided), so pin its
        // verdict here so the transcript cannot drift to a wrong answer.
        let syllog = load("dog(Adam).\nanimal(every dog).");
        assert_eq!(status(&syllog, "animal(Adam)."), "TRUE");

        // (The Ch-2 made-up-word "glorp" block retired with the Lojban
        // front-end: KR fails closed on unknown names by design, so the
        // arity-2-tolerance demo has no KR twin.)

        let gdpr = load(
            "owns(some person, some data).\n\
             obliged(every person where owns(it, some data), event { permits() }).",
        );
        assert_eq!(
            status(&gdpr, "obliged(some person, event { permits() })."),
            "TRUE"
        );
    }

    // NOTE: the Ch 20 breach-notification queries (obligated-to-notify) are
    // deliberately NOT exercised here or in the /nibli demo: against the
    // FULL gdpr corpus the traced query does not return in bounded time
    // (confirmed >240s in release, 2026-06-11) — matching the suspicion in
    // code-review-panel-2026-06-10.json. Upstream pins that query shape only
    // against smaller inline KBs (nibli-engine/tests/integration.rs).
    #[test]
    fn gdpr_lawful_basis_and_withdrawal() {
        let session = load(include_str!("../../gdpr.nibli"));
        // Book Ch 20: consent gives Adam a lawful basis.
        assert_eq!(status(&session, "permitted(Adam)."), "TRUE");
        assert_eq!(status(&session, "~permitted(Adam)."), "FALSE");
        // A controller is not a consenting person — a real, exhaustive FALSE.
        assert_eq!(status(&session, "permitted(Gugli)."), "FALSE");
        // Special-category derivation: health record → personal data (Art 4/9).
        assert_eq!(status(&session, "data(Kanrek)."), "TRUE");

        // Withdraw consent (retract `la .adam. cu zanru`) — basis collapses.
        let facts = session.list_facts().unwrap();
        let rows: serde_json::Value = serde_json::from_str(&facts).unwrap();
        let consent_id = rows
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r["label"].as_str().unwrap_or("").contains("approves(Adam)"))
            .expect("consent fact present")["id"]
            .as_u64()
            .unwrap();
        session.retract_fact(consent_id).unwrap();
        assert_eq!(status(&session, "permitted(Adam)."), "FALSE");
        assert_eq!(status(&session, "~permitted(Adam)."), "TRUE");
    }

    #[test]
    fn drug_interaction_chain_and_discontinuation() {
        let session = load(include_str!("../../drug-interactions.nibli"));
        // Book Ch 21: warfarin chain fires end to end.
        assert_eq!(status(&session, "increases(Varfarin)."), "TRUE");
        assert_eq!(status(&session, "dangerous(Varfarin)."), "TRUE");
        assert_eq!(status(&session, "warns(Varfarin)."), "TRUE");
        // Negative control: apixaban (CYP3A4) does not alert.
        assert_eq!(status(&session, "warns(Apiksaban)."), "FALSE");

        // Discontinue fluconazole (retract the inhibition fact) — chain collapses.
        let facts = session.list_facts().unwrap();
        let rows: serde_json::Value = serde_json::from_str(&facts).unwrap();
        let inhibit_id = rows
            .as_array()
            .unwrap()
            .iter()
            .find(|r| {
                let l = r["label"].as_str().unwrap_or("");
                l.contains("prevents(Flukonazol")
            })
            .expect("inhibition fact present")["id"]
            .as_u64()
            .unwrap();
        session.retract_fact(inhibit_id).unwrap();
        assert_eq!(status(&session, "warns(Varfarin)."), "FALSE");
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
            super::back_translate_ir("animal(every dog)."),
            "For every X, if X is a dog, then X is an animal."
        );
        assert_eq!(
            super::back_translate_ir("eats(every animal)."),
            "For every X, if X is an animal, then X eats."
        );
        assert_eq!(super::back_translate_ir("dog(Adam)."), "Adam is a dog.");

        let session = load("animal(every dog).\neats(every animal).\ndog(Adam).");
        let q = |query: &str| -> (String, String, String) {
            let json = session.query_with_proof(query).expect("query failed");
            let v: serde_json::Value = serde_json::from_str(&json).unwrap();
            (
                v["status"].as_str().unwrap().to_string(),
                v["why"].as_str().unwrap_or("").to_string(),
                v["proof_text"]
                    .as_str()
                    .unwrap_or("")
                    .trim_end()
                    .to_string(),
            )
        };

        // 2-hop: does Adam eat?  (the preset's first/auto-run query)
        let (status, why, proof) = q("eats(Adam).");
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
        let (status, why, proof) = q("animal(Adam).");
        assert_eq!(status, "TRUE");
        assert_eq!(why, "Because adam is a dog, adam is an animal.");
        assert_eq!(
            proof,
            "⊢ adam is an animal  [by the rule: every dog is an animal] -> TRUE\n  \
             ▣ adam is a dog  [given] -> TRUE"
        );

        // A real FALSE: is Adam a bird? Closed-world (not derivable), so the proof
        // now carries the symmetric CWA-FALSE caveat.
        let (status, why, proof) = q("bird(Adam).");
        assert_eq!(status, "FALSE");
        assert_eq!(why, "No example could be found that satisfies the query.");
        assert_eq!(
            proof,
            "[Note: FALSE is closed-world — not derivable from the KB, not a proof of the negation]\n\
             ∃ No witness found -> FALSE"
        );
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
            super::back_translate_ir("obliged(some data governs, event { message() })."),
            "X govern, X is data, Y is event, and X is obligated to Y."
        );
        assert_eq!(
            super::back_translate_ir("obliged(every data governs, event { message() })."),
            "For every X, if X govern and X is data, then Y is event and X is obligated to Y."
        );
        // Missing negation (GDPR Art 17), single-condition restrictor so the
        // gloss has no spurious person-split — the dropped `na` is isolated in
        // the antecedent.
        assert_eq!(
            super::back_translate_ir(
                "obligated(every permitted, event { removes(removed: some data) })."
            ),
            "For every X, if something permits X, then Y is event, Z is data, \
             something is removed, and Y is obligated to X."
        );
        assert_eq!(
            super::back_translate_ir(
                "obligated(every ~permitted, event { removes(removed: some data) })."
            ),
            "For every X, if it is not the case that something permits X, then Y is \
             event, Z is data, something is removed, and Y is obligated to X."
        );
        // The corrected negated-restrictor rule compiles and enters the KB — the
        // "engine refuses to compile it" claim C19 used to make is stale.
        let session = Session::new();
        assert!(
            session
                .assert_text("obligated(every ~permitted, event { removes(removed: some data) }).")
                .is_ok(),
            "negated-restrictor universal rule should assert, not be rejected"
        );
    }
}
