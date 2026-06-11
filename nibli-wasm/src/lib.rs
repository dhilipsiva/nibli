//! Browser wasm wrapper for the nibli pipeline: gerna → smuni → logji, plus the
//! smuni-dictionary back-translation. Mirrors nibli-engine's no-store path —
//! no persistence, no compute backend, pure in-memory KnowledgeBase.
//!
//! Powers the live Transparency Triad demo at <https://dhilipsiva.dev/nibli>.

use std::collections::HashSet;

use wasm_bindgen::prelude::*;

use nibli_protocol::{
    LogicalTerm as LogicalTermJson, ProofRule as ProofRuleJson, ProofStep as ProofStepJson,
    ProofTrace as ProofTraceJson,
};
use nibli_types::error::NibliError as PipelineError;
use nibli_types::logic as logji_logic;

// ── proof trace conversion (verbatim from nibli-engine, minus store types) ──

fn term_to_json(term: &logji_logic::LogicalTerm) -> LogicalTermJson {
    match term {
        logji_logic::LogicalTerm::Constant(s) => LogicalTermJson {
            kind: "constant".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        logji_logic::LogicalTerm::Variable(s) => LogicalTermJson {
            kind: "variable".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        logji_logic::LogicalTerm::Description(s) => LogicalTermJson {
            kind: "description".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        logji_logic::LogicalTerm::Number(n) => LogicalTermJson {
            kind: "number".to_string(),
            value: None,
            number: Some(*n),
        },
        logji_logic::LogicalTerm::Unspecified => LogicalTermJson {
            kind: "unspecified".to_string(),
            value: None,
            number: None,
        },
    }
}

fn rule_to_json(rule: &logji_logic::ProofRule) -> ProofRuleJson {
    match rule {
        logji_logic::ProofRule::Conjunction => ProofRuleJson::Conjunction,
        logji_logic::ProofRule::DisjunctionCheck(s) => {
            ProofRuleJson::DisjunctionCheck { detail: s.clone() }
        }
        logji_logic::ProofRule::DisjunctionIntro(s) => {
            ProofRuleJson::DisjunctionIntro { side: s.clone() }
        }
        logji_logic::ProofRule::Negation => ProofRuleJson::Negation,
        logji_logic::ProofRule::ModalPassthrough(s) => {
            ProofRuleJson::ModalPassthrough { kind: s.clone() }
        }
        logji_logic::ProofRule::ExistsWitness((var, term)) => ProofRuleJson::ExistsWitness {
            var: var.clone(),
            term: term_to_json(term),
        },
        logji_logic::ProofRule::ExistsFailed => ProofRuleJson::ExistsFailed,
        logji_logic::ProofRule::ForallVacuous => ProofRuleJson::ForallVacuous,
        logji_logic::ProofRule::ForallVerified(entities) => ProofRuleJson::ForallVerified {
            entities: entities.iter().map(term_to_json).collect(),
        },
        logji_logic::ProofRule::ForallCounterexample(term) => ProofRuleJson::ForallCounterexample {
            entity: term_to_json(term),
        },
        logji_logic::ProofRule::CountResult((expected, actual)) => ProofRuleJson::CountResult {
            expected: *expected,
            actual: *actual,
        },
        logji_logic::ProofRule::PredicateCheck((method, detail)) => ProofRuleJson::PredicateCheck {
            method: method.clone(),
            detail: detail.clone(),
        },
        logji_logic::ProofRule::ComputeCheck((method, detail)) => ProofRuleJson::ComputeCheck {
            method: method.clone(),
            detail: detail.clone(),
        },
        logji_logic::ProofRule::Asserted(fact) => ProofRuleJson::Asserted { fact: fact.clone() },
        logji_logic::ProofRule::Derived((label, fact)) => ProofRuleJson::Derived {
            label: label.clone(),
            fact: fact.clone(),
        },
        logji_logic::ProofRule::ProofRef(fact) => ProofRuleJson::ProofRef { fact: fact.clone() },
        logji_logic::ProofRule::EqualitySubstitution((o, d, s)) => {
            ProofRuleJson::EqualitySubstitution {
                original: o.clone(),
                du_facts: d.clone(),
                substituted: s.clone(),
            }
        }
        logji_logic::ProofRule::RuleAttemptFailed((l, c)) => ProofRuleJson::RuleAttemptFailed {
            rule_label: l.clone(),
            failed_condition: c.clone(),
        },
        logji_logic::ProofRule::PredicateNotFound(p) => ProofRuleJson::PredicateNotFound {
            predicate: p.clone(),
        },
    }
}

fn proof_trace_to_wire(trace: &logji_logic::ProofTrace) -> ProofTraceJson {
    ProofTraceJson {
        steps: trace
            .steps
            .iter()
            .map(|step| ProofStepJson {
                rule: rule_to_json(&step.rule),
                holds: step.holds,
                children: step.children.clone(),
            })
            .collect(),
        root: trace.root,
        naf_dependent: trace.has_naf_dependency(),
    }
}

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
        let mut compute_predicates = HashSet::new();
        compute_predicates.insert("pilji".to_string());
        compute_predicates.insert("sumji".to_string());
        compute_predicates.insert("dilcu".to_string());
        Session {
            kb: logji::KnowledgeBase::new(),
            compute_predicates,
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
        let wire = proof_trace_to_wire(&trace);
        let out = serde_json::json!({
            "status": result.status_label(),
            "detail": result.detail_label(),
            "naf_dependent": wire.naf_dependent,
            "proof_text": wire.to_pretty_text(),
            "proof": serde_json::from_str::<serde_json::Value>(&wire.to_json())
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
        let parse_result = gerna::parse_text_native(input.to_string())
            .map_err(|e: PipelineError| e.to_string())?;

        if !parse_result.errors.is_empty() {
            let msgs: Vec<String> = parse_result
                .errors
                .iter()
                .map(|e| e.message.clone())
                .collect();
            return Err(format!("syntax: {}", msgs.join("; ")));
        }

        let mut buf = smuni::compile_from_gerna_ast(parse_result.buffer)
            .map_err(|e: PipelineError| e.to_string())?;
        logji::transform_compute_nodes(&mut buf, &self.compute_predicates);
        Ok(buf)
    }
}

fn js_err(msg: impl std::fmt::Display) -> JsError {
    JsError::new(&msg.to_string())
}

/// Word-by-word robotic back-translation (smuni-dictionary, 10k+ jbovlaste
/// entries). Mechanical by design — it is the verification surface, not prose.
#[wasm_bindgen]
pub fn back_translate(lojban: &str) -> String {
    smuni_dictionary::back_translate(lojban)
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
    fn back_translation_matches_the_book() {
        assert_eq!(
            super::back_translate("ro lo gerku cu danlu"),
            "all the dog animal"
        );
    }
}
