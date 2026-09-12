//! Shared wire-format types for the nibli proof trace protocol.
//!
//! Both nibli-engine (native, serializes) and nibli-ui (browser WASM, deserializes)
//! depend on this crate. The proof types (`ProofRule`/`ProofStep`/`ProofTrace`/
//! `LogicalTerm`) ARE the canonical `nibli-types` types, re-exported here; this
//! crate owns only their JSON helpers and the KB-status wire types.
//!
//! Human-readable RENDERING of these types (proof text, the `RenderedNode` tree,
//! and fact humanization) lives in `nibli-render`, not here — this crate is the
//! wire-format authority only.

use serde::{Deserialize, Serialize};

// The canonical proof types in `nibli-types` ARE the serde wire types; re-export
// them so every consumer keeps using `nibli_protocol::{ProofRule, ProofStep,
// ProofTrace, LogicalTerm}` unchanged. The JSON (de)serialization helpers live
// below as free functions (`proof_trace_to_json` / `proof_trace_from_json`).
pub use nibli_types::logic::{
    AssertionCitation, EngineProfile, FactId, LogicalTerm, PROOF_ENVELOPE_SCHEMA, ProofEnvelope,
    ProofRule, ProofStep, ProofTrace, QueryResult, ResourceKind, RuleCitation, UnknownReason,
    WitnessBinding, WitnessOrigin, validate_envelope,
};

/// The native TCP compute-backend JSON-Lines client, shared by nibli-host (the WASM
/// host) and nibli-engine (the native embedder). Gated behind the
/// `compute-client` feature so `std::net` never enters the browser build.
#[cfg(feature = "compute-client")]
pub mod compute_client;

// ── KB status wire types ──

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LineResult {
    pub line_number: u32,
    pub text: String,
    pub success: bool,
    pub fact_id: Option<u64>,
    pub error: Option<String>,
    /// Non-blocking nibli KR lint notes for this line (NIBLI_KR §12
    /// L1–L9), rendered as `[Note: …]` rows. `default` keeps old wire JSON
    /// (no field) deserializing.
    #[serde(default)]
    pub notes: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct KbStatus {
    pub asserted: u32,
    pub errors: u32,
    pub skipped: u32,
    pub line_results: Vec<LineResult>,
}

// ── Proof trace JSON helpers ──
//
// `ProofTrace` is re-exported from `nibli-types` (it IS the serde wire type), so
// these JSON helpers live here as free functions — `nibli-types` stays free of
// serde_json (and so does the WASM guest, which never serializes proofs to JSON).

/// Serialize a proof trace to its wire JSON string.
pub fn proof_trace_to_json(trace: &ProofTrace) -> String {
    serde_json::to_string(trace).unwrap_or_default()
}

/// Deserialize a proof trace from its wire JSON string.
pub fn proof_trace_from_json(s: &str) -> Option<ProofTrace> {
    serde_json::from_str(s).ok()
}

/// Serialize a proof envelope (verdict + trace + profile + version, bound) to
/// its wire JSON string.
pub fn envelope_to_json(envelope: &ProofEnvelope) -> String {
    serde_json::to_string(envelope).unwrap_or_default()
}

/// Deserialize a proof envelope from its wire JSON string.
pub fn envelope_from_json(s: &str) -> Option<ProofEnvelope> {
    let envelope: ProofEnvelope = serde_json::from_str(s).ok()?;
    (envelope.schema == PROOF_ENVELOPE_SCHEMA).then_some(envelope)
}

// Term display (`LogicalTerm::display` / `trace_display`) now lives as inherent
// methods on the canonical `nibli_types::logic::LogicalTerm` enum (re-exported
// here), so it is shared by find-witness formatting and proof rendering alike.

#[cfg(test)]
mod tests {
    use super::*;

    fn one_step(rule: ProofRule) -> ProofTrace {
        ProofTrace {
            steps: vec![ProofStep {
                rule,
                holds: true,
                children: vec![],
            }],
            root: 0,
            naf_dependent: false,
            cwa_false: false,
        }
    }

    #[test]
    fn proof_trace_json_roundtrip() {
        let trace = one_step(ProofRule::Asserted {
            fact: "gerku(adam)".to_string(),
            sources: vec![AssertionCitation {
                id: 7,
                label: "dog(Adam).".to_string(),
            }],
        });
        let json = proof_trace_to_json(&trace);
        let back = proof_trace_from_json(&json).unwrap();
        assert_eq!(trace, back);
    }

    #[test]
    fn asserted_wire_json_carries_stable_source_identity() {
        let trace = one_step(ProofRule::Asserted {
            fact: "gerku(adam)".to_string(),
            sources: vec![AssertionCitation {
                id: 7,
                label: "dog(Adam).".to_string(),
            }],
        });
        let json = proof_trace_to_json(&trace);
        assert!(json.contains(r#""type":"asserted""#), "json: {json}");
        assert!(json.contains(r#""fact":"gerku(adam)""#), "json: {json}");
        assert!(
            json.contains(r#""sources":[{"id":7,"label":"dog(Adam)."}]"#),
            "json: {json}"
        );
    }

    #[test]
    fn old_asserted_and_derived_json_default_to_empty_sources() {
        let old = r#"{"steps":[{"rule":{"type":"asserted","fact":"dog(adam)"},"holds":true,"children":[]},{"rule":{"type":"derived","label":"dog -> animal","fact":"animal(adam)"},"holds":true,"children":[0]}],"root":1}"#;
        let trace = proof_trace_from_json(old).expect("pre-origin proof JSON remains readable");
        assert!(matches!(
            &trace.steps[0].rule,
            ProofRule::Asserted { sources, .. } if sources.is_empty()
        ));
        assert!(matches!(
            &trace.steps[1].rule,
            ProofRule::Derived { sources, .. } if sources.is_empty()
        ));
    }

    #[test]
    fn presupposed_wire_json_carries_rule_source() {
        let trace = one_step(ProofRule::Presupposed {
            label: "dog -> animal".to_string(),
            fact: "dog(sk_import_0)".to_string(),
            sources: vec![RuleCitation {
                assertion_id: 11,
                rule_ordinal: 2,
                assertion_label: "Every dog is an animal.".to_string(),
            }],
        });
        let json = proof_trace_to_json(&trace);
        assert!(json.contains(r#""type":"presupposed""#), "json: {json}");
        assert!(json.contains(r#""assertion_id":11"#), "json: {json}");
        assert!(json.contains(r#""rule_ordinal":2"#), "json: {json}");
        assert_eq!(proof_trace_from_json(&json), Some(trace));
    }

    #[test]
    fn predicate_check_serializes_named_fields() {
        let trace = one_step(ProofRule::PredicateCheck {
            method: "store".to_string(),
            detail: "gerku(adam)".to_string(),
        });
        let json = proof_trace_to_json(&trace);
        assert!(json.contains(r#""type":"predicate_check""#), "json: {json}");
        assert!(json.contains(r#""method":"store""#), "json: {json}");
        assert!(json.contains(r#""detail":"gerku(adam)""#), "json: {json}");
    }

    #[test]
    fn exists_witness_term_encoding_is_pinned() {
        // Choice B: the embedded term is the canonical `LogicalTerm` enum
        // (snake_case serde), so the proof JSON nests it as `{"constant":"adam"}`.
        // This is the new term-encoding contract.
        let trace = one_step(ProofRule::ExistsWitness {
            var: "x".to_string(),
            term: LogicalTerm::Constant("adam".to_string()),
            origin: WitnessOrigin::KnowledgeBase,
        });
        let json = proof_trace_to_json(&trace);
        assert!(json.contains(r#""type":"exists_witness""#), "json: {json}");
        assert!(json.contains(r#""var":"x""#), "json: {json}");
        assert!(
            json.contains(r#""origin":"knowledge_base""#),
            "json: {json}"
        );
        assert!(
            json.contains(r#""term":{"constant":"adam"}"#),
            "json: {json}"
        );
    }

    #[test]
    fn generated_witness_origin_json_encoding_is_pinned() {
        let trace = one_step(ProofRule::ExistsWitness {
            var: "x".to_string(),
            term: LogicalTerm::Constant("sk_0".to_string()),
            origin: WitnessOrigin::GeneratedWitness,
        });
        let json = proof_trace_to_json(&trace);
        assert!(
            json.contains(r#""origin":"generated_witness""#),
            "json: {json}"
        );
        assert_eq!(proof_trace_from_json(&json), Some(trace));
    }

    #[test]
    fn forall_entities_carry_origin_in_json() {
        let trace = one_step(ProofRule::ForallVerified {
            entities: vec![WitnessBinding {
                variable: "x".to_string(),
                term: LogicalTerm::Constant("sk_0".to_string()),
                origin: WitnessOrigin::GeneratedWitness,
            }],
        });
        let json = proof_trace_to_json(&trace);
        assert!(json.contains(r#""type":"forall_verified""#), "json: {json}");
        assert!(
            json.contains(r#""origin":"generated_witness""#),
            "json: {json}"
        );
        assert_eq!(proof_trace_from_json(&json), Some(trace));
    }

    /// Every verdict class — TRUE, FALSE, all five UNKNOWN reasons, all three
    /// resource kinds — binds, serializes, deserializes to the identity, and
    /// validates. The wire coverage the live engine matrix cannot fully
    /// construct (some UNKNOWN reasons have no easy live repro).
    #[test]
    fn envelope_round_trips_and_validates_for_every_verdict_class() {
        use nibli_types::logic::{EngineProfile, ProofEnvelope, validate_envelope};
        let verdicts = [
            QueryResult::True,
            QueryResult::False,
            QueryResult::Unknown(UnknownReason::CycleCut),
            QueryResult::Unknown(UnknownReason::IncompleteKnowledge),
            QueryResult::Unknown(UnknownReason::NafDependent),
            QueryResult::Unknown(UnknownReason::BackendUnavailable),
            QueryResult::Unknown(UnknownReason::NonFinite),
            QueryResult::ResourceExceeded(ResourceKind::Depth),
            QueryResult::ResourceExceeded(ResourceKind::Fuel),
            QueryResult::ResourceExceeded(ResourceKind::Memory),
        ];
        for result in verdicts {
            let mut trace = one_step(ProofRule::Asserted {
                fact: "dog(adam)".into(),
                sources: vec![],
            });
            trace.steps[0].holds = !matches!(result, QueryResult::False);
            let envelope = ProofEnvelope::bind(
                "dog(Adam).",
                result.clone(),
                trace,
                EngineProfile {
                    strict: false,
                    existential_import: false,
                    materialization: true,
                    max_chain_depth: 10,
                },
            );
            validate_envelope(&envelope)
                .unwrap_or_else(|e| panic!("{result:?} must validate: {e:?}"));
            let json = envelope_to_json(&envelope);
            assert_eq!(
                envelope_from_json(&json),
                Some(envelope),
                "{result:?}: JSON round trip must be the identity"
            );
        }
    }
    #[test]
    fn legacy_envelopes_require_regeneration_and_depth_is_required() {
        let envelope = ProofEnvelope::bind(
            "dog(Adam).",
            QueryResult::True,
            one_step(ProofRule::Asserted {
                fact: "dog(adam)".into(),
                sources: vec![],
            }),
            EngineProfile {
                strict: false,
                existential_import: false,
                materialization: true,
                max_chain_depth: 17,
            },
        );
        let mut json: serde_json::Value =
            serde_json::from_str(&envelope_to_json(&envelope)).unwrap();
        assert_eq!(json["profile"]["max_chain_depth"], 17);
        assert_eq!(envelope_from_json(&json.to_string()), Some(envelope));
        json["schema"] = 1.into();
        assert!(envelope_from_json(&json.to_string()).is_none());
        json["schema"] = PROOF_ENVELOPE_SCHEMA.into();
        json["profile"]
            .as_object_mut()
            .unwrap()
            .remove("max_chain_depth");
        assert!(envelope_from_json(&json.to_string()).is_none());
    }
}
