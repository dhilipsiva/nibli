//! Shared wire-format types for the nibli proof trace protocol.
//!
//! Both nibli-engine (native, serializes) and nibli-ui (browser WASM, deserializes)
//! depend on this crate. The proof types (`ProofRule`/`ProofStep`/`ProofTrace`/
//! `LogicalTerm`) ARE the canonical `nibli-types` types, re-exported here; this
//! crate owns only their JSON helpers and the gossip/KB-status wire types.
//!
//! Human-readable RENDERING of these types (proof text, the `RenderedNode` tree,
//! and fact humanization) lives in `nibli-render`, not here — this crate is the
//! wire-format authority only.

use serde::{Deserialize, Serialize};

// The canonical proof types in `nibli-types` ARE the serde wire types; re-export
// them so every consumer keeps using `nibli_protocol::{ProofRule, ProofStep,
// ProofTrace, LogicalTerm}` unchanged. The JSON (de)serialization helpers live
// below as free functions (`proof_trace_to_json` / `proof_trace_from_json`).
pub use nibli_types::logic::{LogicalTerm, ProofRule, ProofStep, ProofTrace};

/// The native TCP compute-backend JSON-Lines client, shared by gasnu (the WASM
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

// ── Gossip network types (shared between nibli-server and nibli-ui) ──

/// A gossip event pushed to the UI via GraphQL subscription or WebRTC.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum GossipEvent {
    /// New envelope received and ingested.
    #[serde(rename = "envelope")]
    NewEnvelope {
        envelope_id: String,
        author: String,
        lojban: Option<String>,
        stance: String,
        topics: Vec<String>,
        timestamp: String,
    },
    /// Contradiction detected between two assertions.
    #[serde(rename = "contradiction")]
    Contradiction {
        id: usize,
        envelope_id: String,
        assertion: String,
        author: String,
    },
    /// Trust change (trust or distrust).
    #[serde(rename = "trust_change")]
    TrustChange {
        from: String,
        to: String,
        trusted: bool,
    },
    /// Peer connected or disconnected.
    #[serde(rename = "peer_change")]
    PeerChange { peer_id: String, connected: bool },
    /// Sync completed with a peer.
    #[serde(rename = "sync")]
    Sync {
        peer_id: String,
        envelope_count: usize,
    },
}

/// Summary of a gossip agent visible on the network.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct NetworkAgent {
    pub name: String,
    pub envelope_count: u32,
    pub stance_counts: StanceCounts,
    pub topics: Vec<String>,
    pub is_local: bool,
}

/// Distribution of epistemic stances for an agent.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct StanceCounts {
    pub deduced: u32,
    pub expected: u32,
    pub opinion: u32,
    pub hearsay: u32,
}

/// Summary of an envelope for the UI.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct EnvelopeSummary {
    pub id: String,
    pub author: String,
    pub lojban: Option<String>,
    pub stance: String,
    pub topics: Vec<String>,
    pub timestamp: String,
    pub is_retraction: bool,
    pub is_quarantined: bool,
}

/// Summary of a contradiction for the UI.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ContradictionSummary {
    pub id: usize,
    pub envelope_id: String,
    pub assertion: String,
    pub author: String,
    pub resolved: bool,
}

/// Full gossip network state snapshot.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct NetworkSnapshot {
    pub agents: Vec<NetworkAgent>,
    pub envelopes: Vec<EnvelopeSummary>,
    pub contradictions: Vec<ContradictionSummary>,
    pub peers: Vec<String>,
    pub local_agent: String,
    pub total_facts: u32,
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
        }
    }

    #[test]
    fn proof_trace_json_roundtrip() {
        let trace = one_step(ProofRule::Asserted {
            fact: "gerku(adam)".to_string(),
        });
        let json = proof_trace_to_json(&trace);
        let back = proof_trace_from_json(&json).unwrap();
        assert_eq!(trace, back);
    }

    #[test]
    fn wire_json_shape_is_byte_stable() {
        // The rule-level wire JSON the UI parses must be byte-stable across the
        // consolidation: an Asserted rule serializes with the `asserted` tag and
        // the named `fact` field. (Rule tags + string fields are unchanged by the
        // canonical-as-wire unification — only nested term encoding changed.)
        let trace = one_step(ProofRule::Asserted {
            fact: "gerku(adam)".to_string(),
        });
        let json = proof_trace_to_json(&trace);
        assert!(json.contains(r#""type":"asserted""#), "json: {json}");
        assert!(json.contains(r#""fact":"gerku(adam)""#), "json: {json}");
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
        });
        let json = proof_trace_to_json(&trace);
        assert!(json.contains(r#""type":"exists_witness""#), "json: {json}");
        assert!(json.contains(r#""var":"x""#), "json: {json}");
        assert!(
            json.contains(r#""term":{"constant":"adam"}"#),
            "json: {json}"
        );
    }
}
