//! Shared wire-format types for the nibli proof trace protocol.
//!
//! Both nibli-engine (native, serializes) and nibli-ui (browser WASM, deserializes)
//! depend on this crate. It has no heavy dependencies — serde plus the canonical
//! `nibli-types` (for the single `from_canonical` converter).
//!
//! Human-readable RENDERING of these types (proof text, the `RenderedNode` tree,
//! and fact humanization) lives in `nibli-render`, not here — this crate is the
//! wire-format authority only.

use serde::{Deserialize, Serialize};

use nibli_types::logic as canon;

// ── Proof trace wire types ──

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ProofTrace {
    pub steps: Vec<ProofStep>,
    pub root: u32,
    /// True if any step in this trace used negation-as-failure (CWA assumption).
    /// Under open-world semantics, NAF-dependent conclusions would be Unknown.
    #[serde(default)]
    pub naf_dependent: bool,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ProofStep {
    pub rule: ProofRule,
    pub holds: bool,
    pub children: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LogicalTerm {
    pub kind: String,
    pub value: Option<String>,
    pub number: Option<f64>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ProofRule {
    #[serde(rename = "conjunction")]
    Conjunction,
    #[serde(rename = "disjunction_check")]
    DisjunctionCheck { detail: String },
    #[serde(rename = "disjunction_intro")]
    DisjunctionIntro { side: String },
    #[serde(rename = "negation")]
    Negation,
    #[serde(rename = "modal_passthrough")]
    ModalPassthrough { kind: String },
    #[serde(rename = "exists_witness")]
    ExistsWitness { var: String, term: LogicalTerm },
    #[serde(rename = "exists_failed")]
    ExistsFailed,
    #[serde(rename = "forall_vacuous")]
    ForallVacuous,
    #[serde(rename = "forall_verified")]
    ForallVerified { entities: Vec<LogicalTerm> },
    #[serde(rename = "forall_counterexample")]
    ForallCounterexample { entity: LogicalTerm },
    #[serde(rename = "count_result")]
    CountResult { expected: u32, actual: u32 },
    #[serde(rename = "predicate_check")]
    PredicateCheck { method: String, detail: String },
    #[serde(rename = "compute_check")]
    ComputeCheck { method: String, detail: String },
    #[serde(rename = "asserted")]
    Asserted { fact: String },
    #[serde(rename = "derived")]
    Derived { label: String, fact: String },
    #[serde(rename = "proof_ref")]
    ProofRef { fact: String },
    #[serde(rename = "equality_substitution")]
    EqualitySubstitution {
        original: String,
        du_facts: String,
        substituted: String,
    },
    #[serde(rename = "rule_attempt_failed")]
    RuleAttemptFailed {
        rule_label: String,
        failed_condition: String,
    },
    #[serde(rename = "predicate_not_found")]
    PredicateNotFound { predicate: String },
}

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

// ── Serialization helper ──

impl ProofTrace {
    /// Serialize to JSON string for wire transport.
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap_or_default()
    }

    /// Deserialize from JSON string.
    pub fn from_json(s: &str) -> Option<Self> {
        serde_json::from_str(s).ok()
    }
}

// ── Canonical (nibli-types) → wire conversion ──
//
// The SINGLE logji→wire conversion lattice. nibli-engine and nibli-wasm both call
// these (they previously hand-wrote identical copies); lasna's logji→WIT lattice
// is separate by necessity (a WASM guest cannot depend on this crate). See the
// `__exhaustiveness_guard` in nibli-types for the full list of conversion sites.

/// Convert a canonical logical term into its wire form.
pub fn from_canonical_term(term: &canon::LogicalTerm) -> LogicalTerm {
    match term {
        canon::LogicalTerm::Constant(s) => LogicalTerm {
            kind: "constant".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        canon::LogicalTerm::Variable(s) => LogicalTerm {
            kind: "variable".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        canon::LogicalTerm::Description(s) => LogicalTerm {
            kind: "description".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        canon::LogicalTerm::Number(n) => LogicalTerm {
            kind: "number".to_string(),
            value: None,
            number: Some(*n),
        },
        canon::LogicalTerm::Unspecified => LogicalTerm {
            kind: "unspecified".to_string(),
            value: None,
            number: None,
        },
    }
}

/// Convert a canonical proof rule into its wire form.
pub fn from_canonical_rule(rule: &canon::ProofRule) -> ProofRule {
    match rule {
        canon::ProofRule::Conjunction => ProofRule::Conjunction,
        canon::ProofRule::DisjunctionCheck(s) => ProofRule::DisjunctionCheck { detail: s.clone() },
        canon::ProofRule::DisjunctionIntro(s) => ProofRule::DisjunctionIntro { side: s.clone() },
        canon::ProofRule::Negation => ProofRule::Negation,
        canon::ProofRule::ModalPassthrough(s) => ProofRule::ModalPassthrough { kind: s.clone() },
        canon::ProofRule::ExistsWitness((var, term)) => ProofRule::ExistsWitness {
            var: var.clone(),
            term: from_canonical_term(term),
        },
        canon::ProofRule::ExistsFailed => ProofRule::ExistsFailed,
        canon::ProofRule::ForallVacuous => ProofRule::ForallVacuous,
        canon::ProofRule::ForallVerified(entities) => ProofRule::ForallVerified {
            entities: entities.iter().map(from_canonical_term).collect(),
        },
        canon::ProofRule::ForallCounterexample(term) => ProofRule::ForallCounterexample {
            entity: from_canonical_term(term),
        },
        canon::ProofRule::CountResult((expected, actual)) => ProofRule::CountResult {
            expected: *expected,
            actual: *actual,
        },
        canon::ProofRule::PredicateCheck((method, detail)) => ProofRule::PredicateCheck {
            method: method.clone(),
            detail: detail.clone(),
        },
        canon::ProofRule::ComputeCheck((method, detail)) => ProofRule::ComputeCheck {
            method: method.clone(),
            detail: detail.clone(),
        },
        canon::ProofRule::Asserted(fact) => ProofRule::Asserted { fact: fact.clone() },
        canon::ProofRule::Derived((label, fact)) => ProofRule::Derived {
            label: label.clone(),
            fact: fact.clone(),
        },
        canon::ProofRule::ProofRef(fact) => ProofRule::ProofRef { fact: fact.clone() },
        canon::ProofRule::EqualitySubstitution((o, d, s)) => ProofRule::EqualitySubstitution {
            original: o.clone(),
            du_facts: d.clone(),
            substituted: s.clone(),
        },
        canon::ProofRule::RuleAttemptFailed((l, c)) => ProofRule::RuleAttemptFailed {
            rule_label: l.clone(),
            failed_condition: c.clone(),
        },
        canon::ProofRule::PredicateNotFound(p) => ProofRule::PredicateNotFound {
            predicate: p.clone(),
        },
    }
}

/// Convert a canonical proof trace into its wire form.
pub fn from_canonical(trace: &canon::ProofTrace) -> ProofTrace {
    ProofTrace {
        steps: trace
            .steps
            .iter()
            .map(|step| ProofStep {
                rule: from_canonical_rule(&step.rule),
                holds: step.holds,
                children: step.children.clone(),
            })
            .collect(),
        root: trace.root,
        naf_dependent: trace.has_naf_dependency(),
    }
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

// ── Display helpers ──
//
// These are inherent display methods on the wire term, used by find-witness
// formatting (nibli-engine `display_term`, gasnu) AND by `nibli-render`'s proof
// labels. Proof-rule rendering itself lives in `nibli-render`.

impl LogicalTerm {
    /// Human-readable rendering of a logical term.
    pub fn display(&self) -> String {
        match self.kind.as_str() {
            "constant" => self.value.clone().unwrap_or_default(),
            "number" => self.number.map(|n| format!("{n}")).unwrap_or_default(),
            "variable" => self.value.clone().unwrap_or_else(|| "?".to_string()),
            "skolem" => self.value.clone().unwrap_or_else(|| "sk?".to_string()),
            "description" => format!("le_{}", self.value.as_deref().unwrap_or("?")),
            _ => format!("({})", self.kind),
        }
    }

    /// Compact textual rendering used in CLI proof traces.
    pub fn trace_display(&self) -> String {
        match self.kind.as_str() {
            "constant" => self.value.clone().unwrap_or_default(),
            "number" => match self.number {
                Some(n) if n == (n as i64) as f64 => format!("{}", n as i64),
                Some(n) => format!("{n}"),
                None => String::new(),
            },
            "variable" => format!("?{}", self.value.clone().unwrap_or_default()),
            "description" => format!("lo {}", self.value.as_deref().unwrap_or("?")),
            "unspecified" => "zo'e".to_string(),
            _ => self.display(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_trace_json_roundtrip() {
        let trace = ProofTrace {
            steps: vec![ProofStep {
                rule: ProofRule::Asserted {
                    fact: "gerku(adam)".to_string(),
                },
                holds: true,
                children: vec![],
            }],
            root: 0,
            naf_dependent: false,
        };
        let json = trace.to_json();
        let back = ProofTrace::from_json(&json).unwrap();
        assert_eq!(trace, back);
    }

    #[test]
    fn from_canonical_preserves_wire_json_shape() {
        // The wire JSON the UI parses must be byte-stable across the consolidation:
        // a canonical Asserted rule must serialize with the named `fact` field and
        // the `asserted` tag.
        let canon_trace = canon::ProofTrace {
            steps: vec![canon::ProofStep {
                rule: canon::ProofRule::Asserted("gerku(adam)".to_string()),
                holds: true,
                children: vec![],
            }],
            root: 0,
        };
        let wire = from_canonical(&canon_trace);
        let json = wire.to_json();
        assert!(json.contains(r#""type":"asserted""#), "json: {json}");
        assert!(json.contains(r#""fact":"gerku(adam)""#), "json: {json}");
    }

    #[test]
    fn from_canonical_maps_named_fields() {
        let rule = from_canonical_rule(&canon::ProofRule::PredicateCheck((
            "store".to_string(),
            "gerku(adam)".to_string(),
        )));
        assert_eq!(
            rule,
            ProofRule::PredicateCheck {
                method: "store".to_string(),
                detail: "gerku(adam)".to_string(),
            }
        );
    }
}
