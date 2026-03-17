//! Shared wire-format types for the nibli proof trace protocol.
//!
//! Both nibli-engine (native, serializes) and nibli-ui (browser WASM, deserializes)
//! depend on this crate. It has no heavy dependencies — just serde.

use serde::{Deserialize, Serialize};

// ── Proof trace wire types ──

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ProofTrace {
    pub steps: Vec<ProofStep>,
    pub root: u32,
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
    Asserted { sexp: String },
    #[serde(rename = "derived")]
    Derived { label: String, sexp: String },
    #[serde(rename = "proof_ref")]
    ProofRef { sexp: String },
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

// ── Display helpers ──

impl LogicalTerm {
    /// Human-readable rendering of a logical term.
    pub fn display(&self) -> String {
        match self.kind.as_str() {
            "constant" => self.value.clone().unwrap_or_default(),
            "number" => self.number.map(|n| format!("{}", n)).unwrap_or_default(),
            "variable" => self.value.clone().unwrap_or("?".to_string()),
            "skolem" => self.value.clone().unwrap_or("sk?".to_string()),
            "description" => format!("le_{}", self.value.as_deref().unwrap_or("?")),
            _ => format!("({})", self.kind),
        }
    }
}

impl ProofRule {
    /// Unicode icon for this proof rule type.
    pub fn icon(&self) -> &'static str {
        match self {
            Self::Conjunction => "∧",
            Self::DisjunctionCheck { .. } | Self::DisjunctionIntro { .. } => "∨",
            Self::Negation => "¬",
            Self::ModalPassthrough { .. } => "◷",
            Self::ExistsWitness { .. } | Self::ExistsFailed => "∃",
            Self::ForallVacuous | Self::ForallVerified { .. } | Self::ForallCounterexample { .. } => "∀",
            Self::CountResult { .. } => "#",
            Self::PredicateCheck { .. } | Self::ComputeCheck { .. } => "⊢",
            Self::Asserted { .. } => "▣",
            Self::Derived { .. } => "⊢",
            Self::ProofRef { .. } => "↑",
        }
    }

    /// Human-readable label describing the proof step.
    pub fn label(&self) -> String {
        match self {
            Self::Conjunction => "Conjunction".to_string(),
            Self::DisjunctionCheck { detail } => format!("Disjunction Check: {}", detail),
            Self::DisjunctionIntro { side } => format!("Disjunction Intro: {}", side),
            Self::Negation => "Negation".to_string(),
            Self::ModalPassthrough { kind } => kind.to_string(),
            Self::ExistsWitness { var, term } => format!("Witness: {} = {}", var, term.display()),
            Self::ExistsFailed => "No witness found".to_string(),
            Self::ForallVacuous => "Vacuously true".to_string(),
            Self::ForallVerified { entities } => {
                let names: Vec<String> = entities.iter().map(|t| t.display()).collect();
                format!("Verified: [{}]", names.join(", "))
            }
            Self::ForallCounterexample { entity } => format!("Counterexample: {}", entity.display()),
            Self::CountResult { expected, actual } => format!("Count: expected {}, got {}", expected, actual),
            Self::PredicateCheck { method, detail } => format!("Predicate ({}): {}", method, detail),
            Self::ComputeCheck { method, detail } => format!("Compute ({}): {}", method, detail),
            Self::Asserted { sexp } => format!("Asserted: {}", sexp),
            Self::Derived { label, sexp } => format!("Derived ({}): {}", label, sexp),
            Self::ProofRef { sexp } => format!("(proved above): {}", sexp),
        }
    }

    /// CSS class for color-coding in the UI proof tree.
    pub fn css_class(&self) -> &'static str {
        match self {
            Self::Asserted { .. } => "proof-asserted",
            Self::Derived { .. } => "proof-derived",
            Self::ProofRef { .. } => "proof-ref",
            Self::ExistsWitness { .. } | Self::ModalPassthrough { .. } => "proof-exists",
            Self::ExistsFailed | Self::ForallCounterexample { .. } => "proof-failed",
            Self::Negation => "proof-negation",
            Self::PredicateCheck { .. } | Self::ComputeCheck { .. } => "proof-check",
            Self::Conjunction => "proof-conjunction",
            Self::DisjunctionCheck { .. } | Self::DisjunctionIntro { .. } => "proof-derived",
            Self::ForallVacuous | Self::ForallVerified { .. } => "proof-exists",
            Self::CountResult { .. } => "proof-check",
        }
    }
}
