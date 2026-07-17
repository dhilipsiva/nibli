//! First-Order Logic types produced by the nibli-semantics compiler and consumed by nibli-reason.
//!
//! Flat index-based representation: `LogicBuffer` contains a `nodes` array
//! of `LogicNode` variants, referenced by `u32` indices.

/// A logical term — the typed representation of an FOL argument.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum LogicalTerm {
    /// A bound or free variable (e.g., Skolem variables, universally quantified vars).
    Variable(String),
    /// A ground constant (e.g., entity names from `la`).
    Constant(String),
    /// An opaque description reference (from `le` determiner).
    Description(String),
    /// Unspecified placeholder (from `zo'e`).
    Unspecified,
    /// Numeric literal (from `li` + PA).
    Number(f64),
}

impl LogicalTerm {
    /// Human-readable rendering of a logical term (UI labels / witness display).
    /// Ported from the former `nibli-protocol` wire-term display.
    pub fn display(&self) -> String {
        match self {
            LogicalTerm::Constant(s) => s.clone(),
            LogicalTerm::Number(n) => format!("{n}"),
            LogicalTerm::Variable(s) => s.clone(),
            LogicalTerm::Description(s) => format!("the_{s}"),
            LogicalTerm::Unspecified => "(unspecified)".to_string(),
        }
    }

    /// Compact textual rendering used in CLI proof traces.
    /// Ported from the former `nibli-protocol` wire-term `trace_display`.
    pub fn trace_display(&self) -> String {
        match self {
            LogicalTerm::Constant(s) => s.clone(),
            LogicalTerm::Number(n) => {
                if *n == (*n as i64) as f64 {
                    format!("{}", *n as i64)
                } else {
                    format!("{n}")
                }
            }
            LogicalTerm::Variable(s) => format!("?{s}"),
            LogicalTerm::Description(s) => format!("the {s}"),
            LogicalTerm::Unspecified => "something".to_string(),
        }
    }
}

/// A node in the flat logic graph. Each variant corresponds to an FOL constructor.
/// Nodes reference children by `u32` index into the `LogicBuffer.nodes` array.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum LogicNode {
    /// Ground or quantified predicate. Fields: (relation-name, argument-terms).
    Predicate((String, Vec<LogicalTerm>)),
    /// A predicate dispatched to an external compute backend for evaluation.
    ComputeNode((String, Vec<LogicalTerm>)),
    /// Conjunction: left ∧ right. Fields: (left-node-id, right-node-id).
    AndNode((u32, u32)),
    /// Disjunction: left ∨ right. Fields: (left-node-id, right-node-id).
    OrNode((u32, u32)),
    /// Negation: ¬inner. Payload: inner-node-id.
    NotNode(u32),
    /// Existential quantifier: ∃var. body. Fields: (variable-name, body-node-id).
    ExistsNode((String, u32)),
    /// Universal quantifier: ∀var. body. Fields: (variable-name, body-node-id).
    ForAllNode((String, u32)),
    /// Past tense wrapper (pu). Payload: inner-node-id.
    PastNode(u32),
    /// Present tense wrapper (ca). Payload: inner-node-id.
    PresentNode(u32),
    /// Future tense wrapper (ba). Payload: inner-node-id.
    FutureNode(u32),
    /// Deontic obligation wrapper (ei/bilga). Payload: inner-node-id.
    ObligatoryNode(u32),
    /// Deontic permission wrapper (e'e/curmi). Payload: inner-node-id.
    PermittedNode(u32),
    /// Exactly N entities satisfy the body. Fields: (variable-name, count, body-node-id).
    CountNode((String, u32, u32)),
}

/// Flat logic buffer: a `nodes` array plus root indices.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LogicBuffer {
    pub nodes: Vec<LogicNode>,
    pub roots: Vec<u32>,
}

impl LogicBuffer {
    /// Split a multi-root buffer into one independent single-root buffer per root,
    /// so an `.i`-separated multi-sentence compile becomes N independently
    /// assertable / retractable facts.
    ///
    /// The split is exactly the `roots` boundary: nibli-semantics emits **one root per bare
    /// `.i` sentence**, but a **single root** (an `AndNode`/`OrNode`) for logical
    /// connectives (`.ije`/`.ija`/`ge…gi`). So bare `.i` splits into N buffers while
    /// a connective stays as one compound fact — automatically, no text parsing.
    ///
    /// Share-nodes strategy: each sub-buffer reuses the full `nodes` arena and
    /// exposes a single root. Unreachable nodes belonging to sibling roots are inert
    /// because every consumer traverses only from `roots` (see
    /// `nibli_reason::process_assertion`). No index remapping, so no risk of a
    /// mis-remapped child edge (notably `CountNode`'s middle field is a COUNT, not a
    /// node index). `roots.len() <= 1` returns a single clone (identity) so the
    /// single-sentence path is unchanged.
    pub fn split_roots(&self) -> Vec<LogicBuffer> {
        if self.roots.len() <= 1 {
            return vec![self.clone()];
        }
        self.roots
            .iter()
            .map(|&r| LogicBuffer {
                nodes: self.nodes.clone(),
                roots: vec![r],
            })
            .collect()
    }
}

/// A single witness binding: variable name → logical term value.
#[derive(Clone, Debug, PartialEq)]
pub struct WitnessBinding {
    pub variable: String,
    pub term: LogicalTerm,
}

/// Why the engine cannot currently return a definitive `True` or `False`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnknownReason {
    /// Search encountered a recursive cycle and cut it rather than diverging.
    CycleCut,
    /// Result depends on knowledge the current KB does not have yet.
    IncompleteKnowledge,
    /// Result depends on negation-as-failure and is therefore not classically proved.
    NafDependent,
    /// An external compute predicate could not be evaluated because its backend was
    /// unreachable or unregistered — the result is genuinely undetermined, NOT false.
    BackendUnavailable,
    /// A numeric operand or computed result is non-finite (±inf/NaN) — e.g. a literal
    /// too large for an f64 (~309+ digits overflows to ±inf). The comparison/arithmetic
    /// is genuinely undetermined, NOT a confident TRUE/FALSE.
    NonFinite,
}

/// Which resource or search bound prevented a definitive answer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResourceKind {
    Depth,
    Fuel,
    Memory,
}

/// Top-level entailment result returned by the reasoning engine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QueryResult {
    True,
    False,
    Unknown(UnknownReason),
    ResourceExceeded(ResourceKind),
}

impl QueryResult {
    pub fn is_true(&self) -> bool {
        matches!(self, Self::True)
    }

    pub fn is_false(&self) -> bool {
        matches!(self, Self::False)
    }

    pub fn is_definitive(&self) -> bool {
        matches!(self, Self::True | Self::False)
    }

    pub fn status_label(&self) -> &'static str {
        match self {
            Self::True => "TRUE",
            Self::False => "FALSE",
            Self::Unknown(_) => "UNKNOWN",
            Self::ResourceExceeded(_) => "RESOURCE_EXCEEDED",
        }
    }

    pub fn detail_label(&self) -> Option<&'static str> {
        match self {
            Self::Unknown(UnknownReason::CycleCut) => Some("cycle-cut"),
            Self::Unknown(UnknownReason::IncompleteKnowledge) => Some("incomplete-knowledge"),
            Self::Unknown(UnknownReason::NafDependent) => Some("naf-dependent"),
            Self::Unknown(UnknownReason::BackendUnavailable) => Some("backend-unavailable"),
            Self::Unknown(UnknownReason::NonFinite) => Some("non-finite"),
            Self::ResourceExceeded(ResourceKind::Depth) => Some("depth"),
            Self::ResourceExceeded(ResourceKind::Fuel) => Some("fuel"),
            Self::ResourceExceeded(ResourceKind::Memory) => Some("memory"),
            _ => None,
        }
    }
}

/// Proof rule applied at a single proof step.
///
/// This IS the serde wire type (named fields, `#[serde(tag = "type")]`): the same
/// type crosses every native boundary (nibli-reason → nibli-engine/nibli-wasm → JSON →
/// nibli-ui). `nibli-protocol` re-exports it and owns only the JSON helpers; the WIT
/// boundary (nibli-pipeline/nibli-host) keeps its generated tuple-shaped mirror by necessity.
/// The serde attributes are the JSON contract — do not rename a field or tag.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(tag = "type"))]
pub enum ProofRule {
    #[cfg_attr(feature = "serde", serde(rename = "conjunction"))]
    Conjunction,
    #[cfg_attr(feature = "serde", serde(rename = "disjunction_check"))]
    DisjunctionCheck { detail: String },
    #[cfg_attr(feature = "serde", serde(rename = "disjunction_intro"))]
    DisjunctionIntro { side: String },
    #[cfg_attr(feature = "serde", serde(rename = "negation"))]
    Negation,
    #[cfg_attr(feature = "serde", serde(rename = "modal_passthrough"))]
    ModalPassthrough { kind: String },
    #[cfg_attr(feature = "serde", serde(rename = "exists_witness"))]
    ExistsWitness { var: String, term: LogicalTerm },
    #[cfg_attr(feature = "serde", serde(rename = "exists_failed"))]
    ExistsFailed,
    #[cfg_attr(feature = "serde", serde(rename = "forall_vacuous"))]
    ForallVacuous,
    #[cfg_attr(feature = "serde", serde(rename = "forall_verified"))]
    ForallVerified { entities: Vec<LogicalTerm> },
    #[cfg_attr(feature = "serde", serde(rename = "forall_counterexample"))]
    ForallCounterexample { entity: LogicalTerm },
    #[cfg_attr(feature = "serde", serde(rename = "count_result"))]
    CountResult { expected: u32, actual: u32 },
    #[cfg_attr(feature = "serde", serde(rename = "predicate_check"))]
    PredicateCheck { method: String, detail: String },
    #[cfg_attr(feature = "serde", serde(rename = "compute_check"))]
    ComputeCheck { method: String, detail: String },
    #[cfg_attr(feature = "serde", serde(rename = "asserted"))]
    Asserted { fact: String },
    #[cfg_attr(feature = "serde", serde(rename = "derived"))]
    Derived { label: String, fact: String },
    #[cfg_attr(feature = "serde", serde(rename = "proof_ref"))]
    ProofRef { fact: String },
    /// Equality substitution: fact proved by substituting equivalent terms.
    /// Fields: original fact, equality facts used, substituted fact that was found.
    #[cfg_attr(feature = "serde", serde(rename = "equality_substitution"))]
    EqualitySubstitution {
        original: String,
        equality_facts: String,
        substituted: String,
    },
    /// Rule was tried but a condition failed.
    #[cfg_attr(feature = "serde", serde(rename = "rule_attempt_failed"))]
    RuleAttemptFailed {
        rule_label: String,
        failed_condition: String,
    },
    /// Predicate not found in fact store and no rule could derive it.
    #[cfg_attr(feature = "serde", serde(rename = "predicate_not_found"))]
    PredicateNotFound { predicate: String },
}

/// A single step in a proof trace.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofStep {
    pub rule: ProofRule,
    pub holds: bool,
    pub children: Vec<u32>,
}

/// Complete proof trace: steps array + root index.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofTrace {
    pub steps: Vec<ProofStep>,
    pub root: u32,
    /// True if any step in this trace used negation-as-failure (CWA assumption).
    /// Under open-world semantics, NAF-dependent conclusions would be Unknown.
    /// Populated by nibli-reason at trace construction; serialized over the wire.
    #[cfg_attr(feature = "serde", serde(default))]
    pub naf_dependent: bool,
    /// True if the verdict is a CLOSED-WORLD `FALSE`: not derivable from the KB
    /// (the closed-world assumption), as opposed to a numeric/arithmetic FALSE that
    /// was genuinely DECIDED (e.g. `5 dunli 3`). A closed-world FALSE is the dual of
    /// `naf_dependent` — under open-world semantics it would be Unknown, not a proof
    /// of the negation. Computed by nibli-reason from the verdict (it needs to distinguish
    /// FALSE from Unknown, both of which have a non-holding root), so unlike
    /// `naf_dependent` it cannot be recomputed from the steps alone.
    #[cfg_attr(feature = "serde", serde(default))]
    pub cwa_false: bool,
}

impl ProofTrace {
    /// Returns true if any step in this proof trace used negation-as-failure.
    /// A Negation step with `holds: true` means the inner formula was unprovable
    /// and NAF flipped it to True — this is the CWA assumption in action.
    /// Under open-world semantics, the same conclusion would be Unknown.
    pub fn has_naf_dependency(&self) -> bool {
        self.steps
            .iter()
            .any(|s| matches!(s.rule, ProofRule::Negation) && s.holds)
    }

    /// Collect indices of all NAF-dependent steps in this trace.
    pub fn naf_dependent_steps(&self) -> Vec<u32> {
        self.steps
            .iter()
            .enumerate()
            .filter(|(_, s)| matches!(s.rule, ProofRule::Negation) && s.holds)
            .map(|(i, _)| i as u32)
            .collect()
    }
}

/// Aggregation operation for numeric witness values.
#[derive(Clone, Debug)]
pub enum AggregateOp {
    Sum,
    Min,
    Max,
    Avg,
}

/// Unique identifier for a stored fact in the knowledge base.
pub type FactId = u64;

/// Summary of an active fact in the knowledge base.
#[derive(Clone, Debug)]
pub struct FactSummary {
    pub id: FactId,
    pub label: String,
    pub root_count: u32,
}

/// Compile-time exhaustiveness anchor for the cross-crate conversion lattices.
///
/// `LogicNode`, `LogicalTerm`, and `ProofRule` are each converted by hand in
/// several places that no single crate can see at once, so adding a variant to
/// any of them silently leaves stale converters elsewhere — the build would
/// break, but with scattered `E0004` errors and no roadmap. This function exists
/// only to make that breakage land in ONE discoverable, documented location: its
/// wildcard-free matches force `E0004` *here* the moment a variant is added, and
/// the checklist below names every site that must then be updated.
///
/// When you add or remove a variant of any of these three enums, update:
/// - `nibli-pipeline/src/lib.rs` — `convert_logical_term_to_export` /
///   `convert_logical_term_from_export` / `convert_proof_rule` (→ WIT guest types);
///   for a new `LogicNode`/`LogicalTerm` variant also `convert_logic_node_to_export`
///   / `convert_logic_buffer_to_export` (the `:debug` typed-buffer export)
/// - `nibli-protocol/src/lib.rs` — **re-exports** `ProofRule`/`ProofStep`/`ProofTrace`
///   (and `LogicalTerm`) from this crate and owns only the `proof_trace_to_json` /
///   `proof_trace_from_json` free fns. No wire mirror or `from_canonical_*` converter
///   remains — `ProofRule` IS the serde wire type (named fields, `serde(tag = "type")`),
///   so it crosses every native boundary unchanged. The serde renames here are the
///   JSON contract.
/// - `nibli-host/src/main.rs` — `rule_to_proto` (WIT `proof-rule` → canonical `ProofRule`);
///   for a new `LogicNode`/`LogicalTerm` variant also `wit_term_to_types` /
///   `wit_logic_node_to_types` / `wit_logic_buffer_to_types` (WIT → `nibli_types`,
///   the `:debug` reverse converter)
/// - `nibli-render/src/proof.rs` — `icon` / `label` / `css_class` / `trace_display`
///   for a new `ProofRule` variant (the readable rendering of the wire rule)
/// - `wit/world.wit` — the `logical-term` / `proof-rule` variant lists, then
///   regenerate bindings with `cargo component build`
/// - for a new `LogicNode`/`LogicalTerm` variant: nibli-reason lowering + evaluation,
///   `nibli-render/src/logic.rs` (`render_logic_buffer` English + `render_logic_tree`
///   structural tree) + `term.rs` (IR back-translation rendering), and
///   the serde persistence round-trip test
///   (`nibli-engine`'s `logic_buffer_serde_postcard_roundtrip_covers_all_variants`)
///
/// Never called at runtime; `#[doc(hidden)]` keeps it off the public API surface.
/// (A macro-driven codegen of the conversion lattices was evaluated and declined
/// on readability grounds — the JSON RHS field names are bespoke per variant, so a
/// macro must spell every variant out anyway; see `todo.md`.)
#[doc(hidden)]
pub fn __exhaustiveness_guard(node: &LogicNode, term: &LogicalTerm, rule: &ProofRule) {
    match node {
        LogicNode::Predicate(_) => {}
        LogicNode::ComputeNode(_) => {}
        LogicNode::AndNode(_) => {}
        LogicNode::OrNode(_) => {}
        LogicNode::NotNode(_) => {}
        LogicNode::ExistsNode(_) => {}
        LogicNode::ForAllNode(_) => {}
        LogicNode::PastNode(_) => {}
        LogicNode::PresentNode(_) => {}
        LogicNode::FutureNode(_) => {}
        LogicNode::ObligatoryNode(_) => {}
        LogicNode::PermittedNode(_) => {}
        LogicNode::CountNode(_) => {}
    }
    match term {
        LogicalTerm::Variable(_) => {}
        LogicalTerm::Constant(_) => {}
        LogicalTerm::Description(_) => {}
        LogicalTerm::Unspecified => {}
        LogicalTerm::Number(_) => {}
    }
    match rule {
        ProofRule::Conjunction => {}
        ProofRule::DisjunctionCheck { .. } => {}
        ProofRule::DisjunctionIntro { .. } => {}
        ProofRule::Negation => {}
        ProofRule::ModalPassthrough { .. } => {}
        ProofRule::ExistsWitness { .. } => {}
        ProofRule::ExistsFailed => {}
        ProofRule::ForallVacuous => {}
        ProofRule::ForallVerified { .. } => {}
        ProofRule::ForallCounterexample { .. } => {}
        ProofRule::CountResult { .. } => {}
        ProofRule::PredicateCheck { .. } => {}
        ProofRule::ComputeCheck { .. } => {}
        ProofRule::Asserted { .. } => {}
        ProofRule::Derived { .. } => {}
        ProofRule::ProofRef { .. } => {}
        ProofRule::EqualitySubstitution { .. } => {}
        ProofRule::RuleAttemptFailed { .. } => {}
        ProofRule::PredicateNotFound { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Exercises the exhaustiveness anchor with one variant of each enum, so the
    /// guard has a live call site and the three enums are confirmed constructible.
    #[test]
    fn exhaustiveness_guard_is_callable() {
        __exhaustiveness_guard(
            &LogicNode::NotNode(0),
            &LogicalTerm::Unspecified,
            &ProofRule::Conjunction,
        );
    }

    fn pred(name: &str) -> LogicNode {
        LogicNode::Predicate((name.to_string(), vec![]))
    }

    #[test]
    fn split_roots_multi_returns_one_buffer_per_root() {
        // Two independent roots (the bare-`.i` shape nibli-semantics emits).
        let buf = LogicBuffer {
            nodes: vec![pred("gerku"), pred("mlatu")],
            roots: vec![0, 1],
        };
        let parts = buf.split_roots();
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0].roots, vec![0]);
        assert_eq!(parts[1].roots, vec![1]);
        // Share-nodes: each sub-buffer keeps the full arena.
        assert_eq!(parts[0].nodes, buf.nodes);
        assert_eq!(parts[1].nodes, buf.nodes);
    }

    #[test]
    fn split_roots_single_is_identity() {
        let buf = LogicBuffer {
            nodes: vec![pred("gerku")],
            roots: vec![0],
        };
        let parts = buf.split_roots();
        assert_eq!(parts.len(), 1);
        assert_eq!(parts[0], buf);
    }

    #[test]
    fn split_roots_empty_returns_self() {
        let buf = LogicBuffer {
            nodes: vec![],
            roots: vec![],
        };
        let parts = buf.split_roots();
        assert_eq!(parts.len(), 1);
        assert_eq!(parts[0], buf);
    }

    #[test]
    fn split_roots_connective_root_is_not_split() {
        // A connective (`.ije`/`ge…gi`) compiles to a SINGLE root that is an
        // `AndNode` over its operands — one compound fact, must not split.
        let buf = LogicBuffer {
            nodes: vec![pred("gerku"), pred("mlatu"), LogicNode::AndNode((0, 1))],
            roots: vec![2],
        };
        let parts = buf.split_roots();
        assert_eq!(
            parts.len(),
            1,
            "a connective's single And-root must stay one fact"
        );
        assert_eq!(parts[0], buf);
    }
}
