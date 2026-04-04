//! First-Order Logic types produced by the smuni compiler and consumed by logji.
//!
//! Flat index-based representation: `LogicBuffer` contains a `nodes` array
//! of `LogicNode` variants, referenced by `u32` indices.

/// A logical term — the typed representation of an FOL argument.
#[derive(Clone, Debug, PartialEq)]
pub enum LogicalTerm {
    /// A bound or free variable (e.g., Skolem variables, universally quantified vars).
    Variable(String),
    /// A ground constant (e.g., entity names from `la`).
    Constant(String),
    /// An opaque description reference (from `le` gadri).
    Description(String),
    /// Unspecified placeholder (from `zo'e`).
    Unspecified,
    /// Numeric literal (from `li` + PA).
    Number(f64),
}

/// A node in the flat logic graph. Each variant corresponds to an FOL constructor.
/// Nodes reference children by `u32` index into the `LogicBuffer.nodes` array.
#[derive(Clone, Debug, PartialEq)]
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
pub struct LogicBuffer {
    pub nodes: Vec<LogicNode>,
    pub roots: Vec<u32>,
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
            Self::ResourceExceeded(ResourceKind::Depth) => Some("depth"),
            Self::ResourceExceeded(ResourceKind::Fuel) => Some("fuel"),
            Self::ResourceExceeded(ResourceKind::Memory) => Some("memory"),
            _ => None,
        }
    }
}

/// Proof rule applied at a single proof step.
#[derive(Clone, Debug)]
pub enum ProofRule {
    Conjunction,
    DisjunctionCheck(String),
    DisjunctionIntro(String),
    Negation,
    ModalPassthrough(String),
    ExistsWitness((String, LogicalTerm)),
    ExistsFailed,
    ForallVacuous,
    ForallVerified(Vec<LogicalTerm>),
    ForallCounterexample(LogicalTerm),
    CountResult((u32, u32)),
    PredicateCheck((String, String)),
    ComputeCheck((String, String)),
    Asserted(String),
    Derived((String, String)),
    ProofRef(String),
    /// Equality substitution: fact proved by substituting equivalent terms.
    /// Fields: (original fact, du facts used, substituted fact that was found).
    EqualitySubstitution((String, String, String)),
    /// Rule was tried but a condition failed. Fields: (rule_label, failed_condition_display).
    RuleAttemptFailed((String, String)),
    /// Predicate not found in fact store and no rule could derive it. Field: predicate display.
    PredicateNotFound(String),
}

/// A single step in a proof trace.
#[derive(Clone, Debug)]
pub struct ProofStep {
    pub rule: ProofRule,
    pub holds: bool,
    pub children: Vec<u32>,
}

/// Complete proof trace: steps array + root index.
#[derive(Clone, Debug)]
pub struct ProofTrace {
    pub steps: Vec<ProofStep>,
    pub root: u32,
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
