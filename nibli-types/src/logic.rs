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
    /// Exact count over the current domain. Query-only in asserted position;
    /// it may also occur as uninterpreted content inside an opaque abstraction.
    /// Fields: (variable-name, count, body-node-id).
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

/// Where an enumerated witness came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum WitnessOrigin {
    /// A non-generated term supplied by asserted data or a rule template.
    #[default]
    KnowledgeBase,
    /// An opaque witness minted by the reasoner for an existential.
    GeneratedWitness,
    /// A witness minted by the optional legacy existential-import profile.
    ExistentialImport,
}

impl WitnessOrigin {
    pub fn label(self) -> &'static str {
        match self {
            Self::KnowledgeBase => "knowledge-base",
            Self::GeneratedWitness => "generated-witness",
            Self::ExistentialImport => "existential-import",
        }
    }
}

/// A single witness binding: variable name → logical term value, with origin.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct WitnessBinding {
    pub variable: String,
    pub term: LogicalTerm,
    pub origin: WitnessOrigin,
}

/// Why the engine cannot currently return a definitive `True` or `False`.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UnknownReason {
    /// Search encountered a recursive cycle and cut it rather than diverging.
    CycleCut,
    /// Result depends on knowledge the current KB does not have yet.
    IncompleteKnowledge,
    /// Result depends on negation-as-failure and is therefore not classically proved.
    NafDependent,
    /// An external compute predicate could not be evaluated because its backend was
    /// unreachable or unregistered, or because dispatch would expose an opaque
    /// engine-generated witness — the result is genuinely undetermined, NOT false.
    BackendUnavailable,
    /// A numeric operand or computed result is non-finite (±inf/NaN) — e.g. a literal
    /// too large for an f64 (~309+ digits overflows to ±inf). The comparison/arithmetic
    /// is genuinely undetermined, NOT a confident TRUE/FALSE.
    NonFinite,
}

/// Which resource or search bound prevented a definitive answer.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResourceKind {
    Depth,
    Fuel,
    Memory,
}

/// Top-level entailment result returned by the reasoning engine.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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

/// Unique identifier for a stored assertion in the knowledge base.
pub type FactId = u64;

/// A direct assertion that supports an [`ProofRule::Asserted`] fact.
///
/// Identical ground facts may be asserted more than once. Each assertion keeps
/// its own stable ID and source label so a proof can cite every active source
/// instead of collapsing provenance along with fact-store membership.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AssertionCitation {
    pub id: FactId,
    pub label: String,
}

/// A stored rule assertion that supports a derived or presupposed fact.
///
/// `rule_ordinal` distinguishes multiple universal rules compiled from one
/// stored assertion while `assertion_id` and `assertion_label` identify that
/// assertion across rebuilds and persistence replay.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RuleCitation {
    pub assertion_id: FactId,
    pub rule_ordinal: u32,
    pub assertion_label: String,
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
    ExistsWitness {
        var: String,
        term: LogicalTerm,
        #[cfg_attr(feature = "serde", serde(default))]
        origin: WitnessOrigin,
    },
    #[cfg_attr(feature = "serde", serde(rename = "exists_failed"))]
    ExistsFailed,
    #[cfg_attr(feature = "serde", serde(rename = "forall_vacuous"))]
    ForallVacuous,
    #[cfg_attr(feature = "serde", serde(rename = "forall_verified"))]
    ForallVerified { entities: Vec<WitnessBinding> },
    #[cfg_attr(feature = "serde", serde(rename = "forall_counterexample"))]
    ForallCounterexample { entity: WitnessBinding },
    #[cfg_attr(feature = "serde", serde(rename = "count_result"))]
    CountResult {
        expected: u32,
        actual: u32,
        #[cfg_attr(feature = "serde", serde(default))]
        existential_imported: u32,
    },
    #[cfg_attr(feature = "serde", serde(rename = "predicate_check"))]
    PredicateCheck { method: String, detail: String },
    #[cfg_attr(feature = "serde", serde(rename = "compute_check"))]
    ComputeCheck { method: String, detail: String },
    #[cfg_attr(feature = "serde", serde(rename = "asserted"))]
    Asserted {
        fact: String,
        /// Every active direct assertion of this exact fact, in stable order.
        #[cfg_attr(feature = "serde", serde(default))]
        sources: Vec<AssertionCitation>,
    },
    #[cfg_attr(feature = "serde", serde(rename = "derived"))]
    Derived {
        label: String,
        fact: String,
        /// Stored rule assertions whose canonical rule identity supports this step.
        #[cfg_attr(feature = "serde", serde(default))]
        sources: Vec<RuleCitation>,
    },
    /// Fact minted by the optional legacy existential-import profile.
    ///
    /// This is admitted base evidence under that explicit profile, not a direct
    /// user assertion and not an ordinary rule firing.
    #[cfg_attr(feature = "serde", serde(rename = "presupposed"))]
    Presupposed {
        label: String,
        fact: String,
        /// The rule assertion(s) that causally licensed this presupposition.
        #[cfg_attr(feature = "serde", serde(default))]
        sources: Vec<RuleCitation>,
    },
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
    /// (the closed-world assumption), as opposed to a compute-decided FALSE from
    /// local arithmetic or a trusted external backend (e.g. `5 dunli 3`). A
    /// closed-world FALSE is the dual of
    /// `naf_dependent` — under open-world semantics it would be Unknown, not a proof
    /// of the negation. Computed by nibli-reason from the authoritative FALSE
    /// verdict plus a structural open-world re-evaluation of the recorded root;
    /// a failed compute step only removes the caveat when it actually decides
    /// the enclosing formula or quantifier.
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
}

/// Schema version of [`ProofEnvelope`] — bump on any breaking shape change.
/// [`validate_envelope`] fails closed on versions it does not know.
pub const PROOF_ENVELOPE_SCHEMA: u32 = 2;

/// The session profile a certificate was produced under. The same KB answers
/// differently across these switches (strict ingress, legacy existential
/// import, materialisation's depth-bound completeness gain), so a certificate
/// that omitted them could be validated against the wrong semantics.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EngineProfile {
    pub strict: bool,
    pub existential_import: bool,
    pub materialization: bool,
    /// Positive depth bound used for reasoning and generated witness dependencies.
    pub max_chain_depth: u32,
}

/// A verdict BOUND to its certificate: the root [`QueryResult`] (UNKNOWN
/// reason and RESOURCE_EXCEEDED kind included), the [`ProofTrace`], the
/// producing engine's workspace version (lockstep across every crate and
/// surface — `release-check` enforces it, so any surface may stamp its own),
/// the session profile, and the query display text. A serialized
/// [`ProofTrace`] alone cannot prove which non-TRUE verdict it accompanied —
/// its root simply fails to hold for FALSE, UNKNOWN, and RESOURCE_EXCEEDED
/// alike; this envelope is the durable pairing, coherence-checkable by
/// [`validate_envelope`] without a knowledge base.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofEnvelope {
    pub schema: u32,
    pub engine_version: String,
    pub profile: EngineProfile,
    pub query: String,
    pub result: QueryResult,
    pub trace: ProofTrace,
}

impl ProofEnvelope {
    /// Bundle a traced verdict into a schema-stamped envelope. The version is
    /// the compiling workspace's lockstep version (every crate shares it).
    pub fn bind(
        query: impl Into<String>,
        result: QueryResult,
        trace: ProofTrace,
        profile: EngineProfile,
    ) -> Self {
        ProofEnvelope {
            schema: PROOF_ENVELOPE_SCHEMA,
            engine_version: env!("CARGO_PKG_VERSION").to_string(),
            profile,
            query: query.into(),
            result,
            trace,
        }
    }
}

/// Independent coherence check over a [`ProofEnvelope`] — no knowledge base
/// required. Collects EVERY violation rather than stopping at the first, so a
/// tampered or corrupted envelope reports all of what is wrong:
///
/// * unknown schema version (fail closed — later fields may mean other things),
/// * root or child step indices out of bounds,
/// * a `ProofRef` without exactly one child (its back-reference),
/// * root `holds` disagreeing with a definitive verdict (TRUE root must hold,
///   FALSE root must not; UNKNOWN/RESOURCE_EXCEEDED carry best-effort context
///   and constrain nothing),
/// * `cwa_false` on a non-FALSE verdict,
/// * a `naf_dependent` flag that does not match the recomputable property
///   (any `Negation` step with `holds: true`).
pub fn validate_envelope(envelope: &ProofEnvelope) -> Result<(), Vec<String>> {
    let mut errs: Vec<String> = Vec::new();
    if envelope.schema != PROOF_ENVELOPE_SCHEMA {
        return Err(vec![format!(
            "unknown envelope schema {} (validator knows {PROOF_ENVELOPE_SCHEMA}) — refusing \
             to interpret the remaining fields",
            envelope.schema
        )]);
    }
    if envelope.profile.max_chain_depth == 0 {
        errs.push("profile max_chain_depth must be positive".into());
    }
    let steps = &envelope.trace.steps;
    let n = steps.len();
    if envelope.trace.root as usize >= n {
        errs.push(format!(
            "root index {} out of bounds ({n} steps)",
            envelope.trace.root
        ));
    }
    for (i, step) in steps.iter().enumerate() {
        for &child in &step.children {
            if child as usize >= n {
                errs.push(format!(
                    "step {i}: child index {child} out of bounds ({n} steps)"
                ));
            }
        }
        if matches!(step.rule, ProofRule::ProofRef { .. }) && step.children.len() != 1 {
            errs.push(format!(
                "step {i}: ProofRef must carry exactly one back-reference child, has {}",
                step.children.len()
            ));
        }
    }
    if let Some(root) = steps.get(envelope.trace.root as usize) {
        match envelope.result {
            QueryResult::True if !root.holds => {
                errs.push("TRUE verdict but the root step does not hold".to_string());
            }
            QueryResult::False if root.holds => {
                errs.push("FALSE verdict but the root step holds".to_string());
            }
            _ => {}
        }
    }
    if envelope.trace.cwa_false && !matches!(envelope.result, QueryResult::False) {
        errs.push("cwa_false set on a non-FALSE verdict".to_string());
    }
    if envelope.trace.naf_dependent != envelope.trace.has_naf_dependency() {
        errs.push(format!(
            "naf_dependent flag ({}) does not match the trace's recomputable NAF property ({})",
            envelope.trace.naf_dependent,
            envelope.trace.has_naf_dependency()
        ));
    }
    if errs.is_empty() { Ok(()) } else { Err(errs) }
}

/// Aggregation operation for numeric witness values.
#[derive(Clone, Debug)]
pub enum AggregateOp {
    Sum,
    Min,
    Max,
    Avg,
}

/// The fail-closed result of a numeric aggregation over witness bindings.
///
/// `Empty` is a DEFINITIVE zero-witness enumeration — nothing matched, so
/// there is nothing to aggregate — distinct from every defect class, which is
/// an error, never a silent drop: a binding set missing the variable, a
/// nonnumeric value, a non-finite operand, and a non-finite result (overflow)
/// all refuse. `Value` carries the contributing-witness count as provenance,
/// so a caller can state what the figure summarizes.
#[derive(Clone, Debug, PartialEq)]
pub enum AggregateOutcome {
    /// The enumeration was complete and empty: no witness binding sets.
    Empty,
    /// Every binding set contributed exactly one finite numeric value.
    Value { value: f64, witnesses: usize },
}

/// Summary of an active fact in the knowledge base.
#[derive(Clone, Debug)]
pub struct FactSummary {
    pub id: FactId,
    pub label: String,
    pub root_count: u32,
}

/// Current state of a retained assertion record, not an audit chronology.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AssertionStatus {
    Active,
    Withdrawn,
}

/// An assertion's stable identity and display label, including withdrawn records.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AssertionRecordSummary {
    pub id: FactId,
    pub label: String,
    pub status: AssertionStatus,
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
/// Since the WIT `with`-remap (nibli-pipeline/Cargo.toml, 2026-07-18),
/// `LogicNode`/`LogicalTerm` (and `LogicBuffer`/`QueryResult`/errors/witness/
/// fact-summary) ARE the WIT boundary types on the guest side — no converter to
/// touch there for a new variant of those. `ProofRule` alone keeps a hand map
/// (the WIT `proof-rule` is a tuple/newtype-record mirror wit-bindgen can't
/// make struct-variant, so it stays generated).
///
/// When you add or remove a variant of any of these three enums, update:
/// - `nibli-pipeline/src/lib.rs` — `convert_proof_rule` (→ the WIT guest
///   `proof-rule` record mirror); a new `LogicNode`/`LogicalTerm` variant needs
///   NO guest converter (the type is `with`-remapped onto this crate) but DOES
///   need the matching WIT `logic-node`/`logical-term` case in `wit/world.wit`
///   plus a regenerate
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
/// - `wit/world.wit` — the `logical-term` / `proof-rule` variant lists (for
///   `proof-rule`, add both the payload `record …-rule` and the variant case),
///   then regenerate bindings with `cargo component build`
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
        ProofRule::Presupposed { .. } => {}
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

    #[test]
    fn witness_origin_labels_are_stable_and_unambiguous() {
        assert_eq!(WitnessOrigin::KnowledgeBase.label(), "knowledge-base");
        assert_eq!(WitnessOrigin::GeneratedWitness.label(), "generated-witness");
        assert_eq!(
            WitnessOrigin::ExistentialImport.label(),
            "existential-import"
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

#[cfg(test)]
mod envelope_tests {
    use super::*;

    fn leaf(rule: ProofRule, holds: bool, children: Vec<u32>) -> ProofStep {
        ProofStep {
            rule,
            holds,
            children,
        }
    }

    fn valid_true_envelope() -> ProofEnvelope {
        ProofEnvelope::bind(
            "dog(Adam).",
            QueryResult::True,
            ProofTrace {
                steps: vec![leaf(
                    ProofRule::Asserted {
                        fact: "dog(adam)".into(),
                        sources: vec![],
                    },
                    true,
                    vec![],
                )],
                root: 0,
                naf_dependent: false,
                cwa_false: false,
            },
            EngineProfile {
                strict: false,
                existential_import: false,
                materialization: true,
                max_chain_depth: 10,
            },
        )
    }

    #[test]
    fn a_valid_envelope_validates_and_stamps_the_lockstep_version() {
        let e = valid_true_envelope();
        assert_eq!(e.schema, PROOF_ENVELOPE_SCHEMA);
        assert_eq!(e.engine_version, env!("CARGO_PKG_VERSION"));
        validate_envelope(&e).expect("a coherent envelope must validate");
    }

    #[test]
    fn every_incoherence_class_is_reported_by_name() {
        // Unknown schema fails closed, alone.
        let mut e = valid_true_envelope();
        e.schema = 999;
        let errs = validate_envelope(&e).unwrap_err();
        assert!(errs[0].contains("unknown envelope schema"), "{errs:?}");

        let mut e = valid_true_envelope();
        e.profile.max_chain_depth = 0;
        assert!(validate_envelope(&e).unwrap_err()[0].contains("max_chain_depth"));

        // Root out of bounds.
        let mut e = valid_true_envelope();
        e.trace.root = 7;
        assert!(
            validate_envelope(&e).unwrap_err()[0].contains("root index"),
            "root OOB must be named"
        );

        // Child out of bounds + ProofRef arity, collected TOGETHER.
        let mut e = valid_true_envelope();
        e.trace.steps.push(leaf(
            ProofRule::ProofRef {
                fact: "dog(adam)".into(),
            },
            true,
            vec![9, 0],
        ));
        let errs = validate_envelope(&e).unwrap_err();
        assert!(errs.iter().any(|m| m.contains("out of bounds")), "{errs:?}");
        assert!(
            errs.iter()
                .any(|m| m.contains("exactly one back-reference")),
            "{errs:?}"
        );

        // Verdict/holds mismatch, both directions.
        let mut e = valid_true_envelope();
        e.trace.steps[0].holds = false;
        assert!(
            validate_envelope(&e).unwrap_err()[0].contains("TRUE verdict"),
            "TRUE with non-holding root must be named"
        );
        let mut e = valid_true_envelope();
        e.result = QueryResult::False;
        assert!(
            validate_envelope(&e).unwrap_err()[0].contains("FALSE verdict"),
            "FALSE with holding root must be named"
        );

        // cwa_false on a non-FALSE verdict.
        let mut e = valid_true_envelope();
        e.trace.cwa_false = true;
        assert!(
            validate_envelope(&e)
                .unwrap_err()
                .iter()
                .any(|m| m.contains("cwa_false")),
            "cwa_false on TRUE must be named"
        );

        // naf_dependent flag drift from the recomputable property.
        let mut e = valid_true_envelope();
        e.trace.naf_dependent = true;
        assert!(
            validate_envelope(&e)
                .unwrap_err()
                .iter()
                .any(|m| m.contains("naf_dependent")),
            "NAF flag drift must be named"
        );
    }

    #[test]
    fn unknown_and_resource_verdicts_constrain_no_root_holds() {
        for result in [
            QueryResult::Unknown(UnknownReason::CycleCut),
            QueryResult::Unknown(UnknownReason::IncompleteKnowledge),
            QueryResult::Unknown(UnknownReason::NafDependent),
            QueryResult::Unknown(UnknownReason::BackendUnavailable),
            QueryResult::Unknown(UnknownReason::NonFinite),
            QueryResult::ResourceExceeded(ResourceKind::Depth),
            QueryResult::ResourceExceeded(ResourceKind::Fuel),
            QueryResult::ResourceExceeded(ResourceKind::Memory),
        ] {
            let mut e = valid_true_envelope();
            e.result = result.clone();
            validate_envelope(&e).unwrap_or_else(|errs| {
                panic!("{result:?} must not constrain root holds: {errs:?}")
            });
        }
    }
}
