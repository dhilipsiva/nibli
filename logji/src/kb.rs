use super::*;
use std::cell::{Cell, RefCell};

// ═══════════════════════════════════════════════════════════════════
// PREDICATE SIGNATURE VALIDATION
// ═══════════════════════════════════════════════════════════════════

/// How a predicate's arity was determined.
#[derive(Clone, Debug)]
pub enum SignatureSource {
    /// Arity from the jbovlaste PHF dictionary (known gismu/lujvo).
    Dictionary,
    /// Arity inferred from the first assertion (not in dictionary).
    Inferred,
}

/// Registered predicate signature: arity + how it was determined.
#[derive(Clone, Debug)]
pub struct PredicateSignature {
    pub arity: usize,
    pub source: SignatureSource,
    /// Optional sort constraint for each argument position.
    /// Empty string = any sort (no constraint). Set via `set_predicate_sorts`.
    pub arg_sorts: Vec<String>,
}

// ═══════════════════════════════════════════════════════════════════
// INTEGRITY CONSTRAINTS
// ═══════════════════════════════════════════════════════════════════

/// An integrity constraint: a set of conjuncts that must NOT all hold simultaneously.
/// If every conjunct is satisfied in the KB, the constraint is violated.
#[derive(Clone, Debug)]
pub struct IntegrityConstraint {
    /// Human-readable label, e.g. "mutual-exclusion: gerku ∧ mlatu".
    pub label: String,
    /// Facts that must NOT all be true at the same time.
    pub conjuncts: Vec<StoredFact>,
    /// Predicate names appearing in conjuncts (for fast filtering).
    pub predicates: Vec<String>,
}

/// Check integrity constraints relevant to a predicate after a fact insertion.
/// Returns Err with a violation message if any constraint is fully satisfied.
pub(super) fn check_constraints_for_predicate(
    rel: &str,
    inner: &KnowledgeBaseInner,
) -> Option<String> {
    for constraint in &inner.integrity_constraints {
        if !constraint.predicates.iter().any(|p| p == rel) {
            continue;
        }
        let all_hold = constraint
            .conjuncts
            .iter()
            .all(|c| inner.fact_store.contains(c));
        if all_hold {
            let facts: Vec<String> = constraint
                .conjuncts
                .iter()
                .map(|c| c.to_display_string())
                .collect();
            return Some(format!(
                "Integrity violation '{}': {} all hold simultaneously",
                constraint.label,
                facts.join(" ∧ ")
            ));
        }
    }
    None
}

/// Bounds-checked node access. Returns a descriptive error instead of panicking
/// if node_id is out of range (e.g., from a malformed LogicBuffer).
pub(super) fn get_node(buffer: &LogicBuffer, node_id: u32) -> Result<&LogicNode, String> {
    buffer.nodes.get(node_id as usize).ok_or_else(|| {
        format!(
            "invalid node index {} (buffer has {} nodes)",
            node_id,
            buffer.nodes.len()
        )
    })
}

// ─── Typed Fact Representation ────────────────────────────────────
//
// These types replace the internal representation string layer. Facts are stored and
// matched structurally instead of via string serialization/tokenization.

/// A ground term — the typed representation of a ground term.
/// Implements Hash/Eq for direct use in HashSet-based fact stores.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum GroundTerm {
    /// Named constant (e.g., "adam", "paris", "sk_0").
    /// Also used for Skolem constants — the internal format does not distinguish them.
    Constant(String),
    /// Floating-point number stored as bit pattern for Hash/Eq.
    Number(u64),
    /// Opaque description term (le-gadri).
    Description(String),
    /// Unspecified argument (zo'e).
    Unspecified,
    /// Dependent Skolem function (e.g., SkolemFn("sk_1", Constant("adam"))).
    SkolemFn(String, Box<GroundTerm>),
    /// Multi-dependency pairing for SkolemFn with multiple universals.
    DepPair(Box<GroundTerm>, Box<GroundTerm>),
    /// Pattern variable — only used in rule templates, never in the fact store.
    PatternVar(String),
}

impl GroundTerm {
    /// Create a Number term from f64.
    pub fn from_f64(v: f64) -> Self {
        GroundTerm::Number(v.to_bits())
    }

    /// Extract f64 from a Number term.
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            GroundTerm::Number(bits) => Some(f64::from_bits(*bits)),
            _ => None,
        }
    }

    /// Human-readable display string.
    pub fn to_display_string(&self) -> String {
        match self {
            GroundTerm::Constant(s) => s.clone(),
            GroundTerm::Number(bits) => {
                let v = f64::from_bits(*bits);
                if v == v.floor() && v.abs() < 1e15 {
                    format!("{}", v as i64)
                } else {
                    format!("{v}")
                }
            }
            GroundTerm::Description(s) => format!("le {s}"),
            GroundTerm::Unspecified => "_".to_string(),
            GroundTerm::SkolemFn(name, dep) => {
                format!("{name}({})", dep.to_display_string())
            }
            GroundTerm::DepPair(a, b) => {
                format!("({}, {})", a.to_display_string(), b.to_display_string())
            }
            GroundTerm::PatternVar(s) => format!("?{s}"),
        }
    }
}

/// A ground predicate — relation name plus argument list.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GroundFact {
    pub relation: String,
    pub args: Vec<GroundTerm>,
}

impl GroundFact {
    pub fn new(relation: impl Into<String>, args: Vec<GroundTerm>) -> Self {
        GroundFact {
            relation: relation.into(),
            args,
        }
    }

    /// Human-readable display: relation(arg1, arg2, ...)
    pub fn to_display_string(&self) -> String {
        if self.args.is_empty() {
            self.relation.clone()
        } else {
            let args_str: Vec<String> = self.args.iter().map(|a| a.to_display_string()).collect();
            format!("{}({})", self.relation, args_str.join(", "))
        }
    }
}

/// A fact with optional tense/deontic wrapper — the atomic unit of the fact store.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StoredFact {
    Bare(GroundFact),
    Past(GroundFact),
    Present(GroundFact),
    Future(GroundFact),
    Obligatory(GroundFact),
    Permitted(GroundFact),
}

impl StoredFact {
    /// Get the inner predicate's relation name.
    pub fn relation(&self) -> &str {
        match self {
            StoredFact::Bare(f)
            | StoredFact::Past(f)
            | StoredFact::Present(f)
            | StoredFact::Future(f)
            | StoredFact::Obligatory(f)
            | StoredFact::Permitted(f) => &f.relation,
        }
    }

    /// Get a reference to the inner GroundFact.
    pub fn inner(&self) -> &GroundFact {
        match self {
            StoredFact::Bare(f)
            | StoredFact::Past(f)
            | StoredFact::Present(f)
            | StoredFact::Future(f)
            | StoredFact::Obligatory(f)
            | StoredFact::Permitted(f) => f,
        }
    }

    /// Wrap a GroundFact with the same tense/deontic context as another StoredFact.
    pub fn with_tense_from(fact: GroundFact, source: &StoredFact) -> Self {
        match source {
            StoredFact::Bare(_) => StoredFact::Bare(fact),
            StoredFact::Past(_) => StoredFact::Past(fact),
            StoredFact::Present(_) => StoredFact::Present(fact),
            StoredFact::Future(_) => StoredFact::Future(fact),
            StoredFact::Obligatory(_) => StoredFact::Obligatory(fact),
            StoredFact::Permitted(_) => StoredFact::Permitted(fact),
        }
    }

    /// Wrap a GroundFact with a tense/deontic context.
    pub fn with_tense(fact: GroundFact, tense: Option<&str>) -> Self {
        match tense {
            Some("Past") => StoredFact::Past(fact),
            Some("Present") => StoredFact::Present(fact),
            Some("Future") => StoredFact::Future(fact),
            Some("Obligatory") => StoredFact::Obligatory(fact),
            Some("Permitted") => StoredFact::Permitted(fact),
            _ => StoredFact::Bare(fact),
        }
    }

    /// Human-readable display string.
    pub fn to_display_string(&self) -> String {
        match self {
            StoredFact::Bare(f) => f.to_display_string(),
            StoredFact::Past(f) => format!("Past({})", f.to_display_string()),
            StoredFact::Present(f) => format!("Present({})", f.to_display_string()),
            StoredFact::Future(f) => format!("Future({})", f.to_display_string()),
            StoredFact::Obligatory(f) => format!("Obligatory({})", f.to_display_string()),
            StoredFact::Permitted(f) => format!("Permitted({})", f.to_display_string()),
        }
    }
}

/// Structural unification: match a template (with PatternVars) against a concrete fact.
/// Returns variable bindings on success, None on mismatch.
pub fn unify_facts(
    template: &StoredFact,
    concrete: &StoredFact,
) -> Option<HashMap<String, GroundTerm>> {
    // Tense/deontic wrapper must match.
    let (t_inner, c_inner) = match (template, concrete) {
        (StoredFact::Bare(t), StoredFact::Bare(c)) => (t, c),
        (StoredFact::Past(t), StoredFact::Past(c)) => (t, c),
        (StoredFact::Present(t), StoredFact::Present(c)) => (t, c),
        (StoredFact::Future(t), StoredFact::Future(c)) => (t, c),
        (StoredFact::Obligatory(t), StoredFact::Obligatory(c)) => (t, c),
        (StoredFact::Permitted(t), StoredFact::Permitted(c)) => (t, c),
        _ => return None,
    };

    // Relation name must match.
    if t_inner.relation != c_inner.relation {
        return None;
    }

    // Arg count must match.
    if t_inner.args.len() != c_inner.args.len() {
        return None;
    }

    // Unify each argument pair.
    let mut bindings = HashMap::new();
    for (t_arg, c_arg) in t_inner.args.iter().zip(c_inner.args.iter()) {
        if !unify_terms(t_arg, c_arg, &mut bindings) {
            return None;
        }
    }
    Some(bindings)
}

/// Unify a template term against a concrete term, accumulating bindings.
fn unify_terms(
    template: &GroundTerm,
    concrete: &GroundTerm,
    bindings: &mut HashMap<String, GroundTerm>,
) -> bool {
    match template {
        GroundTerm::PatternVar(name) => {
            if let Some(existing) = bindings.get(name) {
                // Variable already bound — must match.
                existing == concrete
            } else {
                bindings.insert(name.clone(), concrete.clone());
                true
            }
        }
        // Structural match for non-variable terms.
        GroundTerm::Constant(a) => matches!(concrete, GroundTerm::Constant(b) if a == b),
        GroundTerm::Number(a) => matches!(concrete, GroundTerm::Number(b) if a == b),
        GroundTerm::Description(a) => matches!(concrete, GroundTerm::Description(b) if a == b),
        GroundTerm::Unspecified => matches!(concrete, GroundTerm::Unspecified),
        GroundTerm::SkolemFn(name_a, dep_a) => {
            if let GroundTerm::SkolemFn(name_b, dep_b) = concrete {
                name_a == name_b && unify_terms(dep_a, dep_b, bindings)
            } else {
                false
            }
        }
        GroundTerm::DepPair(a1, a2) => {
            if let GroundTerm::DepPair(b1, b2) = concrete {
                unify_terms(a1, b1, bindings) && unify_terms(a2, b2, bindings)
            } else {
                false
            }
        }
    }
}

/// Apply bindings to a template fact, replacing PatternVars with bound values.
pub fn substitute_fact(
    template: &StoredFact,
    bindings: &HashMap<String, GroundTerm>,
) -> StoredFact {
    let sub_inner = |f: &GroundFact| -> GroundFact {
        GroundFact {
            relation: f.relation.clone(),
            args: f
                .args
                .iter()
                .map(|a| substitute_term(a, bindings).into_owned())
                .collect(),
        }
    };
    match template {
        StoredFact::Bare(f) => StoredFact::Bare(sub_inner(f)),
        StoredFact::Past(f) => StoredFact::Past(sub_inner(f)),
        StoredFact::Present(f) => StoredFact::Present(sub_inner(f)),
        StoredFact::Future(f) => StoredFact::Future(sub_inner(f)),
        StoredFact::Obligatory(f) => StoredFact::Obligatory(sub_inner(f)),
        StoredFact::Permitted(f) => StoredFact::Permitted(sub_inner(f)),
    }
}

/// Apply bindings to a single term.
pub fn substitute_term<'a>(
    term: &'a GroundTerm,
    bindings: &HashMap<String, GroundTerm>,
) -> Cow<'a, GroundTerm> {
    match term {
        GroundTerm::PatternVar(name) => match bindings.get(name) {
            Some(replacement) => Cow::Owned(replacement.clone()),
            None => Cow::Borrowed(term),
        },
        GroundTerm::SkolemFn(name, dep) => {
            let new_dep = substitute_term(dep, bindings);
            match new_dep {
                Cow::Borrowed(_) => Cow::Borrowed(term),
                Cow::Owned(d) => Cow::Owned(GroundTerm::SkolemFn(name.clone(), Box::new(d))),
            }
        }
        GroundTerm::DepPair(a, b) => {
            let new_a = substitute_term(a, bindings);
            let new_b = substitute_term(b, bindings);
            match (&new_a, &new_b) {
                (Cow::Borrowed(_), Cow::Borrowed(_)) => Cow::Borrowed(term),
                _ => Cow::Owned(GroundTerm::DepPair(
                    Box::new(new_a.into_owned()),
                    Box::new(new_b.into_owned()),
                )),
            }
        }
        // All other terms are ground — no substitution needed.
        _ => Cow::Borrowed(term),
    }
}

// ─── Knowledge Base State ────────────────────────────────────────

/// Registry entry for a SkolemFn created by native rule compilation.
/// Used by query-side existential checking to generate SkolemFn witness terms.
#[derive(Clone)]
pub(super) struct SkolemFnEntry {
    pub(super) base_name: String,
    pub(super) dep_count: usize,
}

/// Prefix used for dependent Skolem placeholder variables.
/// A dependent Skolem is an ∃ variable nested under a ∀.
pub(super) const SKDEP_PREFIX: &str = "__skdep__";

/// Build a human-readable rule label from typed conditions and conclusions.
pub(super) fn build_typed_rule_label(
    conditions: &[StoredFact],
    conclusions: &[StoredFact],
) -> String {
    let conds: Vec<String> = conditions
        .iter()
        .map(|f| f.relation().to_string())
        .collect();
    let concls: Vec<String> = conclusions
        .iter()
        .map(|f| f.relation().to_string())
        .collect();
    if conds.is_empty() {
        concls.join(" ∧ ")
    } else {
        format!("{} → {}", conds.join(" ∧ "), concls.join(" ∧ "))
    }
}

/// Records the structure of a compiled universal rule for backward-chaining provenance.
/// Templates use bare pattern variables (e.g., `x__v0`) instead of bound values.
#[derive(Clone)]
pub(super) struct UniversalRuleRecord {
    /// Human-readable label, e.g. "gerku → danlu"
    pub(super) label: String,
    /// Condition templates (with PatternVar terms for structural unification).
    pub(super) typed_conditions: Vec<StoredFact>,
    /// Conclusion templates (with PatternVar terms for structural unification).
    pub(super) typed_conclusions: Vec<StoredFact>,
    /// Pattern variable names used in templates, e.g. ["x__v0"].
    pub(super) pattern_var_names: Vec<String>,
    /// Indices into `typed_conditions` that were originally under negation.
    /// Used for stratification checking — a negated condition creates a
    /// "negative" dependency edge in the predicate dependency graph.
    pub(super) negated_condition_indices: Vec<usize>,
    /// When true, this rule fires eagerly on fact assertion (forward chaining).
    /// When false (default), the rule only fires via backward-chaining queries.
    pub(super) forward: bool,
    /// Rule priority (default 0). Higher = more important. When multiple rules
    /// match a goal, higher-priority rules are tried first (defeasible reasoning).
    pub(super) priority: u32,
}

/// Registry entry for a single asserted fact, supporting retraction and rebuild.
#[derive(Clone)]
pub(super) struct FactRecord {
    pub(super) id: u64,
    pub(super) buffer: LogicBuffer,
    pub(super) label: String,
    pub(super) retracted: bool,
}

/// All mutable KB state behind a single RefCell.
pub(super) struct KnowledgeBaseInner {
    pub(super) skolem_counter: usize,
    pub(super) known_entities: HashSet<String>,
    /// Event Skolem constants (from `_ev*` variables). Tracked for witness search
    /// and proof tracing, but NOT registered in `known_entities`
    /// to prevent quadratic blowup in guarded conjunction introduction.
    pub(super) known_event_entities: HashSet<String>,
    /// Known description terms (from `le` gadri), tracked separately for InDomain.
    pub(super) known_descriptions: HashSet<String>,
    pub(super) known_rules: HashSet<u64>,
    pub(super) skolem_fn_registry: Vec<SkolemFnEntry>,
    /// Pluggable fact store (in-memory or persistent).
    pub(super) fact_store: Box<dyn crate::fact_store::FactStore>,
    /// Compiled universal rule templates indexed by conclusion predicate name.
    /// Each predicate name maps to the rules whose conclusion templates mention it.
    /// Rc-wrapped to avoid cloning rule records during backward-chain snapshots.
    pub(super) universal_rules: HashMap<String, Vec<Arc<UniversalRuleRecord>>>,
    /// Monotonically increasing fact ID counter.
    pub(super) fact_counter: u64,
    /// Registry of all asserted facts (including retracted ones, for ID stability).
    pub(super) fact_registry: HashMap<u64, FactRecord>,
    /// Suppresses diagnostic prints during rebuild replay.
    pub(super) rebuilding: bool,
    /// Configuration parameter preserved across reset/rebuild (kept for WIT API compatibility).
    /// Cached typed domain members — invalidated when entities/descriptions change.
    pub(super) typed_domain_members_cache: Vec<GroundTerm>,
    pub(super) domain_members_dirty: bool,
    /// Maximum backward-chaining depth for inference (default: 10).
    pub(super) max_chain_depth: usize,
    /// Predicate dependency graph for stratification checking.
    /// Maps conclusion predicate → Vec<(condition predicate, is_negative)>.
    pub(super) pred_dep_graph: HashMap<String, Vec<(String, bool)>>,
    /// Union-Find parent map for du-equivalence. Maps term → parent term.
    pub(super) equivalence_parent: HashMap<GroundTerm, GroundTerm>,
    /// Reverse index: canonical representative → all members of its class.
    pub(super) equivalence_classes: HashMap<GroundTerm, Vec<GroundTerm>>,
    /// Predicate signature registry: tracks arity + source for each predicate.
    /// Populated lazily on first assertion. Warns on arity mismatch.
    pub(super) predicate_registry: HashMap<String, PredicateSignature>,
    /// Integrity constraints: conjunct sets that must NOT all hold simultaneously.
    /// Checked after each fact insertion. Violations are warnings in permissive mode.
    pub(super) integrity_constraints: Vec<IntegrityConstraint>,
    /// Argument-position index: (relation, arg_position) → {value → [facts]}.
    /// Speeds up witness extraction and ground-argument queries.
    pub(super) arg_position_index: HashMap<(String, usize), HashMap<GroundTerm, Vec<StoredFact>>>,
    /// Maps fact_registry ID → rule predicate keys inserted into universal_rules.
    /// Used for incremental retraction: when a fact that compiled rules is retracted,
    /// the corresponding rules can be removed without full rebuild.
    pub(super) rule_source_map: HashMap<u64, Vec<String>>,
    /// The current assertion's fact_registry ID (set during process_assertion).
    /// Used by compile_forall_to_rule to record rule sources.
    pub(super) current_assertion_id: Option<u64>,
    /// Depth counter for forward chaining recursion. Prevents infinite loops.
    pub(super) forward_depth: usize,
    /// Sort hierarchy: sort_name → set of parent sort names (transitive).
    /// e.g., "person" → {"animal"}, "animal" → {"entity"}
    pub(super) sort_hierarchy: HashMap<String, HashSet<String>>,
    /// Entity sort assignments: entity_name → sort_name.
    /// e.g., "adam" → "person"
    pub(super) entity_sorts: HashMap<String, String>,
    /// Predicates being traced for interactive debugging.
    /// When a traced predicate is encountered during reasoning, diagnostic
    /// output is printed showing depth, rule matches, and condition results.
    pub(super) traced_predicates: HashSet<String>,
    /// Explicitly asserted NEGATIVE ground facts (`na <selbri>`), stored as
    /// template groups for contradiction detection (`check_contradictions`).
    /// Each group is the conjunction of leaves under one negation, with event
    /// Skolem arguments generalized to pattern variables (see
    /// `record_negative_ground_fact`). Negatives never enter the positive fact
    /// store or predicate index — queries keep NAF/CWA semantics unchanged.
    pub(super) negative_facts: HashSet<Vec<StoredFact>>,
    /// Cooperative cancellation flag (None = never cancels). Set by a native
    /// caller (the nibli-server request watchdog) when a query's wall-clock
    /// budget elapses; checked at the central reasoning entry points, which
    /// abort via the `Result::Err` channel. Default `None` keeps gasnu/lasna/
    /// tests byte-identical and needs no clock — the WASI sandbox forbids one.
    pub(super) cancel: Option<Arc<std::sync::atomic::AtomicBool>>,
    /// Per-instance external compute dispatch (replaces the old thread-local
    /// `register_compute_dispatch`, which the multithreaded server could never
    /// register because each tokio worker had its own `None` thread-local). Set
    /// via `KnowledgeBase::set_compute_dispatch`. Like `cancel`, this is
    /// CONFIGURATION, not derived state — NOT cleared by `reset()`. `None` means
    /// external predicates return an error (built-in arithmetic still works).
    pub(super) compute_eval: Option<crate::compute::EvalFn>,
    pub(super) compute_batch_eval: Option<crate::compute::BatchEvalFn>,
    /// Per-instance predicate-result cache (was a thread-local shared across all
    /// KBs on a thread). Interior-mutable because the backward-chain reads/writes
    /// it through a SHARED `&inner` (`check_predicate_in_kb_typed`). Only
    /// definitive True/False are cached; cleared at every KB mutation and at
    /// query start. `pred_cache_enabled` gates lookups (off during assertion
    /// replay, on during a query so results table across iterative-deepening
    /// passes). Per-KB isolation is a strict improvement for the multithreaded
    /// server (the old thread-local leaked across distinct KBs on a reused
    /// blocking-pool worker); byte-identical for single-KB embedders.
    pub(super) pred_cache: RefCell<HashMap<StoredFact, QueryResult>>,
    pub(super) pred_cache_enabled: Cell<bool>,
}

impl Clone for KnowledgeBaseInner {
    fn clone(&self) -> Self {
        Self {
            skolem_counter: self.skolem_counter,
            known_entities: self.known_entities.clone(),
            known_event_entities: self.known_event_entities.clone(),
            known_descriptions: self.known_descriptions.clone(),
            known_rules: self.known_rules.clone(),
            skolem_fn_registry: self.skolem_fn_registry.clone(),
            fact_store: self.fact_store.clone_box(),
            universal_rules: self.universal_rules.clone(),
            fact_counter: self.fact_counter,
            fact_registry: self.fact_registry.clone(),
            rebuilding: false,
            typed_domain_members_cache: self.typed_domain_members_cache.clone(),
            domain_members_dirty: self.domain_members_dirty,
            max_chain_depth: self.max_chain_depth,
            pred_dep_graph: self.pred_dep_graph.clone(),
            equivalence_parent: self.equivalence_parent.clone(),
            equivalence_classes: self.equivalence_classes.clone(),
            predicate_registry: self.predicate_registry.clone(),
            integrity_constraints: self.integrity_constraints.clone(),
            arg_position_index: self.arg_position_index.clone(),
            rule_source_map: self.rule_source_map.clone(),
            current_assertion_id: None,
            forward_depth: 0,
            sort_hierarchy: self.sort_hierarchy.clone(),
            entity_sorts: self.entity_sorts.clone(),
            traced_predicates: self.traced_predicates.clone(),
            negative_facts: self.negative_facts.clone(),
            cancel: self.cancel.clone(),
            compute_eval: self.compute_eval,
            compute_batch_eval: self.compute_batch_eval,
            pred_cache: RefCell::new(HashMap::new()),
            pred_cache_enabled: Cell::new(false),
        }
    }
}

impl KnowledgeBaseInner {
    pub(super) fn new() -> Self {
        Self {
            skolem_counter: 0,
            known_entities: HashSet::new(),
            known_event_entities: HashSet::new(),
            known_descriptions: HashSet::new(),
            known_rules: HashSet::new(),
            skolem_fn_registry: Vec::new(),
            fact_store: Box::new(crate::fact_store::InMemoryFactStore::new()),
            universal_rules: HashMap::new(),
            fact_counter: 0,
            fact_registry: HashMap::new(),
            rebuilding: false,
            typed_domain_members_cache: Vec::new(),
            domain_members_dirty: true,
            max_chain_depth: 10,
            pred_dep_graph: HashMap::new(),
            equivalence_parent: HashMap::new(),
            equivalence_classes: HashMap::new(),
            predicate_registry: HashMap::new(),
            integrity_constraints: Vec::new(),
            arg_position_index: HashMap::new(),
            rule_source_map: HashMap::new(),
            current_assertion_id: None,
            forward_depth: 0,
            sort_hierarchy: HashMap::new(),
            entity_sorts: HashMap::new(),
            traced_predicates: HashSet::new(),
            negative_facts: HashSet::new(),
            cancel: None,
            compute_eval: None,
            compute_batch_eval: None,
            pred_cache: RefCell::new(HashMap::new()),
            pred_cache_enabled: Cell::new(false),
        }
    }

    pub(super) fn reset(&mut self) {
        self.skolem_counter = 0;
        self.known_entities.clear();
        self.known_event_entities.clear();
        self.known_descriptions.clear();
        self.known_rules.clear();
        self.skolem_fn_registry.clear();
        self.fact_store.clear();
        self.universal_rules.clear();
        self.fact_counter = 0;
        self.fact_registry.clear();
        self.rebuilding = false;
        self.typed_domain_members_cache.clear();
        self.domain_members_dirty = true;
        self.pred_dep_graph.clear();
        self.equivalence_parent.clear();
        self.equivalence_classes.clear();
        self.predicate_registry.clear();
        self.arg_position_index.clear();
        self.rule_source_map.clear();
        self.current_assertion_id = None;
        self.forward_depth = 0;
        self.negative_facts.clear();
        self.pred_cache.borrow_mut().clear();
        self.pred_cache_enabled.set(false);
        // Note: integrity_constraints, compute_eval/compute_batch_eval, and
        // cancel are NOT cleared on reset — they're structural declarations /
        // configuration, not derived state. Clear explicitly if needed.
    }

    pub(super) fn fresh_fact_id(&mut self) -> u64 {
        let id = self.fact_counter;
        self.fact_counter += 1;
        id
    }

    pub(super) fn fresh_skolem(&mut self) -> String {
        let sk = format!("sk_{}", self.skolem_counter);
        self.skolem_counter += 1;
        sk
    }

    pub(super) fn note_entity(&mut self, name: &str) {
        if self.known_entities.insert(name.to_string()) {
            self.domain_members_dirty = true;
        }
    }

    /// Track an event Skolem constant for witness search and proof tracing,
    /// without registering it in `known_entities`.
    pub(super) fn note_event_entity(&mut self, name: &str) {
        if self.known_event_entities.insert(name.to_string()) {
            self.domain_members_dirty = true;
        }
    }

    pub(super) fn note_description(&mut self, name: &str) {
        if self.known_descriptions.insert(name.to_string()) {
            self.domain_members_dirty = true;
        }
    }

    /// Return all known domain members as (representation, LogicalTerm) pairs.
    /// Ensure the domain members cache is up-to-date. Call before any query.
    pub(super) fn ensure_domain_members_cached(&mut self) {
        if !self.domain_members_dirty {
            return;
        }
        let mut typed_members = Vec::new();
        for e in &self.known_entities {
            typed_members.push(GroundTerm::Constant(e.clone()));
        }
        for e in &self.known_event_entities {
            typed_members.push(GroundTerm::Constant(e.clone()));
        }
        for d in &self.known_descriptions {
            typed_members.push(GroundTerm::Description(d.clone()));
        }

        // Determinism: the source sets are HashSets whose iteration order
        // depends on the process hasher seed. Sort once at the cache boundary
        // so domain iteration (ForAll/Exists evaluation, witness search,
        // ForallVerified proof output) is byte-reproducible across runs.
        typed_members.sort();

        self.typed_domain_members_cache = typed_members;
        self.domain_members_dirty = false;
    }

    /// Return typed domain members. Call ensure_domain_members_cached() first.
    pub(super) fn all_typed_domain_members(&self) -> &[GroundTerm] {
        &self.typed_domain_members_cache
    }
}

// ═══════════════════════════════════════════════════════════════════
// EQUALITY / UNION-FIND for `du` predicate
// ═══════════════════════════════════════════════════════════════════

/// Find the canonical representative of a term (path-compressing).
pub(super) fn find_canonical(
    parent: &mut HashMap<GroundTerm, GroundTerm>,
    term: &GroundTerm,
) -> GroundTerm {
    let p = match parent.get(term) {
        Some(p) => p.clone(),
        None => return term.clone(),
    };
    if &p == term {
        return p;
    }
    let root = find_canonical(parent, &p);
    // Path compression
    parent.insert(term.clone(), root.clone());
    root
}

/// Non-compressing find (for `&` contexts where mutation is not available).
pub(super) fn find_canonical_readonly(
    parent: &HashMap<GroundTerm, GroundTerm>,
    term: &GroundTerm,
) -> GroundTerm {
    let mut current = term.clone();
    loop {
        match parent.get(&current) {
            Some(p) if p != &current => current = p.clone(),
            _ => return current,
        }
    }
}

/// Union two terms under the `du` equivalence relation.
pub(super) fn union_terms(inner: &mut KnowledgeBaseInner, a: &GroundTerm, b: &GroundTerm) {
    let root_a = find_canonical(&mut inner.equivalence_parent, a);
    let root_b = find_canonical(&mut inner.equivalence_parent, b);
    if root_a == root_b {
        return; // Already equivalent.
    }

    // Merge smaller class into larger (union by size).
    let size_a = inner
        .equivalence_classes
        .get(&root_a)
        .map_or(1, |c| c.len());
    let size_b = inner
        .equivalence_classes
        .get(&root_b)
        .map_or(1, |c| c.len());
    let (winner, loser) = if size_a >= size_b {
        (root_a, root_b)
    } else {
        (root_b, root_a)
    };

    // Point loser at winner.
    inner
        .equivalence_parent
        .insert(loser.clone(), winner.clone());

    // Merge class lists.
    let loser_class = inner
        .equivalence_classes
        .remove(&loser)
        .unwrap_or_else(|| vec![loser.clone()]);
    let winner_class = inner
        .equivalence_classes
        .entry(winner.clone())
        .or_insert_with(|| vec![winner.clone()]);
    winner_class.extend(loser_class);
}

/// Get all members of a term's equivalence class (readonly).
pub(super) fn get_equivalence_class_readonly(
    parent: &HashMap<GroundTerm, GroundTerm>,
    classes: &HashMap<GroundTerm, Vec<GroundTerm>>,
    term: &GroundTerm,
) -> Vec<GroundTerm> {
    let canon = find_canonical_readonly(parent, term);
    classes
        .get(&canon)
        .cloned()
        .unwrap_or_else(|| vec![term.clone()])
}

// ═══════════════════════════════════════════════════════════════════
// SORT HIERARCHY
// ═══════════════════════════════════════════════════════════════════

/// Check if `actual_sort` is compatible with `expected_sort`.
/// Compatible means: actual == expected, or actual is a subsort of expected
/// (transitively through the sort hierarchy).
pub(super) fn is_sort_compatible(
    hierarchy: &HashMap<String, HashSet<String>>,
    actual: &str,
    expected: &str,
) -> bool {
    if actual == expected {
        return true;
    }
    // BFS/DFS up the hierarchy from actual to see if we reach expected.
    let mut visited = HashSet::new();
    let mut stack = vec![actual.to_string()];
    while let Some(current) = stack.pop() {
        if !visited.insert(current.clone()) {
            continue;
        }
        if let Some(parents) = hierarchy.get(&current) {
            for parent in parents {
                if parent == expected {
                    return true;
                }
                stack.push(parent.clone());
            }
        }
    }
    false
}

/// The WIT-exported resource type.
/// wit-bindgen generates `&self` for methods, so RefCell provides mutability.
/// This is sound because WASI components are single-threaded.
///
/// Safety: KnowledgeBase is intentionally !Send and !Sync (RefCell is not thread-safe).
/// If you need thread-safe access, wrap in Arc<Mutex<>> at the call site (as nibli-server does).
#[cfg_attr(
    all(not(target_arch = "wasm32"), target_has_atomic = "ptr"),
    doc = "WARNING: This type uses RefCell for interior mutability. \
           It is NOT thread-safe. Use Arc<Mutex<KnowledgeBase>> for multi-threaded contexts."
)]
pub struct KnowledgeBase {
    pub(super) inner: RefCell<KnowledgeBaseInner>,
}

/// Lazy cartesian product iterator over GroundTerm slices.
/// Yields Vec<GroundTerm> combinations (cloned) with given arity.
pub(super) struct GroundTermCartesianProduct<'a> {
    terms: &'a [GroundTerm],
    dep_count: usize,
    indices: Vec<usize>,
    done: bool,
}

impl<'a> GroundTermCartesianProduct<'a> {
    pub(super) fn new(terms: &'a [GroundTerm], dep_count: usize) -> Self {
        let done = dep_count > 0 && terms.is_empty();
        Self {
            terms,
            dep_count,
            indices: vec![0; dep_count],
            done,
        }
    }
}

impl<'a> Iterator for GroundTermCartesianProduct<'a> {
    type Item = Vec<GroundTerm>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        if self.dep_count == 0 {
            self.done = true;
            return Some(vec![]);
        }
        let combo: Vec<GroundTerm> = self
            .indices
            .iter()
            .map(|&i| self.terms[i].clone())
            .collect();
        let mut carry = true;
        for i in (0..self.dep_count).rev() {
            if carry {
                self.indices[i] += 1;
                if self.indices[i] >= self.terms.len() {
                    self.indices[i] = 0;
                } else {
                    carry = false;
                }
            }
        }
        if carry {
            self.done = true;
        }
        Some(combo)
    }
}

// ─── Per-instance predicate result cache (on `KnowledgeBaseInner`) ────

/// Clear and enable the predicate result cache. Called at the start of
/// each top-level query. The cache persists across iterative deepening
/// iterations within a single query (tabling benefit) but is cleared
/// between separate user queries for correctness.
pub(super) fn clear_and_enable_pred_cache(inner: &KnowledgeBaseInner) {
    clear_typed_pred_cache(inner);
    inner.pred_cache_enabled.set(true);
}

/// Enable the predicate cache without clearing. Used within iterative
/// deepening to preserve cached results across depth iterations.
pub(super) fn enable_pred_cache(inner: &KnowledgeBaseInner) {
    inner.pred_cache_enabled.set(true);
}

/// Invalidate the predicate result cache. Call after any KB mutation
/// (assert, retract, reset) to prevent stale cached results.
pub(super) fn invalidate_pred_cache(inner: &KnowledgeBaseInner) {
    clear_typed_pred_cache(inner);
    inner.pred_cache_enabled.set(false);
}

pub(super) fn register_ground_material_conditional(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
) -> Result<bool, String> {
    // Walk through Skolemized Exists and tense wrappers to find the Or(Not(...), ...) pattern.
    // Returns whether a material-conditional rule was registered, so the caller can detect a
    // zero-ingest assertion (a bare disjunction registers nothing here and stores no facts).
    let Ok(node) = get_node(buffer, node_id) else {
        return Ok(false);
    };
    let registered = match node {
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            register_ground_material_conditional(buffer, *body, subs, inner)?
        }
        LogicNode::PastNode(n)
        | LogicNode::PresentNode(n)
        | LogicNode::FutureNode(n)
        | LogicNode::ObligatoryNode(n)
        | LogicNode::PermittedNode(n) => {
            register_ground_material_conditional(buffer, *n, subs, inner)?
        }
        LogicNode::AndNode((l, r)) => {
            let left = register_ground_material_conditional(buffer, *l, subs, inner)?;
            let right = register_ground_material_conditional(buffer, *r, subs, inner)?;
            left || right
        }
        LogicNode::OrNode((l, r)) => {
            // Check for Or(Not(P), Q) — material conditional P → Q
            // The Not here encodes implication (P→Q ≡ ¬P∨Q), not body-negation.
            // The dependency Q→P is positive, so negated_condition_indices is empty.
            if matches!(get_node(buffer, *l), Ok(LogicNode::NotNode(_))) {
                // Reuse the universal-rule compiler with zero entity universals: condition-side
                // event existentials become `ev__` pattern vars (matching any asserted event)
                // and conclusion-side existentials become skolem witnesses, so event-decomposed
                // operands reason via modus ponens. Plain predicates compile identically to the
                // old path, and dedup + negated-condition handling come for free.
                compile_forall_to_rule(buffer, node_id, subs, inner)?;
                true
            }
            // Also check Or(Q, Not(P)) — reversed order (commutativity). smuni never emits this
            // for ganai/go/jo (always Not-on-left), so it stays on the simpler ground path;
            // event-decomposed operands in this orientation are not reachable from the pipeline.
            else if let Ok(LogicNode::NotNode(neg_inner)) = get_node(buffer, *r) {
                let mut typed_conds = Vec::new();
                collect_ground_facts(buffer, *neg_inner, subs, None, &mut typed_conds);
                let mut typed_concls = Vec::new();
                collect_ground_facts(buffer, *l, subs, None, &mut typed_concls);
                let label = build_typed_rule_label(&typed_conds, &typed_concls);
                register_rule(
                    inner,
                    label,
                    vec![],
                    typed_conds,
                    typed_concls,
                    vec![],
                    false,
                )?;
                true
            } else {
                // A bare disjunction Or(P, Q) with no negation is not a material
                // conditional: it registers no rule and stores no fact (the caller's
                // zero-ingest guard rejects it rather than reporting a phantom assertion).
                false
            }
        }
        _ => false,
    };
    Ok(registered)
}

/// True if the formula contains a numeric-quantifier (`CountNode`) anywhere. Count
/// assertions legitimately store no ground leaf and register no rule on the normal
/// path (their witnesses are generated by `generate_count_extra_witnesses`), so the
/// zero-ingest guard must exempt them.
fn contains_count_node(buffer: &LogicBuffer, node_id: u32) -> bool {
    let Ok(node) = get_node(buffer, node_id) else {
        return false;
    };
    match node {
        LogicNode::CountNode(_) => true,
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            contains_count_node(buffer, *l) || contains_count_node(buffer, *r)
        }
        LogicNode::NotNode(n)
        | LogicNode::ExistsNode((_, n))
        | LogicNode::ForAllNode((_, n))
        | LogicNode::PastNode(n)
        | LogicNode::PresentNode(n)
        | LogicNode::FutureNode(n)
        | LogicNode::ObligatoryNode(n)
        | LogicNode::PermittedNode(n) => contains_count_node(buffer, *n),
        _ => false,
    }
}

/// True if the root, after stripping transparent wrappers, is a negated ground fact
/// (`na <selbri>`). These are accepted as no-ops today: under the closed-world
/// assumption `¬P` is already entailed whenever `P` is not derivable, so a bare
/// negative premise is harmless (it is how modus-tollens scenarios are exercised).
/// Storing them as explicit negative facts and flagging a contrary positive as a
/// contradiction is a separate, larger task (todo.md: zero-ingest / negated ground
/// fact). The zero-ingest guard must NOT reject them — doing so would both break
/// existing negative premises and foreclose that future contradiction-detection fix.
fn root_reduces_to_negation(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) -> bool {
    let Ok(node) = get_node(buffer, node_id) else {
        return false;
    };
    match node {
        LogicNode::NotNode(_) => true,
        LogicNode::PastNode(n)
        | LogicNode::PresentNode(n)
        | LogicNode::FutureNode(n)
        | LogicNode::ObligatoryNode(n)
        | LogicNode::PermittedNode(n) => root_reduces_to_negation(buffer, *n, subs),
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            root_reduces_to_negation(buffer, *body, subs)
        }
        _ => false,
    }
}

/// Descend through tense/deontic wrappers and Skolemized Exists to the NotNode,
/// returning the negation body and the accumulated tense context. Companion to
/// `root_reduces_to_negation` (which decides THAT a root is a negation; this
/// returns WHERE its body is). Tense tracking mirrors `collect_ground_facts`:
/// Past/Present/Future set the context, deontic wrappers are transparent.
fn find_negation_body(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
    tense: Option<&'static str>,
) -> Option<(u32, Option<&'static str>)> {
    let node = get_node(buffer, node_id).ok()?;
    match node {
        LogicNode::NotNode(body) => Some((*body, tense)),
        LogicNode::PastNode(n) => find_negation_body(buffer, *n, subs, Some("Past")),
        LogicNode::PresentNode(n) => find_negation_body(buffer, *n, subs, Some("Present")),
        LogicNode::FutureNode(n) => find_negation_body(buffer, *n, subs, Some("Future")),
        LogicNode::ObligatoryNode(n) | LogicNode::PermittedNode(n) => {
            find_negation_body(buffer, *n, subs, tense)
        }
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            find_negation_body(buffer, *body, subs, tense)
        }
        _ => None,
    }
}

/// Record a negated ground root (`na <selbri>`) as an explicit negative-fact
/// template group for contradiction detection.
///
/// THE EVENT TRAP: smuni event-decomposes every predication, so
/// `la .adam. na gerku` compiles to ¬∃e.(gerku(e) ∧ gerku_x1(e, adam) ∧
/// gerku_x2(e, zo'e)), and Skolemization gives the negative leaves an event
/// Skolem (e.g. sk_0) that can NEVER equal the fresh event Skolem a later
/// contrary positive receives (sk_1) — naive `StoredFact` equality would never
/// match. We therefore GENERALIZE event arguments: every constant that was
/// introduced as an event Skolem (an `_ev*` variable; the ground path has
/// already registered it via `note_event_entity`, so `known_event_entities` is
/// the authoritative set — the same set witness search and proof tracing use to
/// distinguish event entities) is replaced by a `PatternVar`, one per DISTINCT
/// event constant, preserving event coreference within the group.
/// `check_contradictions` then unifies the whole group against asserted
/// positives under a single consistent binding (`negative_group_holds`).
///
/// Queries are NOT affected: negative facts live in their own registry, never
/// in the positive fact store or predicate index (NAF/CWA unchanged — a
/// negative premise stays assertable, and `Not` is still computed by
/// failure-to-derive).
pub(super) fn record_negative_ground_fact(
    inner: &mut KnowledgeBaseInner,
    buffer: &LogicBuffer,
    root_id: u32,
    skolem_subs: &HashMap<String, GroundTerm>,
) {
    let Some((body_id, tense)) = find_negation_body(buffer, root_id, skolem_subs, None) else {
        return;
    };
    let mut leaves = Vec::new();
    collect_ground_facts(buffer, body_id, skolem_subs, tense, &mut leaves);
    if leaves.is_empty() {
        // Nothing representable under the negation (e.g. ¬¬P, ¬(P ∨ Q)) —
        // keep the closed-world no-op rather than recording an empty group
        // (an empty group would unify trivially and flag a false contradiction).
        return;
    }

    let mut event_var_map: HashMap<String, String> = HashMap::new();
    let templates: Vec<StoredFact> = leaves
        .iter()
        .map(|f| generalize_event_args(f, &inner.known_event_entities, &mut event_var_map))
        .collect();
    inner.negative_facts.insert(templates);
}

/// Replace event-Skolem constants in a fact with pattern variables (one per
/// distinct event constant), so a negative template matches a contrary positive
/// regardless of which fresh event Skolem that positive assertion received.
/// `PatternVar` never occurs in stored ground facts, so the generalized form
/// cannot collide with a genuine stored fact.
fn generalize_event_args(
    fact: &StoredFact,
    event_entities: &HashSet<String>,
    event_var_map: &mut HashMap<String, String>,
) -> StoredFact {
    let gf = fact.inner();
    let args: Vec<GroundTerm> = gf
        .args
        .iter()
        .map(|arg| match arg {
            GroundTerm::Constant(c) if event_entities.contains(c.as_str()) => {
                let next_idx = event_var_map.len();
                let pvar = event_var_map
                    .entry(c.clone())
                    .or_insert_with(|| format!("__neg_ev{next_idx}"))
                    .clone();
                GroundTerm::PatternVar(pvar)
            }
            other => other.clone(),
        })
        .collect();
    StoredFact::with_tense_from(GroundFact::new(gf.relation.clone(), args), fact)
}

/// Does a negative template group hold against the ASSERTED positive store?
/// True when a single consistent binding of the group's pattern variables (the
/// generalized event arguments) satisfies EVERY template — requiring the whole
/// group to share one event binding prevents false positives from unrelated
/// events that merely share a predicate. Same-tense matching only (the
/// `StoredFact` wrapper must agree, via `unify_facts`); only directly asserted
/// facts are consulted (derived facts are out of scope by design).
pub(super) fn negative_group_holds(
    templates: &[StoredFact],
    store: &dyn crate::fact_store::FactStore,
) -> bool {
    fn solve(
        templates: &[StoredFact],
        idx: usize,
        bindings: &HashMap<String, GroundTerm>,
        store: &dyn crate::fact_store::FactStore,
    ) -> bool {
        let Some(template) = templates.get(idx) else {
            return true; // Every template satisfied under this binding.
        };
        let bound = substitute_fact(template, bindings);
        let Some(candidates) = store.lookup_predicate(bound.relation()) else {
            return false;
        };
        for fact in candidates {
            if let Some(new_bindings) = unify_facts(&bound, fact) {
                let mut merged = bindings.clone();
                merged.extend(new_bindings);
                if solve(templates, idx + 1, &merged, store) {
                    return true;
                }
            }
        }
        false
    }
    solve(templates, 0, &HashMap::new(), store)
}

/// Process a logic buffer into the knowledge base without recording in the fact registry.
/// Used by both initial assertion and rebuild-on-retract replay.
pub(super) fn process_assertion(
    inner: &mut KnowledgeBaseInner,
    logic: &LogicBuffer,
) -> Result<(), String> {
    for &root_id in &logic.roots {
        if root_id as usize >= logic.nodes.len() {
            eprintln!(
                "[Warning] skipping invalid root index {} (buffer has {} nodes)",
                root_id,
                logic.nodes.len()
            );
            continue;
        }
        // Phase 1: Collect existential variables for Skolemization.
        let mut skolem_subs = HashMap::new();
        let mut enclosing_universals = Vec::new();
        collect_exists_for_skolem(
            logic,
            root_id,
            &mut skolem_subs,
            &mut enclosing_universals,
            &mut inner.skolem_counter,
        );

        // Log Skolem substitutions (suppressed during rebuild)
        if !inner.rebuilding && !skolem_subs.is_empty() {
            // Determinism: skolem_subs is a HashMap — sort by variable name so
            // the printed mapping order is byte-reproducible across runs.
            let mut entries: Vec<(&String, &GroundTerm)> = skolem_subs.iter().collect();
            entries.sort_by(|a, b| a.0.cmp(b.0));
            let mapping: Vec<String> = entries
                .iter()
                .map(|(v, gt)| {
                    if let Some(base) = skdep_base_name(gt) {
                        format!("{} ↦ {}(∀-dependent)", v, base)
                    } else {
                        format!("{} ↦ {}", v, gt.to_display_string())
                    }
                })
                .collect();
            println!(
                "[Skolem] {} variable(s) → {}",
                skolem_subs.len(),
                mapping.join(", ")
            );
        }

        // Phase 2: Dispatch based on formula structure
        let is_forall = matches!(get_node(logic, root_id), Ok(LogicNode::ForAllNode(_)));

        if is_forall {
            // ═══ NATIVE RULE PATH ═══
            for (var, gt) in &skolem_subs {
                if !is_skdep(gt) {
                    if let GroundTerm::Constant(sk) = gt {
                        if var.starts_with("_ev") {
                            inner.note_event_entity(sk);
                        } else {
                            inner.note_entity(sk);
                        }
                    }
                }
            }
            collect_and_note_constants(logic, root_id, inner);
            compile_forall_to_rule(logic, root_id, &skolem_subs, inner)?;
        } else {
            // ═══ GROUND FORMULA PATH ═══
            for (var, gt) in &skolem_subs {
                if !is_skdep(gt) {
                    if let GroundTerm::Constant(sk) = gt {
                        if var.starts_with("_ev") {
                            inner.note_event_entity(sk);
                        } else {
                            inner.note_entity(sk);
                        }
                    }
                }
            }
            collect_and_note_constants(logic, root_id, inner);

            // Flatten top-level conjunctions and assert each leaf as a typed fact.
            let mut typed_leaves = Vec::new();
            collect_ground_facts(logic, root_id, &skolem_subs, None, &mut typed_leaves);
            let nothing_collected = typed_leaves.is_empty();
            for fact in &typed_leaves {
                // Intercept `du` facts for equality equivalence indexing.
                if let StoredFact::Bare(gf) = fact {
                    if gf.relation == "du" && gf.args.len() == 2 {
                        union_terms(inner, &gf.args[0], &gf.args[1]);
                    }
                }
            }
            for fact in typed_leaves {
                assert_typed_fact(fact, inner);
            }

            // Register ground material conditionals for backward-chaining
            let registered =
                register_ground_material_conditional(logic, root_id, &skolem_subs, inner)?;

            // FAIL CLOSED: a ground root that stored no fact AND registered no rule has no
            // representable content — a bare disjunction (`.i ja`) or an exclusive-or
            // (`.i ju`, which smuni flattens to And(Or, Not(And)) that this path cannot
            // hold). Returning Ok with a fact id would misrepresent it as asserted when
            // querying it back yields False. Exemptions: numeric quantifiers (Count) store
            // their witnesses separately, and negated ground facts (`na <selbri>`) are
            // accepted — they store nothing in the POSITIVE store (NAF/CWA query semantics
            // unchanged) but are recorded in the negative-fact registry so a later
            // contrary positive is flagged by `check_contradictions`. Universals never
            // reach this branch — they take the rule path above.
            if nothing_collected && !registered {
                if root_reduces_to_negation(logic, root_id, &skolem_subs) {
                    record_negative_ground_fact(inner, logic, root_id, &skolem_subs);
                } else if !contains_count_node(logic, root_id) {
                    return Err(
                        "assertion has no representable content: a bare disjunction or \
                         exclusive-or ingests no facts and registers no rules. Rejecting to \
                         preserve soundness rather than reporting it as asserted (querying it \
                         back would return False)."
                            .to_string(),
                    );
                }
            }
        }

        // Phase 3: Generate extra witnesses for Count quantifiers (n > 1)
        generate_count_extra_witnesses(logic, root_id, &skolem_subs, inner);
    }
    Ok(())
}

/// Entailment-side ∃ candidate narrowing (the ∃-heavy query blowup fix).
///
/// Unlike `collect_candidates` (the find path), this narrows ONLY from
/// MANDATORY positive anchors — predicates not under any `Or` (an Or-branch
/// anchor is optional, so narrowing by it could miss witnesses), and never
/// compute or query-time-evaluated relations (`du`, `zmadu`, `mleca`,
/// `dunli`), whose extensions are not store-backed.
///
/// Completeness relative to the full domain + registry-cartesian scan it
/// replaces: any witness `w` satisfying the body satisfies every mandatory
/// anchor, so `w` is either in the anchor's predicate index (superset
/// extraction, equivalence-expanded) or derivable via a rule concluding the
/// anchor relation — whose conclusion position is ground (added directly),
/// a PatternVar (full member + registry-cartesian superset, same as the old
/// scan), or a dependent-Skolem template (instantiated for THAT base name
/// only — a name-mismatched SkolemFn can never unify, so other bases are
/// dead candidates by construction).
///
/// Returns `None` when no mandatory anchor exists — the caller falls back to
/// the full scan.
pub(super) fn collect_entailment_candidates(
    buffer: &LogicBuffer,
    body_id: u32,
    var_name: &str,
    subs: &HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
    tense: Option<&str>,
) -> Option<Vec<GroundTerm>> {
    let mut anchors = Vec::new();
    collect_mandatory_anchors(buffer, body_id, var_name, subs, tense, &mut anchors);
    if anchors.is_empty() {
        return None;
    }
    let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
    let mut best: Option<HashSet<GroundTerm>> = None;
    for anchor in &anchors {
        let mut candidates = HashSet::new();
        extract_from_index(anchor, inner, &mut candidates);
        extract_rule_candidates_for_entailment(anchor, inner, &members, &mut candidates);
        // Unspecified (zo'e) can appear as a stored argument but is never a
        // meaningful witness value.
        candidates.remove(&GroundTerm::Unspecified);
        match &best {
            None => best = Some(candidates),
            Some(prev) if candidates.len() < prev.len() => best = Some(candidates),
            _ => {}
        }
    }
    best.map(|set| {
        let mut candidates: Vec<GroundTerm> = set.into_iter().collect();
        candidates.sort();
        candidates
    })
}

/// Relations whose truth is not store-backed (query-time evaluation /
/// equivalence machinery) — never sound to narrow candidates from.
fn is_non_indexable_relation(rel: &str) -> bool {
    matches!(rel, "du" | "zmadu" | "mleca" | "dunli")
}

/// Like `collect_predicate_anchors`, but only MANDATORY anchors: descends
/// And/tense/deontic/quantifier bodies, but NOT Or branches (optional) and
/// NOT compute nodes or query-time-evaluated relations.
fn collect_mandatory_anchors(
    buffer: &LogicBuffer,
    node_id: u32,
    var_name: &str,
    subs: &HashMap<String, GroundTerm>,
    tense: Option<&str>,
    anchors: &mut Vec<PredicateAnchor>,
) {
    let Ok(node) = get_node(buffer, node_id) else {
        return;
    };
    match node {
        LogicNode::Predicate((rel, args)) => {
            if is_non_indexable_relation(rel) {
                return;
            }
            if let Some(pos) = find_var_position(args, var_name, subs) {
                anchors.push(PredicateAnchor {
                    relation: rel.clone(),
                    var_position: pos,
                    args: args.clone(),
                    tense: tense_to_static(tense),
                });
            }
        }
        LogicNode::AndNode((l, r)) => {
            collect_mandatory_anchors(buffer, *l, var_name, subs, tense, anchors);
            collect_mandatory_anchors(buffer, *r, var_name, subs, tense, anchors);
        }
        LogicNode::PastNode(inner_id) => {
            collect_mandatory_anchors(buffer, *inner_id, var_name, subs, Some("Past"), anchors);
        }
        LogicNode::PresentNode(inner_id) => {
            collect_mandatory_anchors(buffer, *inner_id, var_name, subs, Some("Present"), anchors);
        }
        LogicNode::FutureNode(inner_id) => {
            collect_mandatory_anchors(buffer, *inner_id, var_name, subs, Some("Future"), anchors);
        }
        LogicNode::ObligatoryNode(inner_id) | LogicNode::PermittedNode(inner_id) => {
            collect_mandatory_anchors(buffer, *inner_id, var_name, subs, tense, anchors);
        }
        // A nested quantifier's body conjuncts are still mandatory for OUR
        // variable (smuni generates unique variable names, so no shadowing).
        LogicNode::ExistsNode((_, body)) | LogicNode::ForAllNode((_, body)) => {
            collect_mandatory_anchors(buffer, *body, var_name, subs, tense, anchors);
        }
        // OrNode: optional branches can't narrow. NotNode: negated predicates
        // can't anchor. CountNode/ComputeNode/others: not store-backed anchors.
        _ => {}
    }
}

/// Rule-derivable candidates for an entailment anchor (see
/// `collect_entailment_candidates` for the completeness argument).
fn extract_rule_candidates_for_entailment(
    anchor: &PredicateAnchor,
    inner: &KnowledgeBaseInner,
    members: &[GroundTerm],
    candidates: &mut HashSet<GroundTerm>,
) {
    let rules = match inner.universal_rules.get(anchor.relation.as_str()) {
        Some(r) => r,
        None => return,
    };
    for rule in rules {
        for conclusion in &rule.typed_conclusions {
            if conclusion.relation() != anchor.relation {
                continue;
            }
            let conc_args = &conclusion.inner().args;
            if conc_args.len() != anchor.args.len() {
                continue;
            }
            match &conc_args[anchor.var_position] {
                GroundTerm::PatternVar(_) => {
                    // The rule's conditions can bind this position to any
                    // domain member, or (via chained rules) to another rule's
                    // dependent-Skolem witness — full superset, same as the
                    // old unconditional scan.
                    candidates.extend(members.iter().cloned());
                    for entry in &inner.skolem_fn_registry {
                        for combo in GroundTermCartesianProduct::new(members, entry.dep_count) {
                            candidates.insert(build_skolem_fn_term(&entry.base_name, &combo));
                        }
                    }
                }
                GroundTerm::SkolemFn(base, _) => {
                    // Anchored cartesian: only THIS base name can unify here.
                    let dep_count = inner
                        .skolem_fn_registry
                        .iter()
                        .find(|e| e.base_name == *base)
                        .map(|e| e.dep_count)
                        .unwrap_or(1);
                    for combo in GroundTermCartesianProduct::new(members, dep_count) {
                        candidates.insert(build_skolem_fn_term(base, &combo));
                    }
                }
                other => {
                    candidates.insert(other.clone());
                }
            }
        }
    }
}

/// An anchor: a positive predicate in the body that mentions the target variable.
struct PredicateAnchor {
    relation: String,
    var_position: usize,
    args: Vec<LogicalTerm>,
    tense: Option<&'static str>,
}

/// Find the position of `var_name` in predicate args.
/// Returns Some(pos) if var_name appears exactly once and all other variables are bound.
fn find_var_position(
    args: &[LogicalTerm],
    var_name: &str,
    subs: &HashMap<String, GroundTerm>,
) -> Option<usize> {
    let mut var_pos = None;
    for (i, arg) in args.iter().enumerate() {
        if let LogicalTerm::Variable(v) = arg {
            if v == var_name {
                if var_pos.is_some() {
                    return None; // Appears more than once — can't extract cleanly
                }
                var_pos = Some(i);
            } else if !subs.contains_key(v) {
                // Another unbound variable — this anchor alone isn't sufficient,
                // but we still collect it. The candidate extraction will be
                // broader (all values at this position) but still narrower than
                // full domain scan.
            }
        }
    }
    var_pos
}

fn tense_to_static(tense: Option<&str>) -> Option<&'static str> {
    match tense {
        Some("Past") => Some("Past"),
        Some("Present") => Some("Present"),
        Some("Future") => Some("Future"),
        _ => None,
    }
}

/// Resolve a LogicalTerm to a GroundTerm using current substitutions.
fn resolve_arg(arg: &LogicalTerm, subs: &HashMap<String, GroundTerm>) -> Option<GroundTerm> {
    match arg {
        LogicalTerm::Variable(v) => subs.get(v).cloned(),
        LogicalTerm::Constant(c) => Some(GroundTerm::Constant(c.clone())),
        LogicalTerm::Number(n) => Some(GroundTerm::from_f64(*n)),
        LogicalTerm::Description(d) => Some(GroundTerm::Description(d.clone())),
        LogicalTerm::Unspecified => Some(GroundTerm::Unspecified),
    }
}

/// Extract candidates from the typed fact index for a predicate anchor.
fn extract_from_index(
    anchor: &PredicateAnchor,
    inner: &KnowledgeBaseInner,
    candidates: &mut HashSet<GroundTerm>,
) {
    let facts = match inner.fact_store.lookup_predicate(anchor.relation.as_str()) {
        Some(f) => f,
        None => return,
    };

    for stored_fact in facts {
        // Check tense matches
        let tense_matches = match (anchor.tense, stored_fact) {
            (None, StoredFact::Bare(_)) => true,
            (Some("Past"), StoredFact::Past(_)) => true,
            (Some("Present"), StoredFact::Present(_)) => true,
            (Some("Future"), StoredFact::Future(_)) => true,
            _ => false,
        };
        if !tense_matches {
            continue;
        }

        let fact_args = &stored_fact.inner().args;
        if fact_args.len() != anchor.args.len() {
            continue;
        }

        // For the variable position, extract the value.
        // For other positions, we don't filter here — the full body
        // verification in find_witnesses handles correctness.
        // This gives us a superset of valid candidates, which is safe.
        let direct = fact_args[anchor.var_position].clone();
        candidates.insert(direct.clone());
        // Expand by equivalence class.
        if !inner.equivalence_parent.is_empty() {
            for equiv in get_equivalence_class_readonly(
                &inner.equivalence_parent,
                &inner.equivalence_classes,
                &direct,
            ) {
                candidates.insert(equiv);
            }
        }
    }
}
