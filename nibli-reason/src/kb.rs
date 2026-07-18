use super::*;
use std::cell::{Cell, RefCell};

// ═══════════════════════════════════════════════════════════════════
// PREDICATE SIGNATURE VALIDATION
// ═══════════════════════════════════════════════════════════════════

/// How a predicate's arity was determined.
#[derive(Clone, Debug)]
pub enum SignatureSource {
    /// Arity from the committed English corpus (known predicate).
    Dictionary,
    /// Arity inferred from the first assertion (not in the corpus).
    Inferred,
    /// An engine-synthesized `rel_xN` role predicate (from event
    /// decomposition — always arity 2 `(event, filler)`). Never user-authored,
    /// so it is NOT arity-validated: the "inferred from first use" label and
    /// the arity-mismatch warning would both be category-confused for it.
    Synthetic,
}

/// Whether a relation name is an engine-synthesized `rel_xN` role predicate
/// (event decomposition emits `goes_x1`, `goes_x2`, … — always arity 2). These
/// are never user-authored, so they are classified `Synthetic` and exempt from
/// arity validation. Matches the `_x<digits>` suffix (the same role-predicate
/// convention used in nibli-semantics, e.g. `helpers.rs`/`lib.rs`).
pub(super) fn is_synthetic_role_predicate(rel: &str) -> bool {
    match rel.rsplit_once("_x") {
        Some((base, suffix)) => {
            !base.is_empty() && !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit())
        }
        None => false,
    }
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

/// A disjunctive rule conclusion `∀x. P(x) → (Q(x) ∨ R(x))`, kept as the integrity
/// constraint `¬(P(x) ∧ ¬Q(x) ∧ ¬R(x))` rather than a derivation rule — a disjunctive
/// head is NOT a Horn clause, so deriving either disjunct alone would be unsound.
/// `check_contradictions` flags it when, for one consistent binding, every `conditions`
/// template (P) holds in the positive store AND every disjunct group is EXPLICITLY
/// denied (a stored `na <predicate>` covers it). The positive use ("is X a Q or an R?")
/// is served by a disjunctive QUERY, not by this constraint.
#[derive(Clone, Debug)]
pub(super) struct DisjunctiveConstraint {
    /// Human-readable label, e.g. "gerku → danlu ∨ xanlu".
    pub(super) label: String,
    /// Antecedent P templates (pattern vars), like a rule's `typed_conditions`.
    pub(super) conditions: Vec<StoredFact>,
    /// One template group per disjunct; each event-decomposes to ≥1 leaf template.
    pub(super) disjuncts: Vec<Vec<StoredFact>>,
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

/// Relation-name prefix of the opaque abstraction marker emitted by nibli-semantics for
/// `nu`/`du'u`/`ka`/`ni`/`si'o`. The marker is a content-hashed unary predicate
/// over the abstraction referent; in `And(marker, body)` the right sibling is the
/// abstraction BODY, which reasoning treats as OPAQUE — never collected as ground
/// facts, never checked — so asserting an abstraction (a belief, an obligation's
/// content) does not leak its inner predicates as free-standing truths. The marker
/// itself IS reasoned over: same content → same marker (abstractions unify),
/// different content → different marker (no spurious match). The body survives only
/// for rendering. See nibli-semantics `apply_predicate` (Abstraction arm).
pub(super) const ABSTRACTION_MARKER_PREFIX: &str = "__abs_";

/// True if `node_id` is the opaque abstraction marker predicate.
pub(super) fn is_abstraction_marker(buffer: &LogicBuffer, node_id: u32) -> bool {
    matches!(
        get_node(buffer, node_id),
        Ok(LogicNode::Predicate((rel, _))) if rel.starts_with(ABSTRACTION_MARKER_PREFIX)
    )
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
    /// Opaque description term (le-determiner).
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

/// A negated, event-decomposed restrictor (`poi na <predicate>`) compiled as a
/// negation-as-failure check over an existential group. The condition holds for a
/// bound universal `x` iff NO binding of `event_var` satisfies ALL `conditions` —
/// e.g. `Not(Exists(ev, zanru(ev) ∧ zanru_x1(ev, x__v0) ∧ zanru_x2(ev, zo'e)))`
/// ("x has not consented"). The inner conjuncts are flat templates sharing the
/// universal's pattern var (`x__v0`) and a group-local event pattern var
/// (`ev___ev0`) enumerated during firing. A flat negated ATOM (`na broda`) stays
/// in `negated_condition_indices`; only a negated EXISTENTIAL GROUP lands here.
#[derive(Clone)]
pub(super) struct NegatedExistsGroup {
    /// Inner conjunct templates, e.g. `[zanru(ev), zanru_x1(ev, x__v0), zanru_x2(ev, zo'e)]`.
    pub(super) conditions: Vec<StoredFact>,
    /// Group-local event pattern-var name (e.g. `"ev___ev0"`), enumerated during firing.
    pub(super) event_var: String,
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
    /// Negated event-decomposed restrictor groups (`poi na <predicate>`), each
    /// evaluated by NAF over an existential during firing. Empty for ordinary rules.
    pub(super) negated_exists_groups: Vec<NegatedExistsGroup>,
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
    /// Known description terms (from `le` determiner), tracked separately for InDomain.
    pub(super) known_descriptions: HashSet<String>,
    pub(super) known_rules: HashSet<u64>,
    pub(super) skolem_fn_registry: Vec<SkolemFnEntry>,
    /// Pluggable fact store (in-memory or persistent).
    pub(super) fact_store: Box<dyn crate::fact_store::FactStore>,
    /// Compiled universal rule templates indexed by conclusion predicate name.
    /// Each predicate name maps to the rules whose conclusion templates mention it.
    /// Arc-wrapped so the backward-chain read path can borrow rules without cloning.
    /// INVARIANT: every bucket is kept sorted by DESCENDING priority at mutation
    /// time (`register_rule`, `set_rule_priority` call `sort_rule_bucket`), so the
    /// hot read path (`matching_rules_typed`) borrows a pre-sorted slice — no
    /// per-node clone or re-sort.
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
    /// Cached domain members of the INDIVIDUAL sort only (entities + le-descriptions,
    /// excluding event Skolems). The direct ForAll evaluator quantifies an
    /// individual variable, so it ranges over this — an event Skolem is never a
    /// legitimate counterexample for an individual universal. Built alongside the
    /// full cache; same dirty flag.
    pub(super) typed_non_event_members_cache: Vec<GroundTerm>,
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
    /// Explicitly asserted NEGATIVE ground facts (`na <predicate>`), stored as
    /// template groups for contradiction detection (`check_contradictions`).
    /// Each group is the conjunction of leaves under one negation, with event
    /// Skolem arguments generalized to pattern variables (see
    /// `record_negative_ground_fact`). Negatives never enter the positive fact
    /// store or predicate index — queries keep NAF/CWA semantics unchanged.
    pub(super) negative_facts: HashSet<Vec<StoredFact>>,
    /// Disjunctive rule conclusions registered as integrity constraints (see
    /// `DisjunctiveConstraint`). DERIVED from assertions → cleared on reset/rebuild
    /// and re-derived on replay (mirrors `negative_facts`/rules, NOT the standalone
    /// programmatic `integrity_constraints`).
    pub(super) disjunctive_constraints: Vec<DisjunctiveConstraint>,
    /// Cooperative cancellation flag (None = never cancels). Set by a native
    /// caller (the nibli-server request watchdog) when a query's wall-clock
    /// budget elapses; checked at the central reasoning entry points, which
    /// abort via the `Result::Err` channel. Default `None` keeps nibli-host/nibli-pipeline/
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
    /// SOUND DEPTH-CUT TABLE (the deep-chain-cliff fix): goal → the MAXIMUM
    /// remaining budget (`max_chain_depth - depth`) at which the goal is
    /// KNOWN to return `ResourceExceeded(Depth)`. Budget monotonicity makes
    /// the entry reusable for any remaining budget ≤ the recorded one (less
    /// budget can never prove more, and a definitive False requires an
    /// exhaustive search a smaller budget cuts even earlier) — within a
    /// deepening pass AND across passes (a deeper pass queries a larger
    /// budget, misses, re-derives once, raises the entry). Entries are only
    /// written when the derivation subtree saw NO cycle cut
    /// (`cycle_cut_epoch` unchanged) — a cycle-contaminated Depth is
    /// path-dependent and tabling it would be a completeness regression.
    /// Same lifecycle as `pred_cache` (cleared by `clear_typed_pred_cache`,
    /// gated by `pred_cache_enabled`, empty in Clone/reset). This is what
    /// keeps iterative deepening from re-deriving every horizon-cut subgoal
    /// ~30×/hop (see GUARANTEES §Completeness).
    pub(super) depth_cut_table: RefCell<HashMap<StoredFact, usize>>,
    /// Monotone counter bumped at every cycle cut — the contamination
    /// detector for `depth_cut_table` inserts (snapshot before deriving a
    /// goal; unchanged ⇒ the subtree's Depth verdict is path-independent).
    pub(super) cycle_cut_epoch: Cell<u64>,
    /// Transient SHARED budget for du-equivalence variant derivations
    /// (`DU_VARIANT_BOUND`): the OUTERMOST fallback invocation owns it
    /// (None → Some(bound)), nested probe fallbacks drain the same budget —
    /// a variant's Cartesian product is the SAME class product as the
    /// original goal's, so nested re-enumeration is redundant work, and the
    /// shared budget caps the TOTAL probe count per top-level fallback.
    /// Always restored to None by the owner.
    pub(super) du_variant_budget: Cell<Option<usize>>,
    /// Diagnostic verbosity. When `false` (the default) the informational stdout
    /// `println!` diagnostics (`[Rule]`/`[Skolem]`/`[Constraint] Registered`) are
    /// suppressed — a silent library for the server/validate/tavla. nibli-pipeline (the
    /// nibli-host REPL) and the native `nibli` REPL opt in via `set_verbose(true)`.
    /// Like `cancel`/`compute_eval`, this is CONFIGURATION, not derived state —
    /// NOT cleared by `reset()`. The `eprintln!` warning/error sites ignore it.
    pub(super) verbose: bool,
    /// STRICT MODE (opt-in): arity mismatches and integrity-constraint
    /// violations REJECT the offending fact instead of warn-and-insert. Like
    /// `verbose`, configuration — NOT cleared by `reset()`, and inert during
    /// `rebuilding` (a retraction replay must faithfully restore facts that
    /// were accepted when asserted).
    pub(super) strict: bool,
    /// EXISTENTIAL-IMPORT MODE (default ON — the v0.1 xorlo behavior, kept
    /// byte-identical). When true, a DESCRIPTION universal (`animal(every dog).`)
    /// mints a presupposition witness (see `presupposition_witnesses`) so
    /// `∃x. dog(x)` holds. Set false for the clean-core `some` = plain ∃ profile
    /// (NIBLI_KR §14.4 item 3): no phantom entity is injected. Like `strict`,
    /// this is CONFIGURATION — NOT cleared by `reset()`.
    pub(super) existential_import: bool,
    /// Constants minted as existential-import PRESUPPOSITION witnesses at
    /// description-universal registration (`animal(every dog).` presupposes
    /// ≥1 dog — Lojban's xorlo rule, kept by design).
    /// They satisfy ∃/∀ like any entity, but are EXCLUDED from counting
    /// surfaces (`PA lo` tallies, `??` witness enumeration): a phantom entity
    /// a rule presupposed must not change "how many" (GUARANTEES §Aggregation).
    pub(super) presupposition_witnesses: HashSet<String>,
    /// Violations collected by `assert_typed_fact` while strict mode rejects
    /// facts; drained by `process_assertion` into its error return. Internal
    /// insertions (forward chaining, compute auto-assert) also reject loudly
    /// but have no error channel — their entries are cleared at the next
    /// assertion boundary.
    pub(super) strict_violations: Vec<String>,
    /// Transient (per `query_find`): set when witness enumeration drops a candidate
    /// because its leaf check hit the depth/cycle horizon (`ResourceExceeded` /
    /// `Unknown(CycleCut)` / …) rather than a genuine False. `query_find_inner`
    /// resets it before enumeration and checks it after, so `count_witnesses` /
    /// `aggregate` REFUSE to emit a definitive (under)count when the search was cut.
    /// Not configuration; not cleared by `reset()` (query_find owns its lifecycle).
    pub(super) find_horizon_hit: bool,
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
            typed_non_event_members_cache: self.typed_non_event_members_cache.clone(),
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
            disjunctive_constraints: self.disjunctive_constraints.clone(),
            cancel: self.cancel.clone(),
            compute_eval: self.compute_eval,
            compute_batch_eval: self.compute_batch_eval,
            pred_cache: RefCell::new(HashMap::new()),
            pred_cache_enabled: Cell::new(false),
            depth_cut_table: RefCell::new(HashMap::new()),
            cycle_cut_epoch: Cell::new(0),
            du_variant_budget: Cell::new(None),
            verbose: self.verbose,
            strict: self.strict,
            existential_import: self.existential_import,
            strict_violations: Vec::new(),
            presupposition_witnesses: self.presupposition_witnesses.clone(),
            find_horizon_hit: false,
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
            typed_non_event_members_cache: Vec::new(),
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
            disjunctive_constraints: Vec::new(),
            cancel: None,
            compute_eval: None,
            compute_batch_eval: None,
            pred_cache: RefCell::new(HashMap::new()),
            pred_cache_enabled: Cell::new(false),
            depth_cut_table: RefCell::new(HashMap::new()),
            cycle_cut_epoch: Cell::new(0),
            du_variant_budget: Cell::new(None),
            verbose: false,
            strict: false,
            // Existential import defaults ON — the v0.1 xorlo behavior kept
            // byte-identical; clean-core opts OUT via `set_existential_import(false)`.
            existential_import: true,
            strict_violations: Vec::new(),
            presupposition_witnesses: HashSet::new(),
            find_horizon_hit: false,
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
        self.typed_non_event_members_cache.clear();
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
        self.disjunctive_constraints.clear();
        self.presupposition_witnesses.clear();
        self.pred_cache.borrow_mut().clear();
        self.pred_cache_enabled.set(false);
        self.depth_cut_table.borrow_mut().clear();
        // Note: integrity_constraints, compute_eval/compute_batch_eval, cancel,
        // verbose, strict, and existential_import are NOT cleared on reset —
        // they're structural declarations / configuration, not derived state.
        // (The `presupposition_witnesses` SET above IS cleared — it's derived,
        // re-minted on replay — but the flag that gates minting survives.)
        // Clear explicitly if needed.
    }

    /// Whether informational stdout diagnostics should print: only when the
    /// caller opted into verbosity AND we are not mid-rebuild (replay re-emits
    /// already-seen state). The `eprintln!` warning/error sites are independent.
    #[inline]
    pub(super) fn diag_enabled(&self) -> bool {
        !self.rebuilding && self.verbose
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
        // The non-event (individual) cache: entities + le-descriptions, no event
        // Skolems. Built in the SAME pass — individual-sort members go into both.
        let mut non_event_members = Vec::new();
        for e in &self.known_entities {
            let t = GroundTerm::Constant(e.clone());
            typed_members.push(t.clone());
            non_event_members.push(t);
        }
        for e in &self.known_event_entities {
            // Event Skolems are a distinct sort — full cache only.
            typed_members.push(GroundTerm::Constant(e.clone()));
        }
        for d in &self.known_descriptions {
            let t = GroundTerm::Description(d.clone());
            typed_members.push(t.clone());
            non_event_members.push(t);
        }

        // Determinism: the source sets are HashSets whose iteration order
        // depends on the process hasher seed. Sort once at the cache boundary
        // so domain iteration (ForAll/Exists evaluation, witness search,
        // ForallVerified proof output) is byte-reproducible across runs.
        typed_members.sort();
        non_event_members.sort();

        self.typed_domain_members_cache = typed_members;
        self.typed_non_event_members_cache = non_event_members;
        self.domain_members_dirty = false;
    }

    /// Return typed domain members. Call ensure_domain_members_cached() first.
    pub(super) fn all_typed_domain_members(&self) -> &[GroundTerm] {
        &self.typed_domain_members_cache
    }

    /// Return the INDIVIDUAL-sort domain members (entities + le-descriptions,
    /// excluding event Skolems). Used by the direct ForAll evaluator — an event
    /// Skolem is never a legitimate counterexample for an individual universal.
    /// Call ensure_domain_members_cached() first.
    pub(super) fn all_non_event_domain_members(&self) -> &[GroundTerm] {
        &self.typed_non_event_members_cache
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
        // Transparent tense/deontic strip. SURFACE-UNREACHABLE: tense (pu/ca/ba) and
        // deontics (ei/e'e) are proposition-level, never wrapping a sentence connective —
        // `pu ganai P gi Q` does not parse — so nibli-semantics never produces a tensed/deontic
        // ground material conditional `Past(Or(Not(P), Q))`. Kept as dead-defensive
        // raw-FOL completeness (mirrors the assert-path strip in `collect_ground_facts`).
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
            // Also check Or(Q, Not(P)) — reversed order (commutativity). nibli-semantics's
            // ganai/go/jo always emit Not-on-left, but a `na` on the RIGHT operand of a
            // disjunction (`mi klama .i ja mi na citka`, `… gi'a na citka`) lands here.
            // KNOWN LIMITATION (completeness only, see TODO.md): this simpler path bakes
            // the assertion's own event-Skolem CONSTANTS into the condition templates, so
            // an event-decomposed condition never unifies with a later assertion's fresh
            // event Skolem — the registered conditional is inert (never fires modus
            // ponens). The forward arm above was upgraded to `compile_forall_to_rule`
            // (ev__ pattern vars) precisely to fix that orientation; mirroring it here is
            // tracked in TODO.md. Never unsound — a missing derivation is FALSE = "not
            // derivable", within stated semantics.
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
/// (`na <predicate>`). Under the closed-world assumption `¬P` is already entailed
/// whenever `P` is not derivable, so a negative premise stores nothing in the
/// positive store; it IS recorded in the negative-fact registry (via
/// `record_negative_ground_fact`) so a later contrary positive is flagged by
/// `check_contradictions`. The zero-ingest guard must NOT reject these — see
/// `all_conjuncts_reduce_to_negation` for the conjunction generalization.
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

/// True if every conjunct of a top-level And-spine reduces to a negation
/// (`na A .i je na B`, a GIhA chain of all-`na` tails). Generalizes
/// `root_reduces_to_negation`: a single negated root trivially satisfies it.
/// Such an assertion has representable content — each negated conjunct is
/// recorded in the negative-fact registry exactly like a standalone `na`
/// assertion — so the zero-ingest guard must not reject it. An abstraction
/// group (`And(__abs_<hash>, body)`) is NOT a negative-only conjunction: its
/// marker is a positive leaf.
fn all_conjuncts_reduce_to_negation(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) -> bool {
    let Ok(node) = get_node(buffer, node_id) else {
        return false;
    };
    match node {
        LogicNode::AndNode((l, r)) if !is_abstraction_marker(buffer, *l) => {
            all_conjuncts_reduce_to_negation(buffer, *l, subs)
                && all_conjuncts_reduce_to_negation(buffer, *r, subs)
        }
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            all_conjuncts_reduce_to_negation(buffer, *body, subs)
        }
        // Tense/deontic wrappers around a NotNode are handled by
        // `find_negation_body`'s own descent (a wrapper around a whole
        // And-spine does not occur: nibli-semantics wraps tense per predication).
        // The exemption holds only for negations the registry can FULLY
        // represent — an impure body (e.g. Not(Or(..))) must fall through to
        // the loud fail-closed rejection, not become a silent no-op.
        _ => match find_negation_body(buffer, node_id, subs, None) {
            Some((body, _)) => negation_body_purely_representable(buffer, body, subs),
            None => false,
        },
    }
}

/// True if a negation BODY is a pure positive conjunction — the only shape the
/// negative-fact registry can represent faithfully. `collect_ground_facts`
/// silently drops NotNode/OrNode/ForAll leaves, so recording a body that
/// contains one would register a STRENGTHENED claim: `¬(P ∧ ¬Q)` — e.g. the
/// `Not(And(..))` half of nibli-semantics's Xor lowering, or a `jenai` under a proposition
/// `na` — would degrade to the group [P], i.e. `¬P`, fabricating contradiction
/// reports on consistent KBs. Mirrors `collect_ground_facts`' transparent
/// arms; an abstraction group counts as representable (the marker predicate
/// stands for the whole opaque body by design).
fn negation_body_purely_representable(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) -> bool {
    let Ok(node) = get_node(buffer, node_id) else {
        return false;
    };
    match node {
        LogicNode::AndNode((l, r)) => {
            if is_abstraction_marker(buffer, *l) {
                true
            } else {
                negation_body_purely_representable(buffer, *l, subs)
                    && negation_body_purely_representable(buffer, *r, subs)
            }
        }
        LogicNode::ExistsNode((v, body)) => {
            subs.contains_key(v.as_str()) && negation_body_purely_representable(buffer, *body, subs)
        }
        LogicNode::PastNode(n)
        | LogicNode::PresentNode(n)
        | LogicNode::FutureNode(n)
        | LogicNode::ObligatoryNode(n)
        | LogicNode::PermittedNode(n) => negation_body_purely_representable(buffer, *n, subs),
        LogicNode::Predicate(_) => true,
        _ => false,
    }
}

/// Walk a top-level And-spine and record EVERY conjunct that reduces to a
/// negation in the negative-fact registry (`P .i je na Q`, a `na`-negated
/// GIhA tail, or a bare negated root). `collect_ground_facts` skips `NotNode`
/// leaves — a negation is not a positive ground fact — so without this walk a
/// negated conjunct inside a compound assertion would vanish with no trace,
/// while the SAME negation asserted alone is recorded (an asymmetry that
/// silently dropped the `na` half of `mi klama .i je mi na citka`). Mirrors
/// `collect_ground_facts`' structural arms; abstraction bodies stay opaque
/// (their inner negations are quoted content, not asserted claims). Called
/// only after the ground path's fail-closed guards pass, so a rejected
/// assertion records nothing.
fn record_negative_conjuncts(
    inner: &mut KnowledgeBaseInner,
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) {
    let Ok(node) = get_node(buffer, node_id) else {
        return;
    };
    match node {
        LogicNode::AndNode((l, r)) => {
            if !is_abstraction_marker(buffer, *l) {
                record_negative_conjuncts(inner, buffer, *l, subs);
                record_negative_conjuncts(inner, buffer, *r, subs);
            }
        }
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            record_negative_conjuncts(inner, buffer, *body, subs)
        }
        // Any non-And conjunct: record from THIS node (not its inner NotNode)
        // so `find_negation_body` accumulates a tense/deontic wrapper into the
        // stored template, exactly as a root-level negation would.
        _ => {
            if root_reduces_to_negation(buffer, node_id, subs) {
                record_negative_ground_fact(inner, buffer, node_id, subs);
            }
        }
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

/// Record a negated ground root (`na <predicate>`) as an explicit negative-fact
/// template group for contradiction detection.
///
/// THE EVENT TRAP: nibli-semantics event-decomposes every predication, so
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
    if !negation_body_purely_representable(buffer, body_id, skolem_subs) {
        // The body contains sub-formulas `collect_ground_facts` would DROP
        // (a nested Not/Or/ForAll, e.g. the Not(And(P, ¬Q)) half of an Xor
        // lowering, or `na … jenai …`). Recording the partial body would
        // register a STRENGTHENED negation (¬(P ∧ ¬Q) degraded to ¬P) and
        // fabricate contradiction reports on consistent KBs — keep the
        // closed-world no-op instead.
        return;
    }
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

/// Enumerate ALL consistent bindings of a template group's pattern variables against
/// the asserted positive store — the all-bindings analog of `negative_group_holds`.
/// Used by the disjunctive-conclusion constraint check, which must try each binding
/// where the antecedent P holds. (Same one-consistent-binding-per-template solve.)
pub(super) fn solve_group_bindings(
    templates: &[StoredFact],
    store: &dyn crate::fact_store::FactStore,
) -> Vec<HashMap<String, GroundTerm>> {
    fn solve(
        templates: &[StoredFact],
        idx: usize,
        bindings: &HashMap<String, GroundTerm>,
        store: &dyn crate::fact_store::FactStore,
        out: &mut Vec<HashMap<String, GroundTerm>>,
    ) {
        let Some(template) = templates.get(idx) else {
            out.push(bindings.clone());
            return;
        };
        let bound = substitute_fact(template, bindings);
        let Some(candidates) = store.lookup_predicate(bound.relation()) else {
            return;
        };
        for fact in candidates {
            if let Some(new_bindings) = unify_facts(&bound, fact) {
                let mut merged = bindings.clone();
                merged.extend(new_bindings);
                solve(templates, idx + 1, &merged, store, out);
            }
        }
    }
    let mut out = Vec::new();
    solve(templates, 0, &HashMap::new(), store, &mut out);
    out
}

/// True if a stored `na <predicate>` group (its `__neg_ev` pattern vars bindable) unifies
/// ENTIRELY against `facts` under one consistent binding — i.e. the (already
/// P-substituted, ground) disjunct group is explicitly denied. Mirrors
/// `negative_group_holds` but matches against a fact list rather than the store.
fn neg_group_covers(templates: &[StoredFact], facts: &[StoredFact]) -> bool {
    fn solve(
        templates: &[StoredFact],
        idx: usize,
        bindings: &HashMap<String, GroundTerm>,
        facts: &[StoredFact],
    ) -> bool {
        let Some(template) = templates.get(idx) else {
            return true;
        };
        let bound = substitute_fact(template, bindings);
        for fact in facts {
            if bound.relation() != fact.relation() {
                continue;
            }
            if let Some(new_bindings) = unify_facts(&bound, fact) {
                let mut merged = bindings.clone();
                merged.extend(new_bindings);
                if solve(templates, idx + 1, &merged, facts) {
                    return true;
                }
            }
        }
        false
    }
    solve(templates, 0, &HashMap::new(), facts)
}

/// True if `disjunct` (a P-substituted, ground disjunct template group) is explicitly
/// denied by some stored `na <predicate>` group. The disjunct's event is an existential
/// witness (SkolemFn) and the `na` group's event is a `__neg_ev` pattern var, so they
/// unify freely; only the entity arguments (and tense, via `unify_facts`) must agree.
pub(super) fn disjunct_explicitly_denied(
    disjunct: &[StoredFact],
    negative_facts: &HashSet<Vec<StoredFact>>,
) -> bool {
    negative_facts
        .iter()
        .any(|neg_group| neg_group_covers(neg_group, disjunct))
}

/// Process a logic buffer into the knowledge base without recording in the fact registry.
/// Used by both initial assertion and rebuild-on-retract replay.
/// True if `node_id` is a `ForAllNode`, possibly under leading tense/deontic
/// wrappers (`pu ro lo gerku cu danlu` → `Past(ForAll(...))`). Such a
/// whole-rule-tensed/deontic universal is routed to the RULE path so
/// `compile_forall_to_rule` rejects it on its spine with the clear whole-rule
/// message — instead of falling to the ground path, where it collects no fact
/// and is rejected with the misleading "bare disjunction" zero-ingest message.
/// A bare `ForAll` returns true immediately; `Past(Predicate)` / `Past(Or(..))`
/// etc. return false (correctly staying on the ground path).
fn node_is_forall_through_tense(buffer: &LogicBuffer, node_id: u32) -> bool {
    let mut current = node_id;
    loop {
        match get_node(buffer, current) {
            Ok(LogicNode::ForAllNode(_)) => return true,
            Ok(LogicNode::PastNode(n))
            | Ok(LogicNode::PresentNode(n))
            | Ok(LogicNode::FutureNode(n))
            | Ok(LogicNode::ObligatoryNode(n))
            | Ok(LogicNode::PermittedNode(n)) => current = *n,
            _ => return false,
        }
    }
}

/// If `node_id` is a chain of leading ground-skolemized `Exists` nodes wrapping a
/// `ForAll` (`da citka ro lo gerku` → `Exists(da, ForAll(x, …))`), return the
/// inner `ForAll` node id. Phase-1 skolemization (`collect_exists_for_skolem`)
/// maps each leading ∃ — which has no enclosing universals at the root — to a
/// fresh ground constant in `subs`, so routing the inner ∀ to
/// `compile_forall_to_rule` (which substitutes those ground skolems into the rule
/// templates) is sound: `∃y.∀x.P(x,y)` is equisatisfiable with `∀x.P(x,sk₀)` for
/// a fresh constant sk₀. Returns `None` unless at least one ground-skolemized ∃
/// wraps a `ForAll` (so a pure ∃∃ ground assertion stays on the ground path).
/// Does NOT strip tense/deontic — a whole-rule-tensed ∃∀ is handled separately.
fn leading_skolemized_exists_over_forall(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) -> Option<u32> {
    let mut current = node_id;
    let mut peeled = false;
    loop {
        match get_node(buffer, current) {
            Ok(LogicNode::ExistsNode((v, body))) => match subs.get(v.as_str()) {
                Some(gt) if !is_skdep(gt) => {
                    peeled = true;
                    current = *body;
                }
                _ => return None,
            },
            Ok(LogicNode::ForAllNode(_)) if peeled => return Some(current),
            _ => return None,
        }
    }
}

/// True if a tense (`pu`/`ca`/`ba`) or deontic (`ei`/`e'e`) wrapper sits over a
/// leading-∃-over-∀ rule (`pu da citka ro lo gerku` → `Past(Exists(da, ForAll))`).
/// Such a whole-rule tense cannot be soundly carried by a timeless
/// backward-chaining rule (mirrors `compile_forall_to_rule`'s spine rejection),
/// so the caller rejects it with the clear whole-rule-tense message instead of
/// letting the ground path misreport it as a "bare disjunction".
fn tense_wraps_skolemized_exists_over_forall(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) -> bool {
    let mut current = node_id;
    let mut saw_tense = false;
    loop {
        match get_node(buffer, current) {
            Ok(LogicNode::PastNode(n))
            | Ok(LogicNode::PresentNode(n))
            | Ok(LogicNode::FutureNode(n))
            | Ok(LogicNode::ObligatoryNode(n))
            | Ok(LogicNode::PermittedNode(n)) => {
                saw_tense = true;
                current = *n;
            }
            _ => {
                return saw_tense
                    && leading_skolemized_exists_over_forall(buffer, current, subs).is_some();
            }
        }
    }
}

pub(super) fn process_assertion(
    inner: &mut KnowledgeBaseInner,
    logic: &LogicBuffer,
) -> Result<(), String> {
    // Strict-mode violations from PREVIOUS work (e.g. a mid-query compute
    // auto-assert, which has no error channel) must not bleed into THIS
    // assertion's verdict.
    inner.strict_violations.clear();
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

        // Log Skolem substitutions (suppressed during rebuild + when not verbose)
        if inner.diag_enabled() && !skolem_subs.is_empty() {
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

        // Phase 2: Note skolem witness + ground constants — identical for every
        // dispatch path below, so done once up front.
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

        // Dispatch on root shape. A universal (optionally under whole-rule
        // tense/deontic, which `compile_forall_to_rule` rejects on its spine with
        // the clear message) takes the rule path. A leading bare variable
        // outscoping a universal (`da citka ro lo gerku` → ∃da.∀x) takes the ∃∀
        // rule path. Everything else is a ground formula.
        let is_forall = node_is_forall_through_tense(logic, root_id);

        if is_forall {
            // ═══ NATIVE RULE PATH ═══
            compile_forall_to_rule(logic, root_id, &skolem_subs, inner)?;
        } else if let Some(inner_forall_id) =
            leading_skolemized_exists_over_forall(logic, root_id, &skolem_subs)
        {
            // ═══ ∃∀ RULE PATH ═══ A leading bare variable outscopes a universal.
            // Phase-1 already skolemized each leading ∃ to a fresh ground constant
            // (no enclosing universals at the root), so route the inner ForAll to
            // rule compilation; `compile_forall_to_rule` substitutes the ground
            // skolem into the rule templates. Sound: ∃y.∀x.P(x,y) ≡ ∀x.P(x,sk₀).
            compile_forall_to_rule(logic, inner_forall_id, &skolem_subs, inner)?;
        } else if tense_wraps_skolemized_exists_over_forall(logic, root_id, &skolem_subs) {
            // A tense/deontic wrapping a whole ∃∀ rule (`pu da citka ro lo gerku`)
            // cannot carry whole-rule tense soundly — reject with the same clear
            // message `compile_forall_to_rule` uses for `pu ro lo gerku cu danlu`,
            // rather than the ground path's misleading "bare disjunction" error.
            return Err("cannot compile a tense (pu/ca/ba) or deontic (ei/e'e) \
                 wrapping a whole universal/conditional rule: a timeless \
                 backward-chaining rule cannot carry whole-rule tense or \
                 modality without over-claiming on untensed facts. Rejecting \
                 the assertion to preserve soundness; restate the \
                 temporal/deontic scope on the relevant predicate instead."
                .to_string());
        } else {
            // ═══ GROUND FORMULA PATH ═══

            // Flatten top-level conjunctions and assert each leaf as a typed fact.
            let mut typed_leaves = Vec::new();
            collect_ground_facts(logic, root_id, &skolem_subs, None, &mut typed_leaves);

            // FAIL CLOSED: a numeric comparison (zmadu/mleca/dunli over number
            // literals) is computed ground truth — the engine evaluates it at query
            // time and the computed value always wins (try_numeric_comparison runs
            // before the store), so an asserted one could only ever be a shadowed,
            // unreachable fact. Reject it rather than store a lie. (A non-numeric
            // comparison like `zmadu(alis, bob)` is a relational fact and stores.)
            if let Some(rel) = asserted_numeric_comparison(&typed_leaves) {
                return Err(format!(
                    "`{rel}` over numeric literals is a computed comparison, not an \
                     assertable fact: the engine evaluates it at query time and the \
                     computed value always wins, so an asserted fact could never be \
                     consulted. (A non-numeric comparison like `la .alis. cu zmadu \
                     la .bob.` is a relational fact and asserts normally.)"
                ));
            }

            let nothing_collected = typed_leaves.is_empty();
            for fact in &typed_leaves {
                // Intercept `du` facts for equality equivalence indexing.
                if let StoredFact::Bare(gf) = fact {
                    if gf.relation == nibli_types::relations::IDENTITY && gf.args.len() == 2 {
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
            // (`.i ju`, which nibli-semantics flattens to And(Or, Not(And)) that this path cannot
            // hold). Returning Ok with a fact id would misrepresent it as asserted when
            // querying it back yields False. Exemptions: numeric quantifiers (Count) store
            // their witnesses separately, and negated ground facts (`na <predicate>`,
            // including a conjunction whose EVERY conjunct is negated) are accepted —
            // they store nothing in the POSITIVE store (NAF/CWA query semantics
            // unchanged) but are recorded in the negative-fact registry so a later
            // contrary positive is flagged by `check_contradictions`. Universals never
            // reach this branch — they take the rule path above.
            if nothing_collected
                && !registered
                && !all_conjuncts_reduce_to_negation(logic, root_id, &skolem_subs)
                && !contains_count_node(logic, root_id)
            {
                return Err(
                    "assertion has no representable content: a bare disjunction, an \
                     exclusive-or, or a negation whose body is not a plain conjunction \
                     of positive facts ingests no facts and registers no rules. \
                     Rejecting to preserve soundness rather than reporting it as \
                     asserted (querying it back would return False)."
                        .to_string(),
                );
            }

            // Record every conjunct that reduces to a negation (a bare negated
            // root, `P .i je na Q`, a `na`-negated GIhA tail) in the
            // negative-fact registry. Runs AFTER the fail-closed guards so a
            // rejected assertion records nothing. Previously only a root-level
            // negation was recorded — a negated conjunct inside a compound
            // assertion was silently dropped.
            record_negative_conjuncts(inner, logic, root_id, &skolem_subs);
        }

        // Phase 3: Generate extra witnesses for Count quantifiers (n > 1)
        generate_count_extra_witnesses(logic, root_id, &skolem_subs, inner);
    }
    // STRICT MODE: any fact this assertion tried to insert that was rejected
    // (arity mismatch / integrity-constraint violation) fails the whole
    // assertion. The caller (`assert_fact_inner`) then rolls back ATOMICALLY —
    // its registry rebuild discards every partial mutation of the failed
    // assertion, and the replay runs with `rebuilding = true`, where strict is
    // inert (previously-accepted facts restore faithfully).
    if !inner.strict_violations.is_empty() {
        let joined = inner.strict_violations.drain(..).collect::<Vec<_>>();
        return Err(format!("strict mode rejected: {}", joined.join("; ")));
    }
    Ok(())
}

/// Detect an asserted NUMERIC comparison (zmadu/mleca/dunli over number
/// LITERALS) among the collected ground leaves — both the flat 2-arg form
/// `rel(num, num)` and the event-decomposed form `rel_x1(ev, num) ∧
/// rel_x2(ev, num)` (the todo requires covering both). Returns the relation
/// name if found. A non-numeric comparison (`zmadu(alis, bob)`, the relational
/// "taller-than" reading) returns None and asserts/stores normally, since it is
/// answered from the store, not the built-in evaluator.
fn asserted_numeric_comparison(leaves: &[StoredFact]) -> Option<&'static str> {
    const CMP: [&str; 3] = ["greater", "less", "num_equal"];
    let is_num = |t: &GroundTerm| matches!(t, GroundTerm::Number(_));
    // Flat: rel(num, num, ...) — the evaluator (`try_numeric_comparison`) reads
    // only the first two operands, so a flat fact at full arity (`zmadu(5,3,_,_)`)
    // counts whenever those two are numeric.
    for f in leaves {
        let gf = f.inner();
        if gf.args.len() >= 2 && is_num(&gf.args[0]) && is_num(&gf.args[1]) {
            if let Some(rel) = CMP.iter().copied().find(|&c| c == gf.relation.as_str()) {
                return Some(rel);
            }
        }
    }
    // Decomposed: rel_x1(ev, num) ∧ rel_x2(ev, num) sharing the event arg.
    for &base in &CMP {
        let (x1, x2) = (format!("{base}_x1"), format!("{base}_x2"));
        for a in leaves {
            let ga = a.inner();
            if ga.relation == x1
                && ga.args.len() == 2
                && is_num(&ga.args[1])
                && leaves.iter().any(|b| {
                    let gb = b.inner();
                    gb.relation == x2
                        && gb.args.len() == 2
                        && gb.args[0] == ga.args[0]
                        && is_num(&gb.args[1])
                })
            {
                return Some(base);
            }
        }
    }
    None
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
    nibli_types::relations::is_identity(rel) || nibli_types::relations::is_numeric_comparison(rel)
}

/// Candidate narrowing for a negated-exists group's event variable — the
/// firing-time analog of `collect_entailment_candidates`, driven by the group's
/// `StoredFact` condition TEMPLATES rather than a buffer sub-tree. Returns the
/// smallest superset of events that could satisfy the inner existential: index
/// hits (events at the var position of an asserted fact of the relation,
/// equivalence-expanded) ∪ rule-derivable witnesses. Soundness: a witness `ev`
/// satisfying ALL conditions satisfies the anchor condition too, so it is in the
/// anchor's candidate set — narrowing never drops a real witness (so it never
/// produces a spurious "no witness" → spurious obligation). Without it the group
/// enumerates the full `members^k` pool per firing. `None` when no condition
/// cleanly anchors the event var (caller falls back to the full pool).
pub(super) fn collect_group_event_candidates(
    conditions: &[StoredFact],
    event_var: &str,
    inner: &KnowledgeBaseInner,
) -> Option<Vec<GroundTerm>> {
    let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
    let mut best: Option<HashSet<GroundTerm>> = None;
    for cond in conditions {
        let gf = cond.inner();
        if is_non_indexable_relation(&gf.relation) {
            continue;
        }
        // The event var must appear exactly once (as a PatternVar) in this cond.
        let positions: Vec<usize> = gf
            .args
            .iter()
            .enumerate()
            .filter(|(_, a)| matches!(a, GroundTerm::PatternVar(s) if s == event_var))
            .map(|(i, _)| i)
            .collect();
        if positions.len() != 1 {
            continue;
        }
        let anchor = PredicateAnchor {
            relation: gf.relation.clone(),
            var_position: positions[0],
            // Only the arity (`args.len()`) is consulted by `extract_from_index`;
            // the values are ignored (the full per-binding check filters later).
            args: vec![LogicalTerm::Unspecified; gf.args.len()],
            tense: match cond {
                StoredFact::Past(_) => Some("Past"),
                StoredFact::Present(_) => Some("Present"),
                StoredFact::Future(_) => Some("Future"),
                _ => None,
            },
        };
        let mut candidates = HashSet::new();
        extract_from_index(&anchor, inner, &mut candidates);
        extract_rule_candidates_for_entailment(&anchor, inner, &members, &mut candidates);
        candidates.remove(&GroundTerm::Unspecified);
        match &best {
            None => best = Some(candidates),
            Some(prev) if candidates.len() < prev.len() => best = Some(candidates),
            _ => {}
        }
    }
    best.map(|set| {
        let mut v: Vec<GroundTerm> = set.into_iter().collect();
        v.sort();
        v
    })
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
        // variable (nibli-semantics generates unique variable names, so no shadowing).
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
        Some("Obligatory") => Some("Obligatory"),
        Some("Permitted") => Some("Permitted"),
        _ => None,
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
            (Some("Obligatory"), StoredFact::Obligatory(_)) => true,
            (Some("Permitted"), StoredFact::Permitted(_)) => true,
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
