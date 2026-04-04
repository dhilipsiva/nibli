use super::*;
use std::cell::Cell;

/// Bounds-checked node access. Returns a descriptive error instead of panicking
/// if node_id is out of range (e.g., from a malformed LogicBuffer).
pub(super) fn get_node(buffer: &LogicBuffer, node_id: u32) -> Result<&LogicNode, String> {
    buffer
        .nodes
        .get(node_id as usize)
        .ok_or_else(|| {
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
            args: f.args.iter().map(|a| substitute_term(a, bindings).into_owned()).collect(),
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
pub(super) fn build_typed_rule_label(conditions: &[StoredFact], conclusions: &[StoredFact]) -> String {
    let conds: Vec<String> = conditions.iter().map(|f| f.relation().to_string()).collect();
    let concls: Vec<String> = conclusions.iter().map(|f| f.relation().to_string()).collect();
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
#[derive(Clone)]
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
    /// Typed ground facts — the canonical fact store.
    pub(super) typed_facts: HashSet<StoredFact>,
    /// Typed predicate index: relation name → set of StoredFacts.
    pub(super) typed_predicate_facts: HashMap<String, HashSet<StoredFact>>,
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
            typed_facts: HashSet::new(),
            typed_predicate_facts: HashMap::new(),
            universal_rules: HashMap::new(),
            fact_counter: 0,
            fact_registry: HashMap::new(),
            rebuilding: false,
            typed_domain_members_cache: Vec::new(),
            domain_members_dirty: true,
            max_chain_depth: 10,
            pred_dep_graph: HashMap::new(),
        }
    }

    pub(super) fn reset(&mut self) {
        self.skolem_counter = 0;
        self.known_entities.clear();
        self.known_event_entities.clear();
        self.known_descriptions.clear();
        self.known_rules.clear();
        self.skolem_fn_registry.clear();
        self.typed_facts.clear();
        self.typed_predicate_facts.clear();
        self.universal_rules.clear();
        self.fact_counter = 0;
        self.fact_registry.clear();
        self.rebuilding = false;
        self.typed_domain_members_cache.clear();
        self.domain_members_dirty = true;
        self.pred_dep_graph.clear();
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

        self.typed_domain_members_cache = typed_members;
        self.domain_members_dirty = false;
    }

    /// Return typed domain members. Call ensure_domain_members_cached() first.
    pub(super) fn all_typed_domain_members(&self) -> &[GroundTerm] {
        &self.typed_domain_members_cache
    }
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

// ─── Thread-local predicate result cache ─────────────────────────────

thread_local! {
    /// Flag to enable/disable predicate caching (disabled during assertion replay).
    pub(super) static PRED_CACHE_ENABLED: Cell<bool> = const { Cell::new(false) };
}

/// Clear the predicate result cache. Call at the start of each query.
pub(super) fn clear_pred_cache() {
    clear_typed_pred_cache();
    PRED_CACHE_ENABLED.with(|e| e.set(true));
}

pub(super) fn register_ground_material_conditional(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
) -> Result<(), String> {
    // Walk through Skolemized Exists and tense wrappers to find the Or(Not(...), ...) pattern
    let Ok(node) = get_node(buffer, node_id) else { return Ok(()) };
    match node {
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            register_ground_material_conditional(buffer, *body, subs, inner)?;
        }
        LogicNode::PastNode(n)
        | LogicNode::PresentNode(n)
        | LogicNode::FutureNode(n)
        | LogicNode::ObligatoryNode(n)
        | LogicNode::PermittedNode(n) => {
            register_ground_material_conditional(buffer, *n, subs, inner)?;
        }
        LogicNode::AndNode((l, r)) => {
            register_ground_material_conditional(buffer, *l, subs, inner)?;
            register_ground_material_conditional(buffer, *r, subs, inner)?;
        }
        LogicNode::OrNode((l, r)) => {
            // Check for Or(Not(P), Q) — material conditional P → Q
            // The Not here encodes implication (P→Q ≡ ¬P∨Q), not body-negation.
            // The dependency Q→P is positive, so negated_condition_indices is empty.
            if let Ok(LogicNode::NotNode(neg_inner)) = get_node(buffer, *l) {
                let mut typed_conds = Vec::new();
                collect_ground_facts(buffer, *neg_inner, subs, None, &mut typed_conds);
                let mut typed_concls = Vec::new();
                collect_ground_facts(buffer, *r, subs, None, &mut typed_concls);
                let label = build_typed_rule_label(&typed_conds, &typed_concls);
                register_rule(inner, label, vec![], typed_conds, typed_concls, vec![])?;
            }
            // Also check Or(Q, Not(P)) — reversed order (commutativity)
            else if let Ok(LogicNode::NotNode(neg_inner)) = get_node(buffer, *r) {
                let mut typed_conds = Vec::new();
                collect_ground_facts(buffer, *neg_inner, subs, None, &mut typed_conds);
                let mut typed_concls = Vec::new();
                collect_ground_facts(buffer, *l, subs, None, &mut typed_concls);
                let label = build_typed_rule_label(&typed_conds, &typed_concls);
                register_rule(inner, label, vec![], typed_conds, typed_concls, vec![])?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// Process a logic buffer into the knowledge base without recording in the fact registry.
/// Used by both initial assertion and rebuild-on-retract replay.
pub(super) fn process_assertion(inner: &mut KnowledgeBaseInner, logic: &LogicBuffer) -> Result<(), String> {
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
            let mapping: Vec<String> = skolem_subs
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
            for fact in typed_leaves {
                assert_typed_fact(fact, inner);
            }

            // Register ground material conditionals for backward-chaining
            register_ground_material_conditional(logic, root_id, &skolem_subs, inner)?;
        }

        // Phase 3: Generate extra witnesses for Count quantifiers (n > 1)
        generate_count_extra_witnesses(logic, root_id, &skolem_subs, inner);
    }
    Ok(())
}

/// Collect candidate GroundTerm values for an existential variable by walking
/// the body structure and extracting from the predicate index + backward-chaining
/// rule conclusions.
///
/// Strategy:
/// - Walk the body to find all positive predicates mentioning `var_name`
/// - For AND bodies: extract from the first anchor predicate (smallest candidate set)
/// - For OR bodies: union candidates from both branches
/// - For tense/deontic wrappers: unwrap and recurse
/// - For NOT bodies: cannot narrow (need all entities NOT satisfying P) — returns None
/// - Includes backward-chain rule conclusions to cover derived facts
///
/// Returns `Some(candidates)` with deduplicated candidate values, or `None` if
/// no positive predicate anchor exists (pure negation — genuinely requires domain scan).
pub(super) fn collect_candidates(
    buffer: &LogicBuffer,
    body_id: u32,
    var_name: &str,
    subs: &HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
    tense: Option<&str>,
) -> Option<Vec<GroundTerm>> {
    let mut anchors = Vec::new();
    collect_predicate_anchors(buffer, body_id, var_name, subs, tense, &mut anchors);

    if anchors.is_empty() {
        return None; // No positive predicate mentions this variable — must brute-force
    }

    // Extract candidates from the best anchor (smallest result set).
    // Try each anchor's index + backward-chain rules, pick the smallest.
    let mut best: Option<HashSet<GroundTerm>> = None;
    for anchor in &anchors {
        let mut candidates = HashSet::new();

        // Direct index lookup
        extract_from_index(anchor, inner, &mut candidates);

        // Backward-chain rule conclusions: if rules derive this predicate,
        // include candidates that rules could produce.
        extract_from_rules(anchor, var_name, subs, inner, &mut candidates);

        match &best {
            None => best = Some(candidates),
            Some(prev) if candidates.len() < prev.len() => best = Some(candidates),
            _ => {}
        }
    }

    best.map(|set| set.into_iter().collect())
}

/// An anchor: a positive predicate in the body that mentions the target variable.
struct PredicateAnchor {
    relation: String,
    var_position: usize,
    args: Vec<LogicalTerm>,
    tense: Option<&'static str>,
}

/// Walk the body and collect all positive predicates where `var_name` appears.
fn collect_predicate_anchors(
    buffer: &LogicBuffer,
    node_id: u32,
    var_name: &str,
    subs: &HashMap<String, GroundTerm>,
    tense: Option<&str>,
    anchors: &mut Vec<PredicateAnchor>,
) {
    let Ok(node) = get_node(buffer, node_id) else { return };
    match node {
        LogicNode::Predicate((rel, args)) | LogicNode::ComputeNode((rel, args)) => {
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
            collect_predicate_anchors(buffer, *l, var_name, subs, tense, anchors);
            collect_predicate_anchors(buffer, *r, var_name, subs, tense, anchors);
        }
        LogicNode::OrNode((l, r)) => {
            collect_predicate_anchors(buffer, *l, var_name, subs, tense, anchors);
            collect_predicate_anchors(buffer, *r, var_name, subs, tense, anchors);
        }
        LogicNode::PastNode(inner_id) => {
            collect_predicate_anchors(buffer, *inner_id, var_name, subs, Some("Past"), anchors);
        }
        LogicNode::PresentNode(inner_id) => {
            collect_predicate_anchors(buffer, *inner_id, var_name, subs, Some("Present"), anchors);
        }
        LogicNode::FutureNode(inner_id) => {
            collect_predicate_anchors(buffer, *inner_id, var_name, subs, Some("Future"), anchors);
        }
        LogicNode::ObligatoryNode(inner_id) | LogicNode::PermittedNode(inner_id) => {
            collect_predicate_anchors(buffer, *inner_id, var_name, subs, tense, anchors);
        }
        LogicNode::ExistsNode((_, body)) | LogicNode::ForAllNode((_, body)) => {
            collect_predicate_anchors(buffer, *body, var_name, subs, tense, anchors);
        }
        // NotNode: don't descend — negated predicates can't anchor candidates
        // CountNode: complex, skip
        _ => {}
    }
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
    let facts = match inner.typed_predicate_facts.get(anchor.relation.as_str()) {
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
        candidates.insert(fact_args[anchor.var_position].clone());
    }
}

/// Extract candidates from backward-chaining rule conclusions.
/// If rules can derive `relation(... x ...)`, include values from
/// the rule's conclusion template matched against the fact store.
fn extract_from_rules(
    anchor: &PredicateAnchor,
    _var_name: &str,
    _subs: &HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
    candidates: &mut HashSet<GroundTerm>,
) {
    let rules = match inner.universal_rules.get(anchor.relation.as_str()) {
        Some(r) => r,
        None => return,
    };

    // For each rule whose conclusion matches this predicate, extract
    // candidate values by looking at what the rule's conditions could bind.
    // We do one level of backward chaining: check which domain members
    // satisfy the rule's condition predicates.
    for rule in rules {
        for conclusion in &rule.typed_conclusions {
            if conclusion.relation() != anchor.relation {
                continue;
            }
            let conc_args = &conclusion.inner().args;
            if conc_args.len() != anchor.args.len() {
                continue;
            }

            // The conclusion template has PatternVar entries for universally
            // quantified variables. We need to find which pattern var maps
            // to our target position.
            let conc_term = &conc_args[anchor.var_position];

            match conc_term {
                // If the conclusion position is a pattern variable, that
                // variable is bound by the rule's conditions. Look at what
                // entities satisfy the conditions.
                GroundTerm::PatternVar(_) => {
                    // Include all entities that could trigger this rule.
                    // This is a safe superset — the full body verification
                    // in find_witnesses prunes false positives.
                    for entity in &inner.known_entities {
                        candidates.insert(GroundTerm::Constant(entity.clone()));
                    }
                    for entity in &inner.known_event_entities {
                        candidates.insert(GroundTerm::Constant(entity.clone()));
                    }
                    for desc in &inner.known_descriptions {
                        candidates.insert(GroundTerm::Description(desc.clone()));
                    }
                }
                // If the conclusion position is a ground term, that's a
                // direct candidate.
                other => {
                    candidates.insert(other.clone());
                }
            }
        }
    }
}
