use super::*;
use std::cell::Cell;

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
) {
    // Walk through Skolemized Exists and tense wrappers to find the Or(Not(...), ...) pattern
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            register_ground_material_conditional(buffer, *body, subs, inner);
        }
        LogicNode::PastNode(n)
        | LogicNode::PresentNode(n)
        | LogicNode::FutureNode(n)
        | LogicNode::ObligatoryNode(n)
        | LogicNode::PermittedNode(n) => {
            register_ground_material_conditional(buffer, *n, subs, inner);
        }
        LogicNode::AndNode((l, r)) => {
            register_ground_material_conditional(buffer, *l, subs, inner);
            register_ground_material_conditional(buffer, *r, subs, inner);
        }
        LogicNode::OrNode((l, r)) => {
            // Check for Or(Not(P), Q) — material conditional P → Q
            if let LogicNode::NotNode(neg_inner) = &buffer.nodes[*l as usize] {
                let mut typed_conds = Vec::new();
                collect_ground_facts(buffer, *neg_inner, subs, None, &mut typed_conds);
                let mut typed_concls = Vec::new();
                collect_ground_facts(buffer, *r, subs, None, &mut typed_concls);
                let label = build_typed_rule_label(&typed_conds, &typed_concls);
                register_rule(inner, label, vec![], typed_conds, typed_concls);
            }
            // Also check Or(Q, Not(P)) — reversed order (commutativity)
            else if let LogicNode::NotNode(neg_inner) = &buffer.nodes[*r as usize] {
                let mut typed_conds = Vec::new();
                collect_ground_facts(buffer, *neg_inner, subs, None, &mut typed_conds);
                let mut typed_concls = Vec::new();
                collect_ground_facts(buffer, *l, subs, None, &mut typed_concls);
                let label = build_typed_rule_label(&typed_conds, &typed_concls);
                register_rule(inner, label, vec![], typed_conds, typed_concls);
            }
        }
        _ => {}
    }
}

/// Process a logic buffer into the knowledge base without recording in the fact registry.
/// Used by both initial assertion and rebuild-on-retract replay.
pub(super) fn process_assertion(inner: &mut KnowledgeBaseInner, logic: &LogicBuffer) -> Result<(), String> {
    for &root_id in &logic.roots {
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
        let is_forall = matches!(&logic.nodes[root_id as usize], LogicNode::ForAllNode(_));

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
            register_ground_material_conditional(logic, root_id, &skolem_subs, inner);
        }

        // Phase 3: Generate extra witnesses for Count quantifiers (n > 1)
        generate_count_extra_witnesses(logic, root_id, &skolem_subs, inner);
    }

    Ok(())
}
