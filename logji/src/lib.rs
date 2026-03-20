//! Logji (logic/reasoning) engine: FOL assertion and query via demand-driven backward-chaining.
//!
//! This is the core inference component of Nibli. It maintains a stateful knowledge
//! base with a fact index and backward-chaining rule engine:
//!
//! - **Fact assertion** — Ground predicates stored in `asserted_sexps` HashSet.
//!   Universal quantifiers compile to `UniversalRuleRecord` templates for backward-chaining.
//! - **Entailment queries** — Recursive formula checking via [`check_formula_holds`] with
//!   demand-driven backward-chaining through universal rules.
//! - **Proof traces** — [`check_formula_holds_traced`] builds a proof tree recording which
//!   rule/axiom was applied at each step (15 proof rule variants). Multi-hop derivation
//!   provenance traces derived facts through universal rule chains via backward-chaining.
//! - **Witness extraction** — [`find_witnesses`] returns all satisfying entity bindings for
//!   existential variables.
//! - **Compute dispatch** — `ComputeNode` predicates are forwarded to the host-provided
//!   `compute-backend` WIT interface for external evaluation.
//!
//! The knowledge base uses `RefCell` (not `Mutex`) — single-threaded WASI, no global state.

#[allow(warnings)]
pub mod bindings;

use crate::bindings::exports::lojban::nibli::logji::{Guest, GuestKnowledgeBase};
use crate::bindings::lojban::nibli::error_types::NibliError;
use crate::bindings::lojban::nibli::logic_types::{
    FactSummary, LogicBuffer, LogicNode, LogicalTerm, ProofRule, ProofStep, ProofTrace,
    WitnessBinding,
};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

// ─── S-Expression String Interner ─────────────────────────────────

/// Lightweight string interner for s-expression deduplication.
/// Stores unique strings once and returns u32 keys for O(1) equality checks.
/// Resolves keys back to &str in O(1) via index lookup.
struct SexpInterner {
    strings: Vec<String>,
    lookup: HashMap<String, u32>,
}

impl SexpInterner {
    fn new() -> Self {
        Self {
            strings: Vec::new(),
            lookup: HashMap::new(),
        }
    }

    /// Intern a string, returning its unique key. Deduplicates on insert.
    fn intern(&mut self, s: &str) -> u32 {
        if let Some(&key) = self.lookup.get(s) {
            return key;
        }
        let key = self.strings.len() as u32;
        self.lookup.insert(s.to_string(), key);
        self.strings.push(s.to_string());
        key
    }

    /// Intern an owned string, avoiding a copy if it's new.
    fn intern_owned(&mut self, s: String) -> u32 {
        if let Some(&key) = self.lookup.get(&s) {
            return key;
        }
        let key = self.strings.len() as u32;
        self.strings.push(s.clone());
        self.lookup.insert(s, key);
        key
    }

    /// Resolve a key back to its string. Panics on invalid key.
    fn resolve(&self, key: u32) -> &str {
        &self.strings[key as usize]
    }

    /// Check if a string is already interned, returning its key if so.
    fn get(&self, s: &str) -> Option<u32> {
        self.lookup.get(s).copied()
    }

    fn clear(&mut self) {
        self.strings.clear();
        self.lookup.clear();
    }
}

// ─── Columnar Fact Store ─────────────────────────────────────────

/// Sorted u32 vector for columnar fact storage.
///
/// Stores interned s-expression keys in sorted order for:
/// - O(log n) membership test via binary search (cache-friendly)
/// - 4 bytes per entry (vs ~32 bytes for HashSet<u32>)
/// - Future SIMD batch membership via aligned u32 scans
/// - Merge-join subset check for ∀ verification
///
/// Insert is O(n) due to shift, but assertions are infrequent
/// compared to queries in a demand-driven backward-chaining engine.
#[derive(Clone)]
struct SortedU32Vec {
    data: Vec<u32>,
}

impl SortedU32Vec {
    fn new() -> Self {
        Self { data: Vec::new() }
    }

    /// Insert a key, maintaining sorted order. Returns true if newly added.
    fn insert(&mut self, val: u32) -> bool {
        match self.data.binary_search(&val) {
            Ok(_) => false, // already present
            Err(pos) => {
                self.data.insert(pos, val);
                true
            }
        }
    }

    /// O(log n) membership test via binary search.
    fn contains(&self, val: &u32) -> bool {
        self.data.binary_search(val).is_ok()
    }

    fn len(&self) -> usize {
        self.data.len()
    }

    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    fn clear(&mut self) {
        self.data.clear();
    }

    /// Merge-join subset check: is every element in `self` also in `other`?
    /// Both vectors are sorted, so this is O(n + m) with no allocations.
    /// Useful for ∀ verification: "every x in predicate A is also in predicate B".
    #[allow(dead_code)]
    fn is_subset_of(&self, other: &SortedU32Vec) -> bool {
        let mut j = 0;
        for &val in &self.data {
            while j < other.data.len() && other.data[j] < val {
                j += 1;
            }
            if j >= other.data.len() || other.data[j] != val {
                return false;
            }
        }
        true
    }

    /// Merge-join intersection: returns elements present in both sorted vectors.
    /// O(n + m) with a single output allocation. Useful for SIMD batch membership.
    #[allow(dead_code)]
    fn intersection(&self, other: &SortedU32Vec) -> SortedU32Vec {
        let mut result = Vec::new();
        let (mut i, mut j) = (0, 0);
        while i < self.data.len() && j < other.data.len() {
            match self.data[i].cmp(&other.data[j]) {
                std::cmp::Ordering::Less => i += 1,
                std::cmp::Ordering::Greater => j += 1,
                std::cmp::Ordering::Equal => {
                    result.push(self.data[i]);
                    i += 1;
                    j += 1;
                }
            }
        }
        SortedU32Vec { data: result }
    }
}

impl Default for SortedU32Vec {
    fn default() -> Self {
        Self::new()
    }
}

// ─── Knowledge Base State ────────────────────────────────────────

/// Registry entry for a SkolemFn created by native rule compilation.
/// Used by query-side existential checking to generate SkolemFn witness terms.
#[derive(Clone)]
struct SkolemFnEntry {
    base_name: String,
    dep_count: usize,
}

/// Prefix used for dependent Skolem placeholder variables.
/// A dependent Skolem is an ∃ variable nested under a ∀.
const SKDEP_PREFIX: &str = "__skdep__";

// ─── Structural S-Expression Tree ─────────────────────────────────

/// Pre-parsed s-expression tree for structural pattern matching.
/// Eliminates repeated string tokenization during backward chaining.
#[derive(Clone, Debug)]
enum SexpTree {
    /// A literal atom (e.g., `Pred`, `"gerku"`, `Const`, `Nil`).
    Atom(String),
    /// A parenthesized list of sub-expressions.
    List(Vec<SexpTree>),
    /// A pattern variable (e.g., `x__v0`) — matches any complete sub-expression.
    Var(String),
}

impl SexpTree {
    /// Parse an s-expression string into a tree, marking pattern variables.
    fn parse(s: &str, var_names: &[String]) -> Self {
        let tokens = sexp_tokenize(s);
        let (tree, _) = Self::parse_tokens(&tokens, 0, var_names);
        tree
    }

    fn parse_tokens(tokens: &[String], pos: usize, var_names: &[String]) -> (Self, usize) {
        if pos >= tokens.len() {
            return (SexpTree::Atom(String::new()), pos);
        }
        if tokens[pos] == "(" {
            let mut children = Vec::new();
            let mut i = pos + 1;
            while i < tokens.len() && tokens[i] != ")" {
                let (child, next) = Self::parse_tokens(tokens, i, var_names);
                children.push(child);
                i = next;
            }
            (SexpTree::List(children), i + 1) // skip ")"
        } else if var_names.contains(&tokens[pos]) {
            (SexpTree::Var(tokens[pos].clone()), pos + 1)
        } else {
            (SexpTree::Atom(tokens[pos].clone()), pos + 1)
        }
    }

    /// Match this tree (as pattern) against a concrete s-expression string.
    /// Returns bindings mapping variable names to matched sub-expression strings.
    fn match_against(&self, concrete: &str) -> Option<HashMap<String, String>> {
        let conc_tokens = sexp_tokenize(concrete);
        self.match_against_tokens(&conc_tokens)
    }

    /// Match against pre-tokenized concrete sexp (avoids re-tokenization when
    /// multiple rules are tried against the same query).
    fn match_against_tokens(&self, conc_tokens: &[String]) -> Option<HashMap<String, String>> {
        let mut bindings = HashMap::new();
        let (_, end) = self.match_tokens(conc_tokens, 0, &mut bindings)?;
        if end == conc_tokens.len() {
            Some(bindings)
        } else {
            None
        }
    }

    fn match_tokens(
        &self,
        tokens: &[String],
        pos: usize,
        bindings: &mut HashMap<String, String>,
    ) -> Option<((), usize)> {
        if pos >= tokens.len() {
            return None;
        }
        match self {
            SexpTree::Var(name) => {
                // Match a complete sub-expression
                let (end, sub_sexp) = extract_sexp_at(tokens, pos)?;
                if let Some(existing) = bindings.get(name.as_str()) {
                    if *existing != sub_sexp {
                        return None;
                    }
                } else {
                    bindings.insert(name.clone(), sub_sexp);
                }
                Some(((), end))
            }
            SexpTree::Atom(atom) => {
                if &tokens[pos] == atom {
                    Some(((), pos + 1))
                } else {
                    None
                }
            }
            SexpTree::List(children) => {
                if tokens[pos] != "(" {
                    return None;
                }
                let mut ci = pos + 1;
                for child in children {
                    if ci >= tokens.len() {
                        return None;
                    }
                    let (_, next) = child.match_tokens(tokens, ci, bindings)?;
                    ci = next;
                }
                if ci >= tokens.len() || tokens[ci] != ")" {
                    return None;
                }
                Some(((), ci + 1))
            }
        }
    }

    /// Substitute bindings into this tree, producing an s-expression string.
    fn substitute(&self, bindings: &HashMap<String, String>) -> String {
        let mut buf = String::new();
        self.substitute_into(&mut buf, bindings);
        buf
    }

    /// Write substituted s-expression into a buffer (avoids per-level allocation).
    fn substitute_into(&self, buf: &mut String, bindings: &HashMap<String, String>) {
        match self {
            SexpTree::Var(name) => {
                match bindings.get(name.as_str()) {
                    Some(val) => buf.push_str(val),
                    None => buf.push_str(name),
                }
            }
            SexpTree::Atom(atom) => buf.push_str(atom),
            SexpTree::List(children) => {
                buf.push('(');
                for (i, child) in children.iter().enumerate() {
                    if i > 0 {
                        buf.push(' ');
                    }
                    child.substitute_into(buf, bindings);
                }
                buf.push(')');
            }
        }
    }

    /// Check if this tree contains a given variable name.
    fn contains_var(&self, var: &str) -> bool {
        match self {
            SexpTree::Var(name) => name == var,
            SexpTree::Atom(_) => false,
            SexpTree::List(children) => children.iter().any(|c| c.contains_var(var)),
        }
    }
}

/// Records the structure of a compiled universal rule for backward-chaining provenance.
/// Templates use bare pattern variables (e.g., `x__v0`) instead of bound values.
#[derive(Clone)]
struct UniversalRuleRecord {
    /// Human-readable label, e.g. "gerku → danlu"
    label: String,
    /// Interned s-expression keys for the rule's conditions.
    condition_templates: Vec<u32>,
    /// Interned s-expression keys for the rule's conclusions.
    conclusion_templates: Vec<u32>,
    /// Pre-parsed condition templates for structural matching.
    condition_trees: Vec<SexpTree>,
    /// Pre-parsed conclusion templates for structural matching.
    conclusion_trees: Vec<SexpTree>,
    /// Pattern variable names used in templates, e.g. ["x__v0"].
    pattern_var_names: Vec<String>,
}

/// Registry entry for a single asserted fact, supporting retraction and rebuild.
#[derive(Clone)]
struct FactRecord {
    id: u64,
    buffer: LogicBuffer,
    label: String,
    retracted: bool,
}

/// All mutable KB state behind a single RefCell.
struct KnowledgeBaseInner {
    /// S-expression string interner — deduplicates all sexp strings.
    interner: SexpInterner,
    skolem_counter: usize,
    known_entities: HashSet<String>,
    /// Event Skolem constants (from `_ev*` variables). Tracked for witness search
    /// and proof tracing, but NOT registered in `known_entities`
    /// to prevent quadratic blowup in guarded conjunction introduction.
    known_event_entities: HashSet<String>,
    /// Known description terms (from `le` gadri), tracked separately for InDomain.
    known_descriptions: HashSet<String>,
    known_rules: HashSet<String>,
    skolem_fn_registry: Vec<SkolemFnEntry>,
    /// Ground facts as interned s-expression keys (sorted columnar storage).
    /// Binary search for O(log n) membership, 4 bytes per entry.
    asserted_sexps: SortedU32Vec,
    /// Columnar index: predicate name → sorted interned sexp keys.
    /// Enables predicate-scoped enumeration and merge-join subset checks.
    predicate_facts: HashMap<String, SortedU32Vec>,
    /// Compiled universal rule templates indexed by conclusion predicate name.
    /// Each predicate name maps to the rules whose conclusion templates mention it.
    /// Rc-wrapped to avoid cloning rule records during backward-chain snapshots.
    universal_rules: HashMap<String, Vec<Arc<UniversalRuleRecord>>>,
    /// Monotonically increasing fact ID counter.
    fact_counter: u64,
    /// Registry of all asserted facts (including retracted ones, for ID stability).
    fact_registry: HashMap<u64, FactRecord>,
    /// Suppresses diagnostic prints during rebuild replay.
    rebuilding: bool,
    /// Configuration parameter preserved across reset/rebuild (kept for WIT API compatibility).
    run_bound: u32,
    /// Cached domain members — invalidated when entities/descriptions change.
    domain_members_cache: Vec<(String, LogicalTerm)>,
    domain_members_dirty: bool,
}

impl KnowledgeBaseInner {
    fn new() -> Self {
        Self {
            interner: SexpInterner::new(),
            skolem_counter: 0,
            known_entities: HashSet::new(),
            known_event_entities: HashSet::new(),
            known_descriptions: HashSet::new(),
            known_rules: HashSet::new(),
            skolem_fn_registry: Vec::new(),
            asserted_sexps: SortedU32Vec::new(),
            predicate_facts: HashMap::new(), // values are SortedU32Vec via Default
            universal_rules: HashMap::new(),
            fact_counter: 0,
            fact_registry: HashMap::new(),
            rebuilding: false,
            run_bound: 100,
            domain_members_cache: Vec::new(),
            domain_members_dirty: true,
        }
    }

    fn reset(&mut self) {
        self.interner.clear();
        self.skolem_counter = 0;
        self.known_entities.clear();
        self.known_event_entities.clear();
        self.known_descriptions.clear();
        self.known_rules.clear();
        self.skolem_fn_registry.clear();
        self.asserted_sexps.clear();
        self.predicate_facts.clear();
        self.universal_rules.clear();
        self.fact_counter = 0;
        self.fact_registry.clear();
        self.rebuilding = false;
        self.domain_members_cache.clear();
        self.domain_members_dirty = true;
    }

    fn fresh_fact_id(&mut self) -> u64 {
        let id = self.fact_counter;
        self.fact_counter += 1;
        id
    }

    fn fresh_skolem(&mut self) -> String {
        let sk = format!("sk_{}", self.skolem_counter);
        self.skolem_counter += 1;
        sk
    }

    fn note_entity(&mut self, name: &str) {
        if self.known_entities.insert(name.to_string()) {
            self.domain_members_dirty = true;
        }
    }

    /// Track an event Skolem constant for witness search and proof tracing,
    /// without registering it in `known_entities`.
    fn note_event_entity(&mut self, name: &str) {
        if self.known_event_entities.insert(name.to_string()) {
            self.domain_members_dirty = true;
        }
    }

    fn note_description(&mut self, name: &str) {
        if self.known_descriptions.insert(name.to_string()) {
            self.domain_members_dirty = true;
        }
    }

    /// Return all known domain members as (s-expression, LogicalTerm) pairs.
    /// Ensure the domain members cache is up-to-date. Call before any query.
    fn ensure_domain_members_cached(&mut self) {
        if !self.domain_members_dirty {
            return;
        }
        let mut members = Vec::new();
        for e in &self.known_entities {
            members.push((
                format!("(Const \"{}\")", e),
                LogicalTerm::Constant(e.clone()),
            ));
        }
        for e in &self.known_event_entities {
            members.push((
                format!("(Const \"{}\")", e),
                LogicalTerm::Constant(e.clone()),
            ));
        }
        for d in &self.known_descriptions {
            members.push((
                format!("(Desc \"{}\")", d),
                LogicalTerm::Description(d.clone()),
            ));
        }
        self.domain_members_cache = members;
        self.domain_members_dirty = false;
    }

    /// Return cached domain members. Panics if cache is dirty — call ensure_domain_members_cached() first.
    fn all_domain_members(&self) -> &[(String, LogicalTerm)] {
        &self.domain_members_cache
    }
}

/// The WIT-exported resource type.
/// wit-bindgen generates `&self` for methods, so RefCell provides mutability.
pub struct KnowledgeBase {
    inner: RefCell<KnowledgeBaseInner>,
}

/// Build a SkolemFn s-expression from a base name and dependency terms.
/// Single dep: `(SkolemFn "sk_N" dep0)` — backward compatible.
/// Multi dep: `(SkolemFn "sk_N" (DepPair dep0 (DepPair dep1 dep2)))` — right-nested pairs.
fn build_skolem_fn_sexp(base_name: &str, deps: &[&str]) -> String {
    let dep_term = match deps.len() {
        0 => "(Zoe)".to_string(),
        1 => deps[0].to_string(),
        _ => {
            // Right-nested DepPair encoding: [a, b, c] → (DepPair a (DepPair b c))
            let mut acc = deps.last().unwrap().to_string();
            for dep in deps[..deps.len() - 1].iter().rev() {
                acc = format!("(DepPair {} {})", dep, acc);
            }
            acc
        }
    };
    format!("(SkolemFn \"{}\" {})", base_name, dep_term)
}

/// Build a ground SkolemFn s-expression with a Const entity argument.
/// Generate cartesian product of s-expression strings with given arity.
/// Lazy cartesian product iterator: yields one combination at a time.
/// Avoids materializing all M^N combinations in memory — stops at first match.
struct CartesianProduct<'a> {
    entities: &'a [String],
    dep_count: usize,
    indices: Vec<usize>,
    done: bool,
}

impl<'a> CartesianProduct<'a> {
    fn new(entities: &'a [String], dep_count: usize) -> Self {
        let done = dep_count > 0 && entities.is_empty();
        Self {
            entities,
            dep_count,
            indices: vec![0; dep_count],
            done,
        }
    }
}

impl<'a> Iterator for CartesianProduct<'a> {
    type Item = Vec<&'a str>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        if self.dep_count == 0 {
            self.done = true;
            return Some(vec![]);
        }
        let combo: Vec<&str> = self.indices.iter().map(|&i| self.entities[i].as_str()).collect();
        // Advance indices (odometer-style, rightmost first)
        let mut carry = true;
        for i in (0..self.dep_count).rev() {
            if carry {
                self.indices[i] += 1;
                if self.indices[i] >= self.entities.len() {
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

/// Lazy multi-set cartesian product iterator: one combination at a time.
/// Each set can have a different size (used after per-variable pre-filtering).
struct MultiCartesianProduct<'a> {
    sets: &'a [Vec<String>],
    indices: Vec<usize>,
    done: bool,
}

impl<'a> MultiCartesianProduct<'a> {
    fn new(sets: &'a [Vec<String>]) -> Self {
        let done = sets.iter().any(|s| s.is_empty());
        Self {
            sets,
            indices: vec![0; sets.len()],
            done,
        }
    }
}

impl<'a> Iterator for MultiCartesianProduct<'a> {
    type Item = Vec<&'a str>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done || self.sets.is_empty() {
            if self.sets.is_empty() && !self.done {
                self.done = true;
                return Some(vec![]);
            }
            return None;
        }
        let combo: Vec<&str> = self.indices.iter().enumerate()
            .map(|(set_idx, &item_idx)| self.sets[set_idx][item_idx].as_str())
            .collect();
        // Advance indices
        let mut carry = true;
        for i in (0..self.sets.len()).rev() {
            if carry {
                self.indices[i] += 1;
                if self.indices[i] >= self.sets[i].len() {
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

use std::cell::Cell;

thread_local! {
    /// Cache for backward-chain predicate results within a single query.
    /// Maps ground predicate s-expression → holds (true/false).
    /// Cleared at the start of each query to avoid stale results.
    static PRED_CACHE: RefCell<HashMap<String, bool>> = RefCell::new(HashMap::new());
    /// Flag to enable/disable predicate caching (disabled during assertion replay).
    static PRED_CACHE_ENABLED: Cell<bool> = const { Cell::new(false) };
}

/// Clear the predicate result cache. Call at the start of each query.
fn clear_pred_cache() {
    PRED_CACHE.with(|c| c.borrow_mut().clear());
    PRED_CACHE_ENABLED.with(|e| e.set(true));
}

/// Disable predicate caching (e.g., during assertion processing).
fn disable_pred_cache() {
    PRED_CACHE_ENABLED.with(|e| e.set(false));
}

// ─── WIT Export Implementation ────────────────────────────────────

struct LogjiComponent;

impl Guest for LogjiComponent {
    type KnowledgeBase = KnowledgeBase;
}

/// Collect leaf node IDs from a ground conjunction tree in the LogicBuffer.
/// Descends through And nodes (flattening), Skolemized Exists nodes (stripped),
/// and deontic wrappers (transparent). Tracks tense context (Past/Present/Future)
/// so each leaf can be wrapped appropriately.
/// Everything else (Pred, Or, Not, etc.) is a leaf.
fn collect_ground_leaves(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
    tense: Option<&str>,
    leaves: &mut Vec<(u32, Option<String>)>,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => {
            collect_ground_leaves(buffer, *l, subs, tense, leaves);
            collect_ground_leaves(buffer, *r, subs, tense, leaves);
        }
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            // Skolemized existential — descend through it
            collect_ground_leaves(buffer, *body, subs, tense, leaves);
        }
        LogicNode::PastNode(inner) => {
            collect_ground_leaves(buffer, *inner, subs, Some("Past"), leaves);
        }
        LogicNode::PresentNode(inner) => {
            collect_ground_leaves(buffer, *inner, subs, Some("Present"), leaves);
        }
        LogicNode::FutureNode(inner) => {
            collect_ground_leaves(buffer, *inner, subs, Some("Future"), leaves);
        }
        LogicNode::ObligatoryNode(inner) | LogicNode::PermittedNode(inner) => {
            // Deontic wrappers are transparent
            collect_ground_leaves(buffer, *inner, subs, tense, leaves);
        }
        _ => {
            leaves.push((node_id, tense.map(|t| t.to_string())));
        }
    }
}

/// Detect ground material conditionals (Or(Not(conditions), conclusion)) in a logic buffer
/// and register them as backward-chaining rules with no pattern variables.
/// Enables backward-chaining modus ponens on ground sentence connectives.
fn register_ground_material_conditional(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
) {
    // Walk through Skolemized Exists and tense wrappers to find the Or(Not(...), ...) pattern
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            register_ground_material_conditional(buffer, *body, subs, inner);
        }
        LogicNode::PastNode(n) | LogicNode::PresentNode(n) | LogicNode::FutureNode(n)
        | LogicNode::ObligatoryNode(n) | LogicNode::PermittedNode(n) => {
            register_ground_material_conditional(buffer, *n, subs, inner);
        }
        LogicNode::AndNode((l, r)) => {
            register_ground_material_conditional(buffer, *l, subs, inner);
            register_ground_material_conditional(buffer, *r, subs, inner);
        }
        LogicNode::OrNode((l, r)) => {
            // Check for Or(Not(P), Q) — material conditional P → Q
            if let LogicNode::NotNode(neg_inner) = &buffer.nodes[*l as usize] {
                let raw_subs: HashMap<String, String> = subs
                    .iter()
                    .filter(|(_, v)| !v.starts_with(SKDEP_PREFIX))
                    .map(|(k, v)| (k.clone(), format!("(Const \"{}\")", v)))
                    .collect();
                // Extract condition(s) — may be a conjunction
                let mut condition_sexps = Vec::new();
                collect_material_condition_leaves(buffer, *neg_inner, &raw_subs, &mut condition_sexps);
                let conclusion_sexp = reconstruct_sexp_with_subs(buffer, *r, &raw_subs);
                let label = format!("{} → {}",
                    condition_sexps.iter().map(|s| extract_pred_name(s).unwrap_or("?")).collect::<Vec<_>>().join(" ∧ "),
                    extract_pred_name(&conclusion_sexp).unwrap_or("?")
                );
                register_rule(inner, label, condition_sexps, vec![conclusion_sexp], vec![]);
            }
            // Also check Or(Q, Not(P)) — reversed order (commutativity)
            else if let LogicNode::NotNode(neg_inner) = &buffer.nodes[*r as usize] {
                let raw_subs: HashMap<String, String> = subs
                    .iter()
                    .filter(|(_, v)| !v.starts_with(SKDEP_PREFIX))
                    .map(|(k, v)| (k.clone(), format!("(Const \"{}\")", v)))
                    .collect();
                let mut condition_sexps = Vec::new();
                collect_material_condition_leaves(buffer, *neg_inner, &raw_subs, &mut condition_sexps);
                let conclusion_sexp = reconstruct_sexp_with_subs(buffer, *l, &raw_subs);
                let label = format!("{} → {}",
                    condition_sexps.iter().map(|s| extract_pred_name(s).unwrap_or("?")).collect::<Vec<_>>().join(" ∧ "),
                    extract_pred_name(&conclusion_sexp).unwrap_or("?")
                );
                register_rule(inner, label, condition_sexps, vec![conclusion_sexp], vec![]);
            }
        }
        _ => {}
    }
}

/// Helper: collect leaf s-expressions from the condition side of a material conditional.
/// Follows And nodes to flatten conjunctive conditions.
fn collect_material_condition_leaves(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
    leaves: &mut Vec<String>,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => {
            collect_material_condition_leaves(buffer, *l, subs, leaves);
            collect_material_condition_leaves(buffer, *r, subs, leaves);
        }
        _ => {
            leaves.push(reconstruct_sexp_with_subs(buffer, node_id, subs));
        }
    }
}

/// Process a logic buffer into the knowledge base without recording in the fact registry.
/// Used by both initial assertion and rebuild-on-retract replay.
fn process_assertion(inner: &mut KnowledgeBaseInner, logic: &LogicBuffer) -> Result<(), String> {
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
                .map(|(v, sk)| {
                    if sk.starts_with(SKDEP_PREFIX) {
                        format!("{} ↦ {}(∀-dependent)", v, &sk[SKDEP_PREFIX.len()..])
                    } else {
                        format!("{} ↦ {}", v, sk)
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
        let is_forall = matches!(
            &logic.nodes[root_id as usize],
            LogicNode::ForAllNode(_)
        );

        if is_forall {
            // ═══ NATIVE RULE PATH ═══
            for (var, sk) in &skolem_subs {
                if !sk.starts_with(SKDEP_PREFIX) {
                    if var.starts_with("_ev") {
                        inner.note_event_entity(sk);
                    } else {
                        inner.note_entity(sk);
                    }
                }
            }
            collect_and_note_constants(logic, root_id, inner);
            compile_forall_to_rule(logic, root_id, &skolem_subs, inner)?;
        } else {
            // ═══ GROUND FORMULA PATH ═══
            for (var, sk) in &skolem_subs {
                if !sk.starts_with(SKDEP_PREFIX) {
                    if var.starts_with("_ev") {
                        inner.note_event_entity(sk);
                    } else {
                        inner.note_entity(sk);
                    }
                }
            }
            collect_and_note_constants(logic, root_id, inner);

            let raw_subs: HashMap<String, String> = skolem_subs
                .iter()
                .filter(|(_, v)| !v.starts_with(SKDEP_PREFIX))
                .map(|(k, v)| (k.clone(), format!("(Const \"{}\")", v)))
                .collect();

            // Flatten top-level conjunctions and assert each leaf individually.
            let mut leaves = Vec::new();
            collect_ground_leaves(logic, root_id, &skolem_subs, None, &mut leaves);

            for (leaf_id, tense) in &leaves {
                let leaf_sexp = reconstruct_sexp_with_subs(logic, *leaf_id, &raw_subs);
                let wrapped = match tense {
                    Some(t) => format!("({} {})", t, leaf_sexp),
                    None => leaf_sexp,
                };
                // Record as asserted fact for provenance tracking and backward-chaining
                assert_sexp(wrapped.clone(), inner);
            }

            // Register ground material conditionals for backward-chaining
            register_ground_material_conditional(logic, root_id, &skolem_subs, inner);
        }

        // Phase 3: Generate extra witnesses for Count quantifiers (n > 1)
        generate_count_extra_witnesses(logic, root_id, &skolem_subs, inner);
    }

    Ok(())
}

/// Internal methods that return `Result<_, String>` for use by both the WIT boundary and tests.
impl KnowledgeBase {
    /// Assert FOL facts from a logic buffer into the knowledge base.
    /// Stores the buffer in the fact registry and returns a unique fact ID.
    fn assert_fact_inner(&self, logic: LogicBuffer, label: String) -> Result<u64, String> {
        let mut inner = self.inner.borrow_mut();
        let id = inner.fresh_fact_id();
        inner.fact_registry.insert(id, FactRecord {
            id,
            buffer: logic.clone(),
            label,
            retracted: false,
        });
        process_assertion(&mut inner, &logic)?;
        Ok(id)
    }

    /// Assert a fact with a pre-assigned ID. Used for replay from persistent store.
    /// Advances the internal counter past the given ID.
    pub fn assert_fact_with_id(&self, logic: LogicBuffer, label: String, id: u64) -> Result<(), String> {
        let mut inner = self.inner.borrow_mut();
        // Advance counter past the provided ID.
        if id >= inner.fact_counter {
            inner.fact_counter = id + 1;
        }
        inner.fact_registry.insert(id, FactRecord {
            id,
            buffer: logic.clone(),
            label,
            retracted: false,
        });
        process_assertion(&mut inner, &logic)?;
        Ok(())
    }

    /// Retract a previously asserted fact by its ID. Triggers a full KB rebuild
    /// from remaining (non-retracted) facts.
    fn retract_fact_inner(&self, id: u64) -> Result<(), String> {
        let mut inner = self.inner.borrow_mut();
        match inner.fact_registry.get_mut(&id) {
            None => Err(format!("Fact #{} not found", id)),
            Some(r) if r.retracted => Ok(()), // idempotent
            Some(r) => {
                r.retracted = true;
                Self::rebuild_inner(&mut inner)
            }
        }
    }

    /// Rebuild the KB from all non-retracted facts.
    /// Preserves fact_registry and fact_counter; resets all derived state.
    fn rebuild_inner(inner: &mut KnowledgeBaseInner) -> Result<(), String> {
        // Reset derived state (interner too — all interned keys become invalid)
        inner.interner.clear();
        inner.skolem_counter = 0;
        inner.known_entities.clear();
        inner.known_event_entities.clear();
        inner.known_descriptions.clear();
        inner.known_rules.clear();
        inner.skolem_fn_registry.clear();
        inner.asserted_sexps.clear();
        inner.predicate_facts.clear();
        inner.universal_rules.clear();

        // Collect non-retracted buffers ordered by ID (clone to avoid borrow conflict)
        let mut entries: Vec<(&u64, &FactRecord)> = inner
            .fact_registry
            .iter()
            .filter(|(_, r)| !r.retracted)
            .collect();
        entries.sort_by_key(|(id, _)| **id);
        let buffers: Vec<LogicBuffer> = entries
            .iter()
            .map(|(_, r)| r.buffer.clone())
            .collect();

        // Replay with diagnostic output suppressed
        inner.rebuilding = true;
        for buf in &buffers {
            process_assertion(inner, buf)?;
        }
        inner.rebuilding = false;
        Ok(())
    }

    /// List all active (non-retracted) facts in the KB.
    fn list_facts_inner(&self) -> Result<Vec<FactSummary>, String> {
        let inner = self.inner.borrow();
        let mut facts: Vec<FactSummary> = inner
            .fact_registry
            .values()
            .filter(|r| !r.retracted)
            .map(|r| FactSummary {
                id: r.id,
                label: r.label.clone(),
                root_count: r.buffer.roots.len() as u32,
            })
            .collect();
        facts.sort_by_key(|f| f.id);
        Ok(facts)
    }

    fn set_run_bound_inner(&self, n: u32) {
        self.inner.borrow_mut().run_bound = n;
    }

    fn get_run_bound_inner(&self) -> u32 {
        self.inner.borrow().run_bound
    }

    /// Check whether all root formulas in the logic buffer are entailed by the KB.
    fn query_entailment_inner(&self, logic: LogicBuffer) -> Result<bool, String> {
        clear_pred_cache();
        let mut inner = self.inner.borrow_mut();
        inner.ensure_domain_members_cached();
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            if !check_formula_holds(&logic, root_id, &mut subs, &mut inner, None)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Find all satisfying binding sets for existential variables in the query formula.
    /// Returns one `Vec<WitnessBinding>` per satisfying assignment.
    fn query_find_inner(&self, logic: LogicBuffer) -> Result<Vec<Vec<WitnessBinding>>, String> {
        clear_pred_cache();
        let mut inner = self.inner.borrow_mut();
        inner.ensure_domain_members_cached();
        let mut result_sets: Option<Vec<Vec<(String, String)>>> = None;
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            let witnesses = find_witnesses(&logic, root_id, &mut subs, &mut inner, None)?;
            match result_sets {
                None => result_sets = Some(witnesses),
                Some(ref _prev) => {
                    if witnesses.is_empty() {
                        return Ok(vec![]);
                    }
                    result_sets = Some(witnesses);
                }
            }
        }
        let binding_sets = result_sets.unwrap_or_default();
        Ok(binding_sets
            .into_iter()
            .map(|bindings| {
                bindings
                    .into_iter()
                    .map(|(var, sexp)| WitnessBinding {
                        variable: var,
                        term: parse_sexp_to_term(&sexp),
                    })
                    .collect()
            })
            .collect())
    }

    fn query_entailment_with_proof_inner(
        &self,
        logic: LogicBuffer,
    ) -> Result<(bool, ProofTrace), String> {
        clear_pred_cache();
        let mut inner = self.inner.borrow_mut();
        inner.ensure_domain_members_cached();
        let mut steps: Vec<ProofStep> = Vec::new();
        let mut memo: HashMap<String, u32> = HashMap::new();
        let mut root_children: Vec<u32> = Vec::new();
        let mut all_hold = true;
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            let (holds, step_idx) =
                check_formula_holds_traced(&logic, root_id, &mut subs, &mut inner, &mut steps, None, &mut memo)?;
            root_children.push(step_idx);
            if !holds {
                all_hold = false;
            }
        }
        let root = if root_children.len() == 1 {
            root_children[0]
        } else {
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::Conjunction,
                holds: all_hold,
                children: root_children,
            });
            idx
        };
        Ok((all_hold, ProofTrace { steps, root }))
    }
}

impl GuestKnowledgeBase for KnowledgeBase {
    fn new() -> Self {
        KnowledgeBase {
            inner: RefCell::new(KnowledgeBaseInner::new()),
        }
    }

    fn assert_fact(&self, logic: LogicBuffer, label: String) -> Result<u64, NibliError> {
        self.assert_fact_inner(logic, label)
            .map_err(NibliError::Reasoning)
    }

    fn query_entailment(&self, logic: LogicBuffer) -> Result<bool, NibliError> {
        self.query_entailment_inner(logic)
            .map_err(NibliError::Reasoning)
    }

    fn query_find(&self, logic: LogicBuffer) -> Result<Vec<Vec<WitnessBinding>>, NibliError> {
        self.query_find_inner(logic).map_err(NibliError::Reasoning)
    }

    fn query_entailment_with_proof(
        &self,
        logic: LogicBuffer,
    ) -> Result<(bool, ProofTrace), NibliError> {
        self.query_entailment_with_proof_inner(logic)
            .map_err(NibliError::Reasoning)
    }

    fn reset(&self) -> Result<(), NibliError> {
        self.inner.borrow_mut().reset();
        Ok(())
    }

    fn retract_fact(&self, id: u64) -> Result<(), NibliError> {
        self.retract_fact_inner(id)
            .map_err(NibliError::Reasoning)
    }

    fn list_facts(&self) -> Result<Vec<FactSummary>, NibliError> {
        self.list_facts_inner().map_err(NibliError::Reasoning)
    }

    fn set_run_bound(&self, n: u32) {
        self.set_run_bound_inner(n);
    }

    fn get_run_bound(&self) -> u32 {
        self.get_run_bound_inner()
    }
}

// ─── Numeric Comparison Helpers ──────────────────────────────────

/// Extract an i64 numeric value from a LogicalTerm.
/// Handles direct Number literals and Variables substituted to "(Num N)" form.
fn extract_num_value(term: &LogicalTerm, subs: &HashMap<String, String>) -> Option<i64> {
    match term {
        LogicalTerm::Number(n) => Some(*n as i64),
        LogicalTerm::Variable(v) => {
            let s = subs.get(v.as_str())?;
            s.strip_prefix("(Num ")?.strip_suffix(')')?.parse::<i64>().ok()
        }
        _ => None,
    }
}

/// Evaluate zmadu/mleca/dunli when first two args are Num.
/// Returns None for non-numeric args (fall through to standard KB check).
fn try_numeric_comparison(
    rel: &str,
    args: &[LogicalTerm],
    subs: &HashMap<String, String>,
) -> Option<bool> {
    let a = extract_num_value(args.get(0)?, subs)?;
    let b = extract_num_value(args.get(1)?, subs)?;
    match rel {
        "zmadu" => Some(a > b),
        "mleca" => Some(a < b),
        "dunli" => Some(a == b),
        _ => None,
    }
}

/// Evaluate arithmetic predicates (pilji/sumji/dilcu) when all three args are Num.
/// Place structure: x1 = op(x2, x3).
fn try_arithmetic_evaluation(
    rel: &str,
    args: &[LogicalTerm],
    subs: &HashMap<String, String>,
) -> Option<bool> {
    let x1 = extract_num_value(args.get(0)?, subs)?;
    let x2 = extract_num_value(args.get(1)?, subs)?;
    let x3 = extract_num_value(args.get(2)?, subs)?;
    match rel {
        "pilji" => Some(x1 == x2 * x3),
        "sumji" => Some(x1 == x2 + x3),
        "dilcu" => {
            if x3 == 0 {
                return Some(false);
            }
            Some(x1 == x2 / x3)
        }
        _ => None,
    }
}

// ─── Compute Dispatch Helpers ────────────────────────────────────

/// Parse an s-expression string back into a [`LogicalTerm`] for witness extraction.
/// Recognizes `(Const "...")`, `(Desc "...")`, `(Num ...)`, `(Zoe)` patterns.
fn parse_sexp_to_term(sexp: &str) -> LogicalTerm {
    if let Some(name) = sexp
        .strip_prefix("(Const \"")
        .and_then(|s| s.strip_suffix("\")"))
    {
        LogicalTerm::Constant(name.to_string())
    } else if let Some(n) = sexp
        .strip_prefix("(Num ")
        .and_then(|s| s.strip_suffix(')'))
    {
        LogicalTerm::Number(n.parse::<f64>().unwrap_or(0.0))
    } else if let Some(name) = sexp
        .strip_prefix("(Desc \"")
        .and_then(|s| s.strip_suffix("\")"))
    {
        LogicalTerm::Description(name.to_string())
    } else if sexp == "(Zoe)" {
        LogicalTerm::Unspecified
    } else if let Some(name) = sexp
        .strip_prefix("(Var \"")
        .and_then(|s| s.strip_suffix("\")"))
    {
        LogicalTerm::Variable(name.to_string())
    } else {
        LogicalTerm::Variable(sexp.to_string())
    }
}

/// Resolve variable substitutions in args back to concrete LogicalTerm values
/// for passing to the compute backend.
fn resolve_args_for_dispatch(
    args: &[LogicalTerm],
    subs: &HashMap<String, String>,
) -> Vec<LogicalTerm> {
    args.iter()
        .map(|a| match a {
            LogicalTerm::Variable(v) => {
                if let Some(s) = subs.get(v.as_str()) {
                    parse_sexp_to_term(s)
                } else {
                    a.clone()
                }
            }
            _ => a.clone(),
        })
        .collect()
}

/// Dispatch a compute predicate to the WIT compute-backend import.
/// On native (non-wasm32) targets, returns Err (backend unavailable).
#[cfg(target_arch = "wasm32")]
fn dispatch_to_backend(rel: &str, args: &[LogicalTerm]) -> Result<bool, String> {
    crate::bindings::lojban::nibli::compute_backend::evaluate(rel, args)
        .map_err(|e| format!("{}", e))
}

#[cfg(not(target_arch = "wasm32"))]
fn dispatch_to_backend(_rel: &str, _args: &[LogicalTerm]) -> Result<bool, String> {
    Err("Compute backend unavailable in native mode".to_string())
}

/// A single compute request for batch dispatch.
struct ComputeRequest {
    relation: String,
    args: Vec<LogicalTerm>,
}

/// Dispatch a batch of compute predicates to the WIT compute-backend import.
/// Returns results in the same order as the input requests.
/// Each result is independent — one failure does not affect others.
#[cfg(target_arch = "wasm32")]
fn dispatch_batch_to_backend(requests: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    use crate::bindings::lojban::nibli::compute_backend as cb;
    let wit_requests: Vec<cb::ComputeRequest> = requests
        .iter()
        .map(|r| cb::ComputeRequest {
            relation: r.relation.clone(),
            args: r.args.clone(),
        })
        .collect();
    let results = cb::evaluate_batch(&wit_requests);
    results
        .into_iter()
        .map(|r| match r {
            cb::ComputeResult::Ok(b) => Ok(b),
            cb::ComputeResult::Err(msg) => Err(msg),
        })
        .collect()
}

#[cfg(not(target_arch = "wasm32"))]
fn dispatch_batch_to_backend(requests: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    requests
        .iter()
        .map(|_| Err("Compute backend unavailable in native mode".to_string()))
        .collect()
}

/// Query the compute backend for domain members satisfying a predicate at a given place.
/// Returns ground terms that can fill the `place_index` slot while other args are fixed.
/// Returns empty Vec if enumeration is not supported (e.g., infinite arithmetic domains).
#[cfg(target_arch = "wasm32")]
fn dispatch_check_membership(
    rel: &str,
    args: &[LogicalTerm],
    place_index: u32,
) -> Result<Vec<LogicalTerm>, String> {
    crate::bindings::lojban::nibli::compute_backend::check_membership(rel, args, place_index)
        .map_err(|e| format!("{}", e))
}

#[cfg(not(target_arch = "wasm32"))]
fn dispatch_check_membership(
    _rel: &str,
    _args: &[LogicalTerm],
    _place_index: u32,
) -> Result<Vec<LogicalTerm>, String> {
    Ok(vec![]) // Native mode: no external membership, fall back to KB enumeration
}

/// Build an s-expression for a ground predicate from resolved args.
/// Returns None if any argument is still a Variable (not fully ground).
/// Output: `(Pred "rel" (Cons (Num 8) (Cons (Num 2) (Cons (Num 3) (Nil)))))`.
/// Returns `None` if any argument is a non-ground variable (cannot be fully resolved).
fn build_ground_predicate_sexp(rel: &str, resolved_args: &[LogicalTerm]) -> Option<String> {
    for arg in resolved_args {
        if matches!(arg, LogicalTerm::Variable(_)) {
            return None;
        }
    }
    let mut args_str = String::from("(Nil)");
    for arg in resolved_args.iter().rev() {
        let term_str = match arg {
            LogicalTerm::Number(n) => format!("(Num {})", *n as i64),
            LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
            LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
            LogicalTerm::Unspecified => "(Zoe)".to_string(),
            LogicalTerm::Variable(_) => unreachable!(),
        };
        args_str = format!("(Cons {} {})", term_str, args_str);
    }
    Some(format!("(Pred \"{}\" {})", rel, args_str))
}

// ─── Batch Compute Evaluation ────────────────────────────────────

/// Batch-evaluate a ComputeNode predicate over all domain members by substituting
/// `var` with each member's s-expression. Tries built-in arithmetic first (zero
/// boundary crossing), then batch-dispatches remaining to the compute backend.
///
/// Returns `Some(results)` if evaluation succeeded for ALL members.
/// Returns `None` if any backend request failed — caller should fall back to sequential.
/// Auto-ingests true results into the KB fact store.
fn batch_evaluate_compute_for_members(
    rel: &str,
    args: &[LogicalTerm],
    var: &str,
    members: &[(String, LogicalTerm)],
    subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
) -> Option<Vec<bool>> {
    let mut results = vec![false; members.len()];
    let mut pending: Vec<(usize, Vec<LogicalTerm>)> = Vec::new();

    for (i, (member_sexp, _)) in members.iter().enumerate() {
        let mut s = subs.clone();
        s.insert(var.to_string(), member_sexp.clone());

        // Try arithmetic first (zero overhead, no boundary crossing)
        if let Some(r) = try_arithmetic_evaluation(rel, args, &s) {
            results[i] = r;
            if r {
                let resolved = resolve_args_for_dispatch(args, &s);
                if let Some(sexp) = build_ground_predicate_sexp(rel, &resolved) {
                    assert_sexp(sexp, inner);
                }
            }
        } else {
            let resolved = resolve_args_for_dispatch(args, &s);
            pending.push((i, resolved));
        }
    }

    if pending.is_empty() {
        return Some(results); // All resolved via arithmetic
    }

    // Batch dispatch remaining (non-arithmetic) requests — 1 boundary crossing for N predicates
    let requests: Vec<ComputeRequest> = pending
        .iter()
        .map(|(_, resolved)| ComputeRequest {
            relation: rel.to_string(),
            args: resolved.clone(),
        })
        .collect();
    let batch_results = dispatch_batch_to_backend(&requests);

    for (batch_idx, result) in batch_results.into_iter().enumerate() {
        let member_idx = pending[batch_idx].0;
        match result {
            Ok(r) => {
                results[member_idx] = r;
                if r {
                    if let Some(sexp) = build_ground_predicate_sexp(rel, &pending[batch_idx].1) {
                        assert_sexp(sexp, inner);
                    }
                }
            }
            Err(_) => return None, // Any failure → fall back to sequential
        }
    }
    Some(results)
}

// ─── Query Decomposition ─────────────────────────────────────────

/// Wrap an s-expression with a temporal operator if a tense context is active.
fn wrap_with_tense(tense: Option<&str>, sexp: &str) -> String {
    match tense {
        Some(t) => format!("({} {})", t, sexp),
        None => sexp.to_string(),
    }
}

/// Recursively check whether a formula (identified by `node_id`) is entailed by the KB.
///
/// Handles all FOL node types: conjunction, disjunction, negation, quantifiers,
/// tense/deontic wrappers, count quantifiers, compute nodes, and predicate leaves.
/// Variable substitutions are threaded through `subs` for universal quantifier instantiation.
/// The `tense` parameter propagates a temporal context (Past/Present/Future) through the
/// formula tree — tense nodes set it, leaf predicates wrap their s-expression with it.
fn check_formula_holds(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
) -> Result<bool, String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => Ok(check_formula_holds(buffer, *l, subs, inner, tense)?
            && check_formula_holds(buffer, *r, subs, inner, tense)?),
        LogicNode::OrNode((l, r)) => {
            Ok(check_formula_holds(buffer, *l, subs, inner, tense)?
                || check_formula_holds(buffer, *r, subs, inner, tense)?)
        }
        LogicNode::NotNode(inner_node) => Ok(!check_formula_holds(buffer, *inner_node, subs, inner, tense)?),
        LogicNode::PastNode(inner_node) => check_formula_holds(buffer, *inner_node, subs, inner, Some("Past")),
        LogicNode::PresentNode(inner_node) => check_formula_holds(buffer, *inner_node, subs, inner, Some("Present")),
        LogicNode::FutureNode(inner_node) => check_formula_holds(buffer, *inner_node, subs, inner, Some("Future")),
        LogicNode::ObligatoryNode(inner_node)
        | LogicNode::PermittedNode(inner_node) => check_formula_holds(buffer, *inner_node, subs, inner, tense),
        LogicNode::ExistsNode((v, body)) => {
            let members: Vec<(String, LogicalTerm)> = inner.all_domain_members().to_vec();
            // Fast path: batch dispatch when body is a ComputeNode
            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) = batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner) {
                    if batch_results.iter().any(|r| *r) {
                        return Ok(true);
                    }
                    // No witness among known members — continue to SkolemFn witnesses below
                } else {
                    // Batch dispatch failed — fall through to sequential
                }
            }
            let v_key = v.clone();
            let prev = subs.remove(&v_key);
            for (member_sexp, _) in &members {
                subs.insert(v_key.clone(), member_sexp.clone());
                if check_formula_holds(buffer, *body, subs, inner, tense)? {
                    // Restore previous binding before returning
                    match prev {
                        Some(p) => { subs.insert(v_key, p); }
                        None => { subs.remove(&v_key); }
                    }
                    return Ok(true);
                }
            }
            // Try SkolemFn witnesses
            let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
            for entry in &entries {
                let dep_sexps: Vec<String> = members.iter().map(|(s, _)| s.clone()).collect();
                for combo in CartesianProduct::new(&dep_sexps, entry.dep_count) {
                    let witness_sexp = build_skolem_fn_sexp(&entry.base_name, &combo);
                    subs.insert(v_key.clone(), witness_sexp);
                    if check_formula_holds(buffer, *body, subs, inner, tense)? {
                        match prev {
                            Some(p) => { subs.insert(v_key, p); }
                            None => { subs.remove(&v_key); }
                        }
                        return Ok(true);
                    }
                }
            }
            // Restore previous binding
            match prev {
                Some(p) => { subs.insert(v_key, p); }
                None => { subs.remove(&v_key); }
            }
            Ok(false)
        }
        LogicNode::ForAllNode((v, body)) => {
            let members: Vec<(String, LogicalTerm)> = inner.all_domain_members().to_vec();
            if members.is_empty() {
                return Ok(true);
            }
            // Fast path: batch dispatch when body is a ComputeNode
            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) = batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner) {
                    return Ok(batch_results.iter().all(|r| *r));
                }
                // Batch dispatch failed — fall through to sequential
            }
            let v_key = v.clone();
            let prev = subs.remove(&v_key);
            for (member_sexp, _) in &members {
                subs.insert(v_key.clone(), member_sexp.clone());
                if !check_formula_holds(buffer, *body, subs, inner, tense)? {
                    match prev {
                        Some(p) => { subs.insert(v_key, p); }
                        None => { subs.remove(&v_key); }
                    }
                    return Ok(false);
                }
            }
            match prev {
                Some(p) => { subs.insert(v_key, p); }
                None => { subs.remove(&v_key); }
            }
            Ok(true)
        }
        LogicNode::CountNode((v, count, body)) => {
            let members: Vec<(String, LogicalTerm)> = inner.all_domain_members().to_vec();
            // Fast path: batch dispatch when body is a ComputeNode
            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) = batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner) {
                    let satisfying = batch_results.iter().filter(|r| **r).count() as u32;
                    return Ok(satisfying == *count);
                }
                // Batch dispatch failed — fall through to sequential
            }
            let mut satisfying = 0u32;
            let v_key = v.clone();
            let prev = subs.remove(&v_key);
            for (member_sexp, _) in &members {
                subs.insert(v_key.clone(), member_sexp.clone());
                if check_formula_holds(buffer, *body, subs, inner, tense)? {
                    satisfying += 1;
                }
            }
            match prev {
                Some(p) => { subs.insert(v_key, p); }
                None => { subs.remove(&v_key); }
            }
            Ok(satisfying == *count)
        }
        LogicNode::Predicate((rel, args)) => {
            // Try numeric comparison short-circuit for zmadu/mleca/dunli (timeless)
            if let Some(result) = try_numeric_comparison(rel, args, subs) {
                return Ok(result);
            }
            // Fact index + backward chain check
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let wrapped = wrap_with_tense(tense, &sexp);
            let mut visited = HashSet::new();
            Ok(check_predicate_in_kb(&wrapped, &*inner, 0, &mut visited))
        }
        LogicNode::ComputeNode((rel, args)) => {
            // 1. Try WIT dispatch to external compute backend (wasm32 only)
            let resolved = resolve_args_for_dispatch(args, subs);
            if let Ok(result) = dispatch_to_backend(rel, &resolved) {
                if result {
                    if let Some(sexp) = build_ground_predicate_sexp(rel, &resolved) {
                        assert_sexp(sexp, inner);
                    }
                }
                return Ok(result);
            }
            // 2. Try built-in arithmetic evaluation
            if let Some(result) = try_arithmetic_evaluation(rel, args, subs) {
                if result {
                    if let Some(sexp) = build_ground_predicate_sexp(rel, &resolved) {
                        assert_sexp(sexp, inner);
                    }
                }
                return Ok(result);
            }
            // 3. Fall back to fact index check
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let wrapped = wrap_with_tense(tense, &sexp);
            let mut visited = HashSet::new();
            Ok(check_predicate_in_kb(&wrapped, &*inner, 0, &mut visited))
        }
    }
}

// ─── Witness Extraction ──────────────────────────────────────────

/// Find all satisfying binding sets for existential variables in a formula.
/// Returns Vec<Vec<(variable_name, sexp_value)>> — each inner Vec is one
/// complete assignment. Empty outer Vec means no witnesses found.
fn find_witnesses(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
) -> Result<Vec<Vec<(String, String)>>, String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) => {
            let mut results = Vec::new();

            // 1. Try all known domain members (Const + Desc) as witnesses
            let members: Vec<(String, LogicalTerm)> = inner.all_domain_members().to_vec();
            for (sexp, _) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                let sub_results = find_witnesses(buffer, *body, &mut new_subs, inner, tense)?;
                for mut bindings in sub_results {
                    bindings.push((v.clone(), sexp.clone()));
                    results.push(bindings);
                }
            }

            // 2. Try SkolemFn witnesses from the registry
            let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
            for entry in &entries {
                let dep_sexps: Vec<String> = members.iter().map(|(s, _)| s.clone()).collect();
                for combo in CartesianProduct::new(&dep_sexps, entry.dep_count) {
                    let witness_sexp = build_skolem_fn_sexp(&entry.base_name, &combo);
                    let mut new_subs = subs.clone();
                    new_subs.insert(v.clone(), witness_sexp.clone());
                    let sub_results = find_witnesses(buffer, *body, &mut new_subs, inner, tense)?;
                    for mut bindings in sub_results {
                        bindings.push((v.clone(), witness_sexp.clone()));
                        results.push(bindings);
                    }
                }
            }

            Ok(results)
        }
        // Temporal nodes: set tense context
        LogicNode::PastNode(inner_node) => find_witnesses(buffer, *inner_node, subs, inner, Some("Past")),
        LogicNode::PresentNode(inner_node) => find_witnesses(buffer, *inner_node, subs, inner, Some("Present")),
        LogicNode::FutureNode(inner_node) => find_witnesses(buffer, *inner_node, subs, inner, Some("Future")),
        LogicNode::AndNode((l, r)) => {
            // Cross-product: for each left binding set, check right with merged subs
            let left_results = find_witnesses(buffer, *l, subs, inner, tense)?;
            let mut results = Vec::new();
            for left_bindings in left_results {
                let mut merged_subs = subs.clone();
                for (k, v) in &left_bindings {
                    merged_subs.insert(k.clone(), v.clone());
                }
                let right_results = find_witnesses(buffer, *r, &mut merged_subs, inner, tense)?;
                for right_bindings in right_results {
                    let mut combined = left_bindings.clone();
                    combined.extend(right_bindings);
                    results.push(combined);
                }
            }
            Ok(results)
        }
        LogicNode::OrNode((l, r)) => {
            // Union: collect from both sides
            let mut results = find_witnesses(buffer, *l, subs, inner, tense)?;
            results.extend(find_witnesses(buffer, *r, subs, inner, tense)?);
            Ok(results)
        }
        // For all other node types, delegate to boolean check.
        // If the formula holds, return one empty binding set; otherwise empty.
        _ => {
            if check_formula_holds(buffer, node_id, subs, inner, tense)? {
                Ok(vec![vec![]])
            } else {
                Ok(vec![])
            }
        }
    }
}

// ─── Proof Trace Generation ──────────────────────────────────────

// ─── Backward-Chaining Provenance ────────────────────────────────

/// Maximum backward-chaining depth to prevent infinite recursion on cyclic rules.
const MAX_BACKWARD_CHAIN_DEPTH: usize = 10;

/// Try to explain a derived fact by backward-chaining through universal rules.
/// Returns the proof step index if a derivation is found.
fn try_backward_chain_traced(
    sexp: &str,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    depth: usize,
    memo: &mut HashMap<String, u32>,
) -> Option<u32> {
    // Snapshot rules to avoid borrow conflict
    let rules = collect_matching_rules(sexp, &inner.universal_rules);
    // Pre-tokenize concrete sexp once for all rule matching attempts
    let sexp_tokens = sexp_tokenize(sexp);

    for rule in &rules {
        for concl_tree in &rule.conclusion_trees {
            if let Some(mut bindings) = concl_tree.match_against_tokens(&sexp_tokens)
            {
                let unbound_event_vars: Vec<String> = rule
                    .pattern_var_names
                    .iter()
                    .filter(|pv| pv.starts_with("ev__") && !bindings.contains_key(pv.as_str()))
                    .cloned()
                    .collect();

                if !unbound_event_vars.is_empty() {
                    let members = inner.all_domain_members();
                    let member_sexps: Vec<String> =
                        members.iter().map(|(s, _)| s.clone()).collect();
                    let mut all_candidates: Vec<String> = member_sexps.clone();
                    let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
                    for entry in &entries {
                        for combo in CartesianProduct::new(&member_sexps, entry.dep_count) {
                            all_candidates.push(build_skolem_fn_sexp(&entry.base_name, &combo));
                        }
                    }

                    let mut per_var_candidates: Vec<Vec<String>> = Vec::new();
                    for ev_var in &unbound_event_vars {
                        // Use structural contains_var instead of string contains
                        let single_var_cond_indices: Vec<usize> = rule.condition_trees
                            .iter()
                            .enumerate()
                            .filter(|(_, ct)| {
                                ct.contains_var(ev_var)
                                    && unbound_event_vars
                                        .iter()
                                        .all(|other| other == ev_var || !ct.contains_var(other))
                            })
                            .map(|(i, _)| i)
                            .collect();

                        if single_var_cond_indices.is_empty() {
                            per_var_candidates.push(all_candidates.clone());
                        } else {
                            let filtered: Vec<String> = all_candidates
                                .iter()
                                .filter(|candidate| {
                                    let mut test_bindings = bindings.clone();
                                    test_bindings.insert(ev_var.clone(), (*candidate).clone());
                                    single_var_cond_indices.iter().all(|&idx| {
                                        let cs = rule.condition_trees[idx].substitute(&test_bindings);
                                        check_predicate_in_kb(&cs, &*inner, depth + 1, &mut HashSet::new())
                                    })
                                })
                                .cloned()
                                .collect();
                            per_var_candidates.push(filtered);
                        }
                    }

                    if per_var_candidates.iter().any(|pvc| pvc.is_empty()) {
                        continue;
                    }

                    let mut found = false;
                    for combo in MultiCartesianProduct::new(&per_var_candidates) {
                        for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                            bindings.insert(ev_var.clone(), combo[i].to_string());
                        }
                        let all_hold = rule.condition_trees.iter().all(|ct| {
                            let cs = ct.substitute(&bindings);
                            check_predicate_in_kb(&cs, &*inner, depth + 1, &mut HashSet::new())
                        });
                        if all_hold {
                            found = true;
                            break;
                        }
                        for ev_var in &unbound_event_vars {
                            bindings.remove(ev_var.as_str());
                        }
                    }
                    if !found {
                        continue;
                    }
                }

                // Verify all conditions hold via fact index + backward chain
                let mut all_conditions_hold = true;
                let mut condition_sexps = Vec::new();

                for cond_tree in &rule.condition_trees {
                    let cond_sexp = cond_tree.substitute(&bindings);
                    if check_predicate_in_kb(&cond_sexp, &*inner, depth + 1, &mut HashSet::new()) {
                        condition_sexps.push(cond_sexp);
                    } else {
                        all_conditions_hold = false;
                        break;
                    }
                }

                if !all_conditions_hold {
                    continue;
                }

                // For bare rules (no conditions), just record the derivation
                if rule.condition_templates.is_empty() {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::Derived((rule.label.clone(), sexp.to_string())),
                        holds: true,
                        children: vec![],
                    });
                    return Some(idx);
                }

                // Recursively trace each condition
                let mut child_indices = Vec::new();
                for cond_sexp in &condition_sexps {
                    let child_idx =
                        trace_predicate_provenance(cond_sexp, inner, steps, depth + 1, memo);
                    child_indices.push(child_idx);
                }

                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::Derived((rule.label.clone(), sexp.to_string())),
                    holds: true,
                    children: child_indices,
                });
                return Some(idx);
            }
        }
    }

    // ── Lazy tense lifting (traced) ──
    if let Some((tense, inner_sexp)) = strip_tense_wrapper(sexp) {
        let bare_rules = collect_matching_rules(inner_sexp, &inner.universal_rules);
        let inner_tokens = sexp_tokenize(inner_sexp);
        for rule in &bare_rules {
            for concl_tree in &rule.conclusion_trees {
                let bindings_opt = concl_tree.match_against_tokens(&inner_tokens);
                if bindings_opt.is_none() {
                    continue;
                }
                let mut bindings = bindings_opt.unwrap();

                // Handle unbound event pattern variables
                let unbound_event_vars: Vec<String> = rule
                    .pattern_var_names
                    .iter()
                    .filter(|pv| pv.starts_with("ev__") && !bindings.contains_key(pv.as_str()))
                    .cloned()
                    .collect();

                if !unbound_event_vars.is_empty() {
                    let members = inner.all_domain_members();
                    let member_sexps: Vec<String> = members.iter().map(|(s, _)| s.clone()).collect();
                    let mut all_candidates: Vec<String> = member_sexps.clone();
                    let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
                    for entry in &entries {
                        for combo in CartesianProduct::new(&member_sexps, entry.dep_count) {
                            all_candidates.push(build_skolem_fn_sexp(&entry.base_name, &combo));
                        }
                    }

                    let mut per_var_candidates: Vec<Vec<String>> = Vec::new();
                    for ev_var in &unbound_event_vars {
                        let single_var_cond_indices: Vec<usize> = rule.condition_trees
                            .iter()
                            .enumerate()
                            .filter(|(_, ct)| {
                                ct.contains_var(ev_var)
                                    && unbound_event_vars
                                        .iter()
                                        .all(|other| other == ev_var || !ct.contains_var(other))
                            })
                            .map(|(i, _)| i)
                            .collect();

                        if single_var_cond_indices.is_empty() {
                            per_var_candidates.push(all_candidates.clone());
                        } else {
                            let filtered: Vec<String> = all_candidates
                                .iter()
                                .filter(|candidate| {
                                    let mut test_bindings = bindings.clone();
                                    test_bindings.insert(ev_var.clone(), (*candidate).clone());
                                    single_var_cond_indices.iter().all(|&idx| {
                                        let bare_cs = rule.condition_trees[idx].substitute(&test_bindings);
                                        let tensed_cs = wrap_tense(tense, &bare_cs);
                                        check_predicate_in_kb(&tensed_cs, &*inner, depth + 1, &mut HashSet::new())
                                    })
                                })
                                .cloned()
                                .collect();
                            per_var_candidates.push(filtered);
                        }
                    }

                    if per_var_candidates.iter().any(|pvc| pvc.is_empty()) {
                        continue;
                    }

                    let mut found = false;
                    for combo in MultiCartesianProduct::new(&per_var_candidates) {
                        for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                            bindings.insert(ev_var.clone(), combo[i].to_string());
                        }
                        let all_hold = rule.condition_trees.iter().all(|ct| {
                            let bare_cs = ct.substitute(&bindings);
                            let tensed_cs = wrap_tense(tense, &bare_cs);
                            check_predicate_in_kb(&tensed_cs, &*inner, depth + 1, &mut HashSet::new())
                        });
                        if all_hold {
                            found = true;
                            break;
                        }
                        for ev_var in &unbound_event_vars {
                            bindings.remove(ev_var.as_str());
                        }
                    }
                    if !found {
                        continue;
                    }
                }

                // Check all conditions with tense wrapper applied
                let mut all_conditions_hold = true;
                let mut condition_sexps = Vec::new();
                for cond_tree in &rule.condition_trees {
                    let bare_cs = cond_tree.substitute(&bindings);
                    let tensed_cs = wrap_tense(tense, &bare_cs);
                    if check_predicate_in_kb(&tensed_cs, &*inner, depth + 1, &mut HashSet::new()) {
                        condition_sexps.push(tensed_cs);
                    } else {
                        all_conditions_hold = false;
                        break;
                    }
                }

                if !all_conditions_hold {
                    continue;
                }

                if rule.condition_trees.is_empty() {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::Derived((
                            format!("{} [{}]", rule.label, tense),
                            sexp.to_string(),
                        )),
                        holds: true,
                        children: vec![],
                    });
                    return Some(idx);
                }

                let mut child_indices = Vec::new();
                for cond_sexp in &condition_sexps {
                    let child_idx =
                        trace_predicate_provenance(cond_sexp, inner, steps, depth + 1, memo);
                    child_indices.push(child_idx);
                }

                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::Derived((
                        format!("{} [{}]", rule.label, tense),
                        sexp.to_string(),
                    )),
                    holds: true,
                    children: child_indices,
                });
                return Some(idx);
            }
        }
    }

    None
}

// ─── Non-traced backward-chaining (demand-driven reasoning) ─────────

/// Check if a predicate s-expression holds in the knowledge base.
/// First checks `asserted_sexps` (ground facts), then backward-chains
/// through universal rules. Results are cached in the thread-local
/// `PRED_CACHE` to avoid redundant derivation attempts.
fn check_predicate_in_kb(
    sexp: &str,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<String>,
) -> bool {
    if sexp_is_asserted(sexp, inner) {
        return true;
    }
    // Check the predicate result cache (avoids redundant backward-chain attempts)
    let cached = PRED_CACHE_ENABLED.with(|e| {
        if e.get() {
            PRED_CACHE.with(|c| c.borrow().get(sexp).copied())
        } else {
            None
        }
    });
    if let Some(result) = cached {
        return result;
    }
    let result = try_backward_chain(sexp, inner, depth, visited);
    // Cache the result
    PRED_CACHE_ENABLED.with(|e| {
        if e.get() {
            PRED_CACHE.with(|c| c.borrow_mut().insert(sexp.to_string(), result));
        }
    });
    result
}

/// Maximum backward-chaining depth for non-traced queries.
const MAX_BACKWARD_CHAIN_DEPTH_UNTRACED: usize = 10;

/// Try to derive a predicate s-expression by backward-chaining through universal rules.
/// Non-traced equivalent of `try_backward_chain_traced` — returns `bool` only.
/// Depth-limited and cycle-safe via `visited` set.
///
/// When a rule has unbound event pattern variables (condition-side existentials from
/// Neo-Davidsonian event decomposition), uses per-variable pre-filtering to avoid
/// exponential cartesian product explosion. For each unbound variable, conditions
/// that only involve that one variable are used to filter candidates BEFORE computing
/// the cross-product.
fn try_backward_chain(
    sexp: &str,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<String>,
) -> bool {
    if depth >= MAX_BACKWARD_CHAIN_DEPTH_UNTRACED {
        return false;
    }
    // Prevent infinite recursion on the same sexp
    if !visited.insert(sexp.to_string()) {
        return false;
    }

    let rules_snapshot = collect_matching_rules(sexp, &inner.universal_rules);
    let sexp_tokens = sexp_tokenize(sexp);

    for rule in &rules_snapshot {
        for concl_tree in &rule.conclusion_trees {
            let bindings_opt = concl_tree.match_against_tokens(&sexp_tokens);
            if bindings_opt.is_none() {
                continue;
            }
            let mut bindings = bindings_opt.unwrap();

            // Handle unbound event pattern variables (condition-side existentials)
            let unbound_event_vars: Vec<String> = rule
                .pattern_var_names
                .iter()
                .filter(|pv| pv.starts_with("ev__") && !bindings.contains_key(pv.as_str()))
                .cloned()
                .collect();

            if !unbound_event_vars.is_empty() {
                let members = inner.all_domain_members();
                let member_sexps: Vec<String> = members.iter().map(|(s, _)| s.clone()).collect();
                let mut all_candidates: Vec<String> = member_sexps.clone();
                for entry in &inner.skolem_fn_registry {
                    for combo in CartesianProduct::new(&member_sexps, entry.dep_count) {
                        all_candidates.push(build_skolem_fn_sexp(&entry.base_name, &combo));
                    }
                }

                let mut per_var_candidates: Vec<Vec<String>> = Vec::new();
                for ev_var in &unbound_event_vars {
                    let single_var_cond_indices: Vec<usize> = rule.condition_trees
                        .iter()
                        .enumerate()
                        .filter(|(_, ct)| {
                            ct.contains_var(ev_var)
                                && unbound_event_vars
                                    .iter()
                                    .all(|other| other == ev_var || !ct.contains_var(other))
                        })
                        .map(|(i, _)| i)
                        .collect();

                    if single_var_cond_indices.is_empty() {
                        per_var_candidates.push(all_candidates.clone());
                    } else {
                        let filtered: Vec<String> = all_candidates
                            .iter()
                            .filter(|candidate| {
                                let mut test_bindings = bindings.clone();
                                test_bindings.insert(ev_var.clone(), (*candidate).clone());
                                single_var_cond_indices.iter().all(|&idx| {
                                    let cs = rule.condition_trees[idx].substitute(&test_bindings);
                                    check_predicate_in_kb(&cs, inner, depth + 1, visited)
                                })
                            })
                            .cloned()
                            .collect();
                        per_var_candidates.push(filtered);
                    }
                }

                if per_var_candidates.iter().any(|pvc| pvc.is_empty()) {
                    continue;
                }

                let mut found = false;
                for combo in MultiCartesianProduct::new(&per_var_candidates) {
                    for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                        bindings.insert(ev_var.clone(), combo[i].to_string());
                    }
                    let all_hold = rule.condition_trees.iter().all(|ct| {
                        let cs = ct.substitute(&bindings);
                        check_predicate_in_kb(&cs, inner, depth + 1, visited)
                    });
                    if all_hold {
                        found = true;
                        break;
                    }
                    for ev_var in &unbound_event_vars {
                        bindings.remove(ev_var.as_str());
                    }
                }
                if !found {
                    continue;
                }
            }

            // Verify all conditions hold
            let all_conditions_hold = rule.condition_trees.iter().all(|ct| {
                let cs = ct.substitute(&bindings);
                check_predicate_in_kb(&cs, inner, depth + 1, visited)
            });

            if all_conditions_hold {
                visited.remove(sexp);
                return true;
            }
        }
    }

    // ── Lazy tense lifting ──
    // If the queried sexp is tense-wrapped (e.g., (Past (Pred "danlu" ...))),
    // try bare (untensed) rules with tense applied to conditions on-the-fly.
    if let Some((tense, inner_sexp)) = strip_tense_wrapper(sexp) {
        let bare_rules = collect_matching_rules(inner_sexp, &inner.universal_rules);
        let inner_tokens = sexp_tokenize(inner_sexp);
        for rule in &bare_rules {
            for concl_tree in &rule.conclusion_trees {
                let bindings_opt = concl_tree.match_against_tokens(&inner_tokens);
                if bindings_opt.is_none() {
                    continue;
                }
                let mut bindings = bindings_opt.unwrap();

                // Handle unbound event pattern variables (same as main block)
                let unbound_event_vars: Vec<String> = rule
                    .pattern_var_names
                    .iter()
                    .filter(|pv| pv.starts_with("ev__") && !bindings.contains_key(pv.as_str()))
                    .cloned()
                    .collect();

                if !unbound_event_vars.is_empty() {
                    let members = inner.all_domain_members();
                    let member_sexps: Vec<String> = members.iter().map(|(s, _)| s.clone()).collect();
                    let mut all_candidates: Vec<String> = member_sexps.clone();
                    for entry in &inner.skolem_fn_registry {
                        for combo in CartesianProduct::new(&member_sexps, entry.dep_count) {
                            all_candidates.push(build_skolem_fn_sexp(&entry.base_name, &combo));
                        }
                    }

                    // Per-variable pre-filtering with tense wrapping
                    let mut per_var_candidates: Vec<Vec<String>> = Vec::new();
                    for ev_var in &unbound_event_vars {
                        let single_var_cond_indices: Vec<usize> = rule.condition_trees
                            .iter()
                            .enumerate()
                            .filter(|(_, ct)| {
                                ct.contains_var(ev_var)
                                    && unbound_event_vars
                                        .iter()
                                        .all(|other| other == ev_var || !ct.contains_var(other))
                            })
                            .map(|(i, _)| i)
                            .collect();

                        if single_var_cond_indices.is_empty() {
                            per_var_candidates.push(all_candidates.clone());
                        } else {
                            let filtered: Vec<String> = all_candidates
                                .iter()
                                .filter(|candidate| {
                                    let mut test_bindings = bindings.clone();
                                    test_bindings.insert(ev_var.clone(), (*candidate).clone());
                                    single_var_cond_indices.iter().all(|&idx| {
                                        let bare_cs = rule.condition_trees[idx].substitute(&test_bindings);
                                        let tensed_cs = wrap_tense(tense, &bare_cs);
                                        check_predicate_in_kb(&tensed_cs, inner, depth + 1, visited)
                                    })
                                })
                                .cloned()
                                .collect();
                            per_var_candidates.push(filtered);
                        }
                    }

                    if per_var_candidates.iter().any(|pvc| pvc.is_empty()) {
                        continue;
                    }

                    let mut found = false;
                    for combo in MultiCartesianProduct::new(&per_var_candidates) {
                        for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                            bindings.insert(ev_var.clone(), combo[i].to_string());
                        }
                        let all_hold = rule.condition_trees.iter().all(|ct| {
                            let bare_cs = ct.substitute(&bindings);
                            let tensed_cs = wrap_tense(tense, &bare_cs);
                            check_predicate_in_kb(&tensed_cs, inner, depth + 1, visited)
                        });
                        if all_hold {
                            found = true;
                            break;
                        }
                        for ev_var in &unbound_event_vars {
                            bindings.remove(ev_var.as_str());
                        }
                    }
                    if !found {
                        continue;
                    }
                }

                // Check all conditions with tense wrapper applied
                let all_conditions_hold = rule.condition_trees.iter().all(|ct| {
                    let bare_cs = ct.substitute(&bindings);
                    let tensed_cs = wrap_tense(tense, &bare_cs);
                    check_predicate_in_kb(&tensed_cs, inner, depth + 1, visited)
                });

                if all_conditions_hold {
                    visited.remove(sexp);
                    return true;
                }
            }
        }
    }

    visited.remove(sexp);
    false
}

/// Trace the provenance of a predicate fact known to hold in the KB.
/// Returns the proof step index. Uses `memo` to avoid re-deriving
/// the same sub-proof (turns the proof tree into a DAG).
fn trace_predicate_provenance(
    sexp: &str,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    depth: usize,
    memo: &mut HashMap<String, u32>,
) -> u32 {
    // Check memo — if already proved, emit lightweight reference
    if memo.contains_key(sexp) {
        let idx = steps.len() as u32;
        steps.push(ProofStep {
            rule: ProofRule::ProofRef(sexp.to_string()),
            holds: true,
            children: vec![],
        });
        return idx;
    }

    // 1. Was this fact directly asserted?
    if sexp_is_asserted(sexp, inner) {
        let idx = steps.len() as u32;
        steps.push(ProofStep {
            rule: ProofRule::Asserted(sexp.to_string()),
            holds: true,
            children: vec![],
        });
        memo.insert(sexp.to_string(), idx);
        return idx;
    }

    // 2. Try backward-chaining through universal rules
    if depth < MAX_BACKWARD_CHAIN_DEPTH {
        if let Some(idx) = try_backward_chain_traced(sexp, inner, steps, depth, memo) {
            memo.insert(sexp.to_string(), idx);
            return idx;
        }
    }

    // 3. Fallback: can't trace derivation
    let idx = steps.len() as u32;
    steps.push(ProofStep {
        rule: ProofRule::PredicateCheck(("unknown".to_string(), sexp.to_string())),
        holds: true,
        children: vec![],
    });
    memo.insert(sexp.to_string(), idx);
    idx
}

/// Like `check_formula_holds` but builds a proof trace as it recurses.
/// Returns (result, step_index) where step_index is the index of this
/// step in the `steps` Vec. Uses `memo` to deduplicate predicate proofs.
fn check_formula_holds_traced(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    tense: Option<&str>,
    memo: &mut HashMap<String, u32>,
) -> Result<(bool, u32), String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => {
            let (l_result, l_idx) = check_formula_holds_traced(buffer, *l, subs, inner, steps, tense, memo)?;
            // Short-circuit: if left side fails, skip right side entirely.
            // This prevents exponential blowup when nested existentials try
            // many candidate bindings — wrong candidates fail fast at the
            // first predicate instead of recursing into all remaining branches.
            if !l_result {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::Conjunction,
                    holds: false,
                    children: vec![l_idx],
                });
                return Ok((false, idx));
            }
            let (r_result, r_idx) = check_formula_holds_traced(buffer, *r, subs, inner, steps, tense, memo)?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::Conjunction,
                holds: r_result,
                children: vec![l_idx, r_idx],
            });
            Ok((r_result, idx))
        }
        LogicNode::OrNode((l, r)) => {
            // Try left then right
            let (l_result, l_idx) = check_formula_holds_traced(buffer, *l, subs, inner, steps, tense, memo)?;
            if l_result {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::DisjunctionIntro("left".to_string()),
                    holds: true,
                    children: vec![l_idx],
                });
                return Ok((true, idx));
            }
            let (r_result, r_idx) = check_formula_holds_traced(buffer, *r, subs, inner, steps, tense, memo)?;
            if r_result {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::DisjunctionIntro("right".to_string()),
                    holds: true,
                    children: vec![r_idx],
                });
                return Ok((true, idx));
            }
            // Neither holds
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::DisjunctionIntro("neither".to_string()),
                holds: false,
                children: vec![l_idx, r_idx],
            });
            Ok((false, idx))
        }
        LogicNode::NotNode(inner_node) => {
            let (inner_result, inner_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, tense, memo)?;
            let result = !inner_result;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::Negation,
                holds: result,
                children: vec![inner_idx],
            });
            Ok((result, idx))
        }
        // Temporal nodes: set tense context for inner formula
        LogicNode::PastNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, Some("Past"), memo)?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("past".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::PresentNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, Some("Present"), memo)?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("present".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::FutureNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, Some("Future"), memo)?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("future".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        // Deontic nodes: remain transparent, pass through current tense
        LogicNode::ObligatoryNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, tense, memo)?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("obligatory".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::PermittedNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, tense, memo)?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("permitted".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::ExistsNode((v, body)) => {
            // Pre-screen witnesses using the cheap non-traced path before
            // building expensive proof trees.  This turns O(M^D) expensive
            // traced calls into O(M^D) cheap boolean checks + O(1) trace.
            let members: Vec<(String, LogicalTerm)> = inner.all_domain_members().to_vec();

            // Fast path: batch pre-screen when body is a ComputeNode
            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) = batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner) {
                    if let Some(winner_idx) = batch_results.iter().position(|r| *r) {
                        // Witness found — trace only the successful path
                        let mut new_subs = subs.clone();
                        new_subs.insert(v.clone(), members[winner_idx].0.clone());
                        let (_, body_idx) =
                            check_formula_holds_traced(buffer, *body, &mut new_subs, inner, steps, tense, memo)?;
                        let idx = steps.len() as u32;
                        steps.push(ProofStep {
                            rule: ProofRule::ExistsWitness((v.clone(), members[winner_idx].1.clone())),
                            holds: true,
                            children: vec![body_idx],
                        });
                        return Ok((true, idx));
                    }
                    // No witness among known members — continue to SkolemFn witnesses below
                }
            }

            // 1. Try all known domain members (Const + Desc)
            for (sexp, term) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                // Cheap boolean check first — no ProofStep allocation
                if check_formula_holds(buffer, *body, &mut new_subs, inner, tense)? {
                    // Witness found — now trace only the successful path
                    let (_, body_idx) =
                        check_formula_holds_traced(buffer, *body, &mut new_subs, inner, steps, tense, memo)?;
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::ExistsWitness((v.clone(), term.clone())),
                        holds: true,
                        children: vec![body_idx],
                    });
                    return Ok((true, idx));
                }
            }
            // 2. Try SkolemFn witnesses
            let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
            for entry in &entries {
                let dep_sexps: Vec<String> = members.iter().map(|(s, _)| s.clone()).collect();
                for combo in CartesianProduct::new(&dep_sexps, entry.dep_count) {
                    let witness_sexp = build_skolem_fn_sexp(&entry.base_name, &combo);
                    let mut new_subs = subs.clone();
                    new_subs.insert(v.clone(), witness_sexp.clone());
                    // Cheap boolean check first
                    if check_formula_holds(buffer, *body, &mut new_subs, inner, tense)? {
                        // Witness found — now trace only the successful path
                        let (_, body_idx) =
                            check_formula_holds_traced(buffer, *body, &mut new_subs, inner, steps, tense, memo)?;
                        let idx = steps.len() as u32;
                        steps.push(ProofStep {
                            rule: ProofRule::ExistsWitness((
                                v.clone(),
                                parse_sexp_to_term(&witness_sexp),
                            )),
                            holds: true,
                            children: vec![body_idx],
                        });
                        return Ok((true, idx));
                    }
                }
            }
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ExistsFailed,
                holds: false,
                children: vec![],
            });
            Ok((false, idx))
        }
        LogicNode::ForAllNode((v, body)) => {
            let members: Vec<(String, LogicalTerm)> = inner.all_domain_members().to_vec();
            if members.is_empty() {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::ForallVacuous,
                    holds: true,
                    children: vec![],
                });
                return Ok((true, idx));
            }
            // Fast path: batch pre-screen when body is a ComputeNode.
            // Determines pass/fail for all members in one batch dispatch,
            // then generates proof steps only for the relevant outcome.
            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) = batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner) {
                    if let Some(fail_idx) = batch_results.iter().position(|r| !*r) {
                        // Counterexample found — trace only the failing member
                        let mut new_subs = subs.clone();
                        new_subs.insert(v.clone(), members[fail_idx].0.clone());
                        let (_, body_idx) =
                            check_formula_holds_traced(buffer, *body, &mut new_subs, inner, steps, tense, memo)?;
                        let idx = steps.len() as u32;
                        steps.push(ProofStep {
                            rule: ProofRule::ForallCounterexample(members[fail_idx].1.clone()),
                            holds: false,
                            children: vec![body_idx],
                        });
                        return Ok((false, idx));
                    }
                    // All passed — trace each member for the proof tree
                    let mut child_indices = Vec::new();
                    let mut entity_terms = Vec::new();
                    for (sexp, term) in &members {
                        let mut new_subs = subs.clone();
                        new_subs.insert(v.clone(), sexp.clone());
                        let (_, body_idx) =
                            check_formula_holds_traced(buffer, *body, &mut new_subs, inner, steps, tense, memo)?;
                        child_indices.push(body_idx);
                        entity_terms.push(term.clone());
                    }
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::ForallVerified(entity_terms),
                        holds: true,
                        children: child_indices,
                    });
                    return Ok((true, idx));
                }
            }
            let mut child_indices = Vec::new();
            let mut entity_terms = Vec::new();
            for (sexp, term) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                let (holds, body_idx) =
                    check_formula_holds_traced(buffer, *body, &mut new_subs, inner, steps, tense, memo)?;
                if !holds {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::ForallCounterexample(term.clone()),
                        holds: false,
                        children: vec![body_idx],
                    });
                    return Ok((false, idx));
                }
                child_indices.push(body_idx);
                entity_terms.push(term.clone());
            }
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ForallVerified(entity_terms),
                holds: true,
                children: child_indices,
            });
            Ok((true, idx))
        }
        LogicNode::CountNode((v, count, body)) => {
            let members: Vec<(String, LogicalTerm)> = inner.all_domain_members().to_vec();
            // Fast path: batch pre-screen when body is a ComputeNode
            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) = batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner) {
                    let satisfying = batch_results.iter().filter(|r| **r).count() as u32;
                    let result = satisfying == *count;
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::CountResult((*count, satisfying)),
                        holds: result,
                        children: vec![],
                    });
                    return Ok((result, idx));
                }
            }
            let mut satisfying = 0u32;
            for (sexp, _) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                if check_formula_holds(buffer, *body, &mut new_subs, inner, tense)? {
                    satisfying += 1;
                }
            }
            let result = satisfying == *count;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::CountResult((*count, satisfying)),
                holds: result,
                children: vec![],
            });
            Ok((result, idx))
        }
        LogicNode::Predicate((rel, args)) => {
            // Try numeric comparison short-circuit (timeless)
            if let Some(result) = try_numeric_comparison(rel, args, subs) {
                let detail = format!(
                    "{}({}) = {}",
                    rel,
                    args.iter()
                        .map(|a| match a {
                            LogicalTerm::Number(n) => format!("{}", *n as i64),
                            LogicalTerm::Variable(v) => subs
                                .get(v.as_str())
                                .cloned()
                                .unwrap_or_else(|| v.clone()),
                            _ => "?".to_string(),
                        })
                        .collect::<Vec<_>>()
                        .join(", "),
                    result
                );
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::PredicateCheck(("numeric".to_string(), detail)),
                    holds: result,
                    children: vec![],
                });
                return Ok((result, idx));
            }
            // Fact index + backward chain check with tense wrapping
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let wrapped = wrap_with_tense(tense, &sexp);
            let mut visited = HashSet::new();
            if check_predicate_in_kb(&wrapped, &*inner, 0, &mut visited) {
                // Trace provenance: asserted -> derived -> fallback
                let idx = trace_predicate_provenance(&wrapped, inner, steps, 0, memo);
                Ok((true, idx))
            } else {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::PredicateCheck(("kb".to_string(), wrapped)),
                    holds: false,
                    children: vec![],
                });
                Ok((false, idx))
            }
        }
        LogicNode::ComputeNode((rel, args)) => {
            // 1. Try WIT dispatch
            let resolved = resolve_args_for_dispatch(args, subs);
            if let Ok(result) = dispatch_to_backend(rel, &resolved) {
                if result {
                    if let Some(sexp) = build_ground_predicate_sexp(rel, &resolved) {
                        assert_sexp(sexp, inner);
                    }
                }
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::ComputeCheck(("backend".to_string(), rel.clone())),
                    holds: result,
                    children: vec![],
                });
                return Ok((result, idx));
            }
            // 2. Try built-in arithmetic
            if let Some(result) = try_arithmetic_evaluation(rel, args, subs) {
                if result {
                    if let Some(sexp) = build_ground_predicate_sexp(rel, &resolved) {
                        assert_sexp(sexp, inner);
                    }
                }
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::ComputeCheck(("arithmetic".to_string(), rel.clone())),
                    holds: result,
                    children: vec![],
                });
                return Ok((result, idx));
            }
            // 3. Fall back to fact index check
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let wrapped = wrap_with_tense(tense, &sexp);
            let mut visited = HashSet::new();
            let holds = check_predicate_in_kb(&wrapped, &*inner, 0, &mut visited);
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ComputeCheck(("kb".to_string(), rel.clone())),
                holds,
                children: vec![],
            });
            Ok((holds, idx))
        }
    }
}

// ─── Skolemization Helpers ────────────────────────────────────────

fn collect_exists_for_skolem(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, String>,
    enclosing_universals: &mut Vec<String>,
    counter: &mut usize,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) => {
            if !subs.contains_key(v.as_str()) {
                if enclosing_universals.is_empty() {
                    let sk = format!("sk_{}", *counter);
                    *counter += 1;
                    subs.insert(v.clone(), sk);
                } else {
                    let base = format!("sk_{}", *counter);
                    *counter += 1;
                    let placeholder = format!("{}{}", SKDEP_PREFIX, base);
                    subs.insert(v.clone(), placeholder);
                }
            }
            collect_exists_for_skolem(buffer, *body, subs, enclosing_universals, counter);
        }
        LogicNode::ForAllNode((v, body)) => {
            enclosing_universals.push(v.clone());
            collect_exists_for_skolem(buffer, *body, subs, enclosing_universals, counter);
            enclosing_universals.pop();
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_exists_for_skolem(buffer, *l, subs, enclosing_universals, counter);
            collect_exists_for_skolem(buffer, *r, subs, enclosing_universals, counter);
        }
        LogicNode::NotNode(inner) => {
            collect_exists_for_skolem(buffer, *inner, subs, enclosing_universals, counter);
        }
        LogicNode::CountNode((v, count, body)) => {
            if *count > 0 && !subs.contains_key(v.as_str()) {
                if enclosing_universals.is_empty() {
                    let sk = format!("sk_{}", *counter);
                    *counter += 1;
                    subs.insert(v.clone(), sk);
                } else {
                    let base = format!("sk_{}", *counter);
                    *counter += 1;
                    let placeholder = format!("{}{}", SKDEP_PREFIX, base);
                    subs.insert(v.clone(), placeholder);
                }
            }
            collect_exists_for_skolem(buffer, *body, subs, enclosing_universals, counter);
        }
        LogicNode::Predicate(_) | LogicNode::ComputeNode(_) => {}
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner)
        | LogicNode::ObligatoryNode(inner)
        | LogicNode::PermittedNode(inner) => {
            collect_exists_for_skolem(buffer, *inner, subs, enclosing_universals, counter);
        }
    }
}

// ─── Native Rule Compilation ─────────────────────────────────────

/// Decompose a material conditional body into (conditions, action).
/// Decompose a formula into (conditions, consequent) for material conditional rules.
/// Recognizes `Not(And(conditions)) → consequent` and `Or(Not(conditions), consequent)` patterns.
fn decompose_implication(buffer: &LogicBuffer, body_id: u32) -> Option<(Vec<u32>, u32)> {
    let mut conditions = Vec::new();
    let mut current = body_id;

    loop {
        match &buffer.nodes[current as usize] {
            LogicNode::OrNode((left, right)) => {
                match &buffer.nodes[*left as usize] {
                    LogicNode::NotNode(inner) => {
                        conditions.push(*inner);
                        current = *right;
                    }
                    _ => break,
                }
            }
            _ => break,
        }
    }

    if conditions.is_empty() {
        None
    } else {
        Some((conditions, current))
    }
}

/// Flatten nested And nodes into individual atom node IDs.
#[allow(dead_code)]
fn flatten_conjuncts(buffer: &LogicBuffer, node_id: u32) -> Vec<u32> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => {
            let mut result = flatten_conjuncts(buffer, *l);
            result.extend(flatten_conjuncts(buffer, *r));
            result
        }
        _ => vec![node_id],
    }
}

/// Collect existential variable names from condition-side nodes.
/// These variables should become pattern variables (not dependent Skolems)
/// because condition-side ∃ means "if there exists any term satisfying..."
fn collect_condition_exists(
    buffer: &LogicBuffer,
    node_id: u32,
    exists_vars: &mut HashSet<String>,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) => {
            exists_vars.insert(v.clone());
            collect_condition_exists(buffer, *body, exists_vars);
        }
        LogicNode::AndNode((l, r)) => {
            collect_condition_exists(buffer, *l, exists_vars);
            collect_condition_exists(buffer, *r, exists_vars);
        }
        _ => {}
    }
}

/// Like `flatten_conjuncts` but also strips Exists wrappers for condition-side
/// existential variables, exposing inner predicate atoms for rule matching.
fn flatten_conjuncts_through_exists(
    buffer: &LogicBuffer,
    node_id: u32,
    condition_exists: &HashSet<String>,
) -> Vec<u32> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => {
            let mut result = flatten_conjuncts_through_exists(buffer, *l, condition_exists);
            result.extend(flatten_conjuncts_through_exists(buffer, *r, condition_exists));
            result
        }
        LogicNode::ExistsNode((v, body)) if condition_exists.contains(v.as_str()) => {
            flatten_conjuncts_through_exists(buffer, *body, condition_exists)
        }
        _ => vec![node_id],
    }
}

/// Flatten consequent And-nodes and strip Skolemized Exists wrappers.
fn flatten_consequent(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
) -> Vec<u32> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) if skolem_subs.contains_key(v.as_str()) => {
            flatten_consequent(buffer, *body, skolem_subs)
        }
        LogicNode::AndNode((l, r)) => {
            let mut result = flatten_consequent(buffer, *l, skolem_subs);
            result.extend(flatten_consequent(buffer, *r, skolem_subs));
            result
        }
        _ => vec![node_id],
    }
}

/// Note all Const and Desc terms found in the formula as known domain members.
fn collect_and_note_constants(buffer: &LogicBuffer, node_id: u32, inner: &mut KnowledgeBaseInner) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((_, args)) | LogicNode::ComputeNode((_, args)) => {
            for arg in args {
                match arg {
                    LogicalTerm::Constant(c) => inner.note_entity(c),
                    LogicalTerm::Description(d) => inner.note_description(d),
                    _ => {}
                }
            }
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_and_note_constants(buffer, *l, inner);
            collect_and_note_constants(buffer, *r, inner);
        }
        LogicNode::NotNode(inner_node)
        | LogicNode::ExistsNode((_, inner_node))
        | LogicNode::ForAllNode((_, inner_node)) => {
            collect_and_note_constants(buffer, *inner_node, inner);
        }
        LogicNode::CountNode((_, _, body)) => {
            collect_and_note_constants(buffer, *body, inner);
        }
        LogicNode::PastNode(inner_node)
        | LogicNode::PresentNode(inner_node)
        | LogicNode::FutureNode(inner_node)
        | LogicNode::ObligatoryNode(inner_node)
        | LogicNode::PermittedNode(inner_node) => {
            collect_and_note_constants(buffer, *inner_node, inner);
        }
    }
}

/// Reconstruct an s-expression from a logic buffer node, applying variable
/// substitutions and Skolem replacements. Used for building rule templates.
fn reconstruct_rule_sexp(
    buffer: &LogicBuffer,
    node_id: u32,
    pattern_vars: &HashMap<String, String>,
    ground_skolems: &HashMap<String, String>,
    dependent_skolems: &HashMap<String, (String, Vec<String>)>,
) -> String {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((rel, args)) | LogicNode::ComputeNode((rel, args)) => {
            let mut args_str = String::from("(Nil)");
            for arg in args.iter().rev() {
                let term_str = match arg {
                    LogicalTerm::Variable(v) => {
                        if let Some(pvar) = pattern_vars.get(v.as_str()) {
                            pvar.clone()
                        } else if let Some(sk) = ground_skolems.get(v.as_str()) {
                            format!("(Const \"{}\")", sk)
                        } else if let Some((base, pvars)) = dependent_skolems.get(v.as_str()) {
                            let pvar_refs: Vec<&str> = pvars.iter().map(|s| s.as_str()).collect();
                            build_skolem_fn_sexp(base, &pvar_refs)
                        } else {
                            format!("(Var \"{}\")", v)
                        }
                    }
                    LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
                    LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
                    LogicalTerm::Unspecified => "(Zoe)".to_string(),
                    LogicalTerm::Number(n) => format!("(Num {})", *n as i64),
                };
                args_str = format!("(Cons {} {})", term_str, args_str);
            }
            format!("(Pred \"{}\" {})", rel, args_str)
        }
        LogicNode::ExistsNode((v, body)) => {
            if ground_skolems.contains_key(v.as_str())
                || pattern_vars.contains_key(v.as_str())
                || dependent_skolems.contains_key(v.as_str())
            {
                reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems)
            } else {
                format!(
                    "(Exists \"{}\" {})",
                    v,
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems)
                )
            }
        }
        LogicNode::ForAllNode((v, body)) => {
            if pattern_vars.contains_key(v.as_str()) {
                reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems)
            } else {
                format!(
                    "(ForAll \"{}\" {})",
                    v,
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems)
                )
            }
        }
        LogicNode::AndNode((l, r)) => {
            format!(
                "(And {} {})",
                reconstruct_rule_sexp(buffer, *l, pattern_vars, ground_skolems, dependent_skolems),
                reconstruct_rule_sexp(buffer, *r, pattern_vars, ground_skolems, dependent_skolems)
            )
        }
        LogicNode::OrNode((l, r)) => {
            format!(
                "(Or {} {})",
                reconstruct_rule_sexp(buffer, *l, pattern_vars, ground_skolems, dependent_skolems),
                reconstruct_rule_sexp(buffer, *r, pattern_vars, ground_skolems, dependent_skolems)
            )
        }
        LogicNode::NotNode(inner) => {
            format!(
                "(Not {})",
                reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems, dependent_skolems)
            )
        }
        LogicNode::CountNode((v, count, body)) => {
            if *count == 0 {
                let body_sexp =
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems);
                format!("(ForAll \"{}\" (Not {}))", v, body_sexp)
            } else if ground_skolems.contains_key(v.as_str()) {
                reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems)
            } else {
                let body_sexp =
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems);
                format!("(Exists \"{}\" {})", v, body_sexp)
            }
        }
        LogicNode::PastNode(inner) => {
            format!("(Past {})", reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems, dependent_skolems))
        }
        LogicNode::PresentNode(inner) => {
            format!("(Present {})", reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems, dependent_skolems))
        }
        LogicNode::FutureNode(inner) => {
            format!("(Future {})", reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems, dependent_skolems))
        }
        LogicNode::ObligatoryNode(inner)
        | LogicNode::PermittedNode(inner) => {
            reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems, dependent_skolems)
        }
    }
}

/// Extract the predicate name from a bare s-expression like `(Pred "gerku" ...)`.
fn extract_pred_name(sexp: &str) -> Option<&str> {
    let rest = sexp.strip_prefix("(Pred \"")?;
    let end = rest.find('"')?;
    Some(&rest[..end])
}

/// Extract predicate name from an s-expression, handling tense/deontic wrappers.
/// e.g., `(Past (Pred "gerku" ...))` → `"gerku"`, `(Pred "danlu" ...)` → `"danlu"`.
fn extract_pred_name_deep(sexp: &str) -> Option<&str> {
    // Try direct first.
    if let Some(name) = extract_pred_name(sexp) {
        return Some(name);
    }
    // Try stripping tense/deontic wrappers.
    for prefix in &["(Past ", "(Present ", "(Future ", "(Obligation ", "(Permission "] {
        if let Some(rest) = sexp.strip_prefix(prefix) {
            if let Some(inner) = rest.strip_suffix(')') {
                return extract_pred_name(inner);
            }
        }
    }
    None
}

/// Collect all rules that might match a queried s-expression.
/// Looks up by predicate name + always includes fallback rules.
fn collect_matching_rules(sexp: &str, rules: &HashMap<String, Vec<Arc<UniversalRuleRecord>>>) -> Vec<Arc<UniversalRuleRecord>> {
    let mut result = Vec::new();
    if let Some(pred_name) = extract_pred_name_deep(sexp) {
        if let Some(matching) = rules.get(pred_name) {
            result.extend(matching.iter().map(Arc::clone));
        }
    }
    if let Some(fallback) = rules.get("__fallback__") {
        result.extend(fallback.iter().map(Arc::clone));
    }
    result
}

/// Resolve an interned key to its string and look up in asserted_sexps.
fn sexp_is_asserted(sexp: &str, inner: &KnowledgeBaseInner) -> bool {
    // Fast path: check predicate index first for early exit.
    // If the predicate has no facts at all, skip the interner lookup.
    if let Some(pred_name) = extract_pred_name_deep(sexp) {
        if !inner.predicate_facts.contains_key(pred_name) {
            return false;
        }
    }
    inner.interner.get(sexp).is_some_and(|key| inner.asserted_sexps.contains(&key))
}

/// Intern a vec of s-expression strings, returning interned keys.
fn intern_vec(strings: &[String], interner: &mut SexpInterner) -> Vec<u32> {
    strings.iter().map(|s| interner.intern(s)).collect()
}

/// Create and register a universal rule from string templates.
/// Interns the templates, builds the rule, and indexes it.
fn register_rule(
    inner: &mut KnowledgeBaseInner,
    label: String,
    condition_strings: Vec<String>,
    conclusion_strings: Vec<String>,
    pattern_var_names: Vec<String>,
) {
    let cond_keys = intern_vec(&condition_strings, &mut inner.interner);
    let concl_keys = intern_vec(&conclusion_strings, &mut inner.interner);
    // Pre-parse templates into structural trees for fast matching.
    let condition_trees: Vec<SexpTree> = condition_strings.iter().map(|s| SexpTree::parse(s, &pattern_var_names)).collect();
    let conclusion_trees: Vec<SexpTree> = conclusion_strings.iter().map(|s| SexpTree::parse(s, &pattern_var_names)).collect();
    let rule = UniversalRuleRecord {
        label,
        condition_templates: cond_keys,
        conclusion_templates: concl_keys,
        condition_trees,
        conclusion_trees,
        pattern_var_names,
    };
    add_universal_rule(&mut inner.universal_rules, rule, &inner.interner);
}

/// Intern a string and insert into asserted_sexps + predicate index.
fn assert_sexp(sexp: String, inner: &mut KnowledgeBaseInner) {
    // Extract predicate name before interning (for secondary index).
    let pred_name = extract_pred_name_deep(&sexp).map(|s| s.to_string());
    let key = inner.interner.intern_owned(sexp);
    inner.asserted_sexps.insert(key);
    if let Some(name) = pred_name {
        inner.predicate_facts.entry(name).or_default().insert(key);
    }
}

/// Get all asserted sexp keys for a given predicate name.
fn facts_for_predicate<'a>(pred: &str, inner: &'a KnowledgeBaseInner) -> Option<&'a SortedU32Vec> {
    inner.predicate_facts.get(pred)
}

/// Add a universal rule to the predicate-indexed rule map.
/// Indexes the rule by each conclusion template's predicate name.
/// Resolves interned conclusion keys via the interner to extract predicate names.
fn add_universal_rule(rules: &mut HashMap<String, Vec<Arc<UniversalRuleRecord>>>, rule: UniversalRuleRecord, interner: &SexpInterner) {
    let rc = Arc::new(rule);
    let mut indexed = false;
    for &concl_key in &rc.conclusion_templates {
        let concl_str = interner.resolve(concl_key);
        if let Some(pred_name) = extract_pred_name_deep(concl_str) {
            rules.entry(pred_name.to_string()).or_default().push(Arc::clone(&rc));
            indexed = true;
        }
    }
    if !indexed {
        rules.entry("__fallback__".to_string()).or_default().push(rc);
    }
}

/// Build a human-readable rule label from condition/conclusion template strings.
fn build_rule_label(conditions: &[String], conclusions: &[String]) -> String {
    let cond_names: Vec<&str> = conditions
        .iter()
        .filter_map(|s| extract_pred_name(s))
        .collect();
    let concl_names: Vec<&str> = conclusions
        .iter()
        .filter_map(|s| extract_pred_name(s))
        .collect();
    if cond_names.is_empty() {
        format!("∀ → {}", concl_names.join(" ∧ "))
    } else {
        format!("{} → {}", cond_names.join(" ∧ "), concl_names.join(" ∧ "))
    }
}

/// Compile a ForAll node into a backward-chaining rule.
fn compile_forall_to_rule(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
) -> Result<(), String> {
    // 1. Collect universal variables from nested ForAll nodes
    let mut universals: Vec<String> = Vec::new();
    let mut current = node_id;
    loop {
        match &buffer.nodes[current as usize] {
            LogicNode::ForAllNode((v, body)) => {
                universals.push(v.clone());
                current = *body;
            }
            LogicNode::PastNode(inner_node)
            | LogicNode::PresentNode(inner_node)
            | LogicNode::FutureNode(inner_node)
            | LogicNode::ObligatoryNode(inner_node)
            | LogicNode::PermittedNode(inner_node) => {
                current = *inner_node;
            }
            _ => break,
        }
    }
    let inner_body_id = current;

    // 2. Build pattern variable map: "_v0" -> "x__v0"
    let mut pattern_vars: HashMap<String, String> = universals
        .iter()
        .enumerate()
        .map(|(i, v)| (v.clone(), format!("x__v{}", i)))
        .collect();

    let mut ground_skolems: HashMap<String, String> = skolem_subs
        .iter()
        .filter(|(_, v)| !v.starts_with(SKDEP_PREFIX))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();

    // Entity-only pattern var names (used as SkolemFn dependencies — event vars excluded)
    let pattern_var_names: Vec<String> = universals
        .iter()
        .map(|v| pattern_vars[v].clone())
        .collect();
    let mut dependent_skolems: HashMap<String, (String, Vec<String>)> = skolem_subs
        .iter()
        .filter_map(|(k, v)| {
            v.strip_prefix(SKDEP_PREFIX).map(|base| {
                (k.clone(), (base.to_string(), pattern_var_names.clone()))
            })
        })
        .collect();

    // 3. Decompose inner body
    match decompose_implication(buffer, inner_body_id) {
        Some((condition_ids, consequent_id)) => {
            // ── Condition-side existentials become pattern variables ──
            // In ∀x. [∃e. P(e,x)] → [∃e'. Q(e',x)]:
            //   condition-side ∃e = "match any existing term" → pattern variable
            //   conclusion-side ∃e' = "create new witness" → SkolemFn (stays in dependent_skolems)
            let mut condition_exists_vars: HashSet<String> = HashSet::new();
            for &cid in &condition_ids {
                collect_condition_exists(buffer, cid, &mut condition_exists_vars);
            }
            for var in &condition_exists_vars {
                dependent_skolems.remove(var);
                ground_skolems.remove(var);
                let pvar = format!("ev__{}", var);
                pattern_vars.insert(var.clone(), pvar);
            }

            // Register only conclusion-side dependent Skolems for query-side witness enumeration
            // (condition-side existentials are now pattern variables, not SkolemFn)
            if !dependent_skolems.is_empty() {
                for (_, (base, pvars)) in &dependent_skolems {
                    if !inner.skolem_fn_registry.iter().any(|e| e.base_name == *base) {
                        inner.skolem_fn_registry.push(SkolemFnEntry {
                            base_name: base.clone(),
                            dep_count: pvars.len(),
                        });
                    }
                }
            }

            // Build extended pattern_var_names including event pattern variables
            // (for backward-chaining provenance and temporal lifting)
            let all_pattern_var_names: Vec<String> = {
                let mut names = pattern_var_names.clone();
                for var in &condition_exists_vars {
                    if let Some(pvar) = pattern_vars.get(var) {
                        names.push(pvar.clone());
                    }
                }
                names
            };

            // Flatten conditions through Exists wrappers for condition-side existentials
            let mut all_conditions = Vec::new();
            for cid in &condition_ids {
                all_conditions.extend(flatten_conjuncts_through_exists(
                    buffer,
                    *cid,
                    &condition_exists_vars,
                ));
            }

            let bare_condition_sexps: Vec<String> = all_conditions
                .iter()
                .map(|&cid| {
                    reconstruct_rule_sexp(buffer, cid, &pattern_vars, &ground_skolems, &dependent_skolems)
                })
                .collect();
            let conditions_sexp: Vec<String> = bare_condition_sexps
                .iter()
                .map(|s| format!("(IsTrue {})", s))
                .collect();

            let consequent_atoms = flatten_consequent(buffer, consequent_id, skolem_subs);
            let bare_conclusion_sexps: Vec<String> = consequent_atoms
                .iter()
                .map(|&aid| {
                    reconstruct_rule_sexp(buffer, aid, &pattern_vars, &ground_skolems, &dependent_skolems)
                })
                .collect();
            let actions_sexp: Vec<String> = bare_conclusion_sexps
                .iter()
                .map(|s| format!("(IsTrue {})", s))
                .collect();

            let rule = format!(
                "(rule ({}) ({}))",
                conditions_sexp.join(" "),
                actions_sexp.join(" ")
            );

            if !inner.known_rules.insert(rule.clone()) {
                if !inner.rebuilding {
                    println!(
                        "[Rule] ∀{} already present, skipping",
                        universals.join(",")
                    );
                }
            } else {
                if !inner.rebuilding {
                    println!(
                        "[Rule] Compiled ∀{} to backward-chaining rule",
                        universals.join(",")
                    );
                }

                // Record rule structure for backward-chaining provenance
                let label = build_rule_label(&bare_condition_sexps, &bare_conclusion_sexps);
                register_rule(inner, label, bare_condition_sexps.clone(), bare_conclusion_sexps.clone(), all_pattern_var_names.clone());

                // ── xorlo presupposition: assert restrictor domain is non-empty ──
                // In Lojban, `ro lo P cu Q` presupposes at least one P exists.
                // Create a presupposition Skolem for each restrictor predicate,
                // substituting universal variables with a fresh constant.
                let xp_name = inner.fresh_skolem();
                inner.note_entity(&xp_name);
                let mut xp_subs: HashMap<String, String> = HashMap::new();
                for v in &universals {
                    xp_subs.insert(v.clone(), format!("(Const \"{}\")", xp_name));
                }
                // Merge ground skolems from outer scope
                for (k, v) in &ground_skolems {
                    xp_subs.entry(k.clone()).or_insert_with(|| format!("(Const \"{}\")", v));
                }
                // Add fresh Skolem constants for condition-side existential variables.
                // Event variables (_ev*) are tracked as event entities (not InDomain)
                // to prevent quadratic blowup in guarded conjunction introduction.
                for var in &condition_exists_vars {
                    let ev_sk = inner.fresh_skolem();
                    if var.starts_with("_ev") {
                        inner.note_event_entity(&ev_sk);
                    } else {
                        inner.note_entity(&ev_sk);
                    }
                    xp_subs.insert(var.clone(), format!("(Const \"{}\")", ev_sk));
                }
                for &cid in &all_conditions {
                    let presup = reconstruct_sexp_with_subs(buffer, cid, &xp_subs);
                    // Record xorlo presupposition as asserted for provenance
                    assert_sexp(presup, inner);
                }

                // Tense-lifted variants now generated lazily during backward chaining.
            }
        }
        None => {
            // Register dependent Skolems for bare rules (no condition/conclusion split)
            if !dependent_skolems.is_empty() {
                for (_, (base, pvars)) in &dependent_skolems {
                    if !inner.skolem_fn_registry.iter().any(|e| e.base_name == *base) {
                        inner.skolem_fn_registry.push(SkolemFnEntry {
                            base_name: base.clone(),
                            dep_count: pvars.len(),
                        });
                    }
                }
            }

            let body_sexp =
                reconstruct_rule_sexp(buffer, inner_body_id, &pattern_vars, &ground_skolems, &dependent_skolems);

            let domain_conditions: Vec<String> = universals
                .iter()
                .map(|v| format!("(InDomain {})", pattern_vars[v]))
                .collect();

            let rule = format!(
                "(rule ({}) ((IsTrue {})))",
                domain_conditions.join(" "),
                body_sexp
            );

            if !inner.known_rules.insert(rule.clone()) {
                if !inner.rebuilding {
                    println!(
                        "[Rule] bare ∀{} already present, skipping",
                        universals.join(",")
                    );
                }
            } else {
                if !inner.rebuilding {
                    println!(
                        "[Rule] Compiled bare ∀{} backward-chaining rule",
                        universals.join(",")
                    );
                }

                // Record bare rule structure for backward-chaining provenance
                let label = build_rule_label(&[], &[body_sexp.clone()]);
                register_rule(inner, label, vec![], vec![body_sexp.clone()], pattern_var_names.clone());

                // Tense-lifted variants now generated lazily during backward chaining.
            }
        }
    }

    Ok(())
}

/// Compile Past/Present/Future variants of a universal rule.
/// For each tense T, wraps all conditions and conclusions with T(...).
// Tense-lifted rules are now generated lazily during backward chaining.
// See `strip_tense_wrapper` and the tense-lifting logic in `try_backward_chain`
// and `try_backward_chain_traced`.

/// Strip a tense wrapper from an s-expression, returning (tense_name, inner_sexp).
/// e.g., `(Past (Pred "danlu" ...))` → `Some(("Past", "(Pred \"danlu\" ...)"))`
fn strip_tense_wrapper(sexp: &str) -> Option<(&str, &str)> {
    for tense in &["Past", "Present", "Future"] {
        let prefix = format!("({} ", tense);
        if let Some(rest) = sexp.strip_prefix(&prefix) {
            if let Some(inner) = rest.strip_suffix(')') {
                return Some((tense, inner));
            }
        }
    }
    None
}

/// Wrap an s-expression string with a tense.
fn wrap_tense(tense: &str, sexp: &str) -> String {
    format!("({} {})", tense, sexp)
}

// ─── S-Expression Pattern Matching (for backward-chaining provenance) ────

/// Tokenize an s-expression string into atoms, parens, and quoted strings.
fn sexp_tokenize(s: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(&ch) = chars.peek() {
        match ch {
            '(' => {
                tokens.push("(".to_string());
                chars.next();
            }
            ')' => {
                tokens.push(")".to_string());
                chars.next();
            }
            '"' => {
                chars.next(); // consume opening quote
                let mut quoted = String::from("\"");
                while let Some(&c) = chars.peek() {
                    chars.next();
                    if c == '"' {
                        break;
                    }
                    quoted.push(c);
                }
                quoted.push('"');
                tokens.push(quoted);
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            _ => {
                let mut atom = String::new();
                while let Some(&c) = chars.peek() {
                    if c == '(' || c == ')' || c == '"' || c.is_whitespace() {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                }
                tokens.push(atom);
            }
        }
    }
    tokens
}

/// Extract one complete s-expression starting at position `start` in a token stream.
/// Returns `(end_position, reconstructed_sexp_string)`.
fn extract_sexp_at(tokens: &[String], start: usize) -> Option<(usize, String)> {
    if start >= tokens.len() {
        return None;
    }
    if tokens[start] == "(" {
        let mut depth = 1usize;
        let mut end = start + 1;
        while end < tokens.len() && depth > 0 {
            if tokens[end] == "(" {
                depth += 1;
            } else if tokens[end] == ")" {
                depth -= 1;
            }
            end += 1;
        }
        if depth != 0 {
            return None;
        }
        // Reconstruct the s-expression with proper spacing
        let mut out = String::new();
        for i in start..end {
            if i > start && tokens[i] != ")" && tokens[i - 1] != "(" {
                out.push(' ');
            }
            out.push_str(&tokens[i]);
        }
        Some((end, out))
    } else {
        Some((start + 1, tokens[start].clone()))
    }
}

// ─── S-Expression Reconstruction ─────────────────────────────────

fn reconstruct_sexp_with_subs(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
) -> String {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((rel, args)) | LogicNode::ComputeNode((rel, args)) => {
            let mut args_str = String::from("(Nil)");
            for arg in args.iter().rev() {
                let term_str = match arg {
                    LogicalTerm::Variable(v) => {
                        if let Some(raw_sexp) = subs.get(v.as_str()) {
                            raw_sexp.clone()
                        } else {
                            format!("(Var \"{}\")", v)
                        }
                    }
                    LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
                    LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
                    LogicalTerm::Unspecified => "(Zoe)".to_string(),
                    LogicalTerm::Number(n) => format!("(Num {})", *n as i64),
                };
                args_str = format!("(Cons {} {})", term_str, args_str);
            }
            format!("(Pred \"{}\" {})", rel, args_str)
        }
        LogicNode::ExistsNode((v, body)) => {
            if subs.contains_key(v.as_str()) {
                reconstruct_sexp_with_subs(buffer, *body, subs)
            } else {
                format!(
                    "(Exists \"{}\" {})",
                    v,
                    reconstruct_sexp_with_subs(buffer, *body, subs)
                )
            }
        }
        LogicNode::ForAllNode((v, body)) => {
            if subs.contains_key(v.as_str()) {
                reconstruct_sexp_with_subs(buffer, *body, subs)
            } else {
                format!(
                    "(ForAll \"{}\" {})",
                    v,
                    reconstruct_sexp_with_subs(buffer, *body, subs)
                )
            }
        }
        LogicNode::AndNode((l, r)) => {
            format!(
                "(And {} {})",
                reconstruct_sexp_with_subs(buffer, *l, subs),
                reconstruct_sexp_with_subs(buffer, *r, subs)
            )
        }
        LogicNode::OrNode((l, r)) => {
            format!(
                "(Or {} {})",
                reconstruct_sexp_with_subs(buffer, *l, subs),
                reconstruct_sexp_with_subs(buffer, *r, subs)
            )
        }
        LogicNode::NotNode(inner) => {
            format!("(Not {})", reconstruct_sexp_with_subs(buffer, *inner, subs))
        }
        LogicNode::CountNode((v, count, body)) => {
            if *count == 0 {
                let body_sexp = reconstruct_sexp_with_subs(buffer, *body, subs);
                format!("(ForAll \"{}\" (Not {}))", v, body_sexp)
            } else {
                if subs.contains_key(v.as_str()) {
                    reconstruct_sexp_with_subs(buffer, *body, subs)
                } else {
                    let body_sexp = reconstruct_sexp_with_subs(buffer, *body, subs);
                    format!("(Exists \"{}\" {})", v, body_sexp)
                }
            }
        }
        LogicNode::PastNode(inner) => {
            format!("(Past {})", reconstruct_sexp_with_subs(buffer, *inner, subs))
        }
        LogicNode::PresentNode(inner) => {
            format!("(Present {})", reconstruct_sexp_with_subs(buffer, *inner, subs))
        }
        LogicNode::FutureNode(inner) => {
            format!("(Future {})", reconstruct_sexp_with_subs(buffer, *inner, subs))
        }
        LogicNode::ObligatoryNode(inner)
        | LogicNode::PermittedNode(inner) => reconstruct_sexp_with_subs(buffer, *inner, subs),
    }
}

/// Generate extra Skolem witnesses for Count(x, n, body) where n > 1.
fn generate_count_extra_witnesses(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::CountNode((v, count, body)) => {
            if *count > 1 {
                for _ in 1..*count {
                    let extra_sk = inner.fresh_skolem();
                    inner.note_entity(&extra_sk);

                    let mut extra_subs: HashMap<String, String> = skolem_subs
                        .iter()
                        .filter(|(_, sv)| !sv.starts_with(SKDEP_PREFIX))
                        .map(|(k, sv)| (k.clone(), format!("(Const \"{}\")", sv)))
                        .collect();
                    extra_subs.insert(v.clone(), format!("(Const \"{}\")", extra_sk));

                    let sexp = reconstruct_sexp_with_subs(buffer, *body, &extra_subs);
                    assert_sexp(sexp, inner);
                }
            }
            generate_count_extra_witnesses(buffer, *body, skolem_subs, inner);
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            generate_count_extra_witnesses(buffer, *l, skolem_subs, inner);
            generate_count_extra_witnesses(buffer, *r, skolem_subs, inner);
        }
        LogicNode::NotNode(inner_node)
        | LogicNode::ExistsNode((_, inner_node))
        | LogicNode::ForAllNode((_, inner_node)) => {
            generate_count_extra_witnesses(buffer, *inner_node, skolem_subs, inner);
        }
        LogicNode::PastNode(inner_node)
        | LogicNode::PresentNode(inner_node)
        | LogicNode::FutureNode(inner_node)
        | LogicNode::ObligatoryNode(inner_node)
        | LogicNode::PermittedNode(inner_node) => {
            generate_count_extra_witnesses(buffer, *inner_node, skolem_subs, inner);
        }
        LogicNode::Predicate(_) | LogicNode::ComputeNode(_) => {}
    }
}

#[cfg(target_arch = "wasm32")]
bindings::export!(LogjiComponent with_types_in bindings);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bindings::lojban::nibli::logic_types::{
        LogicBuffer, LogicNode, LogicalTerm, ProofRule, ProofTrace,
    };

    /// Helper: build a Predicate node with the given relation and args.
    fn pred(nodes: &mut Vec<LogicNode>, rel: &str, args: Vec<LogicalTerm>) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::Predicate((rel.to_string(), args)));
        id
    }

    /// Helper: build a NotNode wrapping the given node.
    fn not(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::NotNode(inner));
        id
    }

    /// Helper: build an OrNode.
    fn or(nodes: &mut Vec<LogicNode>, left: u32, right: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::OrNode((left, right)));
        id
    }

    /// Helper: build a ForAllNode.
    fn forall(nodes: &mut Vec<LogicNode>, var: &str, body: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::ForAllNode((var.to_string(), body)));
        id
    }

    /// Helper: build an ExistsNode.
    fn exists(nodes: &mut Vec<LogicNode>, var: &str, body: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::ExistsNode((var.to_string(), body)));
        id
    }

    /// Helper: build an AndNode.
    fn and(nodes: &mut Vec<LogicNode>, left: u32, right: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::AndNode((left, right)));
        id
    }

    fn new_kb() -> KnowledgeBase {
        KnowledgeBase {
            inner: RefCell::new(KnowledgeBaseInner::new()),
        }
    }

    fn assert_buf(kb: &KnowledgeBase, buf: LogicBuffer) {
        kb.assert_fact_inner(buf, String::new()).unwrap();
    }

    fn query(kb: &KnowledgeBase, buf: LogicBuffer) -> bool {
        kb.query_entailment_inner(buf).unwrap()
    }

    /// Build "la .X. P" -> Pred("P", [Const("X"), Zoe])
    fn make_assertion(entity: &str, predicate: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            predicate,
            vec![LogicalTerm::Constant(entity.to_string()), LogicalTerm::Unspecified],
        );
        LogicBuffer { nodes, roots: vec![root] }
    }

    /// Build "ro lo P cu Q" -> ForAll("_v0", Or(Not(Pred("P", [Var("_v0"), Zoe])), Pred("Q", [Var("_v0"), Zoe])))
    fn make_universal(restrictor: &str, consequent: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let restrict = pred(
            &mut nodes,
            restrictor,
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let body = pred(
            &mut nodes,
            consequent,
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let neg = not(&mut nodes, restrict);
        let disj = or(&mut nodes, neg, body);
        let root = forall(&mut nodes, "_v0", disj);
        LogicBuffer { nodes, roots: vec![root] }
    }

    fn make_query(entity: &str, predicate: &str) -> LogicBuffer {
        make_assertion(entity, predicate)
    }

    #[test]
    fn test_native_rule_simple_universal() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_native_rule_entity_after_rule() {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert!(query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_native_rule_selective_application() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("bob", "mlatu"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(query(&kb, make_query("alis", "danlu")));
        assert!(!query(&kb, make_query("bob", "danlu")));
    }

    // ─── Existential introduction (xorlo presupposition) ─────────

    #[test]
    fn test_xorlo_presupposition_basic() {
        // ro lo gerku cu danlu → presupposition: ∃x. gerku(x)
        // Query ∃x. gerku(x) should find the presupposition Skolem
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));

        // Query: ∃x. gerku(x)
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_xorlo_presupposition_consequent() {
        // ro lo gerku cu danlu → presupposition creates sk entity → rule fires
        // Query ∃x. danlu(x) should find the derived fact
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "danlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_xorlo_presupposition_conjunction() {
        // THE BUG FIX: ro lo gerku cu danlu, then ? lo gerku cu danlu
        // (∃x. gerku(x) ∧ danlu(x)) should be TRUE
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));

        let mut nodes = Vec::new();
        let p1 = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let p2 = pred(
            &mut nodes,
            "danlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let conj = and(&mut nodes, p1, p2);
        let root = exists(&mut nodes, "x", conj);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_xorlo_presupposition_with_real_entity() {
        // Real entity + presupposition Skolem both satisfy the query
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_assertion("alis", "gerku"));

        // Both alis and the presupposition Skolem are in the KB
        assert!(query(&kb, make_query("alis", "danlu")));

        // Witness search should find both alis and the presupposition Skolem
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "danlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });
        assert!(results.len() >= 2); // alis + presupposition Skolem
    }

    #[test]
    fn test_xorlo_presupposition_transitive() {
        // ro lo gerku cu danlu, ro lo danlu cu xanlu
        // Each universal creates its own presupposition Skolem
        // Query ∃x. xanlu(x) should find witnesses via chain
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("danlu", "xanlu"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "xanlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_xorlo_presupposition_no_false_positives() {
        // ro lo gerku cu danlu should NOT make mlatu(x) exist
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        assert!(!query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_native_rule_transitive_chain() {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("danlu", "xanlu"));
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert!(query(&kb, make_query("alis", "xanlu")));
    }

    #[test]
    fn test_native_rule_multiple_entities() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("bob", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(query(&kb, make_query("alis", "danlu")));
        assert!(query(&kb, make_query("bob", "danlu")));
    }

    #[test]
    fn test_native_rule_negated_universal() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));

        let mut nodes = Vec::new();
        let restrict = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let body_pred = pred(
            &mut nodes,
            "danlu",
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let neg_body = not(&mut nodes, body_pred);
        let neg_restrict = not(&mut nodes, restrict);
        let disj = or(&mut nodes, neg_restrict, neg_body);
        let root = forall(&mut nodes, "_v0", disj);
        assert_buf(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(!query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_native_rule_duplicate_rule_no_panic() {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert!(query(&kb, make_query("alis", "danlu")));
    }

    // ─── Dependent Skolem (Phase B) Tests ────────────────────────────

    fn make_dependent_skolem_universal(restrictor: &str, consequent: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let restrict = pred(
            &mut nodes,
            restrictor,
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let body = pred(
            &mut nodes,
            consequent,
            vec![
                LogicalTerm::Variable("_v0".to_string()),
                LogicalTerm::Variable("_v1".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let ex = exists(&mut nodes, "_v1", body);
        let neg = not(&mut nodes, restrict);
        let disj = or(&mut nodes, neg, ex);
        let root = forall(&mut nodes, "_v0", disj);
        LogicBuffer { nodes, roots: vec![root] }
    }

    fn make_exists_query(entity: &str, predicate: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            predicate,
            vec![
                LogicalTerm::Constant(entity.to_string()),
                LogicalTerm::Variable("_v1".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = exists(&mut nodes, "_v1", body);
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_dependent_skolem_native_rule() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
        assert!(query(&kb, make_exists_query("alis", "zdani")));
    }

    #[test]
    fn test_dependent_skolem_entity_after_rule() {
        let kb = new_kb();
        assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert!(query(&kb, make_exists_query("alis", "zdani")));
    }

    #[test]
    fn test_dependent_skolem_query_existential() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
        assert!(query(&kb, make_exists_query("alis", "zdani")));
        assert!(!query(&kb, make_exists_query("bob", "zdani")));
    }

    #[test]
    fn test_skolem_fn_multiple_entities() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_assertion("bob", "prenu"));
        assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
        assert!(query(&kb, make_exists_query("alis", "zdani")));
        assert!(query(&kb, make_exists_query("bob", "zdani")));
    }

    #[test]
    fn test_skolem_fn_registry_populated() {
        let kb = new_kb();
        assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
        let inner = kb.inner.borrow();
        assert!(!inner.skolem_fn_registry.is_empty(), "SkolemFn registry should have entries");
        assert_eq!(inner.skolem_fn_registry[0].base_name, "sk_0");
        assert_eq!(inner.skolem_fn_registry[0].dep_count, 1);
    }

    // ─── Multi-Dependency SkolemFn Tests ─────────────────────────

    /// Build: ∀_v0. ∀_v1. (¬(prenu(_v0, zo'e) ∧ mlatu(_v1, zo'e)) ∨ ∃_v2. zdani(_v0, _v1, _v2))
    /// Meaning: for all persons x and cats y, there exists a z such that zdani(x, y, z).
    fn make_multi_dep_skolem_universal() -> LogicBuffer {
        let mut nodes = Vec::new();
        let p = pred(
            &mut nodes,
            "prenu",
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let q = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Variable("_v1".to_string()), LogicalTerm::Unspecified],
        );
        let conj = and(&mut nodes, p, q);
        let body = pred(
            &mut nodes,
            "zdani",
            vec![
                LogicalTerm::Variable("_v0".to_string()),
                LogicalTerm::Variable("_v1".to_string()),
                LogicalTerm::Variable("_v2".to_string()),
            ],
        );
        let ex = exists(&mut nodes, "_v2", body);
        let neg = not(&mut nodes, conj);
        let disj = or(&mut nodes, neg, ex);
        let inner_forall = forall(&mut nodes, "_v1", disj);
        let root = forall(&mut nodes, "_v0", inner_forall);
        LogicBuffer { nodes, roots: vec![root] }
    }

    /// Query: ∃_v2. zdani(entity_a, entity_b, _v2)
    fn make_multi_dep_exists_query(entity_a: &str, entity_b: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "zdani",
            vec![
                LogicalTerm::Constant(entity_a.to_string()),
                LogicalTerm::Constant(entity_b.to_string()),
                LogicalTerm::Variable("_v2".to_string()),
            ],
        );
        let root = exists(&mut nodes, "_v2", body);
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_multi_dep_skolem_two_universals() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_assertion("felix", "mlatu"));
        assert_buf(&kb, make_multi_dep_skolem_universal());
        // ∃z. zdani(alis, felix, z) should be TRUE via SkolemFn with 2 deps
        assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
    }

    #[test]
    fn test_multi_dep_skolem_registry() {
        let kb = new_kb();
        assert_buf(&kb, make_multi_dep_skolem_universal());
        let inner = kb.inner.borrow();
        assert!(!inner.skolem_fn_registry.is_empty());
        assert_eq!(inner.skolem_fn_registry[0].dep_count, 2);
    }

    #[test]
    fn test_multi_dep_skolem_different_entities() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_assertion("bob", "prenu"));
        assert_buf(&kb, make_assertion("felix", "mlatu"));
        assert_buf(&kb, make_assertion("garfield", "mlatu"));
        assert_buf(&kb, make_multi_dep_skolem_universal());
        // All combinations of person × cat should have zdani witnesses
        assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
        assert!(query(&kb, make_multi_dep_exists_query("alis", "garfield")));
        assert!(query(&kb, make_multi_dep_exists_query("bob", "felix")));
        assert!(query(&kb, make_multi_dep_exists_query("bob", "garfield")));
        // Non-prenu or non-mlatu entities should NOT have zdani witnesses
        assert!(!query(&kb, make_multi_dep_exists_query("felix", "alis")));
    }

    #[test]
    fn test_multi_dep_skolem_rule_before_facts() {
        let kb = new_kb();
        // Rule first, then facts
        assert_buf(&kb, make_multi_dep_skolem_universal());
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_assertion("felix", "mlatu"));
        assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
    }

    // ─── Numeric Comparison Tests ────────────────────────────────

    /// Build a comparison predicate: Pred(rel, [Num(a), Num(b), Zoe, ...])
    fn make_numeric_pred(nodes: &mut Vec<LogicNode>, relation: &str, a: f64, b: f64) -> u32 {
        let mut args = vec![
            LogicalTerm::Number(a),
            LogicalTerm::Number(b),
            LogicalTerm::Unspecified,
        ];
        // zmadu and mleca have arity 4; dunli has arity 3
        if relation == "zmadu" || relation == "mleca" {
            args.push(LogicalTerm::Unspecified);
        }
        pred(nodes, relation, args)
    }

    fn make_numeric_query(relation: &str, a: f64, b: f64) -> LogicBuffer {
        let mut nodes = Vec::new();
        let root = make_numeric_pred(&mut nodes, relation, a, b);
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_zmadu_numeric_true() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("zmadu", 2.0, 1.0)));
    }

    #[test]
    fn test_zmadu_numeric_false() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("zmadu", 1.0, 2.0)));
    }

    #[test]
    fn test_zmadu_numeric_equal_false() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("zmadu", 2.0, 2.0)));
    }

    #[test]
    fn test_mleca_numeric_true() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("mleca", 1.0, 2.0)));
    }

    #[test]
    fn test_mleca_numeric_false() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("mleca", 2.0, 1.0)));
    }

    #[test]
    fn test_dunli_numeric_true() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("dunli", 5.0, 5.0)));
    }

    #[test]
    fn test_dunli_numeric_false() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("dunli", 5.0, 3.0)));
    }

    #[test]
    fn test_zmadu_negated() {
        let kb = new_kb();
        // NOT (1 > 2) should be TRUE
        let mut nodes = Vec::new();
        let cmp = make_numeric_pred(&mut nodes, "zmadu", 1.0, 2.0);
        let root = not(&mut nodes, cmp);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_zmadu_non_numeric_fallback() {
        let kb = new_kb();
        // Non-numeric zmadu: assert then query via standard KB path
        let mut a_nodes = Vec::new();
        let a_root = pred(
            &mut a_nodes,
            "zmadu",
            vec![
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Unspecified,
                LogicalTerm::Unspecified,
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![a_root] });

        let mut q_nodes = Vec::new();
        let q_root = pred(
            &mut q_nodes,
            "zmadu",
            vec![
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Unspecified,
                LogicalTerm::Unspecified,
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_zmadu_large_numbers() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("zmadu", 1_000_000.0, 999_999.0)));
    }

    #[test]
    fn test_zmadu_negative_numbers() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("zmadu", -1.0, -2.0)));
        assert!(!query(&kb, make_numeric_query("zmadu", -2.0, -1.0)));
    }

    // ─── ComputeNode Tests ───────────────────────────────────────

    /// Helper: build a ComputeNode with the given relation and args.
    fn compute(nodes: &mut Vec<LogicNode>, rel: &str, args: Vec<LogicalTerm>) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::ComputeNode((rel.to_string(), args)));
        id
    }

    /// Helper: build a ComputeNode query buffer for arithmetic predicates.
    fn make_compute_query(rel: &str, x1: f64, x2: f64, x3: f64) -> LogicBuffer {
        let mut nodes = Vec::new();
        let root = compute(
            &mut nodes,
            rel,
            vec![
                LogicalTerm::Number(x1),
                LogicalTerm::Number(x2),
                LogicalTerm::Number(x3),
            ],
        );
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    }

    #[test]
    fn test_compute_pilji_true() {
        let kb = new_kb();
        // 6 = 2 * 3
        assert!(query(&kb, make_compute_query("pilji", 6.0, 2.0, 3.0)));
    }

    #[test]
    fn test_compute_pilji_false() {
        let kb = new_kb();
        // 7 != 2 * 3
        assert!(!query(&kb, make_compute_query("pilji", 7.0, 2.0, 3.0)));
    }

    #[test]
    fn test_compute_sumji_true() {
        let kb = new_kb();
        // 5 = 2 + 3
        assert!(query(&kb, make_compute_query("sumji", 5.0, 2.0, 3.0)));
    }

    #[test]
    fn test_compute_sumji_false() {
        let kb = new_kb();
        // 4 != 2 + 3
        assert!(!query(&kb, make_compute_query("sumji", 4.0, 2.0, 3.0)));
    }

    #[test]
    fn test_compute_dilcu_true() {
        let kb = new_kb();
        // 3 = 6 / 2
        assert!(query(&kb, make_compute_query("dilcu", 3.0, 6.0, 2.0)));
    }

    #[test]
    fn test_compute_dilcu_division_by_zero() {
        let kb = new_kb();
        // x / 0 is always false
        assert!(!query(&kb, make_compute_query("dilcu", 0.0, 5.0, 0.0)));
    }

    #[test]
    fn test_compute_negated() {
        let kb = new_kb();
        // NOT(7 = 2 * 3) → TRUE (because 7 != 6)
        let mut nodes = Vec::new();
        let inner = compute(
            &mut nodes,
            "pilji",
            vec![
                LogicalTerm::Number(7.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        let root = not(&mut nodes, inner);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_compute_node_kb_fallback() {
        // ComputeNode with non-arithmetic predicate falls back to KB lookup
        let kb = new_kb();

        // Assert: klama(alis, zarci) as a regular fact
        let mut a_nodes = Vec::new();
        let a_root = pred(
            &mut a_nodes,
            "klama",
            vec![
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Constant("zarci".to_string()),
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![a_root] });

        // Query as ComputeNode — unknown to arithmetic, should fall through to KB lookup
        let mut q_nodes = Vec::new();
        let q_root = compute(
            &mut q_nodes,
            "klama",
            vec![
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Constant("zarci".to_string()),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    // ── Material conditional / modus ponens tests ──

    /// Helper: build "ganai la .X. P gi la .X. Q" as Or(Not(Pred(P, [X])), Pred(Q, [X]))
    /// This is the logic IR that sentence connective `ganai...gi` produces.
    fn make_material_conditional(entity: &str, antecedent: &str, consequent: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let ante = pred(
            &mut nodes,
            antecedent,
            vec![LogicalTerm::Constant(entity.to_string()), LogicalTerm::Unspecified],
        );
        let cons = pred(
            &mut nodes,
            consequent,
            vec![LogicalTerm::Constant(entity.to_string()), LogicalTerm::Unspecified],
        );
        let neg_ante = not(&mut nodes, ante);
        let root = or(&mut nodes, neg_ante, cons);
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_material_conditional_modus_ponens() {
        // ganai la .sol. barda gi la .sol. tsali
        // + la .sol. barda
        // → la .sol. tsali should be TRUE via modus ponens
        let kb = new_kb();
        assert_buf(&kb, make_assertion("sol", "barda"));
        assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
        assert!(query(&kb, make_query("sol", "tsali")));
    }

    #[test]
    fn test_material_conditional_modus_ponens_reversed_order() {
        // Assert the conditional FIRST, then the antecedent
        let kb = new_kb();
        assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
        assert_buf(&kb, make_assertion("sol", "barda"));
        assert!(query(&kb, make_query("sol", "tsali")));
    }

    #[test]
    fn test_material_conditional_modus_tollens() {
        // ganai la .sol. barda gi la .sol. tsali
        // + la .sol. na tsali (Not tsali)
        // → la .sol. na barda (Not barda) via modus tollens
        let kb = new_kb();
        assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));

        // Assert Not(tsali(sol))
        let mut neg_nodes = Vec::new();
        let inner = pred(
            &mut neg_nodes,
            "tsali",
            vec![LogicalTerm::Constant("sol".to_string()), LogicalTerm::Unspecified],
        );
        let root = not(&mut neg_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: neg_nodes, roots: vec![root] });

        // Query: barda(sol) should be FALSE (modus tollens derives Not(barda(sol)))
        assert!(!query(&kb, make_query("sol", "barda")));
    }

    #[test]
    fn test_material_conditional_antecedent_not_satisfied() {
        // ganai la .sol. barda gi la .sol. tsali
        // (no barda assertion)
        // → la .sol. tsali should be FALSE (antecedent not satisfied)
        let kb = new_kb();
        assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
        assert!(!query(&kb, make_query("sol", "tsali")));
    }

    #[test]
    fn test_material_conditional_chain() {
        // ganai A gi B, ganai B gi C, assert A → derive C
        let kb = new_kb();
        assert_buf(&kb, make_assertion("sol", "tarci"));
        assert_buf(&kb, make_material_conditional("sol", "tarci", "gusni"));
        assert_buf(&kb, make_material_conditional("sol", "gusni", "melbi"));
        assert!(query(&kb, make_query("sol", "melbi")));
    }

    // ── Deontic predicate tests ──

    /// Helper: build a 3-place deontic assertion: Pred(rel, [Const(entity), Const(action), Zoe])
    fn make_deontic_assertion(entity: &str, relation: &str, action: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            relation,
            vec![
                LogicalTerm::Constant(entity.to_string()),
                LogicalTerm::Constant(action.to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_deontic_bilga_assert_query() {
        // bilga(alis, klama, Zoe) — Alice is obligated to go
        let kb = new_kb();
        assert_buf(&kb, make_deontic_assertion("alis", "bilga", "klama"));
        assert!(query(&kb, make_deontic_assertion("alis", "bilga", "klama")));
        assert!(!query(&kb, make_deontic_assertion("bob", "bilga", "klama")));
    }

    #[test]
    fn test_deontic_curmi_assert_query() {
        // curmi(alis, klama, Zoe) — Alice is permitted to go
        let kb = new_kb();
        assert_buf(&kb, make_deontic_assertion("alis", "curmi", "klama"));
        assert!(query(&kb, make_deontic_assertion("alis", "curmi", "klama")));
        assert!(!query(&kb, make_deontic_assertion("alis", "curmi", "tavla")));
    }

    #[test]
    fn test_deontic_nitcu_assert_query() {
        // nitcu(alis, klama, Zoe) — Alice needs to go
        let kb = new_kb();
        assert_buf(&kb, make_deontic_assertion("alis", "nitcu", "klama"));
        assert!(query(&kb, make_deontic_assertion("alis", "nitcu", "klama")));
        assert!(!query(&kb, make_deontic_assertion("alis", "nitcu", "tavla")));
    }

    #[test]
    fn test_deontic_universal_obligation() {
        // ∀x. prenu(x) → bilga(x, Zoe, Zoe) — all people are obligated
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_universal("prenu", "bilga"));
        assert!(query(&kb, make_query("alis", "bilga")));
        assert!(!query(&kb, make_query("bob", "bilga")));
    }

    #[test]
    fn test_deontic_conditional_chain() {
        // ganai bilga(sol) gi nitcu(sol) — if obligated then needed
        // + bilga(sol) → nitcu(sol) via modus ponens
        let kb = new_kb();
        assert_buf(&kb, make_assertion("sol", "bilga"));
        assert_buf(&kb, make_material_conditional("sol", "bilga", "nitcu"));
        assert!(query(&kb, make_query("sol", "nitcu")));
    }

    // ── Deontic attitudinal tests ──

    /// Helper: build an ObligatoryNode wrapping the given node.
    fn obligatory(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::ObligatoryNode(inner));
        id
    }

    /// Helper: build a PermittedNode wrapping the given node.
    fn permitted(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::PermittedNode(inner));
        id
    }

    #[test]
    fn test_obligatory_assert_query() {
        // Assert Obligatory(klama(alis, zo'e)) then query exact → TRUE
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = obligatory(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = obligatory(&mut q_nodes, q_inner);
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_permitted_assert_query() {
        // Assert Permitted(klama(alis, zo'e)) then query exact → TRUE
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = permitted(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = permitted(&mut q_nodes, q_inner);
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_obligatory_transparent() {
        // Assert Obligatory(klama(alis, zo'e)) then query without wrapper → TRUE (transparent)
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = obligatory(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        // Query without obligatory wrapper → still TRUE (pass-through)
        assert!(query(&kb, make_query("alis", "klama")));
    }

    // ── Compute result ingestion tests ──

    #[test]
    fn test_compute_result_ingested_into_kb() {
        let kb = new_kb();

        // Query pilji(6, 2, 3) via ComputeNode → TRUE (built-in arithmetic)
        // This should auto-ingest the fact into the KB
        let mut q_nodes = Vec::new();
        let q_root = compute(
            &mut q_nodes,
            "pilji",
            vec![
                LogicalTerm::Number(6.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));

        // Now query the SAME fact as a plain Predicate (not ComputeNode)
        // It should be found directly in the KB because of auto-ingestion
        let mut p_nodes = Vec::new();
        let p_root = pred(
            &mut p_nodes,
            "pilji",
            vec![
                LogicalTerm::Number(6.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: p_nodes, roots: vec![p_root] }));
    }

    #[test]
    fn test_compute_false_not_ingested() {
        let kb = new_kb();

        // Query pilji(7, 2, 3) via ComputeNode → FALSE (7 != 2*3)
        let mut q_nodes = Vec::new();
        let q_root = compute(
            &mut q_nodes,
            "pilji",
            vec![
                LogicalTerm::Number(7.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(!query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));

        // Verify the false fact was NOT ingested as a plain Predicate
        let mut p_nodes = Vec::new();
        let p_root = pred(
            &mut p_nodes,
            "pilji",
            vec![
                LogicalTerm::Number(7.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(!query(&kb, LogicBuffer { nodes: p_nodes, roots: vec![p_root] }));
    }

    #[test]
    fn test_ingested_result_available_for_reasoning() {
        let kb = new_kb();

        // Step 1: Query sumji(5, 2, 3) via ComputeNode → TRUE, auto-ingests
        let mut q_nodes = Vec::new();
        let q_root = compute(
            &mut q_nodes,
            "sumji",
            vec![
                LogicalTerm::Number(5.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));

        // Step 2: Assert another fact
        assert_buf(&kb, make_assertion("ok", "derived"));

        // Step 3: Query conjunction: And(sumji(5,2,3), derived("ok", Zoe))
        // Both facts should be in KB: sumji from compute ingestion, derived from assertion
        let mut q2_nodes = Vec::new();
        let left = pred(
            &mut q2_nodes,
            "sumji",
            vec![
                LogicalTerm::Number(5.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        let right = pred(
            &mut q2_nodes,
            "derived",
            vec![
                LogicalTerm::Constant("ok".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = and(&mut q2_nodes, left, right);
        assert!(query(&kb, LogicBuffer { nodes: q2_nodes, roots: vec![root] }));

        // Step 4: Conjunctive query with a non-ingested compute fact fails
        let mut q3_nodes = Vec::new();
        let l2 = pred(
            &mut q3_nodes,
            "sumji",
            vec![
                LogicalTerm::Number(99.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        let r2 = pred(
            &mut q3_nodes,
            "derived",
            vec![
                LogicalTerm::Constant("ok".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root2 = and(&mut q3_nodes, l2, r2);
        assert!(!query(&kb, LogicBuffer { nodes: q3_nodes, roots: vec![root2] }));
    }

    // ─── Witness extraction tests ────────────────────────────────

    fn query_find(kb: &KnowledgeBase, buf: LogicBuffer) -> Vec<Vec<WitnessBinding>> {
        kb.query_find_inner(buf).unwrap()
    }

    #[test]
    fn test_find_witnesses_single() {
        // Assert klama(mi), query ∃x.klama(x) → x = mi
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].len(), 1);
        assert_eq!(results[0][0].variable, "x");
        assert!(matches!(&results[0][0].term, LogicalTerm::Constant(c) if c == "mi"));
    }

    #[test]
    fn test_find_witnesses_multiple() {
        // Assert klama(mi) + klama(do), query ∃x.klama(x) → x = mi, x = do
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));
        assert_buf(&kb, make_assertion("do", "klama"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert_eq!(results.len(), 2);
        let mut found: Vec<String> = results
            .iter()
            .map(|bs| {
                assert_eq!(bs.len(), 1);
                assert_eq!(bs[0].variable, "x");
                match &bs[0].term {
                    LogicalTerm::Constant(c) => c.clone(),
                    _ => panic!("expected Constant"),
                }
            })
            .collect();
        found.sort();
        assert_eq!(found, vec!["do", "mi"]);
    }

    #[test]
    fn test_find_witnesses_conjunction() {
        // Assert klama(mi), prami(mi), klama(do)
        // Query ∃x.(klama(x) ∧ prami(x)) → only x = mi satisfies both
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));
        assert_buf(&kb, make_assertion("mi", "prami"));
        assert_buf(&kb, make_assertion("do", "klama"));

        let mut nodes = Vec::new();
        let p1 = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let p2 = pred(
            &mut nodes,
            "prami",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let conj = and(&mut nodes, p1, p2);
        let root = exists(&mut nodes, "x", conj);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].len(), 1);
        assert_eq!(results[0][0].variable, "x");
        assert!(matches!(&results[0][0].term, LogicalTerm::Constant(c) if c == "mi"));
    }

    #[test]
    fn test_find_witnesses_no_match() {
        // No facts, query ∃x.klama(x) → empty
        let kb = new_kb();

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(results.is_empty());
    }

    #[test]
    fn test_find_witnesses_via_universal_rule() {
        // Assert gerku(alis), ∀x.(gerku(x)→danlu(x))
        // Query ∃x.danlu(x) → should find alis (+ presupposition Skolem)
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "danlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        // At least alis + presupposition Skolem
        assert!(results.len() >= 1);
        let found: Vec<String> = results.iter().filter_map(|bs| {
            match &bs[0].term { LogicalTerm::Constant(c) => Some(c.clone()), _ => None }
        }).collect();
        assert!(found.contains(&"alis".to_string()), "alis should be a witness");
    }

    #[test]
    fn test_find_witnesses_two_variables() {
        // Assert nelci(bob, alis), query ∃x.∃y.nelci(x, y)
        // Should find x=bob, y=alis
        let kb = new_kb();

        let mut anodes = Vec::new();
        let aidx = pred(
            &mut anodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("alis".to_string()),
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes: anodes, roots: vec![aidx] });

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Variable("x".to_string()),
                LogicalTerm::Variable("y".to_string()),
            ],
        );
        let inner = exists(&mut nodes, "y", body);
        let root = exists(&mut nodes, "x", inner);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].len(), 2);
        let vars: std::collections::HashMap<&str, &LogicalTerm> = results[0]
            .iter()
            .map(|b| (b.variable.as_str(), &b.term))
            .collect();
        assert!(matches!(vars["x"], LogicalTerm::Constant(c) if c == "bob"));
        assert!(matches!(vars["y"], LogicalTerm::Constant(c) if c == "alis"));
    }

    #[test]
    fn test_find_witnesses_transitive_chain() {
        // Assert gerku(alis), ∀x.(gerku→danlu), ∀x.(danlu→xanlu)
        // Query ∃x.xanlu(x) → should find alis (+ presupposition Skolems)
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("danlu", "xanlu"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "xanlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(results.len() >= 1);
        let found: Vec<String> = results.iter().filter_map(|bs| {
            match &bs[0].term { LogicalTerm::Constant(c) => Some(c.clone()), _ => None }
        }).collect();
        assert!(found.contains(&"alis".to_string()), "alis should be a witness");
    }

    // ─── Proof trace tests ───────────────────────────────────────

    fn query_with_proof(kb: &KnowledgeBase, buf: LogicBuffer) -> (bool, ProofTrace) {
        kb.query_entailment_with_proof_inner(buf).unwrap()
    }

    #[test]
    fn test_proof_trace_simple_predicate() {
        // Assert klama(mi), query it → single asserted step, result true
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));
        let (result, trace) = query_with_proof(&kb, make_query("mi", "klama"));

        assert!(result);
        assert!(!trace.steps.is_empty());
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
    }

    #[test]
    fn test_proof_trace_false_predicate() {
        // Query non-existent fact → predicate-check with result false
        let kb = new_kb();
        let (result, trace) = query_with_proof(&kb, make_query("mi", "klama"));

        assert!(!result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(!root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::PredicateCheck(_)));
    }

    #[test]
    fn test_proof_trace_conjunction() {
        // Assert klama(mi), prami(mi), query conjunction → conjunction root with two children
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));
        assert_buf(&kb, make_assertion("mi", "prami"));

        let mut nodes = Vec::new();
        let p1 = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
        );
        let p2 = pred(
            &mut nodes,
            "prami",
            vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
        );
        let root = and(&mut nodes, p1, p2);
        let (result, trace) =
            query_with_proof(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Conjunction));
        assert_eq!(root_step.children.len(), 2);
        // Both children should be asserted with result true
        for &child in &root_step.children {
            let child_step = &trace.steps[child as usize];
            assert!(child_step.holds);
            assert!(matches!(&child_step.rule, ProofRule::Asserted(_)));
        }
    }

    #[test]
    fn test_proof_trace_negation() {
        // Query negation of non-existent fact → negation root with result true
        let kb = new_kb();
        let mut nodes = Vec::new();
        let inner = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
        );
        let root = not(&mut nodes, inner);
        let (result, trace) =
            query_with_proof(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Negation));
        assert_eq!(root_step.children.len(), 1);
        // Inner should be predicate-check with result false
        let inner_step = &trace.steps[root_step.children[0] as usize];
        assert!(!inner_step.holds);
    }

    #[test]
    fn test_proof_trace_exists_witness() {
        // Assert klama(alis), query ∃x.klama(x) → exists-witness with x = alis
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "klama"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let (result, trace) =
            query_with_proof(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::ExistsWitness(_)));
        if let ProofRule::ExistsWitness((var, term)) = &root_step.rule {
            assert_eq!(var, "x");
            assert!(matches!(term, LogicalTerm::Constant(c) if c == "alis"));
        }
    }

    #[test]
    fn test_proof_trace_exists_failed() {
        // Query ∃x.klama(x) with no facts → exists-failed
        let kb = new_kb();

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let (result, trace) =
            query_with_proof(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(!result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(!root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::ExistsFailed));
    }

    #[test]
    fn test_proof_trace_forall() {
        // Assert gerku(alis), gerku(bob), query ∀x.gerku(x)→gerku(x) [trivially true]
        // Actually: assert gerku for both entities, query ∀x.(gerku(x)→gerku(x))
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("bob", "gerku"));

        // Query: ∀x. gerku(x) — should be ForAll verified for both entities
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
        );
        let root = forall(&mut nodes, "x", body);
        let (result, trace) =
            query_with_proof(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::ForallVerified(_)));
        if let ProofRule::ForallVerified(entities) = &root_step.rule {
            assert_eq!(entities.len(), 2);
        }
        // Each child should be a predicate-check with result true
        for &child in &root_step.children {
            let child_step = &trace.steps[child as usize];
            assert!(child_step.holds);
        }
    }

    // ─── Derivation Provenance Tests ──────────────────────────────────

    #[test]
    fn test_proof_trace_asserted_fact() {
        // Directly asserted fact should show Asserted, not PredicateCheck
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        let (result, trace) = query_with_proof(&kb, make_query("alis", "gerku"));
        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
        if let ProofRule::Asserted(sexp) = &root_step.rule {
            assert!(sexp.contains("gerku"));
            assert!(sexp.contains("alis"));
        }
    }

    #[test]
    fn test_proof_trace_single_hop_derived() {
        // gerku(alis) + rule gerku→danlu → danlu(alis) should show Derived with Asserted child
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        let (result, trace) = query_with_proof(&kb, make_query("alis", "danlu"));
        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Derived(_)));
        if let ProofRule::Derived((label, sexp)) = &root_step.rule {
            assert!(sexp.contains("danlu"));
            assert!(label.contains("gerku"));
            assert!(label.contains("danlu"));
        }
        assert_eq!(root_step.children.len(), 1);
        // The child should be Asserted (gerku(alis))
        let child_step = &trace.steps[root_step.children[0] as usize];
        assert!(child_step.holds);
        assert!(matches!(&child_step.rule, ProofRule::Asserted(_)));
    }

    #[test]
    fn test_proof_trace_multi_hop_derived() {
        // Chain: gerku(alis) → danlu(alis) → xanlu(alis) via two rules
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("danlu", "xanlu"));
        let (result, trace) = query_with_proof(&kb, make_query("alis", "xanlu"));
        assert!(result);

        // Root: Derived(danlu → xanlu)
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Derived(_)));
        if let ProofRule::Derived((label, _)) = &root_step.rule {
            assert!(label.contains("xanlu"));
        }
        assert_eq!(root_step.children.len(), 1);

        // Child: Derived(gerku → danlu)
        let mid_step = &trace.steps[root_step.children[0] as usize];
        assert!(mid_step.holds);
        assert!(matches!(&mid_step.rule, ProofRule::Derived(_)));
        assert_eq!(mid_step.children.len(), 1);

        // Grandchild: Asserted(gerku(alis))
        let leaf_step = &trace.steps[mid_step.children[0] as usize];
        assert!(leaf_step.holds);
        assert!(matches!(&leaf_step.rule, ProofRule::Asserted(_)));
    }

    #[test]
    fn test_proof_trace_derived_depth_limit() {
        // Self-referencing rule: gerku → gerku. Asserted fact should be found first,
        // preventing infinite backward-chaining.
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "gerku"));
        let (result, trace) = query_with_proof(&kb, make_query("alis", "gerku"));
        assert!(result);
        // Should not panic or infinite-loop. Asserted is checked first.
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
    }

    #[test]
    fn test_proof_trace_xorlo_presup_is_asserted() {
        // Universal "ro lo gerku cu danlu" creates xorlo presupposition Skolem.
        // That fact should show as Asserted, not trigger backward-chaining.
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        // xorlo presupposition creates sk_0 as a gerku
        let (result, trace) = query_with_proof(&kb, make_query("sk_0", "gerku"));
        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
    }

    #[test]
    fn test_sexp_pattern_matching() {
        // Test the structural s-expression pattern matcher
        let var_names = vec!["x__v0".to_string()];

        // Simple predicate match via SexpTree
        let pattern = r#"(Pred "gerku" (Cons x__v0 (Cons (Zoe) (Nil))))"#;
        let concrete = r#"(Pred "gerku" (Cons (Const "alis") (Cons (Zoe) (Nil))))"#;
        let tree = SexpTree::parse(pattern, &var_names);
        let bindings = tree.match_against(concrete).unwrap();
        assert_eq!(bindings.get("x__v0").unwrap(), r#"(Const "alis")"#);

        // Non-matching predicate name
        let wrong = r#"(Pred "mlatu" (Cons (Const "alis") (Cons (Zoe) (Nil))))"#;
        assert!(tree.match_against(wrong).is_none());

        // Substitution via SexpTree
        let template = r#"(Pred "danlu" (Cons x__v0 (Cons (Zoe) (Nil))))"#;
        let template_tree = SexpTree::parse(template, &var_names);
        let result = template_tree.substitute(&bindings);
        assert!(result.contains(r#"Const "alis""#));
        assert!(result.contains("danlu"));
    }

    // ─── Conjunction Introduction (Guarded) Tests ────────────────────

    /// Helper: query whether And(pred1(entity1), pred2(entity2)) holds in the KB.
    fn query_conjunction(kb: &KnowledgeBase, pred1: &str, entity1: &str, pred2: &str, entity2: &str) -> bool {
        let mut nodes = Vec::new();
        let p1 = pred(&mut nodes, pred1, vec![
            LogicalTerm::Constant(entity1.to_string()),
            LogicalTerm::Unspecified,
        ]);
        let p2 = pred(&mut nodes, pred2, vec![
            LogicalTerm::Constant(entity2.to_string()),
            LogicalTerm::Unspecified,
        ]);
        let root = and(&mut nodes, p1, p2);
        query(kb, LogicBuffer { nodes, roots: vec![root] })
    }

    #[test]
    fn test_conjunction_introduction_basic() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("alis", "barda"));

        // Both share entity "alis" in x1 → conjunction should hold
        assert!(
            query_conjunction(&kb, "gerku", "alis", "barda", "alis"),
            "And(gerku(alis), barda(alis)) should hold"
        );
        // Commutativity: reversed order should also hold
        assert!(
            query_conjunction(&kb, "barda", "alis", "gerku", "alis"),
            "And(barda(alis), gerku(alis)) should hold (commutativity)"
        );
    }

    #[test]
    fn test_conjunction_both_individually_true() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("bob", "mlatu"));

        // Both are individually true, so their conjunction holds
        // (no shared entity requirement in demand-driven reasoning)
        assert!(
            query_conjunction(&kb, "gerku", "alis", "mlatu", "bob"),
            "And(gerku(alis), mlatu(bob)) should hold when both are individually true"
        );
    }

    #[test]
    fn test_conjunction_introduction_with_derived() {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu")); // All dogs are animals
        assert_buf(&kb, make_assertion("alis", "gerku"));   // Alice is a dog
        assert_buf(&kb, make_assertion("alis", "barda"));   // Alice is big

        // Rule derives danlu(alis). Conjunction should combine derived + asserted.
        assert!(
            query_conjunction(&kb, "danlu", "alis", "barda", "alis"),
            "And(danlu(alis), barda(alis)) should hold via rule + conjunction"
        );
        // Also: gerku(alis) ∧ danlu(alis) (asserted + derived)
        assert!(
            query_conjunction(&kb, "gerku", "alis", "danlu", "alis"),
            "And(gerku(alis), danlu(alis)) should hold"
        );
    }

    #[test]
    fn test_conjunction_introduction_cross_position() {
        // nelci(bob, alis) and gerku(alis) share "alis" across x2 and x1
        let kb = new_kb();

        // gerku(alis, _)
        assert_buf(&kb, make_assertion("alis", "gerku"));

        // nelci(bob, alis, _)
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes, roots: vec![root] });

        // Check: And(gerku(alis,_), nelci(bob,alis,_)) should hold
        let mut nodes2 = Vec::new();
        let p1 = pred(&mut nodes2, "gerku", vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ]);
        let p2 = pred(&mut nodes2, "nelci", vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ]);
        let root2 = and(&mut nodes2, p1, p2);
        assert!(
            query(&kb, LogicBuffer { nodes: nodes2, roots: vec![root2] }),
            "Cross-position entity sharing should allow conjunction query"
        );
    }

    // ─── SE-conversion + universal rule + targeted witness tests ────

    /// Build a 2-arg universal rule with different argument structures:
    /// ∀x. restrictor(x, _) → consequent(fixed_entity, x, _)
    /// This simulates "ro lo gerku cu se nelci la .bob." where SE swaps x1↔x2,
    /// producing: ∀x. gerku(x) → nelci(bob, x)
    fn make_universal_2arg(
        restrictor: &str,
        consequent: &str,
        fixed_entity: &str,
    ) -> LogicBuffer {
        let mut nodes = Vec::new();
        // restrictor(x, _)
        let restrict = pred(
            &mut nodes,
            restrictor,
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        // consequent(fixed_entity, x, _)
        let body = pred(
            &mut nodes,
            consequent,
            vec![
                LogicalTerm::Constant(fixed_entity.to_string()),
                LogicalTerm::Variable("_v0".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let neg = not(&mut nodes, restrict);
        let disj = or(&mut nodes, neg, body);
        let root = forall(&mut nodes, "_v0", disj);
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_se_conversion_universal_rule() {
        // Simulates the REPL demo:
        //   la .alis. gerku          → gerku(alis)
        //   ro lo gerku cu se nelci la .bob.  → ∀x. gerku(x) → nelci(bob, x)
        //   ? la .bob. nelci la .alis.        → nelci(bob, alis) = TRUE
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

        // Query: nelci(bob, alis) — should be TRUE via universal rule
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_se_conversion_universal_multiple_entities() {
        // Two dogs: both should be liked by bob via universal rule
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("rex", "gerku"));
        assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

        // nelci(bob, alis) = TRUE
        let mut n1 = Vec::new();
        let r1 = pred(
            &mut n1,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: n1, roots: vec![r1] }));

        // nelci(bob, rex) = TRUE
        let mut n2 = Vec::new();
        let r2 = pred(
            &mut n2,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("rex".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: n2, roots: vec![r2] }));

        // nelci(bob, carol) = FALSE (carol is not a dog)
        let mut n3 = Vec::new();
        let r3 = pred(
            &mut n3,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("carol".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        assert!(!query(&kb, LogicBuffer { nodes: n3, roots: vec![r3] }));
    }

    #[test]
    fn test_targeted_witness_search_with_fixed_entity() {
        // Simulates the REPL demo:
        //   la .alis. gerku          → gerku(alis)
        //   ro lo gerku cu se nelci la .bob.  → ∀x. gerku(x) → nelci(bob, x)
        //   ?? ma se nelci la .bob.           → ∃x. nelci(bob, x) → includes alis
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

        // Query: ∃x. nelci(bob, x) — should find alis (+ presupposition Skolem)
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Variable("x".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(results.len() >= 1);
        let found: Vec<String> = results.iter().filter_map(|bs| {
            match &bs[0].term { LogicalTerm::Constant(c) => Some(c.clone()), _ => None }
        }).collect();
        assert!(found.contains(&"alis".to_string()), "alis should be a witness");
    }

    #[test]
    fn test_targeted_witness_search_multiple_matches() {
        // Two dogs → both should appear as witnesses for "who does bob like?"
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("rex", "gerku"));
        assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

        // Query: ∃x. nelci(bob, x) — should find alis AND rex (+ presupposition Skolem)
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Variable("x".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(results.len() >= 2);
        let found: Vec<String> = results.iter().filter_map(|bs| {
            match &bs[0].term { LogicalTerm::Constant(c) => Some(c.clone()), _ => None }
        }).collect();
        assert!(found.contains(&"alis".to_string()), "alis should be a witness");
        assert!(found.contains(&"rex".to_string()), "rex should be a witness");
    }

    #[test]
    fn test_conjunction_introduction_multiple_entities() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("alis", "barda"));
        assert_buf(&kb, make_assertion("bob", "mlatu"));
        assert_buf(&kb, make_assertion("bob", "cmalu"));

        // alis predicates should conjoin with each other
        assert!(query_conjunction(&kb, "gerku", "alis", "barda", "alis"));
        // bob predicates should conjoin with each other
        assert!(query_conjunction(&kb, "mlatu", "bob", "cmalu", "bob"));
        // cross-entity conjunction also holds (both sides individually true)
        assert!(query_conjunction(&kb, "gerku", "alis", "mlatu", "bob"));
    }

    // ─── KB Reset Tests ──────────────────────────────────────────

    #[test]
    fn test_kb_reset_clears_facts() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert!(query(&kb, make_query("alis", "gerku")));

        // Reset the knowledge base
        kb.inner.borrow_mut().reset();

        // After reset, previously asserted fact should no longer hold
        assert!(!query(&kb, make_query("alis", "gerku")));
    }

    #[test]
    fn test_kb_reset_clears_rules() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(query(&kb, make_query("alis", "danlu")));

        kb.inner.borrow_mut().reset();

        // After reset, re-assert the fact but not the rule
        assert_buf(&kb, make_assertion("alis", "gerku"));
        // Rule should not exist anymore
        assert!(!query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_kb_reset_resets_skolem_counter() {
        let kb = new_kb();
        // Assert a universal to trigger Skolem generation
        assert_buf(&kb, make_universal("gerku", "danlu"));
        let counter_before = kb.inner.borrow().skolem_counter;
        assert!(counter_before > 0);

        kb.inner.borrow_mut().reset();
        assert_eq!(kb.inner.borrow().skolem_counter, 0);
    }

    // ─── Empty buffer / edge case tests ──────────────────────────

    #[test]
    fn test_query_with_no_facts() {
        let kb = new_kb();
        assert!(!query(&kb, make_query("alis", "gerku")));
    }

    #[test]
    fn test_assert_and_query_same_fact_twice() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("alis", "gerku"));
        // Should still hold and not cause issues
        assert!(query(&kb, make_query("alis", "gerku")));
    }

    // ─── Disjunction query tests ─────────────────────────────────

    #[test]
    fn test_disjunction_left_true() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));

        let mut nodes = Vec::new();
        let left = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let right = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = or(&mut nodes, left, right);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_disjunction_right_true() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "mlatu"));

        let mut nodes = Vec::new();
        let left = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let right = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = or(&mut nodes, left, right);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_disjunction_both_false() {
        let kb = new_kb();

        let mut nodes = Vec::new();
        let left = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let right = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = or(&mut nodes, left, right);
        assert!(!query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    // ─── Double negation tests ───────────────────────────────────

    #[test]
    fn test_double_negation_elimination() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));

        // Query Not(Not(gerku(alis))) → should be TRUE
        let mut nodes = Vec::new();
        let inner = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let neg1 = not(&mut nodes, inner);
        let root = not(&mut nodes, neg1);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    // ─── Tense wrapper tests ─────────────────────────────────────

    fn past(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::PastNode(inner));
        id
    }

    fn present(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::PresentNode(inner));
        id
    }

    fn future(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::FutureNode(inner));
        id
    }

    #[test]
    fn test_past_tense_wrapper_assert_query() {
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = past(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        // Query same tense wrapper → TRUE
        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = past(&mut q_nodes, q_inner);
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_tense_not_transparent() {
        // Assert Past(klama(alis)), query klama(alis) without tense → FALSE
        // (tense is NOT transparent — tensed assertion ≠ timeless query)
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = past(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        assert!(!query(&kb, make_query("alis", "klama")));
    }

    #[test]
    fn test_tense_discrimination_past_vs_future() {
        // Assert Past(klama(alis)), query Future(klama(alis)) → FALSE
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = past(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = future(&mut q_nodes, q_inner);
        assert!(!query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_tense_discrimination_present_vs_past() {
        // Assert Present(klama(alis)), query Past(klama(alis)) → FALSE
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = present(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = past(&mut q_nodes, q_inner);
        assert!(!query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_untensed_assert_tensed_query() {
        // Assert klama(alis) (bare/timeless), query Past(klama(alis)) → FALSE
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "klama"));

        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = past(&mut q_nodes, q_inner);
        assert!(!query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_temporal_rule_lifting() {
        // Assert: ∀x. gerku(x) → danlu(x) (timeless rule)
        // Assert: Past(gerku(alis))
        // Query: Past(danlu(alis)) → TRUE (temporal lifting)
        let kb = new_kb();

        // Compile the universal rule: ForAll(x, Or(Not(gerku(x)), danlu(x)))
        let mut r_nodes = Vec::new();
        let gerku = pred(
            &mut r_nodes,
            "gerku",
            vec![LogicalTerm::Variable("_v0".into()), LogicalTerm::Unspecified],
        );
        let danlu = pred(
            &mut r_nodes,
            "danlu",
            vec![LogicalTerm::Variable("_v0".into()), LogicalTerm::Unspecified],
        );
        let neg_gerku = not(&mut r_nodes, gerku);
        let impl_body = or(&mut r_nodes, neg_gerku, danlu);
        let forall = {
            let id = r_nodes.len() as u32;
            r_nodes.push(LogicNode::ForAllNode(("_v0".into(), impl_body)));
            id
        };
        assert_buf(&kb, LogicBuffer { nodes: r_nodes, roots: vec![forall] });

        // Assert Past(gerku(alis))
        let mut a_nodes = Vec::new();
        let gerku_alis = pred(
            &mut a_nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let past_gerku = past(&mut a_nodes, gerku_alis);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![past_gerku] });

        // Query Past(danlu(alis)) → TRUE (lifted rule fires on Past premises)
        let mut q_nodes = Vec::new();
        let danlu_alis = pred(
            &mut q_nodes,
            "danlu",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let past_danlu = past(&mut q_nodes, danlu_alis);
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![past_danlu] }));
    }

    #[test]
    fn test_temporal_rule_no_cross_tense() {
        // Assert: ∀x. gerku(x) → danlu(x) (timeless rule)
        // Assert: Past(gerku(alis))
        // Query: Future(danlu(alis)) → FALSE (no cross-tense derivation)
        let kb = new_kb();

        // Universal rule
        let mut r_nodes = Vec::new();
        let gerku = pred(
            &mut r_nodes,
            "gerku",
            vec![LogicalTerm::Variable("_v0".into()), LogicalTerm::Unspecified],
        );
        let danlu = pred(
            &mut r_nodes,
            "danlu",
            vec![LogicalTerm::Variable("_v0".into()), LogicalTerm::Unspecified],
        );
        let neg_gerku = not(&mut r_nodes, gerku);
        let impl_body = or(&mut r_nodes, neg_gerku, danlu);
        let forall = {
            let id = r_nodes.len() as u32;
            r_nodes.push(LogicNode::ForAllNode(("_v0".into(), impl_body)));
            id
        };
        assert_buf(&kb, LogicBuffer { nodes: r_nodes, roots: vec![forall] });

        // Assert Past(gerku(alis))
        let mut a_nodes = Vec::new();
        let gerku_alis = pred(
            &mut a_nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let past_gerku = past(&mut a_nodes, gerku_alis);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![past_gerku] });

        // Query Future(danlu(alis)) → FALSE (Past ≠ Future)
        let mut q_nodes = Vec::new();
        let danlu_alis = pred(
            &mut q_nodes,
            "danlu",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let future_danlu = future(&mut q_nodes, danlu_alis);
        assert!(!query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![future_danlu] }));
    }

    // ─── Multiple roots test ─────────────────────────────────────

    #[test]
    fn test_assert_multiple_roots() {
        let kb = new_kb();
        let mut nodes = Vec::new();
        let r1 = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let r2 = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Constant("bob".into()), LogicalTerm::Unspecified],
        );
        assert_buf(&kb, LogicBuffer { nodes, roots: vec![r1, r2] });

        assert!(query(&kb, make_query("alis", "gerku")));
        assert!(query(&kb, make_query("bob", "mlatu")));
    }

    // ─── Count quantifier test ───────────────────────────────────

    fn count(nodes: &mut Vec<LogicNode>, var: &str, cnt: u32, body: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::CountNode((var.to_string(), cnt, body)));
        id
    }

    #[test]
    fn test_count_exact_match() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("bob", "gerku"));

        // Count(x, 2, gerku(x, _)) → exactly 2 dogs
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
        );
        let root = count(&mut nodes, "x", 2, body);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_count_mismatch() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));

        // Count(x, 2, gerku(x, _)) → only 1 dog, not 2
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
        );
        let root = count(&mut nodes, "x", 2, body);
        assert!(!query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    // ─── Compute builtin arithmetic tests ────────────────────────

    #[test]
    fn test_compute_pilji_correct() {
        let kb = new_kb();
        let buf = make_compute_query("pilji", 6.0, 2.0, 3.0);
        assert!(query(&kb, buf));
    }

    #[test]
    fn test_compute_pilji_incorrect() {
        let kb = new_kb();
        let buf = make_compute_query("pilji", 7.0, 2.0, 3.0);
        assert!(!query(&kb, buf));
    }

    #[test]
    fn test_compute_sumji_correct() {
        let kb = new_kb();
        let buf = make_compute_query("sumji", 5.0, 2.0, 3.0);
        assert!(query(&kb, buf));
    }

    #[test]
    fn test_compute_sumji_incorrect() {
        let kb = new_kb();
        let buf = make_compute_query("sumji", 6.0, 2.0, 3.0);
        assert!(!query(&kb, buf));
    }

    #[test]
    fn test_compute_dilcu_correct() {
        let kb = new_kb();
        let buf = make_compute_query("dilcu", 2.0, 6.0, 3.0);
        assert!(query(&kb, buf));
    }

    #[test]
    fn test_compute_dilcu_incorrect() {
        let kb = new_kb();
        let buf = make_compute_query("dilcu", 3.0, 6.0, 3.0);
        assert!(!query(&kb, buf));
    }

    // ─── Numerical comparison predicate tests ────────────────────

    #[test]
    fn test_zmadu_greater_than() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("zmadu", 5.0, 3.0)));
    }

    #[test]
    fn test_zmadu_not_greater() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("zmadu", 3.0, 5.0)));
    }

    #[test]
    fn test_mleca_less_than() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("mleca", 3.0, 5.0)));
    }

    #[test]
    fn test_dunli_equal() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("dunli", 5.0, 5.0)));
    }

    #[test]
    fn test_dunli_not_equal() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("dunli", 5.0, 3.0)));
    }

    // ─── Assert fact with various term types ──────────────────────

    #[test]
    fn test_assert_fact_with_number_terms() {
        let kb = new_kb();
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "pilji",
            vec![
                LogicalTerm::Number(6.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes, roots: vec![root] });

        // Query the same fact back
        let mut q_nodes = Vec::new();
        let q_root = pred(
            &mut q_nodes,
            "pilji",
            vec![
                LogicalTerm::Number(6.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_assert_fact_with_description_terms() {
        let kb = new_kb();
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Description("lo_gerku".to_string()),
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes, roots: vec![root] });

        // Query back
        let mut q_nodes = Vec::new();
        let q_root = pred(
            &mut q_nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Description("lo_gerku".to_string()),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    // ─── Fact Registry / Retraction Tests ────────────────────────────

    #[test]
    fn test_retract_basic() {
        let kb = new_kb();
        let id = kb.assert_fact_inner(make_assertion("alis", "gerku"), "la alis gerku".into()).unwrap();
        assert!(query(&kb, make_query("alis", "gerku")));
        kb.retract_fact_inner(id).unwrap();
        assert!(!query(&kb, make_query("alis", "gerku")));
    }

    #[test]
    fn test_retract_preserves_other_facts() {
        let kb = new_kb();
        let id1 = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        let _id2 = kb.assert_fact_inner(make_assertion("bob", "mlatu"), String::new()).unwrap();
        kb.retract_fact_inner(id1).unwrap();
        assert!(!query(&kb, make_query("alis", "gerku")));
        assert!(query(&kb, make_query("bob", "mlatu")));
    }

    #[test]
    fn test_retract_derived_facts_gone() {
        let kb = new_kb();
        let base_id = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        let _rule_id = kb.assert_fact_inner(make_universal("gerku", "danlu"), String::new()).unwrap();
        // "alis danlu" should be derivable via the rule
        assert!(query(&kb, make_query("alis", "danlu")));
        kb.retract_fact_inner(base_id).unwrap();
        // After retracting the base fact, "alis danlu" should no longer hold
        assert!(!query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_retract_rule_preserves_base_facts() {
        let kb = new_kb();
        let _base_id = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        let rule_id = kb.assert_fact_inner(make_universal("gerku", "danlu"), String::new()).unwrap();
        assert!(query(&kb, make_query("alis", "danlu")));
        kb.retract_fact_inner(rule_id).unwrap();
        // Base fact preserved
        assert!(query(&kb, make_query("alis", "gerku")));
        // Derived fact gone (rule retracted)
        assert!(!query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_retract_and_reassert_new_id() {
        let kb = new_kb();
        let id1 = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        kb.retract_fact_inner(id1).unwrap();
        let id2 = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        assert!(id2 > id1);
        assert!(query(&kb, make_query("alis", "gerku")));
    }

    #[test]
    fn test_retract_nonexistent_errors() {
        let kb = new_kb();
        assert!(kb.retract_fact_inner(999).is_err());
    }

    #[test]
    fn test_retract_idempotent() {
        let kb = new_kb();
        let id = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        kb.retract_fact_inner(id).unwrap();
        kb.retract_fact_inner(id).unwrap(); // second retract is no-op
        assert!(!query(&kb, make_query("alis", "gerku")));
    }

    #[test]
    fn test_list_facts_empty() {
        let kb = new_kb();
        let facts = kb.list_facts_inner().unwrap();
        assert!(facts.is_empty());
    }

    #[test]
    fn test_list_facts_after_assert() {
        let kb = new_kb();
        kb.assert_fact_inner(make_assertion("alis", "gerku"), "la alis gerku".into()).unwrap();
        let facts = kb.list_facts_inner().unwrap();
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].label, "la alis gerku");
        assert_eq!(facts[0].root_count, 1);
    }

    #[test]
    fn test_list_facts_excludes_retracted() {
        let kb = new_kb();
        let id = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        kb.assert_fact_inner(make_assertion("bob", "mlatu"), "bob mlatu".into()).unwrap();
        kb.retract_fact_inner(id).unwrap();
        let facts = kb.list_facts_inner().unwrap();
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].id, 1); // bob's fact
        assert_eq!(facts[0].label, "bob mlatu");
    }

    #[test]
    fn test_reset_clears_registry() {
        let kb = new_kb();
        kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        kb.inner.borrow_mut().reset();
        let facts = kb.list_facts_inner().unwrap();
        assert!(facts.is_empty());
        assert!(!query(&kb, make_query("alis", "gerku")));
    }

    // ─── C5: Description term opacity tests ──────────────────────

    /// Helper: make an assertion with a Description term in x1.
    fn make_desc_assertion(desc_name: &str, predicate: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            predicate,
            vec![
                LogicalTerm::Description(desc_name.to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        LogicBuffer { nodes, roots: vec![root] }
    }

    /// Helper: make a query with a Description term in x1.
    fn make_desc_query(desc_name: &str, predicate: &str) -> LogicBuffer {
        make_desc_assertion(desc_name, predicate)
    }

    #[test]
    fn test_desc_gets_indomain() {
        // Assert a fact with Description term → Desc should be in InDomain
        let kb = new_kb();
        assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
        let inner = kb.inner.borrow();
        assert!(
            inner.known_descriptions.contains("gerku"),
            "expected 'gerku' in known_descriptions"
        );
    }

    #[test]
    fn test_desc_conjunction_introduction() {
        // Two facts about same Desc term → conjunction should be derivable
        let kb = new_kb();
        assert_buf(&kb, make_desc_assertion("gerku", "danlu"));
        assert_buf(&kb, make_desc_assertion("gerku", "sutra"));

        // Query And(danlu(Desc "gerku"), sutra(Desc "gerku"))
        let mut nodes = Vec::new();
        let p1 = pred(
            &mut nodes,
            "danlu",
            vec![
                LogicalTerm::Description("gerku".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let p2 = pred(
            &mut nodes,
            "sutra",
            vec![
                LogicalTerm::Description("gerku".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = and(&mut nodes, p1, p2);
        assert!(
            query(&kb, LogicBuffer { nodes, roots: vec![root] }),
            "conjunction of two Desc-term facts should hold via conjunction introduction"
        );
    }

    #[test]
    fn test_desc_does_not_trigger_rule_without_restrictor() {
        // Assert sutra(Desc "gerku") (but NOT gerku(Desc "gerku"))
        // Assert rule: ro lo gerku cu danlu (∀x. gerku(x) → danlu(x))
        // Query danlu(Desc "gerku") → should FAIL (the restrictor isn't satisfied)
        let kb = new_kb();
        assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(
            !query(&kb, make_desc_query("gerku", "danlu")),
            "universal rule should NOT fire without restrictor being satisfied for Desc term"
        );
    }

    #[test]
    fn test_desc_triggers_rule_when_restrictor_satisfied() {
        // Assert gerku(Desc "gerku") AND sutra(Desc "gerku")
        // Assert rule: ro lo gerku cu danlu
        // Query danlu(Desc "gerku") → should SUCCEED
        let kb = new_kb();
        assert_buf(&kb, make_desc_assertion("gerku", "gerku"));
        assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(
            query(&kb, make_desc_query("gerku", "danlu")),
            "universal rule should fire when restrictor IS satisfied for Desc term"
        );
    }

    #[test]
    fn test_desc_exists_witness() {
        // Assert sutra(Desc "gerku") → ∃x. sutra(x) should find Desc "gerku" as witness
        let kb = new_kb();
        assert_buf(&kb, make_desc_assertion("gerku", "sutra"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "sutra",
            vec![
                LogicalTerm::Variable("x".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = exists(&mut nodes, "x", body);
        assert!(
            query(&kb, LogicBuffer { nodes, roots: vec![root] }),
            "existential query should find Desc term as witness"
        );
    }

    // ─── Run Bound / Saturation Tests ────────────────────────────────

    #[test]
    fn test_run_bound_default() {
        let kb = new_kb();
        assert_eq!(kb.get_run_bound_inner(), 100);
    }

    #[test]
    fn test_run_bound_configurable() {
        let kb = new_kb();
        kb.set_run_bound_inner(5);
        assert_eq!(kb.get_run_bound_inner(), 5);
        kb.set_run_bound_inner(200);
        assert_eq!(kb.get_run_bound_inner(), 200);
    }

    #[test]
    fn test_run_bound_preserved_across_reset() {
        let kb = new_kb();
        kb.set_run_bound_inner(42);
        kb.inner.borrow_mut().reset();
        assert_eq!(
            kb.get_run_bound_inner(),
            42,
            "run_bound should survive reset (it's config, not derived state)"
        );
    }

    #[test]
    fn test_backward_chain_derives_facts() {
        // Assert a fact and a rule, then verify backward-chaining derives conclusions
        let kb = new_kb();
        // Assert: gerku(alis)
        assert_buf(&kb, make_assertion("alis", "gerku"));

        // Assert: ∀x. ¬gerku(x) ∨ danlu(x) (i.e., gerku → danlu)
        assert_buf(&kb, make_universal("gerku", "danlu"));

        // Query: danlu(alis) — should be derived via backward-chaining
        assert!(
            query(&kb, make_query("alis", "danlu")),
            "backward-chaining should derive danlu(alis) from gerku(alis) and universal rule"
        );

        // run_bound is still stored as config (no-op value)
        kb.set_run_bound_inner(0);
        assert_eq!(kb.get_run_bound_inner(), 0);
    }

    // ─── Event-decomposed universal rule tests ──────────────────────

    /// Build an event-decomposed ground assertion:
    ///   Exists(_ev0, And(P(_ev0), P_x1(_ev0, entity)))
    fn make_event_assertion(entity: &str, predicate: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let p_type = pred(
            &mut nodes,
            predicate,
            vec![LogicalTerm::Variable("_ev0".to_string())],
        );
        let p_role = pred(
            &mut nodes,
            &format!("{}_x1", predicate),
            vec![
                LogicalTerm::Variable("_ev0".to_string()),
                LogicalTerm::Constant(entity.to_string()),
            ],
        );
        let p_and = and(&mut nodes, p_type, p_role);
        let root = exists(&mut nodes, "_ev0", p_and);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    }

    /// Build an event-decomposed universal rule:
    ///   ForAll(_v0, Or(
    ///     Not(Exists(_ev0, And(P(_ev0), P_x1(_ev0, _v0)))),
    ///     Exists(_ev1, And(Q(_ev1), Q_x1(_ev1, _v0)))
    ///   ))
    fn make_event_universal(restrictor: &str, consequent: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        // Condition: Exists(_ev0, And(P(_ev0), P_x1(_ev0, _v0)))
        let p_type = pred(
            &mut nodes,
            restrictor,
            vec![LogicalTerm::Variable("_ev0".to_string())],
        );
        let p_role = pred(
            &mut nodes,
            &format!("{}_x1", restrictor),
            vec![
                LogicalTerm::Variable("_ev0".to_string()),
                LogicalTerm::Variable("_v0".to_string()),
            ],
        );
        let p_and = and(&mut nodes, p_type, p_role);
        let p_exists = exists(&mut nodes, "_ev0", p_and);

        // Consequent: Exists(_ev1, And(Q(_ev1), Q_x1(_ev1, _v0)))
        let q_type = pred(
            &mut nodes,
            consequent,
            vec![LogicalTerm::Variable("_ev1".to_string())],
        );
        let q_role = pred(
            &mut nodes,
            &format!("{}_x1", consequent),
            vec![
                LogicalTerm::Variable("_ev1".to_string()),
                LogicalTerm::Variable("_v0".to_string()),
            ],
        );
        let q_and = and(&mut nodes, q_type, q_role);
        let q_exists = exists(&mut nodes, "_ev1", q_and);

        // Implication: Or(Not(p_exists), q_exists)
        let neg = not(&mut nodes, p_exists);
        let disj = or(&mut nodes, neg, q_exists);
        let root = forall(&mut nodes, "_v0", disj);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    }

    /// Build an event-decomposed existential query (same structure as assertion).
    fn make_event_query(entity: &str, predicate: &str) -> LogicBuffer {
        make_event_assertion(entity, predicate)
    }

    #[test]
    fn test_event_decomposed_rule_fires() {
        let kb = new_kb();
        assert_buf(&kb, make_event_assertion("alis", "gerku"));
        assert_buf(&kb, make_event_universal("gerku", "danlu"));
        assert!(
            query(&kb, make_event_query("alis", "danlu")),
            "event-decomposed rule should derive danlu(alis) from gerku(alis)"
        );
    }

    #[test]
    fn test_event_decomposed_rule_selective() {
        let kb = new_kb();
        assert_buf(&kb, make_event_assertion("alis", "gerku"));
        assert_buf(&kb, make_event_assertion("bob", "mlatu"));
        assert_buf(&kb, make_event_universal("gerku", "danlu"));
        assert!(
            query(&kb, make_event_query("alis", "danlu")),
            "danlu(alis) should hold (alis is a gerku)"
        );
        assert!(
            !query(&kb, make_event_query("bob", "danlu")),
            "danlu(bob) should NOT hold (bob is a mlatu, not gerku)"
        );
    }

    #[test]
    fn test_event_decomposed_entity_after_rule() {
        let kb = new_kb();
        // Add rule first, then fact — should still fire after saturation
        assert_buf(&kb, make_event_universal("gerku", "danlu"));
        assert_buf(&kb, make_event_assertion("alis", "gerku"));
        assert!(
            query(&kb, make_event_query("alis", "danlu")),
            "rule should fire even when added before fact"
        );
    }

    #[test]
    fn test_event_decomposed_temporal_rule() {
        let kb = new_kb();
        // Assert: Past(Exists(_ev0, And(gerku(_ev0), gerku_x1(_ev0, alis))))
        let mut a_nodes = Vec::new();
        let p_type = pred(
            &mut a_nodes,
            "gerku",
            vec![LogicalTerm::Variable("_ev0".to_string())],
        );
        let p_role = pred(
            &mut a_nodes,
            "gerku_x1",
            vec![
                LogicalTerm::Variable("_ev0".to_string()),
                LogicalTerm::Constant("alis".to_string()),
            ],
        );
        let p_and = and(&mut a_nodes, p_type, p_role);
        let p_exists = exists(&mut a_nodes, "_ev0", p_and);
        let a_root = past(&mut a_nodes, p_exists);
        assert_buf(
            &kb,
            LogicBuffer {
                nodes: a_nodes,
                roots: vec![a_root],
            },
        );

        // Add timeless rule: ro lo gerku ku danlu (event-decomposed)
        assert_buf(&kb, make_event_universal("gerku", "danlu"));

        // Query: Past(Exists(_ev0, And(danlu(_ev0), danlu_x1(_ev0, alis))))
        let mut q_nodes = Vec::new();
        let q_type = pred(
            &mut q_nodes,
            "danlu",
            vec![LogicalTerm::Variable("_ev0".to_string())],
        );
        let q_role = pred(
            &mut q_nodes,
            "danlu_x1",
            vec![
                LogicalTerm::Variable("_ev0".to_string()),
                LogicalTerm::Constant("alis".to_string()),
            ],
        );
        let q_and = and(&mut q_nodes, q_type, q_role);
        let q_exists = exists(&mut q_nodes, "_ev0", q_and);
        let q_root = past(&mut q_nodes, q_exists);
        assert!(
            query(
                &kb,
                LogicBuffer {
                    nodes: q_nodes,
                    roots: vec![q_root],
                }
            ),
            "temporal lifting should derive Past(danlu(alis)) from Past(gerku(alis)) and timeless rule"
        );
    }

    #[test]
    fn test_event_decomposed_multi_hop() {
        let kb = new_kb();
        assert_buf(&kb, make_event_assertion("alis", "gerku"));
        assert_buf(&kb, make_event_universal("gerku", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "xanlu"));
        assert!(
            query(&kb, make_event_query("alis", "xanlu")),
            "multi-hop: gerku→danlu→xanlu should derive xanlu(alis)"
        );
    }

    #[test]
    fn test_event_decomposed_proof_trace() {
        let kb = new_kb();
        assert_buf(&kb, make_event_assertion("alis", "gerku"));
        assert_buf(&kb, make_event_universal("gerku", "danlu"));

        // Query with proof trace
        let (holds, trace) = kb
            .query_entailment_with_proof_inner(make_event_query("alis", "danlu"))
            .unwrap();
        assert!(holds, "entailment should hold for derived event-decomposed fact");

        // Check that the proof trace contains a Derived step
        let has_derived = trace.steps.iter().any(|step| {
            matches!(&step.rule, ProofRule::Derived(_))
        });
        assert!(
            has_derived,
            "proof trace should contain at least one Derived step for rule-derived fact"
        );
    }

    #[test]
    fn test_event_decomposed_xorlo() {
        let kb = new_kb();
        // Only add the rule (no ground facts) — xorlo presupposition should
        // create Skolem constants that make the restrictor domain non-empty
        assert_buf(&kb, make_event_universal("gerku", "danlu"));

        // The xorlo presupposition should have created event + entity Skolems
        // such that gerku(sk_ev) and gerku_x1(sk_ev, sk_entity) hold.
        // Query: exists something that is a gerku (via xorlo presupposition)
        let mut q_nodes = Vec::new();
        let q_type = pred(
            &mut q_nodes,
            "gerku",
            vec![LogicalTerm::Variable("_ev0".to_string())],
        );
        let q_role = pred(
            &mut q_nodes,
            "gerku_x1",
            vec![
                LogicalTerm::Variable("_ev0".to_string()),
                LogicalTerm::Variable("_v0".to_string()),
            ],
        );
        let q_and = and(&mut q_nodes, q_type, q_role);
        let q_ev = exists(&mut q_nodes, "_ev0", q_and);
        let q_root = exists(&mut q_nodes, "_v0", q_ev);
        assert!(
            query(
                &kb,
                LogicBuffer {
                    nodes: q_nodes,
                    roots: vec![q_root],
                }
            ),
            "xorlo presupposition should make ∃x.∃e. gerku(e)∧gerku_x1(e,x) hold"
        );
    }

    // ─── Zoo Ontology integration tests (REPL demo scenarios) ───────

    /// Build a temporal event-decomposed assertion:
    ///   Tense(Exists(_ev0, And(P(_ev0), P_x1(_ev0, entity))))
    /// where tense_fn wraps the inner Exists with Past/Present/Future.
    fn make_temporal_event_assertion(
        entity: &str,
        predicate: &str,
        tense_fn: fn(&mut Vec<LogicNode>, u32) -> u32,
    ) -> LogicBuffer {
        let mut nodes = Vec::new();
        let p_type = pred(
            &mut nodes,
            predicate,
            vec![LogicalTerm::Variable("_ev0".to_string())],
        );
        let p_role = pred(
            &mut nodes,
            &format!("{}_x1", predicate),
            vec![
                LogicalTerm::Variable("_ev0".to_string()),
                LogicalTerm::Constant(entity.to_string()),
            ],
        );
        let p_and = and(&mut nodes, p_type, p_role);
        let p_exists = exists(&mut nodes, "_ev0", p_and);
        let root = tense_fn(&mut nodes, p_exists);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    }

    /// Build a temporal event-decomposed query (same structure as temporal assertion).
    fn make_temporal_event_query(
        entity: &str,
        predicate: &str,
        tense_fn: fn(&mut Vec<LogicNode>, u32) -> u32,
    ) -> LogicBuffer {
        make_temporal_event_assertion(entity, predicate, tense_fn)
    }

    #[test]
    fn test_zoo_multi_hop_temporal_past() {
        // REPL: pu la .alis. gerku → ro lo gerku cu danlu → ro lo danlu cu jmive
        // Query: ?! pu la .alis. jmive → TRUE
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
        assert_buf(&kb, make_event_universal("gerku", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "jmive"));
        assert!(
            query(&kb, make_temporal_event_query("alis", "jmive", past)),
            "multi-hop temporal: Past(gerku→danlu→jmive) should derive Past(jmive(alis))"
        );
    }

    #[test]
    fn test_zoo_multi_hop_temporal_present() {
        // REPL: ca la .bob. mlatu → ro lo mlatu cu danlu → ro lo danlu cu jmive
        // Query: ?! ca la .bob. jmive → TRUE
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
        assert_buf(&kb, make_event_universal("mlatu", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "jmive"));
        assert!(
            query(&kb, make_temporal_event_query("bob", "jmive", present)),
            "multi-hop temporal: Present(mlatu→danlu→jmive) should derive Present(jmive(bob))"
        );
    }

    #[test]
    fn test_zoo_tense_discrimination() {
        // Assert Past(gerku(alis)), derive Past(jmive(alis))
        // Query Present(jmive(alis)) → FALSE (strict tense discrimination)
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
        assert_buf(&kb, make_event_universal("gerku", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "jmive"));

        // Past query should succeed
        assert!(
            query(&kb, make_temporal_event_query("alis", "jmive", past)),
            "Past(jmive(alis)) should hold"
        );
        // Present query should FAIL — alice was a dog in the past, not present
        assert!(
            !query(&kb, make_temporal_event_query("alis", "jmive", present)),
            "Present(jmive(alis)) should NOT hold — wrong tense"
        );
    }

    #[test]
    fn test_zoo_mixed_tenses() {
        // REPL demo: two entities with different tenses
        // pu la .alis. gerku + ca la .bob. mlatu + rules
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
        assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
        assert_buf(&kb, make_event_universal("gerku", "danlu"));
        assert_buf(&kb, make_event_universal("mlatu", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "jmive"));

        // Each entity derivable only in its own tense
        assert!(query(&kb, make_temporal_event_query("alis", "jmive", past)));
        assert!(query(&kb, make_temporal_event_query("bob", "jmive", present)));
        // Cross-tense queries fail
        assert!(!query(&kb, make_temporal_event_query("alis", "jmive", present)));
        assert!(!query(&kb, make_temporal_event_query("bob", "jmive", past)));
    }

    #[test]
    fn test_zoo_witness_extraction_event_decomposed() {
        // REPL: ?? ma danlu — find witnesses after event-decomposed derivation
        let kb = new_kb();
        assert_buf(&kb, make_event_assertion("alis", "gerku"));
        assert_buf(&kb, make_event_assertion("bob", "gerku"));
        assert_buf(&kb, make_event_universal("gerku", "danlu"));

        // Query: ∃_v0. ∃_ev0. danlu(_ev0) ∧ danlu_x1(_ev0, _v0)
        let mut q_nodes = Vec::new();
        let q_type = pred(
            &mut q_nodes,
            "danlu",
            vec![LogicalTerm::Variable("_ev0".to_string())],
        );
        let q_role = pred(
            &mut q_nodes,
            "danlu_x1",
            vec![
                LogicalTerm::Variable("_ev0".to_string()),
                LogicalTerm::Variable("_v0".to_string()),
            ],
        );
        let q_and = and(&mut q_nodes, q_type, q_role);
        let q_ev = exists(&mut q_nodes, "_ev0", q_and);
        let q_root = exists(&mut q_nodes, "_v0", q_ev);
        let results = query_find(
            &kb,
            LogicBuffer {
                nodes: q_nodes,
                roots: vec![q_root],
            },
        );

        // Should find witnesses for both alis and bob
        assert!(
            !results.is_empty(),
            "should find witnesses for danlu after event-decomposed derivation"
        );
        // Extract entity bindings (filter to _v0 which is the entity variable)
        let entity_witnesses: Vec<String> = results
            .iter()
            .filter_map(|bindings| {
                bindings.iter().find_map(|b| {
                    if b.variable == "_v0" {
                        match &b.term {
                            LogicalTerm::Constant(c) => Some(c.clone()),
                            _ => None,
                        }
                    } else {
                        None
                    }
                })
            })
            .collect();
        assert!(
            entity_witnesses.contains(&"alis".to_string()),
            "alis should be a witness for danlu"
        );
        assert!(
            entity_witnesses.contains(&"bob".to_string()),
            "bob should be a witness for danlu"
        );
    }

    #[test]
    fn test_zoo_retraction_with_event_decomposition() {
        // REPL demo: retract alice's fact, bob should survive
        let kb = new_kb();
        assert_buf(&kb, make_event_universal("gerku", "danlu"));
        assert_buf(&kb, make_event_universal("mlatu", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "jmive"));

        let alis_id = kb
            .assert_fact_inner(
                make_temporal_event_assertion("alis", "gerku", past),
                "pu la .alis. gerku".into(),
            )
            .unwrap();
        let _bob_id = kb
            .assert_fact_inner(
                make_temporal_event_assertion("bob", "mlatu", present),
                "ca la .bob. mlatu".into(),
            )
            .unwrap();

        // Both should hold before retraction
        assert!(query(&kb, make_temporal_event_query("alis", "jmive", past)));
        assert!(query(&kb, make_temporal_event_query("bob", "jmive", present)));

        // Retract alice's assertion
        kb.retract_fact_inner(alis_id).unwrap();

        // Alice's derivation should be gone
        assert!(
            !query(&kb, make_temporal_event_query("alis", "jmive", past)),
            "after retracting alis's gerku fact, Past(jmive(alis)) should be FALSE"
        );
        // Bob's derivation should still hold
        assert!(
            query(&kb, make_temporal_event_query("bob", "jmive", present)),
            "bob's Present(jmive(bob)) should still hold after retracting alis"
        );
    }

    #[test]
    fn test_zoo_proof_trace_multi_hop_temporal() {
        // REPL: ?! pu la .alis. jmive — proof trace for multi-hop temporal derivation
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
        assert_buf(&kb, make_event_universal("gerku", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "jmive"));

        let (holds, trace) = kb
            .query_entailment_with_proof_inner(make_temporal_event_query("alis", "jmive", past))
            .unwrap();
        assert!(holds, "Past(jmive(alis)) should hold with proof trace");

        // Proof should contain Derived steps (from rule application)
        let derived_count = trace
            .steps
            .iter()
            .filter(|step| matches!(&step.rule, ProofRule::Derived(_)))
            .count();
        assert!(
            derived_count >= 2,
            "multi-hop derivation should have at least 2 Derived steps (gerku→danlu, danlu→jmive), got {}",
            derived_count
        );

        // Proof should contain a ModalPassthrough for past tense
        let has_modal = trace.steps.iter().any(|step| {
            matches!(&step.rule, ProofRule::ModalPassthrough(t) if t == "past")
        });
        assert!(
            has_modal,
            "proof trace should contain a ModalPassthrough(past) step"
        );
    }

    // ---- Proof trace memoization tests ----

    #[test]
    fn test_proof_memo_deduplication() {
        // Multi-hop event-decomposed trace should use ProofRef for repeated sub-proofs.
        // Without memoization: mlatu base facts appear 12× in a 2-hop 3-role chain.
        // With memoization: repeated sexps get ProofRef nodes instead.
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
        assert_buf(&kb, make_event_universal("mlatu", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "jmive"));

        let (holds, trace) = kb
            .query_entailment_with_proof_inner(make_temporal_event_query("bob", "jmive", present))
            .unwrap();
        assert!(holds, "Present(jmive(bob)) should hold");

        // Count ProofRef steps — should be present due to repeated condition proofs
        let proof_ref_count = trace
            .steps
            .iter()
            .filter(|step| matches!(&step.rule, ProofRule::ProofRef(_)))
            .count();
        assert!(
            proof_ref_count > 0,
            "2-hop event-decomposed trace should have ProofRef nodes for deduplicated sub-proofs, got {}",
            proof_ref_count
        );

        // With memoization, condition proofs that repeat across different
        // conclusion derivations get ProofRef instead of full re-expansion.
        // The ExistsNode witness search also generates overhead (failed candidates),
        // but the key improvement is visible in the successful derivation path.
        assert!(
            proof_ref_count >= 3,
            "2-hop event trace should have at least 3 ProofRef nodes (deduplicated conditions), got {}",
            proof_ref_count
        );
    }

    #[test]
    fn test_proof_memo_correctness() {
        // Memoized trace still reports the correct result and contains proper Derived + Asserted steps.
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
        assert_buf(&kb, make_event_universal("gerku", "danlu"));

        let (holds, trace) = kb
            .query_entailment_with_proof_inner(make_temporal_event_query("alis", "danlu", past))
            .unwrap();
        assert!(holds, "Past(danlu(alis)) should hold");

        // Should still have Derived steps from the rule application
        let derived_count = trace
            .steps
            .iter()
            .filter(|step| matches!(&step.rule, ProofRule::Derived(_)))
            .count();
        assert!(
            derived_count >= 1,
            "should have at least 1 Derived step from gerku→danlu rule, got {}",
            derived_count
        );

        // First occurrence of base facts should be Asserted or PredicateCheck (not ProofRef)
        let has_asserted_or_check = trace.steps.iter().any(|step| {
            matches!(&step.rule, ProofRule::Asserted(_))
                || matches!(&step.rule, ProofRule::PredicateCheck(_))
        });
        assert!(
            has_asserted_or_check,
            "first occurrence of base facts should be Asserted or PredicateCheck, not ProofRef"
        );
    }

    #[test]
    fn test_proof_memo_single_hop_no_unnecessary_refs() {
        // Single-hop with one entity: each condition sexp is unique,
        // so no ProofRef should be needed.
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
        assert_buf(&kb, make_event_universal("gerku", "danlu"));

        let (holds, trace) = kb
            .query_entailment_with_proof_inner(make_temporal_event_query("alis", "danlu", past))
            .unwrap();
        assert!(holds, "Past(danlu(alis)) should hold");

        // In a single-hop scenario, conditions are gerku(e), gerku_x1(e, alis), gerku_x2(e, zo'e)
        // These are all unique sexps, so no ProofRef should be needed for condition proofs.
        // ProofRef may still appear if the same fact is checked multiple times through
        // different paths, but the count should be very low.
        let proof_ref_count = trace
            .steps
            .iter()
            .filter(|step| matches!(&step.rule, ProofRule::ProofRef(_)))
            .count();
        // Allow a small number — the point is it's not the cubic blowup
        assert!(
            proof_ref_count <= 3,
            "single-hop trace should have very few ProofRef nodes (unique conditions), got {}",
            proof_ref_count
        );
    }

    // ─── Book example regression test (event Skolem InDomain blowup) ────

    /// Build a 2-argument event-decomposed assertion:
    ///   ∃ev0. P(ev0) ∧ P_x1(ev0, entity1) ∧ P_x2(ev0, entity2)
    /// This models sentences like "lo prenu cu ponse lo datni" where both
    /// the subject and object are concrete entities.
    fn make_event_assertion_2arg(
        entity1: &str,
        entity2: &str,
        predicate: &str,
    ) -> LogicBuffer {
        let mut nodes = Vec::new();
        let p_type = pred(
            &mut nodes,
            predicate,
            vec![LogicalTerm::Variable("_ev0".to_string())],
        );
        let p_role1 = pred(
            &mut nodes,
            &format!("{}_x1", predicate),
            vec![
                LogicalTerm::Variable("_ev0".to_string()),
                LogicalTerm::Constant(entity1.to_string()),
            ],
        );
        let p_role2 = pred(
            &mut nodes,
            &format!("{}_x2", predicate),
            vec![
                LogicalTerm::Variable("_ev0".to_string()),
                LogicalTerm::Constant(entity2.to_string()),
            ],
        );
        let a1 = and(&mut nodes, p_type, p_role1);
        let a2 = and(&mut nodes, a1, p_role2);
        let root = exists(&mut nodes, "_ev0", a2);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    }

    #[test]
    fn test_book_example_no_oom() {
        // Regression test for the book example that was crashing with OOM:
        //   .i lo prenu cu ponse lo datni
        //   .i ro lo prenu poi ponse lo datni cu bilga lo nu curmi
        //   ?! lo prenu cu bilga lo nu curmi
        //
        // The crash was caused by event Skolem constants being registered in
        // `known_entities`, causing O(N²) blowup in guarded
        // conjunction introduction. With 2-arg predicates and universal rules,
        // each event constant linked ~6 predicates → C(6,2)=15 conjunctions
        // → commutativity doubled them → exponential growth.
        //
        // This test models the scenario with multiple entities and predicates
        // to verify no memory explosion occurs.
        let kb = new_kb();

        // Assert: "A person possesses data"
        // ∃ev0. ponse(ev0) ∧ ponse_x1(ev0, prenu_sk) ∧ ponse_x2(ev0, datni_sk)
        assert_buf(&kb, make_event_assertion_2arg("prenu_sk", "datni_sk", "ponse"));

        // Also assert the gadri decompositions (what `lo prenu` and `lo datni` produce):
        // ∃ev1. prenu(ev1) ∧ prenu_x1(ev1, prenu_sk)
        assert_buf(&kb, make_event_assertion("prenu_sk", "prenu"));
        // ∃ev2. datni(ev2) ∧ datni_x1(ev2, datni_sk)
        assert_buf(&kb, make_event_assertion("datni_sk", "datni"));

        // Assert universal rule: "Every person who possesses data is obligated"
        // This is simplified as: ∀x. prenu(x) → bilga(x)
        assert_buf(&kb, make_event_universal("prenu", "bilga"));

        // Add another universal rule to increase backward-chaining depth
        assert_buf(&kb, make_event_universal("bilga", "zukte"));

        // Query: "A person is obligated" — should hold via prenu→bilga derivation
        assert!(
            query(&kb, make_event_assertion("prenu_sk", "bilga")),
            "prenu_sk should be derived as bilga via universal rule"
        );

        // Query with proof trace — this is what was crashing before the fix
        let (holds, _trace) = kb
            .query_entailment_with_proof_inner(make_event_assertion("prenu_sk", "bilga"))
            .unwrap();
        assert!(holds, "proof-traced query should hold for bilga(prenu_sk)");

        // Multi-hop: prenu→bilga→zukte
        assert!(
            query(&kb, make_event_assertion("prenu_sk", "zukte")),
            "multi-hop prenu→bilga→zukte should derive zukte(prenu_sk)"
        );

        // Proof trace for multi-hop should complete without OOM
        let (holds2, _trace2) = kb
            .query_entailment_with_proof_inner(make_event_assertion("prenu_sk", "zukte"))
            .unwrap();
        assert!(holds2, "proof-traced multi-hop should hold for zukte(prenu_sk)");
    }

    // ─── And flattening regression test ────

    #[test]
    fn test_and_flattening_prevents_rewrite_explosion() {
        // Regression test: a deeply nested And tree with 7 leaves (matching the
        // real Neo-Davidsonian decomposition of ".i lo prenu cu ponse lo datni")
        // previously caused combinatorial explosion. After flattening, each leaf
        // is asserted individually, so the fact count should be bounded.
        let kb = new_kb();

        // Build: ∃ev. P1(ev) ∧ P2(ev,a) ∧ P3(ev,b) ∧ P4(a) ∧ P5(b) ∧ P6(a) ∧ P7(b)
        // This simulates a 2-arg predicate with xorlo restrictors.
        let mut nodes = Vec::new();
        let p1 = pred(&mut nodes, "ponse", vec![LogicalTerm::Variable("_ev0".into())]);
        let p2 = pred(&mut nodes, "ponse_x1", vec![
            LogicalTerm::Variable("_ev0".into()),
            LogicalTerm::Variable("_v0".into()),
        ]);
        let p3 = pred(&mut nodes, "ponse_x2", vec![
            LogicalTerm::Variable("_ev0".into()),
            LogicalTerm::Variable("_v1".into()),
        ]);
        let p4 = pred(&mut nodes, "prenu", vec![LogicalTerm::Variable("_v0".into())]);
        let p5 = pred(&mut nodes, "datni", vec![LogicalTerm::Variable("_v1".into())]);
        let p6 = pred(&mut nodes, "prenu_x1", vec![
            LogicalTerm::Variable("_ev1".into()),
            LogicalTerm::Variable("_v0".into()),
        ]);
        let p7 = pred(&mut nodes, "datni_x1", vec![
            LogicalTerm::Variable("_ev2".into()),
            LogicalTerm::Variable("_v1".into()),
        ]);

        // Build deeply nested And tree (7 leaves, 6 And nodes)
        let a1 = and(&mut nodes, p1, p2);
        let a2 = and(&mut nodes, a1, p3);
        let a3 = and(&mut nodes, a2, p4);
        let a4 = and(&mut nodes, a3, p5);
        let a5 = and(&mut nodes, a4, p6);
        let a6 = and(&mut nodes, a5, p7);

        // Wrap in existentials (these will be Skolemized)
        let e0 = exists(&mut nodes, "_ev0", a6);
        let e1 = exists(&mut nodes, "_ev1", e0);
        let e2 = exists(&mut nodes, "_ev2", e1);
        let e3 = exists(&mut nodes, "_v0", e2);
        let root = exists(&mut nodes, "_v1", e3);

        let buf = LogicBuffer {
            nodes,
            roots: vec![root],
        };

        assert_buf(&kb, buf);

        // Verify the fact count is bounded — each leaf gets a single entry
        // in asserted_sexps (no combinatorial And explosion).
        let inner = kb.inner.borrow();
        let fact_count = inner.asserted_sexps.len();
        eprintln!("[Test] asserted_sexps count: {}", fact_count);
        assert!(
            fact_count < 100,
            "Asserted facts should be < 100 after flattening, got {}",
            fact_count
        );
    }
}
