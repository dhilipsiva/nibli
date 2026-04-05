//! Logji (logic/reasoning) engine: FOL assertion and query via demand-driven backward-chaining.
//!
//! This is the core inference component of Nibli. It maintains a stateful knowledge
//! base with a fact index and backward-chaining rule engine:
//!
//! - **Fact assertion** — Ground predicates stored as typed `StoredFact` via pluggable `FactStore` backend.
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

#![allow(dead_code)]

use nibli_types::error::NibliError;
use nibli_types::logic::{
    FactSummary, LogicBuffer, LogicNode, LogicalTerm, ProofRule, ProofStep, ProofTrace,
    QueryResult, ResourceKind, UnknownReason, WitnessBinding,
};
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
mod compute;
/// Fact store abstraction (trait + in-memory implementation).
pub mod fact_store;
/// WASI-compatible lazy-loading fact store (append-only log + LRU cache).
#[cfg(feature = "wasi-store")]
pub mod wasi_fact_store;
mod reasoning;
/// S-expression reconstruction for logic buffers (debug output).
pub mod repr;
mod rules;

pub use compute::{ComputeRequest, register_compute_dispatch};

use compute::*;
use reasoning::*;
use rules::*;

/// Transform registered compute predicates from Predicate → ComputeNode in a logic buffer.
/// Call this after smuni compilation and before asserting/querying.
pub fn transform_compute_nodes(buf: &mut LogicBuffer, compute_preds: &HashSet<String>) {
    let nodes = std::mem::take(&mut buf.nodes);
    buf.nodes = nodes
        .into_iter()
        .map(|node| match &node {
            LogicNode::Predicate((rel, _)) if compute_preds.contains(rel.as_str()) => {
                let LogicNode::Predicate(inner) = node else {
                    unreachable!("already matched as Predicate in guard")
                };
                LogicNode::ComputeNode(inner)
            }
            _ => node,
        })
        .collect();
}

pub mod kb;
pub use kb::KnowledgeBase;
pub(crate) use kb::*;

/// Internal methods that return `Result<_, String>` for use by both the WIT boundary and tests.
impl KnowledgeBase {
    fn combine_root_results(left: QueryResult, right: QueryResult) -> QueryResult {
        if left.is_false() || right.is_false() {
            QueryResult::False
        } else if left.is_true() && right.is_true() {
            QueryResult::True
        } else {
            match (left, right) {
                (QueryResult::ResourceExceeded(kind), _) => QueryResult::ResourceExceeded(kind),
                (_, QueryResult::ResourceExceeded(kind)) => QueryResult::ResourceExceeded(kind),
                (QueryResult::Unknown(reason), _) => QueryResult::Unknown(reason),
                (_, QueryResult::Unknown(reason)) => QueryResult::Unknown(reason),
                _ => QueryResult::False,
            }
        }
    }

    /// Assert FOL facts from a logic buffer into the knowledge base.
    /// Stores the buffer in the fact registry and returns a unique fact ID.
    fn assert_fact_inner(&self, logic: LogicBuffer, label: String) -> Result<u64, String> {
        let mut inner = self.inner.borrow_mut();
        let id = inner.fresh_fact_id();
        inner.current_assertion_id = Some(id);
        process_assertion(&mut inner, &logic)?;
        inner.current_assertion_id = None;
        inner.fact_registry.insert(
            id,
            FactRecord {
                id,
                buffer: logic,
                label,
                retracted: false,
            },
        );
        Ok(id)
    }

    /// Assert a fact with a pre-assigned ID. Used for replay from persistent store.
    /// Advances the internal counter past the given ID.
    pub fn assert_fact_with_id(&self, logic: LogicBuffer, label: String, id: u64) -> Result<(), String> {
        let mut inner = self.inner.borrow_mut();
        if id >= inner.fact_counter {
            inner.fact_counter = id + 1;
        }
        process_assertion(&mut inner, &logic)?;
        inner.fact_registry.insert(
            id,
            FactRecord {
                id,
                buffer: logic,
                label,
                retracted: false,
            },
        );
        Ok(())
    }

    /// Retract a previously asserted fact by its ID.
    /// Uses incremental removal: removes the fact from indexes directly
    /// instead of rebuilding the entire KB.
    fn retract_fact_inner(&self, id: u64) -> Result<(), String> {
        let mut inner = self.inner.borrow_mut();
        let record = match inner.fact_registry.get_mut(&id) {
            None => return Err(format!("Fact #{} not found", id)),
            Some(r) if r.retracted => return Ok(()), // idempotent
            Some(r) => {
                r.retracted = true;
                r.clone()
            }
        };

        // Check if this assertion involved Skolemization (existential variables
        // or ForAll). If so, fall back to full rebuild — re-deriving Skolem subs
        // with a temporary counter won't match the originals.
        let has_skolems = record.buffer.nodes.iter().any(|n| {
            matches!(
                n,
                LogicNode::ExistsNode(_) | LogicNode::ForAllNode(_)
            )
        });

        if has_skolems || inner.rule_source_map.contains_key(&id) {
            // Complex assertion (rules or Skolems) — fall back to full rebuild.
            return Self::rebuild_inner(&mut inner);
        }

        // Simple ground fact — remove incrementally from all indexes.
        let skolem_subs = HashMap::new();
        let mut typed_leaves = Vec::new();
        collect_ground_facts(
            &record.buffer,
            record.buffer.roots.first().copied().unwrap_or(0),
            &skolem_subs,
            None,
            &mut typed_leaves,
        );

        let mut had_du = false;
        for fact in &typed_leaves {
            inner.fact_store.remove(fact);
            let gf = fact.inner();
            for (pos, arg) in gf.args.iter().enumerate() {
                if let Some(val_map) = inner.arg_position_index.get_mut(&(gf.relation.clone(), pos))
                {
                    if let Some(entries) = val_map.get_mut(arg) {
                        entries.retain(|f| f != fact);
                    }
                }
            }
            if let StoredFact::Bare(gf) = fact {
                if gf.relation == "du" {
                    had_du = true;
                }
            }
        }

        // If du facts were removed, rebuild equivalence from remaining du facts.
        if had_du {
            inner.equivalence_parent.clear();
            inner.equivalence_classes.clear();
            let all_facts: Vec<StoredFact> = inner.fact_store.all_facts().iter().cloned().collect();
            for fact in &all_facts {
                if let StoredFact::Bare(gf) = fact {
                    if gf.relation == "du" && gf.args.len() == 2 {
                        union_terms(&mut inner, &gf.args[0], &gf.args[1]);
                    }
                }
            }
        }

        inner.domain_members_dirty = true;
        Ok(())
    }

    /// Full rebuild from non-retracted facts. Kept as fallback / consistency check.
    pub fn rebuild(&self) -> Result<(), String> {
        let mut inner = self.inner.borrow_mut();
        Self::rebuild_inner(&mut inner)
    }

    /// Rebuild the KB from all non-retracted facts.
    /// Preserves fact_registry and fact_counter; resets all derived state.
    fn rebuild_inner(inner: &mut KnowledgeBaseInner) -> Result<(), String> {
        // Reset derived state (interner too — all interned keys become invalid)
        inner.skolem_counter = 0;
        inner.known_entities.clear();
        inner.known_event_entities.clear();
        inner.known_descriptions.clear();
        inner.known_rules.clear();
        inner.skolem_fn_registry.clear();
        inner.fact_store.clear();
        inner.universal_rules.clear();
        inner.pred_dep_graph.clear();
        inner.equivalence_parent.clear();
        inner.equivalence_classes.clear();
        inner.predicate_registry.clear();
        inner.arg_position_index.clear();
        inner.rule_source_map.clear();

        // Collect non-retracted buffers ordered by ID (clone to avoid borrow conflict)
        let mut entries: Vec<(&u64, &FactRecord)> = inner
            .fact_registry
            .iter()
            .filter(|(_, r)| !r.retracted)
            .collect();
        entries.sort_by_key(|(id, _)| **id);
        let buffers: Vec<LogicBuffer> = entries.iter().map(|(_, r)| r.buffer.clone()).collect();

        // Replay with diagnostic output suppressed
        inner.rebuilding = true;
        for buf in &buffers {
            // Stratification check is skipped during rebuild (inner.rebuilding == true).
            let _ = process_assertion(inner, buf);
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

    /// Single-pass entailment check at the current max_chain_depth.
    fn run_entailment_check(&self, logic: &LogicBuffer) -> Result<QueryResult, String> {
        clear_pred_cache();
        let mut inner = self.inner.borrow_mut();
        inner.ensure_domain_members_cached();
        let mut overall = QueryResult::True;
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            let result = check_formula_holds(logic, root_id, &mut subs, &mut inner, None)?;
            overall = Self::combine_root_results(overall, result);
        }
        Ok(overall)
    }

    /// Check whether all root formulas in the logic buffer are entailed by the KB.
    /// Uses iterative deepening: tries depth 1, 2, ..., max_chain_depth.
    /// Guarantees finding the shallowest proof.
    fn query_entailment_inner(&self, logic: LogicBuffer) -> Result<QueryResult, String> {
        let configured_max = self.inner.borrow().max_chain_depth;
        for depth_limit in 1..=configured_max {
            self.inner.borrow_mut().max_chain_depth = depth_limit;
            let result = self.run_entailment_check(&logic)?;
            if !matches!(result, QueryResult::ResourceExceeded(ResourceKind::Depth)) {
                self.inner.borrow_mut().max_chain_depth = configured_max;
                return Ok(result);
            }
        }
        self.inner.borrow_mut().max_chain_depth = configured_max;
        Ok(QueryResult::ResourceExceeded(ResourceKind::Depth))
    }

    /// Find all satisfying binding sets for existential variables in the query formula.
    /// Returns one `Vec<WitnessBinding>` per satisfying assignment.
    fn query_find_inner(&self, logic: LogicBuffer) -> Result<Vec<Vec<WitnessBinding>>, String> {
        clear_pred_cache();
        let mut inner = self.inner.borrow_mut();
        inner.ensure_domain_members_cached();
        let mut result_sets: Option<Vec<Vec<(String, GroundTerm)>>> = None;
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            let witnesses = find_witnesses(&logic, root_id, &mut subs, &mut inner, None)?;
            match result_sets {
                None => result_sets = Some(witnesses),
                Some(prev) => {
                    if witnesses.is_empty() {
                        return Ok(vec![]);
                    }
                    // Join binding sets across roots: shared variables must agree,
                    // and fresh variables from later roots are preserved.
                    let mut joined = Vec::new();
                    for prev_bindings in prev {
                        for witness_bindings in &witnesses {
                            if let Some(combined) =
                                merge_witness_bindings(&prev_bindings, witness_bindings)
                            {
                                joined.push(combined);
                            }
                        }
                    }
                    if joined.is_empty() {
                        return Ok(vec![]);
                    }
                    result_sets = Some(joined);
                }
            }
        }
        let binding_sets = result_sets.unwrap_or_default();
        Ok(binding_sets
            .into_iter()
            .map(|bindings| {
                bindings
                    .into_iter()
                    .map(|(var, gt)| WitnessBinding {
                        variable: var,
                        term: ground_term_to_logical_term(&gt),
                    })
                    .collect()
            })
            .collect())
    }

    /// Single-pass entailment check with proof trace at the current max_chain_depth.
    fn run_entailment_check_with_proof(
        &self,
        logic: &LogicBuffer,
    ) -> Result<(QueryResult, ProofTrace), String> {
        clear_pred_cache();
        let mut inner = self.inner.borrow_mut();
        inner.ensure_domain_members_cached();
        let mut steps: Vec<ProofStep> = Vec::new();
        let mut memo: HashMap<String, u32> = HashMap::new();
        let mut root_children: Vec<u32> = Vec::new();
        let mut overall = QueryResult::True;
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            let result = check_formula_holds(logic, root_id, &mut subs, &mut inner, None)?;
            overall = Self::combine_root_results(overall, result);
            let mut trace_subs = HashMap::new();
            let (holds, step_idx) = check_formula_holds_traced(
                logic,
                root_id,
                &mut trace_subs,
                &mut inner,
                &mut steps,
                None,
                &mut memo,
            )?;
            root_children.push(step_idx);
            let _ = holds;
        }
        let root = if root_children.len() == 1 {
            root_children[0]
        } else {
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::Conjunction,
                holds: overall.is_true(),
                children: root_children,
            });
            idx
        };
        Ok((overall, ProofTrace { steps, root }))
    }

    /// Check entailment with proof trace using iterative deepening.
    fn query_entailment_with_proof_inner(
        &self,
        logic: LogicBuffer,
    ) -> Result<(QueryResult, ProofTrace), String> {
        let configured_max = self.inner.borrow().max_chain_depth;
        let mut last_trace = ProofTrace {
            steps: vec![],
            root: 0,
        };
        for depth_limit in 1..=configured_max {
            self.inner.borrow_mut().max_chain_depth = depth_limit;
            let (result, trace) = self.run_entailment_check_with_proof(&logic)?;
            if !matches!(result, QueryResult::ResourceExceeded(ResourceKind::Depth)) {
                self.inner.borrow_mut().max_chain_depth = configured_max;
                return Ok((result, trace));
            }
            last_trace = trace;
        }
        self.inner.borrow_mut().max_chain_depth = configured_max;
        Ok((
            QueryResult::ResourceExceeded(ResourceKind::Depth),
            last_trace,
        ))
    }
}

fn merge_witness_bindings(
    left: &[(String, GroundTerm)],
    right: &[(String, GroundTerm)],
) -> Option<Vec<(String, GroundTerm)>> {
    let mut combined = left.to_vec();
    for (var, val) in right {
        match combined
            .iter()
            .find(|(existing_var, _)| existing_var == var)
        {
            Some((_, existing_val)) if existing_val != val => return None,
            Some(_) => {}
            None => combined.push((var.clone(), val.clone())),
        }
    }
    Some(combined)
}

/// Public API for native callers (lasna, nibli-engine).
/// Uses smuni's logic types directly — no bridge conversion needed.
impl KnowledgeBase {
    pub fn new() -> Self {
        KnowledgeBase {
            inner: RefCell::new(KnowledgeBaseInner::new()),
        }
    }

    /// Create a KB with a custom fact store backend (e.g., persistent redb).
    pub fn with_store(store: Box<dyn fact_store::FactStore>) -> Self {
        let mut inner = KnowledgeBaseInner::new();
        inner.fact_store = store;
        KnowledgeBase {
            inner: RefCell::new(inner),
        }
    }

    pub fn assert_fact(&self, logic: LogicBuffer, label: String) -> Result<u64, NibliError> {
        self.assert_fact_inner(logic, label)
            .map_err(NibliError::Semantic)
    }

    /// Run a query under temporary assumptions without mutating the real KB.
    /// Clones the KB, asserts all assumptions into the clone, runs the callback,
    /// and discards the clone. The original KB is untouched.
    ///
    /// Supports multiple independent hypotheticals (each gets its own snapshot)
    /// and nesting (the callback receives a `&KnowledgeBase` with `with_assumptions`).
    pub fn with_assumptions<F, R>(
        &self,
        assumptions: &[LogicBuffer],
        f: F,
    ) -> Result<R, NibliError>
    where
        F: FnOnce(&KnowledgeBase) -> R,
    {
        let snapshot = self.inner.borrow().clone();
        let temp_kb = KnowledgeBase {
            inner: RefCell::new(snapshot),
        };
        for buf in assumptions {
            temp_kb.assert_fact(buf.clone(), "assumption".into())?;
        }
        Ok(f(&temp_kb))
    }

    /// Register an integrity constraint: a set of facts that must NOT all hold simultaneously.
    /// Checked after every fact insertion (permissive mode: warns on violation).
    pub fn register_constraint(&self, label: String, conjuncts: Vec<kb::StoredFact>) {
        let predicates: Vec<String> = conjuncts.iter().map(|c| c.relation().to_string()).collect();
        let mut inner = self.inner.borrow_mut();
        inner.integrity_constraints.push(kb::IntegrityConstraint {
            label,
            conjuncts,
            predicates,
        });
    }

    pub fn query_entailment(&self, logic: LogicBuffer) -> Result<QueryResult, NibliError> {
        self.query_entailment_inner(logic).map_err(NibliError::Reasoning)
    }

    pub fn query_find(&self, logic: LogicBuffer) -> Result<Vec<Vec<WitnessBinding>>, NibliError> {
        self.query_find_inner(logic).map_err(NibliError::Reasoning)
    }

    /// Count the number of distinct witness binding sets satisfying the formula.
    pub fn count_witnesses(&self, logic: LogicBuffer) -> Result<usize, NibliError> {
        self.query_find(logic).map(|bindings| bindings.len())
    }

    /// Aggregate numeric values of a named variable across all witness binding sets.
    /// Returns `None` if no numeric witnesses found for the variable.
    pub fn aggregate(
        &self,
        logic: LogicBuffer,
        variable: &str,
        op: nibli_types::logic::AggregateOp,
    ) -> Result<Option<f64>, NibliError> {
        let bindings = self.query_find(logic)?;
        let values: Vec<f64> = bindings
            .iter()
            .filter_map(|binding_set| {
                binding_set
                    .iter()
                    .find(|b| b.variable == variable)
                    .and_then(|b| match &b.term {
                        LogicalTerm::Number(n) => Some(*n),
                        _ => None,
                    })
            })
            .collect();
        if values.is_empty() {
            return Ok(None);
        }
        use nibli_types::logic::AggregateOp;
        let result = match op {
            AggregateOp::Sum => values.iter().sum(),
            AggregateOp::Min => values.iter().cloned().reduce(f64::min).unwrap_or(0.0),
            AggregateOp::Max => values.iter().cloned().reduce(f64::max).unwrap_or(0.0),
            AggregateOp::Avg => values.iter().sum::<f64>() / values.len() as f64,
        };
        Ok(Some(result))
    }

    pub fn query_entailment_with_proof(
        &self,
        logic: LogicBuffer,
    ) -> Result<(QueryResult, ProofTrace), NibliError> {
        self.query_entailment_with_proof_inner(logic)
            .map_err(NibliError::Reasoning)
    }

    pub fn reset(&self) -> Result<(), NibliError> {
        self.inner.borrow_mut().reset();
        Ok(())
    }

    pub fn retract_fact(&self, id: u64) -> Result<(), NibliError> {
        self.retract_fact_inner(id).map_err(NibliError::Reasoning)
    }

    pub fn list_facts(&self) -> Result<Vec<FactSummary>, NibliError> {
        self.list_facts_inner().map_err(NibliError::Reasoning)
    }

    /// Scan the KB for contradictions. Returns a list of human-readable
    /// contradiction descriptions. An empty list means no contradictions found.
    ///
    /// Checks:
    /// 1. Integrity constraint violations (conjuncts that all hold simultaneously)
    /// 2. Predicate arity inconsistencies (same predicate with different arities)
    /// 3. Equality contradictions (du(a,b) where a and b have conflicting properties
    ///    under registered integrity constraints)
    pub fn check_contradictions(&self) -> Vec<String> {
        let mut violations = Vec::new();

        let inner = self.inner.borrow();

        // 1. Check integrity constraints.
        for constraint in &inner.integrity_constraints {
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
                violations.push(format!(
                    "Integrity violation '{}': {} all hold",
                    constraint.label,
                    facts.join(" ∧ ")
                ));
            }
        }

        // 2. Check predicate arity consistency across the fact store.
        // The predicate registry tracks first-seen arity. Scan all facts for mismatches.
        let mut arity_map: HashMap<String, usize> = HashMap::new();
        for fact in inner.fact_store.all_facts() {
            let rel = fact.relation().to_string();
            let arity = fact.inner().args.len();
            match arity_map.get(&rel) {
                Some(&expected) if expected != arity => {
                    violations.push(format!(
                        "Arity inconsistency: '{}' has facts with {} and {} arguments",
                        rel, expected, arity
                    ));
                }
                None => {
                    arity_map.insert(rel, arity);
                }
                _ => {}
            }
        }

        // 3. Check equality-induced constraint violations.
        // If du(a,b) and a constraint says "deny P(a) ∧ Q(a)", but P(a) and Q(b) are
        // asserted (which means Q(a) holds via equivalence), flag it.
        if !inner.equivalence_parent.is_empty() && !inner.integrity_constraints.is_empty() {
            for constraint in &inner.integrity_constraints {
                // For each conjunct, expand by equivalence class and check all combos.
                let expanded: Vec<Vec<StoredFact>> = constraint
                    .conjuncts
                    .iter()
                    .map(|c| {
                        let gf = c.inner();
                        let equiv_args: Vec<Vec<GroundTerm>> = gf
                            .args
                            .iter()
                            .map(|arg| {
                                get_equivalence_class_readonly(
                                    &inner.equivalence_parent,
                                    &inner.equivalence_classes,
                                    arg,
                                )
                            })
                            .collect();
                        // Generate all argument combinations.
                        let mut variants = Vec::new();
                        fn cartesian(
                            sets: &[Vec<GroundTerm>],
                            idx: usize,
                            current: &mut Vec<GroundTerm>,
                            out: &mut Vec<Vec<GroundTerm>>,
                        ) {
                            if idx == sets.len() {
                                out.push(current.clone());
                                return;
                            }
                            for val in &sets[idx] {
                                current.push(val.clone());
                                cartesian(sets, idx + 1, current, out);
                                current.pop();
                            }
                        }
                        let mut buf = Vec::new();
                        cartesian(&equiv_args, 0, &mut buf, &mut variants);
                        variants
                            .into_iter()
                            .map(|args| {
                                StoredFact::with_tense_from(
                                    GroundFact::new(gf.relation.clone(), args),
                                    c,
                                )
                            })
                            .collect()
                    })
                    .collect();

                // Check if any combination of expanded conjuncts all hold.
                fn check_combos(
                    expanded: &[Vec<StoredFact>],
                    idx: usize,
                    store: &dyn crate::fact_store::FactStore,
                ) -> bool {
                    if idx == expanded.len() {
                        return true; // All conjuncts satisfied.
                    }
                    expanded[idx]
                        .iter()
                        .any(|variant| store.contains(variant) && check_combos(expanded, idx + 1, store))
                }

                if check_combos(&expanded, 0, &*inner.fact_store) {
                    let facts: Vec<String> = constraint
                        .conjuncts
                        .iter()
                        .map(|c| c.to_display_string())
                        .collect();
                    let msg = format!(
                        "Equality-expanded integrity violation '{}': {} (via du equivalence)",
                        constraint.label,
                        facts.join(" ∧ ")
                    );
                    if !violations.contains(&msg) {
                        violations.push(msg);
                    }
                }
            }
        }

        violations
    }
}

#[cfg(test)]

#[cfg(test)]
mod tests;
