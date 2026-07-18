//! nibli-reason (logic/reasoning) engine: FOL assertion and query via demand-driven backward-chaining.
//!
//! This is the core inference component of Nibli. It maintains a stateful knowledge
//! base with a fact index and backward-chaining rule engine:
//!
//! - **Fact assertion** — Ground predicates stored as typed `StoredFact` via pluggable `FactStore` backend.
//!   Universal quantifiers compile to `UniversalRuleRecord` templates for backward-chaining.
//! - **Entailment queries** — Recursive formula checking via [`check_formula_holds`] with
//!   demand-driven backward-chaining through universal rules.
//! - **Proof traces** — [`check_formula_holds_recording`] builds a proof tree recording which
//!   rule/axiom was applied at each step (19 proof rule variants). Multi-hop derivation
//!   provenance traces derived facts through universal rule chains via backward-chaining.
//! - **Witness extraction** — [`find_witnesses`] returns all satisfying entity bindings for
//!   existential variables.
//! - **Compute dispatch** — `ComputeNode` predicates are forwarded to the host-provided
//!   `compute-backend` WIT interface for external evaluation.
//!
//! The knowledge base uses `RefCell` (not `Mutex`) — single-threaded WASI. All
//! mutable state — facts, rules, the predicate-result cache, the compute
//! dispatch, and the cancel flag — lives PER-INSTANCE on `KnowledgeBaseInner`;
//! there are no global or thread-local statics, so distinct KBs (e.g. one per
//! request on the multithreaded server) never interfere.

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
mod reasoning;
mod rules;

pub use compute::ComputeRequest;

use compute::*;
use reasoning::*;
use rules::*;

/// The built-in arithmetic predicates marked as `ComputeNode` by default —
/// `product` (×), `sum` (+), `quotient` (÷). The shared default for every
/// embedder (nibli-engine, nibli-pipeline, nibli-wasm), paired with
/// `transform_compute_nodes`.
pub fn default_compute_predicates() -> HashSet<String> {
    nibli_types::relations::BUILTIN_ARITHMETIC
        .iter()
        .map(|s| s.to_string())
        .collect()
}

/// Transform registered compute predicates from Predicate → ComputeNode in a logic buffer.
/// Call this after nibli-semantics compilation and before asserting/querying.
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
            // Shared with And/Or so the four-valued non-definitive precedence cannot drift.
            reasoning::combine_indeterminate(left, right)
        }
    }

    /// Assert FOL facts from a logic buffer into the knowledge base.
    /// Stores the buffer in the fact registry and returns a unique fact ID.
    fn assert_fact_inner(&self, logic: LogicBuffer, label: String) -> Result<u64, String> {
        let mut inner = self.inner.borrow_mut();
        let id = inner.fresh_fact_id();
        inner.current_assertion_id = Some(id);
        let result = process_assertion(&mut inner, &logic);
        // ALWAYS clear: a stale id would mis-attribute the NEXT assertion's rules
        // in rule_source_map (register_rule reads current_assertion_id).
        inner.current_assertion_id = None;
        if let Err(e) = result {
            // Atomic rollback. A multi-root assertion that fails on a later root
            // leaves earlier roots' facts/rules in the live store, but the
            // FactRecord is only inserted on success — so those facts would be
            // orphaned (un-listable, un-retractable). The failed assertion has no
            // FactRecord, so rebuilding from the durable registry reproduces the
            // exact pre-assertion state, discarding the partial mutation.
            let rb = Self::rebuild_inner(&mut inner);
            invalidate_pred_cache(&inner);
            return match rb {
                Ok(()) => Err(e),
                Err(re) => Err(format!("{e} (additionally, rollback failed: {re})")),
            };
        }
        inner.fact_registry.insert(
            id,
            FactRecord {
                id,
                buffer: logic,
                label,
                retracted: false,
            },
        );
        invalidate_pred_cache(&inner); // Tabling: KB mutated, clear cached derivations.
        Ok(id)
    }

    /// Assert a fact with a pre-assigned ID. Used for replay from persistent store.
    /// Advances the internal counter past the given ID.
    pub fn assert_fact_with_id(
        &self,
        logic: LogicBuffer,
        label: String,
        id: u64,
    ) -> Result<(), String> {
        let mut inner = self.inner.borrow_mut();
        if id >= inner.fact_counter {
            inner.fact_counter = id + 1;
        }
        // Attribute any rule compiled during this replay to THIS fact in
        // rule_source_map (otherwise a later retract of a replayed rule-producing
        // fact leaves a stale rule behind).
        inner.current_assertion_id = Some(id);
        let result = process_assertion(&mut inner, &logic);
        inner.current_assertion_id = None;
        if let Err(e) = result {
            let rb = Self::rebuild_inner(&mut inner);
            invalidate_pred_cache(&inner);
            return match rb {
                Ok(()) => Err(e),
                Err(re) => Err(format!("{e} (additionally, rollback failed: {re})")),
            };
        }
        inner.fact_registry.insert(
            id,
            FactRecord {
                id,
                buffer: logic,
                label,
                retracted: false,
            },
        );
        invalidate_pred_cache(&inner);
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

        // Check if any forward-chaining rules are active. If so, forward-derived
        // facts may depend on the retracted fact — fall back to full rebuild.
        let has_forward_rules = inner
            .universal_rules
            .values()
            .flat_map(|v| v.iter())
            .any(|r| r.forward);

        if has_forward_rules {
            let result = Self::rebuild_inner(&mut inner);
            invalidate_pred_cache(&inner);
            return result;
        }

        // Check if this assertion involved Skolemization (existential variables,
        // ForAll, or a numeric Count quantifier). If so, fall back to full rebuild
        // — re-deriving Skolem subs with a temporary counter won't match the
        // originals. A CountNode additionally generates `count-1` extra Skolem
        // witnesses (`generate_count_extra_witnesses`: fresh_skolem + note_entity,
        // plus an asserted witness fact for a flat body) that the incremental path
        // never removes; rebuilding from the surviving records (the retracted
        // count assertion excluded) drops them. Negation-bearing buffers also take
        // the rebuild path: a negated ground root is recorded in the negative-fact
        // registry (see `record_negative_ground_fact`), and replaying the surviving
        // records repopulates that registry exactly.
        let has_skolems = record.buffer.nodes.iter().any(|n| {
            matches!(
                n,
                LogicNode::ExistsNode(_) | LogicNode::ForAllNode(_) | LogicNode::CountNode(_)
            )
        });
        let has_negation = record
            .buffer
            .nodes
            .iter()
            .any(|n| matches!(n, LogicNode::NotNode(_)));

        if has_skolems || has_negation || inner.rule_source_map.contains_key(&id) {
            // Complex assertion (rules, Skolems, or negations) — full rebuild.
            let result = Self::rebuild_inner(&mut inner);
            invalidate_pred_cache(&inner);
            return result;
        }

        // Simple ground fact — remove incrementally from all indexes.
        // Walk ALL roots: assertion processes every root, so retraction must too
        // (processing only the first root left later roots' facts orphaned).
        let skolem_subs = HashMap::new();
        let mut typed_leaves = Vec::new();
        for &root_id in &record.buffer.roots {
            collect_ground_facts(
                &record.buffer,
                root_id,
                &skolem_subs,
                None,
                &mut typed_leaves,
            );
        }

        // The HashSet fact store tracks no multiplicity: if another LIVE record
        // still asserts the same ground fact, removing it here would conflate the
        // two records (queries flip to False while list_facts shows an active
        // record asserting the fact, and a later rebuild resurrects it). Recompute
        // each surviving record's ground leaves and keep any fact that is still
        // asserted elsewhere. This is exact for the buffers this path handles
        // (skolem-free): a skolem-bearing survivor's Exists-wrapped leaves carry
        // assertion-unique Skolem constants and cannot collide with a skolem-free
        // leaf, while its non-quantified leaves ARE recovered by the same
        // empty-substitution walk used here.
        let mut still_asserted: HashSet<StoredFact> = HashSet::new();
        for other in inner.fact_registry.values() {
            if other.retracted {
                continue;
            }
            for &root_id in &other.buffer.roots {
                let mut leaves = Vec::new();
                collect_ground_facts(&other.buffer, root_id, &skolem_subs, None, &mut leaves);
                still_asserted.extend(leaves);
            }
        }

        let mut had_equals = false;
        for fact in &typed_leaves {
            if still_asserted.contains(fact) {
                continue; // Another live record still asserts this fact — keep it.
            }
            inner.fact_store.remove(fact);
            let gf = fact.inner();
            for (pos, arg) in gf.args.iter().enumerate() {
                if let Some(val_map) = inner
                    .arg_position_index
                    .get_mut(&(gf.relation.clone(), pos))
                {
                    if let Some(entries) = val_map.get_mut(arg) {
                        entries.retain(|f| f != fact);
                    }
                }
            }
            if let StoredFact::Bare(gf) = fact {
                if gf.relation == "equals" {
                    had_equals = true;
                }
            }
        }

        // If du facts were removed, rebuild equivalence from remaining du facts.
        if had_equals {
            inner.equivalence_parent.clear();
            inner.equivalence_classes.clear();
            let all_facts: Vec<StoredFact> = inner.fact_store.all_facts().cloned().collect();
            for fact in &all_facts {
                if let StoredFact::Bare(gf) = fact {
                    if gf.relation == "equals" && gf.args.len() == 2 {
                        union_terms(&mut inner, &gf.args[0], &gf.args[1]);
                    }
                }
            }
        }

        inner.domain_members_dirty = true;
        invalidate_pred_cache(&inner); // Tabling: KB mutated.
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
        // Preserve user-declared arg sorts (set via `set_predicate_sorts`): replay
        // only re-infers arity+source per predicate, never the sorts, so clearing
        // `predicate_registry` below would silently drop them.
        let saved_arg_sorts: Vec<(String, Vec<String>)> = inner
            .predicate_registry
            .iter()
            .filter(|(_, sig)| !sig.arg_sorts.is_empty())
            .map(|(pred, sig)| (pred.clone(), sig.arg_sorts.clone()))
            .collect();

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
        inner.negative_facts.clear();
        inner.disjunctive_constraints.clear();

        // Collect non-retracted buffers + their ids ordered by ID (owned, to avoid
        // a borrow conflict with the mutable replay below).
        let mut entries: Vec<(&u64, &FactRecord)> = inner
            .fact_registry
            .iter()
            .filter(|(_, r)| !r.retracted)
            .collect();
        entries.sort_by_key(|(id, _)| **id);
        let ids: Vec<u64> = entries.iter().map(|(id, _)| **id).collect();
        let buffers: Vec<LogicBuffer> = entries.iter().map(|(_, r)| r.buffer.clone()).collect();

        // Replay with diagnostic output + stratification checks suppressed
        // (inner.rebuilding == true). Collect-and-continue: replay EVERY surviving
        // fact so the store stays maximally consistent, accumulating errors rather
        // than silently dropping a fact that fails to replay.
        inner.rebuilding = true;
        let mut replay_errors: Vec<(u64, String)> = Vec::new();
        for (buf, &fid) in buffers.iter().zip(ids.iter()) {
            if let Err(e) = process_assertion(inner, buf) {
                replay_errors.push((fid, e));
            }
        }
        inner.rebuilding = false;

        // Restore the preserved sorts into the re-populated registry.
        for (pred, sorts) in saved_arg_sorts {
            let arity = sorts.len();
            inner
                .predicate_registry
                .entry(pred)
                .or_insert_with(|| PredicateSignature {
                    arity,
                    source: SignatureSource::Inferred,
                    arg_sorts: Vec::new(),
                })
                .arg_sorts = sorts;
        }

        if replay_errors.is_empty() {
            Ok(())
        } else {
            let detail = replay_errors
                .iter()
                .map(|(id, e)| format!("#{id}: {e}"))
                .collect::<Vec<_>>()
                .join("; ");
            Err(format!("rebuild replay errors: {detail}"))
        }
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

    /// Set the backward-chaining depth bound (`max_chain_depth`, default 10) —
    /// the "Configurable" knob `GUARANTEES.md §Resource Limits` documents.
    /// Iterative deepening tries 1..=depth; a query whose shallowest proof needs a
    /// longer chain returns `ResourceExceeded(Depth)`, never FALSE. Practical note:
    /// deepening cost grows steeply with depth (each level re-explores the shallower
    /// search — measured ~15×+ per level on linear rule chains), so the bound is a
    /// soundness/termination contract, not a performance envelope. Values below 1
    /// are clamped to 1.
    pub fn set_max_chain_depth(&self, depth: usize) {
        self.inner.borrow_mut().max_chain_depth = depth.max(1);
    }

    /// Single-pass entailment check at the current max_chain_depth.
    fn run_entailment_check(&self, logic: &LogicBuffer) -> Result<QueryResult, String> {
        // Enable WITHOUT clearing: the cache is cleared once before the
        // iterative-deepening loop in query_entailment_inner, then definitive
        // results persist across depth passes (cross-depth tabling).
        let mut inner = self.inner.borrow_mut();
        enable_pred_cache(&inner);
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
        // Tabling: clear once, persist across depth iterations.
        let configured_max = {
            let inner = self.inner.borrow();
            clear_and_enable_pred_cache(&inner);
            inner.max_chain_depth
        };
        for depth_limit in 1..=configured_max {
            self.inner.borrow_mut().max_chain_depth = depth_limit;
            // Restore the configured depth on EVERY exit, including the error
            // path (e.g. cooperative cancellation), so an aborted query never
            // leaves a reusable KB pinned at a partial deepening depth.
            let result = match self.run_entailment_check(&logic) {
                Ok(result) => result,
                Err(e) => {
                    self.inner.borrow_mut().max_chain_depth = configured_max;
                    return Err(e);
                }
            };
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
        // Surfaced (as an Err) when witness enumeration is CUT at the depth/cycle
        // horizon: find/count/aggregate must refuse a definitive (under)count rather
        // than silently report a wrong quantity. See `find_witnesses` /
        // `find_horizon_hit` — this is the find-path analog of the entailment path's
        // `ResourceExceeded(Depth)` verdict.
        const INCOMPLETE_MSG: &str = "witness enumeration incomplete: a witness exceeds the depth/cycle budget, so \
             find/count/aggregate would undercount — raise the depth limit or simplify the rules";
        let mut inner = self.inner.borrow_mut();
        clear_and_enable_pred_cache(&inner);
        inner.ensure_domain_members_cached();
        inner.find_horizon_hit = false;
        let mut result_sets: Option<Vec<Vec<(String, GroundTerm)>>> = None;
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            let witnesses = find_witnesses(&logic, root_id, &mut subs, &mut inner, None)?;
            match result_sets {
                None => result_sets = Some(witnesses),
                Some(prev) => {
                    if witnesses.is_empty() {
                        if inner.find_horizon_hit {
                            return Err(INCOMPLETE_MSG.to_string());
                        }
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
                        if inner.find_horizon_hit {
                            return Err(INCOMPLETE_MSG.to_string());
                        }
                        return Ok(vec![]);
                    }
                    result_sets = Some(joined);
                }
            }
        }
        // Enumeration finished — but if any witness leaf was cut at the depth/cycle
        // horizon, the result is an under-count, not a definitive one. Refuse it.
        if inner.find_horizon_hit {
            return Err(INCOMPLETE_MSG.to_string());
        }
        let mut binding_sets = result_sets.unwrap_or_default();
        // Determinism + dedup: witness enumeration touches HashSet-backed
        // candidate collections, so the order binding sets arrive in is
        // hasher-seed dependent, and the SAME solution can arrive via distinct
        // candidates (an Or-overlap where one entity satisfies both disjuncts,
        // equivalence-class expansion, or the shared entailment/find candidate
        // superset). Sort the outer list by each set's canonical key (its
        // sorted (var, term) pairs) so `[Find]` output is byte-reproducible
        // across runs and processes, THEN drop adjacent canonical duplicates so
        // `count_witnesses`/`aggregate` count each distinct binding exactly once
        // (an inflated count would be a hallucinated quantity). Comparison is at
        // GroundTerm level — distinct terms never collapse; intra-set binding
        // order (structural, inner-to-outer) is preserved for display.
        // ENTITY-LEVEL identity (GUARANTEES §Aggregation): tuples binding an
        // ENTITY variable to a existential-import presupposition witness are dropped
        // entirely — a phantom entity a rule presupposed satisfies ∃/∀ but is
        // not an enumerable "thing". Entity variables = everything except the
        // `_ev*` EVENT vars (description vars `_v{n}` carry answer entities).
        binding_sets.retain(|bindings| {
            !bindings.iter().any(|(var, gt)| {
                !var.starts_with("_ev")
                    && matches!(gt, GroundTerm::Constant(name)
                        if inner.presupposition_witnesses.contains(name.as_str()))
            })
        });
        // The DEDUP key is the binding set projected onto ENTITY variables —
        // `_ev*` event vars are derivation bookkeeping and must not multiply
        // results (pre-change, one dog answered `?? da gerku` once per
        // derivation event) — with each term du-CANONICALIZED so two names for
        // one entity count once. The sort key appends the full raw key so the
        // total order — and therefore WHICH tuple survives dedup — stays
        // byte-reproducible regardless of hasher-seed-dependent arrival order;
        // the survivor's display terms are real asserted names, not
        // canonicalized rewrites.
        let entity_key = |bindings: &Vec<(String, GroundTerm)>| {
            let mut key: Vec<(String, GroundTerm)> = bindings
                .iter()
                .filter(|(var, _)| !var.starts_with("_ev"))
                .map(|(var, gt)| {
                    (
                        var.clone(),
                        find_canonical_readonly(&inner.equivalence_parent, gt),
                    )
                })
                .collect();
            key.sort();
            key
        };
        let full_key = |bindings: &Vec<(String, GroundTerm)>| {
            let mut key = bindings.clone();
            key.sort();
            key
        };
        binding_sets.sort_by_cached_key(|b| (entity_key(b), full_key(b)));
        binding_sets.dedup_by_key(|bindings| entity_key(bindings));
        Ok(binding_sets
            .into_iter()
            .map(|bindings| {
                bindings
                    .into_iter()
                    .map(|(var, gt)| WitnessBinding {
                        variable: var,
                        term: witness_term_to_logical_term(&gt),
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
        // Enable WITHOUT clearing: cleared once before the iterative-deepening
        // loop in query_entailment_with_proof_inner; definitive results persist
        // across depth passes (cross-depth tabling).
        let mut inner = self.inner.borrow_mut();
        enable_pred_cache(&inner);
        inner.ensure_domain_members_cached();
        let mut steps: Vec<ProofStep> = Vec::new();
        let mut memo: HashMap<String, u32> = HashMap::new();
        let mut root_children: Vec<u32> = Vec::new();
        let mut overall = QueryResult::True;
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            // ONE walk per root: the recording evaluator returns the authoritative
            // four-valued verdict AND builds the proof trace, so the trace's
            // per-node `holds` is natively `verdict.is_true()` — no separate
            // untraced pass and no root `holds` reconciliation needed.
            let (result, step_idx) = check_formula_holds_recording(
                logic, root_id, &mut subs, &mut inner, &mut steps, None, &mut memo,
            )?;
            overall = Self::combine_root_results(overall, result);
            root_children.push(step_idx);
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
        let naf_dependent = steps
            .iter()
            .any(|s| matches!(s.rule, ProofRule::Negation) && s.holds);
        // A FALSE verdict is closed-world ("not derivable from the KB") UNLESS a
        // numeric/arithmetic compute DECIDED it (e.g. `5 dunli 3` is genuinely false).
        // The dual of `naf_dependent`: under open-world semantics it would be Unknown.
        let cwa_false = overall.is_false()
            && !steps.iter().any(|s| {
                !s.holds
                    && matches!(
                        &s.rule,
                        ProofRule::ComputeCheck { method, .. }
                            if method == "numeric" || method == "arithmetic"
                    )
            });
        Ok((
            overall,
            ProofTrace {
                steps,
                root,
                naf_dependent,
                cwa_false,
            },
        ))
    }

    /// Check entailment with proof trace using iterative deepening.
    fn query_entailment_with_proof_inner(
        &self,
        logic: LogicBuffer,
    ) -> Result<(QueryResult, ProofTrace), String> {
        // Tabling: clear once, persist across phases.
        let configured_max = {
            let inner = self.inner.borrow();
            clear_and_enable_pred_cache(&inner);
            inner.max_chain_depth
        };
        // Phase 1: find the resolving depth with the CHEAP untraced walk — no proof
        // trace is built (then discarded) on the probe passes. The costly part of a
        // proof query is the ProofStep-tree construction, which (unlike the verdict,
        // which the predicate cache amortizes across depths) is NOT cross-depth-
        // cached, so the old per-depth loop rebuilt D-1 partial traces only to throw
        // them away. If no depth resolves, `resolving_depth` stays `configured_max`
        // so Phase 2 builds the deepest trace (matching the old `last_trace`).
        let mut resolving_depth = configured_max;
        for depth_limit in 1..=configured_max {
            self.inner.borrow_mut().max_chain_depth = depth_limit;
            // Restore the configured depth on the error path too (see
            // query_entailment_inner) — explicit `match`, NOT `?`, so a cancelled
            // query never leaves the KB pinned at a partial deepening depth.
            let result = match self.run_entailment_check(&logic) {
                Ok(r) => r,
                Err(e) => {
                    self.inner.borrow_mut().max_chain_depth = configured_max;
                    return Err(e);
                }
            };
            if !matches!(result, QueryResult::ResourceExceeded(ResourceKind::Depth)) {
                resolving_depth = depth_limit;
                break;
            }
        }
        // Phase 2: build the proof trace ONCE at the resolving depth. The predicate
        // cache (warmed by Phase 1) makes this build's verdict sub-checks cheap; the
        // trace is byte-identical to the former per-depth build because the trace
        // descent never shortcuts on the verdict cache and the fact store is
        // set-idempotent for the only state it reads (`typed_fact_is_asserted`).
        self.inner.borrow_mut().max_chain_depth = resolving_depth;
        let out = self.run_entailment_check_with_proof(&logic);
        self.inner.borrow_mut().max_chain_depth = configured_max;
        out
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

/// Public API for native callers (nibli-pipeline, nibli-engine).
/// Uses nibli-semantics's logic types directly — no bridge conversion needed.
impl KnowledgeBase {
    /// Create a new knowledge base with the default in-memory fact store.
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

    /// Install a cooperative cancellation flag. When the flag is set to `true`,
    /// the next central reasoning checkpoint aborts the in-flight query via the
    /// `Err` channel (the verdict variants are untouched). The native nibli-server
    /// watchdog sets the flag when a request's wall-clock budget elapses, freeing
    /// the blocking thread instead of letting a pathological query run to
    /// completion. No clock is read inside the engine, so the WASI sandbox
    /// guarantee is preserved; nibli-host/nibli-pipeline never install a flag.
    pub fn set_cancel_flag(&self, flag: std::sync::Arc<std::sync::atomic::AtomicBool>) {
        self.inner.borrow_mut().cancel = Some(flag);
    }

    /// Remove any installed cancellation flag (queries run unbounded again).
    pub fn clear_cancel_flag(&self) {
        self.inner.borrow_mut().cancel = None;
    }

    /// Enable/disable informational stdout diagnostics (`[Rule]`/`[Skolem]`/
    /// `[Constraint] Registered`). Default OFF — a silent library; the
    /// server/validate/tavla stay quiet. nibli-pipeline (the nibli-host REPL) and the native
    /// `nibli` REPL opt in. Configuration, not derived state — survives `reset()`.
    pub fn set_verbose(&self, verbose: bool) {
        self.inner.borrow_mut().verbose = verbose;
    }

    /// Whether diagnostic verbosity is enabled.
    pub fn is_verbose(&self) -> bool {
        self.inner.borrow().verbose
    }

    /// Enable/disable STRICT MODE (default OFF — permissive warn-and-insert,
    /// the documented v1 behavior). When on, an arity mismatch or an
    /// integrity-constraint violation REJECTS the offending fact and fails the
    /// assertion (`Err`) ATOMICALLY — the failed assertion's partial mutations
    /// are rolled back via the registry rebuild, exactly like any other
    /// assertion error. Facts inserted internally (forward chaining, compute
    /// auto-assert) are also rejected loudly but cannot fail a user call.
    /// Configuration, not derived state — survives `reset()`; inert during
    /// retraction-replay rebuilds.
    pub fn set_strict(&self, strict: bool) {
        self.inner.borrow_mut().strict = strict;
    }

    /// Whether strict mode is enabled.
    pub fn is_strict(&self) -> bool {
        self.inner.borrow().strict
    }

    /// Enable/disable EXISTENTIAL-IMPORT MODE (default ON — the v0.1 xorlo
    /// behavior, kept byte-identical). When on, a description universal
    /// (`animal(every dog).`) mints a presupposition witness so `∃x. dog(x)`
    /// holds. Set OFF for the clean-core profile (`some` = plain classical ∃,
    /// no phantom entity injected — NIBLI_KR §14.4 item 3). Configuration, not
    /// derived state — survives `reset()`.
    pub fn set_existential_import(&self, on: bool) {
        self.inner.borrow_mut().existential_import = on;
    }

    /// Whether existential-import (xorlo witness minting) is enabled.
    pub fn is_existential_import(&self) -> bool {
        self.inner.borrow().existential_import
    }

    /// Register this KB's external compute dispatch (per-instance — replaces the
    /// old thread-local `register_compute_dispatch`, which the multithreaded
    /// server could never register because each tokio blocking-pool worker had
    /// its own `None` thread-local). Built-in arithmetic (pilji/sumji/dilcu) is
    /// always evaluated locally; everything else is forwarded to `eval`/
    /// `batch_eval`.
    ///
    /// TRUST BOUNDARY: a `true` reply is auto-asserted as a ground fact mid-query
    /// that downstream universal rules can chain on, so a malicious or MITM
    /// backend can seed arbitrary predicates. The backend is part of the trusted
    /// computing base — run it on localhost or a network segment you control.
    /// (Auto-asserted compute facts are non-durable: no FactRecord, never
    /// replayed by rebuild.)
    pub fn set_compute_dispatch(
        &self,
        eval: crate::compute::EvalFn,
        batch_eval: crate::compute::BatchEvalFn,
    ) {
        let mut inner = self.inner.borrow_mut();
        inner.compute_eval = Some(eval);
        inner.compute_batch_eval = Some(batch_eval);
    }

    /// Assert a compiled FOL formula into the knowledge base. Returns the fact ID.
    pub fn assert_fact(&self, logic: LogicBuffer, label: String) -> Result<u64, NibliError> {
        // The assert IS the reasoning stage: by the time this runs the buffer has
        // already passed nibli-semantics, so every failure here (stratification, fail-closed
        // rule compilation, the zero-ingest guard, rebuild replay) is reasoning-layer.
        // The layer contract is Syntax=nibli-kr / Semantic=nibli-semantics / Reasoning=nibli-reason.
        self.assert_fact_inner(logic, label)
            .map_err(NibliError::Reasoning)
    }

    /// Run a query under temporary assumptions without mutating the real KB.
    /// Clones the KB, asserts all assumptions into the clone, runs the callback,
    /// and discards the clone. The original KB is untouched.
    ///
    /// Supports multiple independent hypotheticals (each gets its own snapshot)
    /// and nesting (the callback receives a `&KnowledgeBase` with `with_assumptions`).
    pub fn with_assumptions<F, R>(&self, assumptions: &[LogicBuffer], f: F) -> Result<R, NibliError>
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

    /// Check whether a formula is entailed by the knowledge base (four-valued result).
    pub fn query_entailment(&self, logic: LogicBuffer) -> Result<QueryResult, NibliError> {
        self.query_entailment_inner(logic)
            .map_err(NibliError::Reasoning)
    }

    /// Find all satisfying witness binding sets for existential variables in the formula.
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

    /// Check entailment and return a proof trace showing the full derivation chain.
    pub fn query_entailment_with_proof(
        &self,
        logic: LogicBuffer,
    ) -> Result<(QueryResult, ProofTrace), NibliError> {
        self.query_entailment_with_proof_inner(logic)
            .map_err(NibliError::Reasoning)
    }

    /// Clear all facts, rules, indexes, and derived state.
    pub fn reset(&self) -> Result<(), NibliError> {
        let mut inner = self.inner.borrow_mut();
        inner.reset();
        invalidate_pred_cache(&inner); // Tabling: KB cleared.
        Ok(())
    }

    /// Retract a fact by ID. Uses incremental removal for ground facts,
    /// full rebuild for facts that compiled into rules.
    pub fn retract_fact(&self, id: u64) -> Result<(), NibliError> {
        self.retract_fact_inner(id).map_err(NibliError::Reasoning)
    }

    /// List all active (non-retracted) facts with their IDs and labels.
    pub fn list_facts(&self) -> Result<Vec<FactSummary>, NibliError> {
        self.list_facts_inner().map_err(NibliError::Reasoning)
    }

    /// Mark all rules concluding the given predicate as forward-chaining enabled.
    /// Forward-enabled rules fire eagerly on fact assertion when all conditions
    /// are directly asserted in the fact store.
    ///
    /// FAIL CLOSED: a rule with a negation-as-failure condition (a flat negated
    /// condition or a `poi na <predicate>` group) is NOT forward-enabled — it stays
    /// backward-only, where it is sound (backward chaining re-evaluates `¬Q` at
    /// query time). Forward chaining + NAF has no truth maintenance: a
    /// forward-derived conclusion would never be retracted when a later assertion
    /// makes the negated dependency true. Positive (negation-free) rules enable
    /// normally; `forward = false` (disabling) always applies.
    pub fn set_rule_forward(&self, conclusion_predicate: &str, forward: bool) {
        let mut inner = self.inner.borrow_mut();
        let rebuilding = inner.rebuilding;
        if let Some(rules) = inner.universal_rules.get_mut(conclusion_predicate) {
            for rule in rules.iter_mut() {
                if forward
                    && (!rule.negated_condition_indices.is_empty()
                        || !rule.negated_exists_groups.is_empty())
                {
                    if !rebuilding {
                        eprintln!(
                            "[Forward] rule '{}' has a negation-as-failure condition; \
                             keeping it backward-only (forward chaining + NAF has no \
                             truth maintenance).",
                            rule.label
                        );
                    }
                    continue;
                }
                // Arc::get_mut only succeeds if there's one strong reference.
                // If shared, clone-on-write.
                if let Some(r) = Arc::get_mut(rule) {
                    r.forward = forward;
                } else {
                    let mut cloned = (**rule).clone();
                    cloned.forward = forward;
                    *rule = Arc::new(cloned);
                }
            }
        }
    }

    /// Set priority for all rules concluding the given predicate.
    /// Higher priority = tried first during backward/forward chaining.
    /// Default is 0. Rules with higher priority override lower-priority ones
    /// (defeasible reasoning / exception hierarchies).
    pub fn set_rule_priority(&self, conclusion_predicate: &str, priority: u32) {
        let mut inner = self.inner.borrow_mut();
        if let Some(rules) = inner.universal_rules.get_mut(conclusion_predicate) {
            for rule in rules.iter_mut() {
                if let Some(r) = Arc::get_mut(rule) {
                    r.priority = priority;
                } else {
                    let mut cloned = (**rule).clone();
                    cloned.priority = priority;
                    *rule = Arc::new(cloned);
                }
            }
            // Re-establish the descending-priority order the backward-chain read
            // path relies on (`matching_rules_typed` borrows the bucket as-is).
            sort_rule_bucket(rules);
        }
    }

    /// Declare that an entity belongs to a sort.
    /// e.g., `declare_entity_sort("adam", "person")` means adam is a person.
    pub fn declare_entity_sort(&self, entity: &str, sort: &str) {
        let mut inner = self.inner.borrow_mut();
        inner
            .entity_sorts
            .insert(entity.to_string(), sort.to_string());
    }

    /// Declare a subsort relationship: child ⊂ parent.
    /// e.g., `declare_subsort("person", "animal")` means every person is an animal.
    /// Transitive: if person ⊂ animal and animal ⊂ entity, then person is compatible with entity.
    pub fn declare_subsort(&self, child: &str, parent: &str) {
        let mut inner = self.inner.borrow_mut();
        inner
            .sort_hierarchy
            .entry(child.to_string())
            .or_default()
            .insert(parent.to_string());
    }

    /// Set expected sorts for a predicate's arguments.
    /// e.g., `set_predicate_sorts("gerku", vec!["animal", ""])` means gerku's x1 must be
    /// an "animal" sort, x2 has no sort constraint.
    /// Empty string = no constraint for that position.
    pub fn set_predicate_sorts(&self, predicate: &str, arg_sorts: Vec<String>) {
        let mut inner = self.inner.borrow_mut();
        if let Some(sig) = inner.predicate_registry.get_mut(predicate) {
            sig.arg_sorts = arg_sorts;
        } else {
            inner.predicate_registry.insert(
                predicate.to_string(),
                PredicateSignature {
                    arity: arg_sorts.len(),
                    source: SignatureSource::Inferred,
                    arg_sorts,
                },
            );
        }
    }

    /// Enable tracing for a predicate. When the predicate is encountered
    /// during backward chaining, diagnostic output is printed showing
    /// depth, rule matches, and results.
    pub fn trace_predicate(&self, predicate: &str) {
        self.inner
            .borrow_mut()
            .traced_predicates
            .insert(predicate.to_string());
    }

    /// Disable tracing for a predicate.
    pub fn untrace_predicate(&self, predicate: &str) {
        self.inner.borrow_mut().traced_predicates.remove(predicate);
    }

    /// List all currently traced predicates.
    pub fn traced_predicates(&self) -> Vec<String> {
        self.inner
            .borrow()
            .traced_predicates
            .iter()
            .cloned()
            .collect()
    }

    /// Scan the KB for contradictions. Returns a list of human-readable
    /// contradiction descriptions. An empty list means no contradictions found.
    ///
    /// Checks:
    /// 1. Integrity constraint violations (conjuncts that all hold simultaneously)
    /// 2. Predicate arity inconsistencies (same predicate with different arities)
    /// 3. Equality contradictions (du(a,b) where a and b have conflicting properties
    ///    under registered integrity constraints)
    /// 4. Negation contradictions (an explicitly asserted `na <predicate>` whose
    ///    positive counterpart is also asserted, matched modulo event Skolems)
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
                    expanded[idx].iter().any(|variant| {
                        store.contains(variant) && check_combos(expanded, idx + 1, store)
                    })
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

        // 4. Explicitly asserted negative facts (`na <predicate>`) whose positive
        //    counterpart is asserted. Each negation is stored as a template group
        //    with event arguments generalized to pattern variables (see
        //    `record_negative_ground_fact`); it is violated when one consistent
        //    binding satisfies EVERY template against the asserted fact store —
        //    the whole-group requirement prevents false positives from unrelated
        //    events sharing a predicate. Scope: directly asserted positives only
        //    (no derived facts), same tense only. Query semantics (NAF/CWA) are
        //    unaffected — negatives never enter the positive store.
        // A negative group that is a single flat 2-arg `du(X, Y)` is an asserted
        // INEQUALITY; it is handled by section 5 (union-find aware) rather than
        // the store-membership check here, because equality can hold
        // transitively (`du(X,Z) ∧ du(Z,Y)`) without `du(X,Y)` ever being stored.
        fn flat_equals_pair(group: &[StoredFact]) -> Option<(&GroundTerm, &GroundTerm)> {
            if group.len() == 1 {
                if let StoredFact::Bare(gf) = &group[0] {
                    if gf.relation == "equals" && gf.args.len() == 2 {
                        return Some((&gf.args[0], &gf.args[1]));
                    }
                }
            }
            None
        }

        for group in &inner.negative_facts {
            if flat_equals_pair(group).is_some() {
                continue;
            }
            if negative_group_holds(group, &*inner.fact_store) {
                let facts: Vec<String> = group.iter().map(|f| f.to_display_string()).collect();
                let msg = format!(
                    "Negation contradiction: ¬({}) was asserted, but the positive \
                     counterpart is also asserted",
                    facts.join(" ∧ ")
                );
                if !violations.contains(&msg) {
                    violations.push(msg);
                }
            }
        }

        // 5. Asserted inequalities (`na du`). A flat `na du(X, Y)` is contradicted
        //    when X and Y are equivalent under the du union-find — catching both
        //    a directly-asserted `du(X, Y)` and transitive equality
        //    (`du(X, Z) ∧ du(Z, Y)`) that a store-membership check would miss.
        //    (Reflexive `na du(a, a)` is correctly always a contradiction.)
        for group in &inner.negative_facts {
            if let Some((x, y)) = flat_equals_pair(group) {
                let rx = find_canonical_readonly(&inner.equivalence_parent, x);
                let ry = find_canonical_readonly(&inner.equivalence_parent, y);
                if rx == ry {
                    let msg = format!(
                        "Inequality contradiction: ¬({}) was asserted, but the terms are \
                         equivalent under du",
                        group[0].to_display_string()
                    );
                    if !violations.contains(&msg) {
                        violations.push(msg);
                    }
                }
            }
        }

        // 6. Disjunctive-conclusion constraints `¬(P ∧ ¬Q ∧ ¬R)` (from a rule with a
        //    disjunctive head, `ro lo X cu Q ja R`). Flag a contradiction when, for some
        //    binding, ALL P-conditions hold in the positive store AND EVERY disjunct is
        //    explicitly denied (a stored `na <predicate>` covers it). A disjunct is never
        //    DERIVED (unsound in a Horn engine — `R` might hold instead); the positive
        //    use is served by a disjunctive QUERY. P uses store-membership only (via
        //    `solve_group_bindings` over `fact_store`): a rule-DERIVED P does NOT trigger
        //    this — sound + conservative (it can only MISS a contradiction, never falsely
        //    flag one). The check holds `self.inner.borrow()` and stays store-bound by
        //    design (re-entering the query engine here would be a borrow / re-entrancy
        //    hazard). Pinned by
        //    `test_mixed_conclusion_conservative_p_check_misses_derived_antecedent`.
        for dc in &inner.disjunctive_constraints {
            let bindings = solve_group_bindings(&dc.conditions, &*inner.fact_store);
            let violated = bindings.iter().any(|b| {
                dc.disjuncts.iter().all(|disj| {
                    let substituted: Vec<StoredFact> =
                        disj.iter().map(|f| substitute_fact(f, b)).collect();
                    disjunct_explicitly_denied(&substituted, &inner.negative_facts)
                })
            });
            if violated {
                let msg = format!(
                    "Disjunctive constraint violated '{}': the antecedent holds but every \
                     disjunct is explicitly denied (na)",
                    dc.label
                );
                if !violations.contains(&msg) {
                    violations.push(msg);
                }
            }
        }

        // Determinism: §2 (arity) iterates `all_facts()` and §4/§5 iterate the
        // `negative_facts` HashSet, so the violation order is otherwise
        // hasher-seed dependent. A single global sort fixes the order of every
        // section at once (ordering only — the SET of violations is unchanged).
        violations.sort();
        violations
    }
}

#[cfg(test)]
mod tests;
