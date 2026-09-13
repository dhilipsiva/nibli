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
//!   rule/source was applied at each step (20 proof rule variants). Multi-hop derivation
//!   provenance traces derived facts through universal rule chains, including conclusions
//!   eagerly inserted by forward chaining.
//! - **Witness extraction** — [`find_witnesses`] returns all satisfying entity bindings for
//!   existential variables only when every evaluated candidate leaf is definitive; collection
//!   APIs refuse an incomplete witness set instead of returning partial rows.
//! - **Compute dispatch** — `ComputeNode` predicates are forwarded to the host-provided
//!   `compute-backend` WIT interface for query-local external evaluation. Results
//!   contribute to the current derivation only; they never mutate the KB.
//!
//! The knowledge base uses `RefCell` (not `Mutex`) — single-threaded WASI. All
//! mutable state — facts, rules, the predicate-result cache, the compute
//! dispatch, and the cancel flag — lives PER-INSTANCE on `KnowledgeBaseInner`;
//! there are no global or thread-local statics, so distinct KBs (e.g. one per
//! request on the multithreaded server) never interfere.

#![allow(dead_code)]

use nibli_types::error::NibliError;
use nibli_types::logic::{
    AssertionCitation, AssertionRecordSummary, AssertionStatus, FactSummary, LogicBuffer,
    LogicNode, LogicalTerm, ProofRule, ProofStep, ProofTrace, QueryResult, ResourceKind,
    RuleCitation, UnknownReason, WitnessBinding,
};
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[cfg(test)]
thread_local! {
    static TEST_REBUILD_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
mod compute;
mod contradictions;
mod domain;
pub use contradictions::{ContradictionGap, ContradictionGapReason, ContradictionReport};
/// Fact store abstraction (trait + in-memory implementation).
pub mod fact_store;
mod materialize;
mod reasoning;
mod rules;

pub use materialize::Ineligible;

/// Completed relation names and reasons other relations refused materialization.
pub type MaterializationReport = (Vec<String>, Vec<(String, String)>);

pub use compute::ComputeRequest;

use compute::*;
use domain::*;
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

/// Transform exact registered relation names from `Predicate` → `ComputeNode`
/// in an already-compiled logic buffer. Call this after nibli-semantics
/// compilation and before asserting/querying. This pointwise rewrite neither
/// declares text vocabulary nor supplies/guesses an arity.
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
pub(crate) use kb::*;
pub use kb::{
    KnowledgeBase, asserted_external_compute_name, contains_asserted_compute_node,
    contains_asserted_count_node, validate_no_external_compute_names,
    validate_no_operational_comparisons,
};

/// The surface relation a role spelling collapses onto (`eats_x1` → `eats`);
/// a non-role name answers itself. The registration guard uses this to refuse
/// role-shaped compute names outright — registering one would mark exactly
/// the role conjuncts every stored anchor fact carries, stranding them behind
/// a name the reference scan never matched.
pub fn role_collapsed_relation(name: &str) -> &str {
    materialize::surface_relation(name)
}

/// One predicate's row in [`KnowledgeBase::stratification_report`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StratumRow {
    /// Surface relation name — role predicates (`p_x1`) collapsed onto their anchor (`p`).
    pub predicate: String,
    /// Stratum level. 0 means nothing negative sits beneath it; each negative edge
    /// crossed raises the level by one, so a rule may only read `~q` from a STRICTLY
    /// lower stratum. This is the assignment `proofs/Stratification.lean` proves exists
    /// whenever `check_stratification` accepted the KB.
    pub stratum: usize,
    /// `true` when NO rule concludes this predicate: base / extensional (EDB).
    /// `false` when at least one rule does: derived / intensional (IDB).
    pub base: bool,
    /// Outgoing dependency edges — "this predicate READS that one" — sorted and
    /// deduplicated.
    pub edges: Vec<StratumEdge>,
}

/// One outgoing dependency edge in a [`StratumRow`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StratumEdge {
    /// The predicate depended upon (surface name).
    pub to: String,
    /// `true` when read under negation-as-failure — the edge that forces a stratum
    /// boundary. `false` for an ordinary positive dependency.
    pub negative: bool,
}

/// Counterfactual status of a recorded proof step when ordinary closed-world
/// misses are weakened to Unknown while the finite query domain and genuine
/// compute decisions are held fixed. This is used only to classify a FALSE
/// proof for `ProofTrace::cwa_false`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OpenWorldStatus {
    True,
    False,
    Unknown,
}

fn open_world_and(left: OpenWorldStatus, right: OpenWorldStatus) -> OpenWorldStatus {
    if left == OpenWorldStatus::False || right == OpenWorldStatus::False {
        OpenWorldStatus::False
    } else if left == OpenWorldStatus::True && right == OpenWorldStatus::True {
        OpenWorldStatus::True
    } else {
        OpenWorldStatus::Unknown
    }
}

fn open_world_or(left: OpenWorldStatus, right: OpenWorldStatus) -> OpenWorldStatus {
    if left == OpenWorldStatus::True || right == OpenWorldStatus::True {
        OpenWorldStatus::True
    } else if left == OpenWorldStatus::False && right == OpenWorldStatus::False {
        OpenWorldStatus::False
    } else {
        OpenWorldStatus::Unknown
    }
}

/// Re-evaluate the recorded proof structure under the open-world
/// counterfactual above. Unlike the former global "any false ComputeCheck"
/// heuristic, this respects which child actually determines conjunction,
/// disjunction, quantifier, and exact-count results.
fn proof_step_open_world_status(
    steps: &[ProofStep],
    index: u32,
    memo: &mut HashMap<u32, OpenWorldStatus>,
    visiting: &mut HashSet<u32>,
) -> OpenWorldStatus {
    if let Some(status) = memo.get(&index) {
        return *status;
    }
    if !visiting.insert(index) {
        return OpenWorldStatus::Unknown;
    }
    let Some(step) = steps.get(index as usize) else {
        visiting.remove(&index);
        return OpenWorldStatus::Unknown;
    };
    let mut children = || {
        step.children
            .iter()
            .map(|child| proof_step_open_world_status(steps, *child, memo, visiting))
            .collect::<Vec<_>>()
    };

    let status = match &step.rule {
        ProofRule::Conjunction => children()
            .into_iter()
            .fold(OpenWorldStatus::True, open_world_and),
        ProofRule::DisjunctionCheck { .. } | ProofRule::DisjunctionIntro { .. } => children()
            .into_iter()
            .fold(OpenWorldStatus::False, open_world_or),
        // Re-evaluate the negation from its child's counterfactual status. A NAF
        // success over an ordinary closed-world miss becomes Unknown, while a
        // negation over a genuinely compute-decided false remains True. This
        // distinction matters when negation is nested inside a FALSE formula.
        ProofRule::Negation => match children().first() {
            Some(OpenWorldStatus::True) => OpenWorldStatus::False,
            Some(OpenWorldStatus::False) => OpenWorldStatus::True,
            Some(OpenWorldStatus::Unknown) | None => OpenWorldStatus::Unknown,
        },
        ProofRule::ModalPassthrough { .. }
        | ProofRule::ExistsWitness { .. }
        | ProofRule::ForallCounterexample { .. } => children()
            .into_iter()
            .next()
            .unwrap_or(OpenWorldStatus::Unknown),
        ProofRule::ExistsFailed => {
            let child_statuses = children();
            if child_statuses.is_empty() || child_statuses.contains(&OpenWorldStatus::Unknown) {
                OpenWorldStatus::Unknown
            } else if child_statuses.contains(&OpenWorldStatus::True) {
                OpenWorldStatus::True
            } else {
                OpenWorldStatus::False
            }
        }
        ProofRule::ForallVacuous => OpenWorldStatus::True,
        ProofRule::ForallVerified { .. } => children()
            .into_iter()
            .fold(OpenWorldStatus::True, open_world_and),
        ProofRule::CountResult { expected, .. } => {
            let child_statuses = children();
            if child_statuses.is_empty() && !step.holds {
                // An empty trace can mean an empty narrowed extension whose
                // absence is exactly the closed-world fact at issue.
                OpenWorldStatus::Unknown
            } else {
                let true_count = child_statuses
                    .iter()
                    .filter(|status| **status == OpenWorldStatus::True)
                    .count() as u32;
                let unknown_count = child_statuses
                    .iter()
                    .filter(|status| **status == OpenWorldStatus::Unknown)
                    .count() as u32;
                if true_count > *expected || true_count + unknown_count < *expected {
                    OpenWorldStatus::False
                } else if unknown_count == 0 && true_count == *expected {
                    OpenWorldStatus::True
                } else {
                    OpenWorldStatus::Unknown
                }
            }
        }
        ProofRule::PredicateCheck { method, .. } if method == "numeric" => {
            if step.holds {
                OpenWorldStatus::True
            } else {
                OpenWorldStatus::False
            }
        }
        ProofRule::ComputeCheck { method, .. }
            if method == "numeric" || method == "arithmetic" || method == "backend" =>
        {
            if step.holds {
                OpenWorldStatus::True
            } else {
                OpenWorldStatus::False
            }
        }
        ProofRule::Asserted { .. } | ProofRule::Presupposed { .. } => {
            if step.holds {
                OpenWorldStatus::True
            } else {
                OpenWorldStatus::Unknown
            }
        }
        ProofRule::Derived { .. }
        | ProofRule::ProofRef { .. }
        | ProofRule::EqualitySubstitution { .. } => {
            let child_statuses = children();
            if child_statuses.is_empty() {
                if step.holds {
                    OpenWorldStatus::True
                } else {
                    OpenWorldStatus::Unknown
                }
            } else {
                child_statuses
                    .into_iter()
                    .fold(OpenWorldStatus::True, open_world_and)
            }
        }
        ProofRule::PredicateCheck { .. }
        | ProofRule::ComputeCheck { .. }
        | ProofRule::RuleAttemptFailed { .. }
        | ProofRule::PredicateNotFound { .. } => OpenWorldStatus::Unknown,
    };
    visiting.remove(&index);
    memo.insert(index, status);
    status
}

fn proof_false_depends_on_closed_world(steps: &[ProofStep], root: u32) -> bool {
    proof_step_open_world_status(steps, root, &mut HashMap::new(), &mut HashSet::new())
        != OpenWorldStatus::False
}

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

    /// Multi-root buffers are a conjunction. When collection enumeration latched
    /// incompleteness in one root, check whether another root makes the WHOLE formula
    /// definitively False before surfacing an error. This mirrors an explicit
    /// `AndNode`: `False ∧ Unknown = False`, independent of root order.
    ///
    /// Called only after an incomplete leaf was observed. A True or non-definitive
    /// overall verdict preserves the collection refusal, including the selected
    /// `Unknown OR True` policy.
    fn multi_root_conjunction_is_definitively_false(
        logic: &LogicBuffer,
        inner: &mut KnowledgeBaseInner,
        compute_memo: &mut QueryComputeMemo,
    ) -> Result<bool, String> {
        if logic.roots.len() < 2 {
            return Ok(false);
        }
        let mut overall = QueryResult::True;
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            let result = check_formula_holds(logic, root_id, &mut subs, inner, None, compute_memo)?;
            overall = Self::combine_root_results(overall, result);
            if overall.is_false() {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Assert FOL facts from a logic buffer into the knowledge base.
    /// Stores the buffer in the fact registry and returns a unique fact ID.
    /// CountNodes and executable ComputeNodes in asserted position (outside
    /// opaque quoted content) are query-only and fail before id allocation.
    #[cfg(test)]
    fn assert_fact_inner(&self, logic: LogicBuffer, label: String) -> Result<u64, String> {
        self.assert_fact(logic, label).map_err(reasoning_message)
    }

    /// Only called on a detached transaction candidate or a fresh unpublished KB.
    /// An error must propagate to its owner, which discards the whole candidate.
    fn assert_unpublished_fact(
        &self,
        mut logic: LogicBuffer,
        label: String,
    ) -> Result<u64, String> {
        // Validate before minting an id or borrowing/mutating the KB. The same
        // guard also lives in process_assertion so rebuild replay cannot bypass it.
        preflight_assertion_buffer(&mut logic)?;
        let mut inner = self.inner.borrow_mut();
        let id = inner.fresh_fact_id()?;
        inner.current_assertion_id = Some(id);
        let result = process_preflighted_assertion(&mut inner, &mut logic);
        // ALWAYS clear: a stale id would mis-attribute the NEXT assertion's
        // rules (register_rule reads current_assertion_id for the rule-source
        // citations proof traces carry).
        inner.current_assertion_id = None;
        result?;
        inner.fact_registry.insert(
            id,
            Arc::new(FactRecord {
                id,
                buffer: Some(logic),
                label,
                retracted: false,
            }),
        );
        // Tabling: KB mutated, clear cached derivations. The SATURATION is not
        // dropped here: every mutation this assertion performed already decided
        // its fate at its own mutation point — a store insert through the
        // cone-relevance filter, a rule registration and a `du` merge
        // unconditionally — so an assertion that touched nothing the saturation
        // depends on leaves it standing. That is the whole point of anchoring
        // invalidation at the mutation point instead of at the caller.
        invalidate_pred_cache_keeping_saturation(&inner);
        Ok(id)
    }

    /// Assert a fact with a pre-assigned ID. Used for replay from persistent store.
    /// Advances the internal counter past the given ID. A CountNode or executable
    /// ComputeNode in asserted position fails before the counter advances, so
    /// legacy query-formula assertions fail closed.
    fn assert_fact_with_id_inner(
        &self,
        mut logic: LogicBuffer,
        label: String,
        id: u64,
    ) -> Result<(), String> {
        // A persisted/pre-assigned row must fail before advancing the live id counter.
        preflight_assertion_buffer(&mut logic)?;
        let mut inner = self.inner.borrow_mut();
        if inner.fact_registry.contains_key(&id) {
            return Err(format!(
                "fact id {id} is already registered; assertion ids are semantic Skolem sources and cannot be reused"
            ));
        }
        if id >= inner.fact_counter {
            inner.fact_counter = id.checked_add(1).ok_or_else(|| {
                "fact id u64::MAX cannot be registered because no collision-free successor remains"
                    .to_string()
            })?;
        }
        // Attribute any rule compiled during this replay to THIS fact — the
        // rule-source citations proof traces carry read current_assertion_id.
        inner.current_assertion_id = Some(id);
        let result = process_preflighted_assertion(&mut inner, &mut logic);
        inner.current_assertion_id = None;
        result?;
        inner.fact_registry.insert(
            id,
            Arc::new(FactRecord {
                id,
                buffer: Some(logic),
                label,
                retracted: false,
            }),
        );
        invalidate_pred_cache(&inner);
        Ok(())
    }

    /// Retract a previously asserted fact by its ID: mark the registry record
    /// retracted, then rebuild from the surviving records.
    ///
    /// There USED to be an "incremental O(1)" branch here for flat skolem-free
    /// ground facts. It was retired (2026-08-01, the numbers-join-the-domain
    /// adversarial review): it was never O(1) — preserving fact multiplicity
    /// already walked every surviving record — and it could not maintain
    /// `retract ≡ never-asserted` for the QUANTIFIER DOMAIN. The noted sets
    /// (`known_entities`/`known_descriptions`/`known_numbers`) are insert-only;
    /// precise un-noting needs cross-record reference counting PLUS the witness
    /// entities minted outside record buffers (existential-import
    /// presuppositions), so a retracted flat
    /// `Adam = Bel.` left both names as quantifier-domain members and a bare
    /// `all $x: p($x).` reported a counterexample the store no longer contained
    /// (22/200 sequences diverged the moment the retraction differential gained
    /// quantified battery rows) — and a lingering NUMBER is worse, satisfying
    /// arithmetic/comparison bodies with no store backing at all. Replay
    /// re-derives every noted set exactly; `retract_diff.rs` pins the
    /// equivalence, and the rebuild is the same primitive `:accept-scoped`
    /// already trusts.
    fn retract_fact_inner(&self, id: u64) -> Result<(), String> {
        let mut inner = self.inner.borrow_mut();
        match inner.fact_registry.get_mut(&id) {
            None => return Err(format!("Fact #{} not found", id)),
            Some(r) if r.retracted => return Ok(()), // idempotent
            Some(r) => {
                let r = Arc::make_mut(r);
                r.retracted = true;
                r.buffer = None;
            }
        }
        let result = Self::rebuild_inner(&mut inner);
        invalidate_pred_cache(&inner);
        result
    }

    /// Full rebuild from non-retracted facts. Kept as fallback / consistency check.
    pub fn rebuild(&self) -> Result<(), String> {
        self.transaction(|candidate| {
            Self::rebuild_inner(&mut candidate.inner.borrow_mut()).map_err(NibliError::Reasoning)
        })
        .map_err(reasoning_message)
    }

    /// Rebuild the KB from all non-retracted facts.
    /// Preserves fact_registry and fact_counter; resets all derived state.
    fn rebuild_inner(inner: &mut KnowledgeBaseInner) -> Result<(), String> {
        #[cfg(test)]
        TEST_REBUILD_COUNT.set(TEST_REBUILD_COUNT.get() + 1);
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
        inner.skolem_local_counter = 0;
        inner.known_entities.clear();
        inner.known_event_entities.clear();
        inner.known_descriptions.clear();
        inner.known_numbers.clear();
        // The member CACHES must go with the sets they were built from, and the
        // dirty flag must be raised HERE rather than left to replay re-noting:
        // `note_entity`/`note_number` set it only on fresh insertion, so a
        // replay of ZERO surviving records (retract the last fact, then query)
        // notes nothing and a warmed cache would keep serving the
        // pre-retraction members — a quantified query then reports a
        // counterexample the store no longer contains.
        inner.typed_domain_members_cache.clear();
        inner.typed_non_event_members_cache.clear();
        inner.domain_members_dirty = true;
        inner.known_rules.clear();
        inner.skolem_fn_registry.clear();
        inner.query_domain = QueryDomain::default();
        inner.fact_store.clear();
        inner.fact_origins.clear();
        inner.universal_rules.clear();
        inner.pred_dep_graph.clear();
        *inner.materialization_plan.borrow_mut() = None;
        inner.equivalence_parent.clear();
        inner.equivalence_classes.clear();
        inner.equality_adjacency.clear();
        inner.predicate_registry.clear();
        inner.arg_position_index.clear();
        inner.current_rule_ordinal = 0;
        inner.negative_facts.clear();
        inner.negative_scan_gaps.clear();
        inner.disjunctive_constraints.clear();
        // The saturated extensions are derived from the rules and facts being cleared
        // right above. Cleared HERE rather than left to the callers' pairing with
        // `invalidate_pred_cache`, because `KnowledgeBase::rebuild` is the one rebuild
        // entry point that does NOT invalidate — a stale extension surviving it would
        // answer `~p(x)` from the pre-rebuild knowledge base.
        *inner.materialized.borrow_mut() = None;

        // Collect non-retracted buffers + their ids ordered by ID (owned, to avoid
        // a borrow conflict with the mutable replay below).
        let mut entries: Vec<(&u64, &FactRecord)> = inner
            .fact_registry
            .iter()
            .filter(|(_, r)| !r.retracted)
            .map(|(id, record)| (id, record.as_ref()))
            .collect();
        entries.sort_by_key(|(id, _)| **id);
        let ids: Vec<u64> = entries.iter().map(|(id, _)| **id).collect();
        let mut buffers: Vec<LogicBuffer> = entries
            .iter()
            .map(|(_, r)| {
                r.buffer
                    .clone()
                    .expect("active assertion has a compiled buffer")
            })
            .collect();

        // Replay with diagnostic output + stratification checks suppressed
        // (inner.rebuilding == true). Collect-and-continue: replay EVERY surviving
        // fact so the store stays maximally consistent, accumulating errors rather
        // than silently dropping a fact that fails to replay.
        inner.rebuilding = true;
        let mut replay_errors: Vec<(u64, String)> = Vec::new();
        for (buf, &fid) in buffers.iter_mut().zip(ids.iter()) {
            inner.current_assertion_id = Some(fid);
            if let Err(e) = process_assertion(inner, buf) {
                replay_errors.push((fid, e));
            }
            inner.current_assertion_id = None;
        }
        inner.rebuilding = false;
        // Graph reachability depends on edge presence, not multiplicity. Keep
        // distinct polarities, but avoid retaining a copy for every compiled
        // condition/head pair. Later registration still appends its own edges,
        // so its failed-insertion length rollback remains exact.
        for edges in inner.pred_dep_graph.values_mut() {
            edges.sort_unstable();
            edges.dedup();
        }
        debug_assert!(inner.fact_origin_invariant_holds());

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
                root_count: r
                    .buffer
                    .as_ref()
                    .expect("active assertion has a compiled buffer")
                    .roots
                    .len() as u32,
            })
            .collect();
        facts.sort_by_key(|f| f.id);
        Ok(facts)
    }

    /// Set the positive reasoning depth budget. The same bound limits generated
    /// witness dependency height; materialization can independently complete a proof.
    pub fn set_max_chain_depth(&self, depth: u32) -> Result<(), NibliError> {
        self.ensure_ready()?;
        if depth == 0 {
            return Err(NibliError::Reasoning(
                "reasoning depth must be a positive u32".into(),
            ));
        }
        let mut inner = self.inner.borrow_mut();
        inner.max_chain_depth = depth as usize;
        invalidate_pred_cache(&inner);
        Ok(())
    }

    /// Current reasoning depth budget (default 10).
    pub fn max_chain_depth(&self) -> u32 {
        self.inner.borrow().max_chain_depth as u32
    }

    /// Saturate the relations this query must read completely, so eligible checks can
    /// use set membership instead of exhaustive proof attempts.
    ///
    /// Negated roots and positive roots whose dependency cone contains NAF are requested
    /// before backward chaining because NAF needs a complete extension. A purely positive
    /// root is requested only after ordinary reasoning remains non-definitive (for example,
    /// at a depth or cycle cut); eager positive saturation can cost far more than an exact
    /// indexed proof. The extension does not depend on the depth budget, so an unchanged
    /// requested-root union is
    /// reused; adding a root recomputes the cumulative union, and KB mutation clears it.
    /// Everything here is best-effort: a relation that cannot be saturated is simply
    /// absent from the completed set, and its NAF takes the ordinary path.
    ///
    /// TARGETS. Relations reachable from the current query roots. For a projectable
    /// rule, `saturate` follows both positive and negative dependencies, so its NAF
    /// relations enter the same query cone. If a query root is not projectable, that
    /// whole path keeps the ordinary backward chainer rather than globally saturating
    /// every unrelated rule merely because one of them contains NAF.
    fn ensure_materialized(&self, logic: &LogicBuffer, include_positive_roots: bool) -> bool {
        let inner = self.inner.borrow();
        if !inner.materialization {
            return false;
        }

        // TARGETS. Only the current query's reachable relations. `saturate` computes the
        // positive and negative dependency closure of projectable roots itself. Seeding
        // this set with every eligible relation — or every NAF-bearing rule in the KB —
        // made an exact query pay for unrelated recursive closures before evaluation.
        let mut targets: HashSet<String> = HashSet::new();
        materialize::collect_negated_relations(logic, &mut targets);
        if include_positive_roots
            || materialize::query_cone_has_negative_dependency(logic, &inner.pred_dep_graph)
        {
            materialize::collect_query_relations(logic, &mut targets);
        }
        materialize::ensure_materialized_targets(&inner, &targets)
    }

    /// Single-pass entailment check at the current max_chain_depth.
    fn run_entailment_check(&self, logic: &LogicBuffer) -> Result<QueryResult, String> {
        self.run_entailment_check_with_compute_memo(logic, &mut QueryComputeMemo::default())
    }

    fn run_entailment_check_with_compute_memo(
        &self,
        logic: &LogicBuffer,
        compute_memo: &mut QueryComputeMemo,
    ) -> Result<QueryResult, String> {
        // Enable WITHOUT clearing: the cache is cleared once before each
        // iterative-deepening run, then definitive
        // results persist across depth passes (cross-depth tabling).
        let mut inner = self.inner.borrow_mut();
        enable_pred_cache(&inner);
        prepare_query_domain(&mut inner)?;
        let mut overall = QueryResult::True;
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            let result =
                check_formula_holds(logic, root_id, &mut subs, &mut inner, None, compute_memo)?;
            overall = Self::combine_root_results(overall, result);
        }
        Ok(overall)
    }

    /// Check whether all root formulas in the logic buffer are entailed by the KB.
    /// Uses iterative deepening: tries depth 1, 2, ..., max_chain_depth.
    /// Guarantees finding the shallowest proof.
    fn query_entailment_inner(&self, mut logic: LogicBuffer) -> Result<QueryResult, String> {
        validate_single_flavor_paths(&logic)?;
        canonicalize_abstraction_markers(&mut logic)?;
        // A NAF-bearing cone requires completeness up front. Purely positive saturation
        // is a fallback only when the exact backward path remains non-definitive.
        self.ensure_materialized(&logic, false);
        let result = self.run_entailment_iterative(&logic)?;
        if !result.is_definitive() && self.ensure_materialized(&logic, true) {
            return self.run_entailment_iterative(&logic);
        }
        Ok(result)
    }

    /// Run one iterative-deepening pass against the current store/materialized cache.
    fn run_entailment_iterative(&self, logic: &LogicBuffer) -> Result<QueryResult, String> {
        // Entailment MAY dispatch; only enumeration refuses (see `find_enumeration`).
        // Cleared here rather than on every `query_find_inner` exit because that
        // function returns from several places, and a latch left set would silently
        // disable the backend for the next ordinary query — the one failure this flag
        // must not cause.
        self.inner.borrow_mut().find_enumeration = false;
        // Tabling: clear once, persist across depth iterations.
        let configured_max = {
            let inner = self.inner.borrow();
            clear_and_enable_pred_cache(&inner);
            inner.max_chain_depth
        };
        let mut compute_memo = QueryComputeMemo::default();
        for depth_limit in 1..=configured_max {
            self.inner.borrow_mut().max_chain_depth = depth_limit;
            // Restore the configured depth on EVERY exit, including the error
            // path (e.g. cooperative cancellation), so an aborted query never
            // leaves a reusable KB pinned at a partial deepening depth.
            let result =
                match self.run_entailment_check_with_compute_memo(&logic, &mut compute_memo) {
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
    /// Returns an incomplete-enumeration error if any final candidate leaf is
    /// `Unknown(_)` or `ResourceExceeded(_)`.
    /// Witness enumeration, with `find_enumeration` scoped to its DYNAMIC EXTENT.
    ///
    /// The latch is cleared here rather than at the entailment entries alone because
    /// this function returns from several places and two thin wrappers
    /// (`run_entailment_check`, `run_entailment_check_with_proof`) reach evaluation
    /// without passing through either clear — so a latch left set would silently
    /// disable the compute backend for a subsequent ordinary query. Clearing on the way
    /// out closes all of them at once.
    ///
    /// Not a `Drop` guard: the inner function holds a `RefMut` for its whole body, so a
    /// guard's destructor would re-borrow while that is live and panic. No save/restore
    /// either — a nested find already panics on the `RefCell`, so the flag cannot be
    /// nested. The entailment-entry clears stay as defence in depth.
    fn query_find_inner(&self, logic: LogicBuffer) -> Result<Vec<Vec<WitnessBinding>>, String> {
        let out = self.query_find_enumerate(logic);
        self.inner.borrow_mut().find_enumeration = false;
        out
    }

    fn query_find_enumerate(&self, logic: LogicBuffer) -> Result<Vec<Vec<WitnessBinding>>, String> {
        let binding_sets = self.query_find_ground(logic)?;
        let inner = self.inner.borrow();
        Ok(Self::present_witness_bindings(&inner, binding_sets))
    }

    /// Internal enumeration keeps generated identities intact for subsequent
    /// constraint matching. Public witness strings are presentation only.
    fn query_find_ground(
        &self,
        mut logic: LogicBuffer,
    ) -> Result<Vec<Vec<(String, GroundTerm)>>, String> {
        validate_single_flavor_paths(&logic)?;
        canonicalize_abstraction_markers(&mut logic)?;
        // Surfaced (as an Err) when any final witness leaf is non-definitive:
        // find/count/aggregate must refuse a partial set rather than silently report a
        // wrong quantity. See `find_witnesses` / `find_enumeration_incomplete` — resource exhaustion
        // remains the find-path analog of the entailment path's
        // `ResourceExceeded(Depth)` verdict.
        //
        // WHAT THIS MEANS SINCE STRATUM-ORDERED MATERIALISATION. A saturated relation
        // returns only definitive verdicts, so the incompleteness latch never fires for a
        // leaf inside the materialised fragment and this refusal never triggers there —
        // no code change was needed for that, it falls out. What remains is the genuine
        // residue: every final candidate that remains `Unknown(_)` or
        // `ResourceExceeded(_)`, including compute predicates (an infinite numeric
        // domain, not a finite set to saturate) and relations the eligibility analysis
        // refused. The refusal therefore means "this query did not decide the complete
        // witness set"; `KnowledgeBase::materialization_report` can explain an
        // unsaturated relation, while non-finite compute and exhausted budgets must be
        // addressed at their source.
        const INCOMPLETE_MSG: &str = "witness enumeration incomplete: domain closure or a witness leaf could not be decided \
             (`UNKNOWN` or `RESOURCE_EXCEEDED`), so find/count/aggregate would undercount — \
             `materialization_report` can explain unsaturated relations; non-finite compute \
             or exhausted budgets must be addressed at their source";
        self.ensure_materialized(&logic, true);
        let mut inner = self.inner.borrow_mut();
        clear_and_enable_pred_cache(&inner);
        prepare_query_domain(&mut inner)?;
        if inner.query_domain.incomplete.is_some() {
            return Err(INCOMPLETE_MSG.to_string());
        }
        inner.find_enumeration_incomplete = false;
        // Enumeration runs its body once per candidate, so external compute is not
        // dispatched from here at all — see `KnowledgeBaseInner::find_enumeration`.
        // Anything locally decidable still decides; anything that would call out
        // refuses, and the non-definitive leaf makes the caller report an incomplete
        // enumeration instead of an undercount.
        inner.find_enumeration = true;
        let mut result_sets: Option<Vec<Vec<(String, GroundTerm)>>> = None;
        let mut compute_memo = QueryComputeMemo::default();
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            let witnesses = find_witnesses(
                &logic,
                root_id,
                &mut subs,
                &mut inner,
                None,
                &mut compute_memo,
            )?;
            match result_sets {
                None => result_sets = Some(witnesses),
                Some(prev) => {
                    if witnesses.is_empty() {
                        if inner.find_enumeration_incomplete {
                            if Self::multi_root_conjunction_is_definitively_false(
                                &logic,
                                &mut inner,
                                &mut compute_memo,
                            )? {
                                inner.find_enumeration_incomplete = false;
                                return Ok(vec![]);
                            }
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
                                merge_witness_bindings(&prev_bindings, witness_bindings, &inner)
                            {
                                joined.push(combined);
                            }
                        }
                    }
                    if joined.is_empty() {
                        if inner.find_enumeration_incomplete {
                            if Self::multi_root_conjunction_is_definitively_false(
                                &logic,
                                &mut inner,
                                &mut compute_memo,
                            )? {
                                inner.find_enumeration_incomplete = false;
                                return Ok(vec![]);
                            }
                            return Err(INCOMPLETE_MSG.to_string());
                        }
                        return Ok(vec![]);
                    }
                    result_sets = Some(joined);
                }
            }
        }
        // Enumeration finished — but if any witness leaf was non-definitive, the result
        // is an under-count, not a complete collection. Refuse it.
        if inner.find_enumeration_incomplete {
            if Self::multi_root_conjunction_is_definitively_false(
                &logic,
                &mut inner,
                &mut compute_memo,
            )? {
                inner.find_enumeration_incomplete = false;
                return Ok(vec![]);
            }
            return Err(INCOMPLETE_MSG.to_string());
        }
        Ok(result_sets.unwrap_or_default())
    }

    fn present_witness_bindings(
        inner: &KnowledgeBaseInner,
        mut binding_sets: Vec<Vec<(String, GroundTerm)>>,
    ) -> Vec<Vec<WitnessBinding>> {
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
                        canonical_witness_term(&inner.equivalence_parent, gt),
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
        let import_rank = |bindings: &Vec<(String, GroundTerm)>| {
            bindings
                .iter()
                .filter(|(var, term)| {
                    !var.starts_with("_ev")
                        && witness_origin(term)
                            == nibli_types::logic::WitnessOrigin::ExistentialImport
                })
                .count()
        };
        // For a du-equivalent imported/KB pair, retain the ordinary KB spelling
        // and report ordinary origin for their one shared entity.
        binding_sets.sort_by_cached_key(|b| (entity_key(b), import_rank(b), full_key(b)));
        binding_sets.dedup_by_key(|bindings| entity_key(bindings));
        binding_sets
            .into_iter()
            .map(|bindings| {
                bindings
                    .into_iter()
                    .map(|(var, gt)| {
                        let origin = witness_origin(&gt);
                        WitnessBinding {
                            variable: var,
                            term: witness_term_to_logical_term(&gt),
                            origin,
                        }
                    })
                    .collect()
            })
            .collect()
    }

    /// Single-pass entailment check with proof trace at the current max_chain_depth.
    fn run_entailment_check_with_proof(
        &self,
        logic: &LogicBuffer,
    ) -> Result<(QueryResult, ProofTrace), String> {
        self.run_entailment_check_with_proof_and_compute_memo(
            logic,
            &mut QueryComputeMemo::default(),
        )
    }

    fn run_entailment_check_with_proof_and_compute_memo(
        &self,
        logic: &LogicBuffer,
        compute_memo: &mut QueryComputeMemo,
    ) -> Result<(QueryResult, ProofTrace), String> {
        // Enable WITHOUT clearing: cleared once before the iterative-deepening
        // loop in query_entailment_with_proof_inner; definitive results persist
        // across depth passes (cross-depth tabling).
        let mut inner = self.inner.borrow_mut();
        enable_pred_cache(&inner);
        prepare_query_domain(&mut inner)?;
        let mut steps: Vec<ProofStep> = Vec::new();
        let mut memo: HashMap<StoredFact, u32> = HashMap::new();
        let mut root_children: Vec<u32> = Vec::new();
        let mut overall = QueryResult::True;
        for &root_id in &logic.roots {
            let mut subs = HashMap::new();
            // ONE walk per root: the recording evaluator returns the authoritative
            // four-valued verdict AND builds the proof trace, so the trace's
            // per-node `holds` is natively `verdict.is_true()` — no separate
            // untraced pass and no root `holds` reconciliation needed.
            let (result, step_idx) = check_formula_holds_recording(
                logic,
                root_id,
                &mut subs,
                &mut inner,
                &mut steps,
                None,
                &mut memo,
                compute_memo,
            )?;
            overall = Self::combine_root_results(overall, result);
            root_children.push(step_idx);
        }
        let root = if root_children.len() == 1 {
            root_children[0]
        } else {
            reasoning::push_proof_step(
                &mut steps,
                ProofStep {
                    rule: ProofRule::Conjunction,
                    holds: overall.is_true(),
                    children: root_children,
                },
            )
        };
        let naf_dependent = steps
            .iter()
            .any(|s| matches!(s.rule, ProofRule::Negation) && s.holds);
        // Classify the ROOT under an open-world counterfactual. A failed compute
        // leaf is definitive, but it only removes the CWA caveat when the
        // formula/quantifier/count structure actually makes that leaf decisive.
        // Conversely, an unrelated failed compute check cannot launder an
        // absence-driven disjunction into a non-CWA result.
        let cwa_false = overall.is_false() && proof_false_depends_on_closed_world(&steps, root);
        // The overflow refusal: past the u32 cap, pushes were poisoned (nothing
        // recorded, sentinel index) — the steps are not a certificate and must
        // not escape as one.
        if reasoning::proof_steps_overflowed(&steps) {
            return Err(
                "proof trace exceeded the indexable size (u32 step indices): the \
                 derivation cannot be certified — simplify the query or knowledge base"
                    .to_string(),
            );
        }
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
        mut logic: LogicBuffer,
    ) -> Result<(QueryResult, ProofTrace), String> {
        validate_single_flavor_paths(&logic)?;
        canonicalize_abstraction_markers(&mut logic)?;
        // Same eager NAF-cone saturation the untraced path uses — the NAF probe stays on,
        // and its trace shape is unaffected (`emit_derived` records a `Negation` leaf per
        // group without re-evaluating it, so `naf_dependent` still computes correctly).
        // A purely positive fallback is intentionally not requested: the positive lookup
        // is disabled below because a complete tuple has no derivation to trace.
        self.ensure_materialized(&logic, false);
        // The POSITIVE lookup, however, is lowered for the whole traced query — BOTH
        // phases. A lookup has no derivation to record, and gating it per-sink would let
        // the untraced phase-1 probe resolve at depth 1 while phase 2 rebuilt the trace by
        // backward chaining at that same depth and failed to reach it, turning a TRUE into
        // `ResourceExceeded(Depth)`. Restored on every exit below, error paths included.
        self.inner.borrow().positive_lookup.set(false);
        // Entailment MAY dispatch — see the twin in `run_entailment_iterative`.
        self.inner.borrow_mut().find_enumeration = false;
        // Tabling: clear once, persist across phases.
        let configured_max = {
            let inner = self.inner.borrow();
            clear_and_enable_pred_cache(&inner);
            inner.max_chain_depth
        };
        let mut compute_memo = QueryComputeMemo::default();
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
            let result =
                match self.run_entailment_check_with_compute_memo(&logic, &mut compute_memo) {
                    Ok(r) => r,
                    Err(e) => {
                        let inner = self.inner.borrow();
                        inner.positive_lookup.set(true);
                        drop(inner);
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
        // set-idempotent for the only state it reads (`typed_fact_is_stored`).
        self.inner.borrow_mut().max_chain_depth = resolving_depth;
        let out = self.run_entailment_check_with_proof_and_compute_memo(&logic, &mut compute_memo);
        {
            let inner = self.inner.borrow();
            inner.positive_lookup.set(true);
        }
        self.inner.borrow_mut().max_chain_depth = configured_max;
        out
    }
}

fn merge_witness_bindings(
    left: &[(String, GroundTerm)],
    right: &[(String, GroundTerm)],
    inner: &KnowledgeBaseInner,
) -> Option<Vec<(String, GroundTerm)>> {
    let mut combined = left.to_vec();
    for (var, val) in right {
        match combined
            .iter()
            .find(|(existing_var, _)| existing_var == var)
        {
            Some((_, existing_val))
                if canonical_witness_term(&inner.equivalence_parent, existing_val)
                    != canonical_witness_term(&inner.equivalence_parent, val) =>
            {
                return None;
            }
            Some(_) => {}
            None => combined.push((var.clone(), val.clone())),
        }
    }
    Some(combined)
}

// String-returning low-level APIs keep the original reasoning message; their
// callers add the structured error class exactly once.
fn reasoning_message(error: NibliError) -> String {
    match error {
        NibliError::Reasoning(message) => message,
        other => other.to_string(),
    }
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

    /// Refuse use of a session whose durable commit outcome is uncertain.
    pub fn ensure_ready(&self) -> Result<(), NibliError> {
        let inner = self.inner.try_borrow().map_err(|_| {
            NibliError::Reasoning("knowledge base busy: mutation in progress".into())
        })?;
        match &inner.recovery_required {
            Some(reason) => Err(NibliError::Reasoning(format!(
                "RecoveryRequired: {reason}; reopen the knowledge base before continuing"
            ))),
            None => Ok(()),
        }
    }

    /// Permanently retire this live instance after an ambiguous durable commit.
    pub fn require_recovery(&self, reason: String) {
        self.inner.borrow_mut().recovery_required = Some(reason);
    }

    /// Stage a mutation on a detached candidate, commit its authoritative storage
    /// inside `operation`, then publish into this same KB identity. The live borrow
    /// prevents reentrant use while a candidate is pending. An error discards it.
    /// The typed store is a recoverable mirror: its infallible writes cannot turn
    /// a committed authoritative mutation into a rejected logical operation.
    pub fn transaction<R>(
        &self,
        operation: impl FnOnce(&KnowledgeBase) -> Result<R, NibliError>,
    ) -> Result<R, NibliError> {
        self.ensure_ready()?;
        let mut live = self.inner.borrow_mut();
        let mut snapshot = live.clone();
        snapshot.deferred_stratification = live.deferred_stratification;
        *snapshot.materialized.get_mut() = live.materialized.borrow().clone();
        let candidate = KnowledgeBase {
            inner: RefCell::new(snapshot),
        };
        let result = operation(&candidate)?;
        candidate.ensure_ready()?;
        let mut published = candidate.inner.into_inner();
        // Keep the caller's typed mirror attached to the existing KB identity.
        // Only apply differences, avoiding an unnecessary rewrite of every tuple.
        let previous: HashSet<_> = live.fact_store.all_facts().cloned().collect();
        let current: HashSet<_> = published.fact_store.all_facts().cloned().collect();
        let mut mirror = std::mem::replace(
            &mut live.fact_store,
            Box::new(fact_store::InMemoryFactStore::new()),
        );
        for fact in previous.difference(&current) {
            mirror.remove(fact);
        }
        for fact in current.difference(&previous) {
            mirror.insert(fact.clone());
        }
        published.fact_store = mirror;
        *live = published;
        Ok(result)
    }

    /// Replay an active assertion with its original identity, atomically.
    pub fn assert_fact_with_id(
        &self,
        logic: LogicBuffer,
        label: String,
        id: u64,
    ) -> Result<(), String> {
        self.transaction(|candidate| {
            candidate
                .assert_fact_with_id_inner(logic, label, id)
                .map_err(NibliError::Reasoning)
        })
        .map_err(reasoning_message)
    }

    /// Restore withdrawn metadata without compiling or activating its old payload.
    pub fn restore_withdrawn_assertion(&self, id: u64, label: String) -> Result<(), NibliError> {
        self.ensure_ready()?;
        let successor = id.checked_add(1).ok_or_else(|| {
            NibliError::Reasoning(
                "fact id u64::MAX cannot be restored: no collision-free successor remains".into(),
            )
        })?;
        let mut inner = self.inner.borrow_mut();
        if inner.fact_registry.contains_key(&id) {
            return Err(NibliError::Reasoning(format!(
                "fact id {id} is already registered"
            )));
        }
        inner.fact_counter = inner.fact_counter.max(successor);
        inner.fact_registry.insert(
            id,
            Arc::new(FactRecord {
                id,
                label,
                buffer: None,
                retracted: true,
            }),
        );
        Ok(())
    }

    /// List active and withdrawn assertion records in stable identity order.
    pub fn list_assertion_records(&self) -> Result<Vec<AssertionRecordSummary>, NibliError> {
        self.ensure_ready()?;
        let inner = self.inner.borrow();
        let mut records: Vec<_> = inner
            .fact_registry
            .values()
            .map(|record| AssertionRecordSummary {
                id: record.id,
                label: record.label.clone(),
                status: if record.retracted {
                    AssertionStatus::Withdrawn
                } else {
                    AssertionStatus::Active
                },
            })
            .collect();
        records.sort_by_key(|record| record.id);
        Ok(records)
    }

    /// Create a KB with a custom fact store backend (e.g., persistent redb).
    ///
    /// The backend must be empty. Persisted typed facts alone are not a complete
    /// KB snapshot: they lack the assertion registry needed to replay rules,
    /// rebuild domain/equality indexes, and retract by source. Install an empty
    /// mirror, then replay the authoritative `LogicBuffer` registry through
    /// [`Self::assert_fact_with_id`] (the path used by `nibli-engine`).
    pub fn with_store(store: Box<dyn fact_store::FactStore>) -> Result<Self, String> {
        if !store.is_empty() {
            return Err(
                "custom fact store is nonempty but has no authoritative assertion registry; install an empty mirror and replay LogicBuffers with assert_fact_with_id"
                    .to_string(),
            );
        }
        let mut inner = KnowledgeBaseInner::new();
        inner.fact_store = store;
        Ok(KnowledgeBase {
            inner: RefCell::new(inner),
        })
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
    /// assertion error. Facts inserted internally by forward chaining are also
    /// rejected loudly but cannot fail a user call.
    /// Configuration, not derived state — survives `reset()`; inert during
    /// retraction-replay rebuilds.
    pub fn set_strict(&self, strict: bool) {
        self.inner.borrow_mut().strict = strict;
    }

    /// Whether strict mode is enabled.
    pub fn is_strict(&self) -> bool {
        self.inner.borrow().strict
    }

    /// Enable/disable legacy EXISTENTIAL-IMPORT MODE (default OFF). When on, a description universal
    /// (`animal(every dog).`) mints a presupposition witness so `∃x. dog(x)`
    /// holds. Set OFF for the clean-core profile (`some` = plain classical ∃,
    /// no phantom entity injected — NIBLI_KR §14.4 item 3). The change applies
    /// transactionally to the whole active KB by replaying it immediately; this
    /// prevents a later unrelated retraction from changing which profile the
    /// already-loaded rules use. Configuration survives `reset()`.
    pub fn set_existential_import(&self, on: bool) -> Result<(), String> {
        self.transaction(|candidate| {
            let mut inner = candidate.inner.borrow_mut();
            if inner.existential_import == on {
                return Ok(());
            }
            inner.existential_import = on;
            Self::rebuild_inner(&mut inner).map_err(NibliError::Reasoning)?;
            invalidate_pred_cache(&inner);
            Ok(())
        })
        .map_err(reasoning_message)
    }

    /// Whether existential-import (xorlo witness minting) is enabled.
    pub fn is_existential_import(&self) -> bool {
        self.inner.borrow().existential_import
    }

    /// Enable/disable STRATUM-ORDERED MATERIALISATION (default ON — see
    /// [`crate::materialize`]). When on, the relations a query reads under `~` are
    /// saturated bottom-up in stratum order before the query runs, and each NAF check
    /// becomes a set-membership test instead of an exhaustive proof attempt. When off,
    /// every NAF takes the backward-chaining path — byte-identical to the pre-2026-07-31
    /// engine, which is what the ON/OFF differential in `nibli-verify` compares against.
    ///
    /// Configuration, not derived state — survives `reset()`. Turning it OFF drops any
    /// existing saturation immediately, so the switch takes effect on the next query
    /// rather than at the next mutation.
    pub fn set_materialization(&self, on: bool) {
        let mut inner = self.inner.borrow_mut();
        inner.materialization = on;
        reasoning::invalidate_materialization(&inner);
    }

    /// Whether stratum-ordered materialisation is enabled — the read twin of
    /// [`Self::set_materialization`] (the proof envelope's profile stamp
    /// reads it).
    pub fn materialization_enabled(&self) -> bool {
        self.inner.borrow().materialization
    }

    /// Whether stratum-ordered materialisation is enabled.
    pub fn is_materialization(&self) -> bool {
        self.inner.borrow().materialization
    }

    /// Prepare the immutable rule projection and dependency strata for reuse by
    /// independent [`Self::with_assumptions`] snapshots.
    ///
    /// This performs no logical query, derives no facts, and does not saturate
    /// any relation. Warming a prepared base before cloning avoids rebuilding
    /// the same rule plan in every otherwise independent fixture. Ordinary
    /// mutation/profile invalidation still applies; stored-fact eligibility is
    /// checked separately when a query actually requests materialization.
    pub fn prepare_materialization_plan(&self) -> Result<(), NibliError> {
        self.ensure_ready()?;
        materialize::materialization_plan(&self.inner.borrow());
        Ok(())
    }

    /// What the last query's saturation actually covered: `(completed relations, why
    /// each refused relation was not)`, both sorted for reproducible output.
    ///
    /// This exists because the optimisation is INVISIBLE when it fails. A knowledge base
    /// whose `~p(x)` still takes seconds has no other way to learn that `p` fell out of
    /// the materialisable fragment, or which of its dependencies did. Empty until a
    /// query has run (the saturation is built lazily) and after any mutation.
    pub fn materialization_report(&self) -> Result<MaterializationReport, NibliError> {
        self.ensure_ready()?;
        let inner = self.inner.borrow();
        let m = inner.materialized.borrow();
        let Some(m) = m.as_ref() else {
            return Ok((Vec::new(), Vec::new()));
        };
        let mut complete: Vec<String> = m.complete.iter().cloned().collect();
        complete.sort();
        let mut refused: Vec<(String, String)> = m
            .refused
            .iter()
            .filter(|(rel, _)| !m.complete.contains(*rel))
            .map(|(rel, why)| (rel.clone(), why.reason()))
            .collect();
        refused.sort();
        Ok((complete, refused))
    }

    #[cfg(test)]
    fn materialization_tuple_bind_attempts(&self, relation: &str) -> usize {
        let inner = self.inner.borrow();
        inner
            .materialized
            .borrow()
            .as_ref()
            .map_or(0, |m| m.work.tuple_bind_attempts(relation))
    }

    /// How many times the live saturation was folded forward incrementally
    /// instead of recomputed (test-only). Zero after a mutation means the
    /// fixpoint was rebuilt from scratch — the discriminator no verdict test
    /// can provide, since both paths answer identically.
    #[cfg(test)]
    pub(crate) fn materialization_resumes(&self) -> usize {
        self.inner
            .borrow()
            .materialized
            .borrow()
            .as_ref()
            .map_or(0, |m| m.work.resumes())
    }

    /// The KB's STRATIFICATION as machine-readable data: every predicate with its
    /// stratum, whether it is base (EDB) or derived (IDB), and its outgoing dependency
    /// edges marked positive or negative.
    ///
    /// Exists so a consuming project does not have to re-implement the stratifier to
    /// read it. A second implementation — a regex over `.nibli` text, say — is a second
    /// thing to keep in sync with this one, and it will drift; anything presented as
    /// *"this order was derived by the engine"* has to come from the engine that
    /// enforces it. Read-only and verdict-inert: it reports `pred_dep_graph`, which
    /// `register_rule` already maintains and `check_stratification` already gates.
    ///
    /// **Surface projection.** The graph the engine stratifies is keyed on
    /// event-decomposed relation names — the anchor `false` alongside its role
    /// predicates `false_x1`, `false_x2`. Those are one atom, so they always carry
    /// identical dependency sets and therefore always land in the same stratum
    /// (pinned by `strata_surface_projection_is_lossless`). The report collapses each
    /// role onto its anchor, because that is the name a KB author wrote and the only
    /// name a reader can check. A self-edge that survives the collapse is GENUINE
    /// recursion, not a decomposition artifact: a rule never reads the roles of its own
    /// conclusion, so `p -> p_x1` edges do not exist to begin with.
    ///
    /// Deterministic by construction: rows sorted by predicate, edges sorted, duplicates
    /// (four raw edges collapsing onto one surface edge) removed — safe to diff across
    /// runs.
    pub fn stratification_report(&self) -> Result<Vec<StratumRow>, NibliError> {
        use std::collections::{BTreeMap, BTreeSet};

        self.ensure_ready()?;
        let inner = self.inner.borrow();
        let strata = materialize::compute_strata(&inner.pred_dep_graph);

        // Anything a rule concludes is DERIVED, whatever else is true of it. Keyed on the
        // raw conclusion relation, so project it the same way as the nodes.
        let derived: BTreeSet<&str> = inner
            .universal_rules
            .keys()
            .map(|k| materialize::surface_relation(k))
            .collect();

        let mut level: BTreeMap<&str, usize> = BTreeMap::new();
        for (raw, lvl) in &strata {
            let surface = materialize::surface_relation(raw);
            // `max` is defensive only — see the lossless-projection pin above.
            let slot = level.entry(surface).or_insert(*lvl);
            *slot = (*slot).max(*lvl);
        }
        // `pred_dep_graph`'s keys are a STRICT SUBSET of the rule heads: a conditionless
        // rule pushes no edges, so its head never becomes a node. Such a head is still a
        // derived predicate and must appear, at stratum 0 — it depends on nothing, so
        // nothing can raise it. Omitting it would drop a whole predicate from a dump whose
        // purpose is to be complete.
        for head in derived.iter() {
            level.entry(head).or_insert(0);
        }

        let mut edges: BTreeMap<&str, BTreeSet<(&str, bool)>> = BTreeMap::new();
        for (head, deps) in &inner.pred_dep_graph {
            let h = materialize::surface_relation(head);
            let bucket = edges.entry(h).or_default();
            for (dep, is_neg) in deps {
                bucket.insert((materialize::surface_relation(dep), *is_neg));
            }
        }

        Ok(level
            .into_iter()
            .map(|(predicate, stratum)| StratumRow {
                stratum,
                base: !derived.contains(predicate),
                edges: edges
                    .get(predicate)
                    .map(|s| {
                        s.iter()
                            .map(|(to, negative)| StratumEdge {
                                to: (*to).to_string(),
                                negative: *negative,
                            })
                            .collect()
                    })
                    .unwrap_or_default(),
                predicate: predicate.to_string(),
            })
            .collect())
    }

    /// Declare `relation` DERIVED-ONLY (intensional / IDB): thereafter it may be
    /// concluded by a rule but never asserted directly — a direct ground
    /// assertion is rejected and the whole assertion unwinds atomically.
    ///
    /// The KB-level spelling is `derived_only("<relation>").`, which routes here;
    /// this is the programmatic twin. Declaring is IDEMPOTENT and one-way within
    /// a session: there is deliberately no `undeclare`, since a relation that
    /// could be re-opened at runtime would give back exactly the capability the
    /// declaration exists to remove. Reopen it by editing the KB.
    ///
    /// Declaring does NOT retroactively remove facts already asserted, and it is
    /// a DECLARATION, not derived state — it survives `reset()` and retraction
    /// replay.
    pub fn declare_derived(&self, relation: &str) {
        self.inner
            .borrow_mut()
            .derived_only
            .insert(relation.to_string());
    }

    /// Declare `relation` ADMITTED base vocabulary. The FIRST such declaration
    /// CLOSES this knowledge base's vocabulary: thereafter a ground assertion of
    /// any relation not admitted is rejected, atomically, the way `derived_only`
    /// rejects. While nothing has been declared the KB is OPEN, which is the
    /// default and what every v0.1 knowledge base gets.
    ///
    /// The KB-level spelling is `admits("<relation>").`; this is the programmatic
    /// twin. It is the DUAL of [`Self::declare_derived`] — that one says a relation
    /// may not be asserted, this one says which relations may — and the pair
    /// together is what lets a document claim its record has exactly these entries
    /// and have the engine hold it to that.
    ///
    /// ORDER IS LOAD-BEARING and enforced: the whole admits block must precede
    /// every ordinary assertion, because a declaration that arrives later would
    /// silently grandfather everything above it. Declaring is idempotent and
    /// one-way within a session, for the same reason `declare_derived` is: a
    /// vocabulary that could be re-opened at runtime gives back exactly the
    /// capability the declaration exists to remove.
    pub fn declare_admitted(&self, relation: &str) {
        self.inner
            .borrow_mut()
            .admitted
            .insert(relation.to_string());
    }

    /// Whether `relation` is admitted base vocabulary. Note an OPEN knowledge base
    /// (nothing declared) returns `false` for everything while still admitting
    /// everything — ask [`Self::vocabulary_is_closed`] first.
    pub fn is_admitted(&self, relation: &str) -> bool {
        self.inner.borrow().admitted.contains(relation)
    }

    /// Whether this KB has closed its vocabulary at all.
    pub fn vocabulary_is_closed(&self) -> bool {
        !self.inner.borrow().admitted.is_empty()
    }

    /// The admitted base vocabulary, sorted. Empty when the KB is open.
    pub fn admitted_relations(&self) -> Vec<String> {
        let mut v: Vec<String> = self.inner.borrow().admitted.iter().cloned().collect();
        v.sort();
        v
    }

    /// Whether `relation` is declared derived-only.
    pub fn is_derived_only(&self, relation: &str) -> bool {
        self.inner.borrow().derived_only.contains(relation)
    }

    /// Every relation declared derived-only, sorted — the KB's closure list, for
    /// tests and for surfaces that want to show it.
    pub fn derived_only_relations(&self) -> Vec<String> {
        let mut v: Vec<String> = self.inner.borrow().derived_only.iter().cloned().collect();
        v.sort();
        v
    }

    /// Register this KB's external compute dispatch (per-instance — replaces the
    /// old thread-local `register_compute_dispatch`, which the multithreaded
    /// server could never register because each tokio blocking-pool worker had
    /// its own `None` thread-local). Valid numeric built-in arithmetic
    /// (pilji/sumji/dilcu) is evaluated locally first; registered calls whose
    /// arguments are not locally evaluable are forwarded to `eval`/`batch_eval`.
    ///
    /// TRUST BOUNDARY: `Ok(bool)` is trusted as the result of that compute step,
    /// so a malicious or compromised dispatcher can make a proof wrong. It is
    /// query-local: never inserted into the logical fact store or assertion
    /// registry, never cached across queries, and never reused during an outage.
    /// The caller owns authentication, integrity, freshness, revocation, and audit
    /// policy before returning that Boolean. An `Err` becomes
    /// `UNKNOWN (backend-unavailable)`; the current proof schema records no policy
    /// receipt or backend identity.
    pub fn set_compute_dispatch(
        &self,
        eval: crate::compute::EvalFn,
        batch_eval: crate::compute::BatchEvalFn,
    ) {
        let mut inner = self.inner.borrow_mut();
        inner.compute_eval = Some(eval);
        inner.compute_batch_eval = Some(batch_eval);
    }

    /// Peek at the next assertion id this KB can accept.
    ///
    /// Persistent wrappers use this together with their durable registry's
    /// allocator so a lower-level in-memory assertion cannot make the two id
    /// spaces collide. The value is only a snapshot: the caller must serialize
    /// mutations and then pass its chosen id to [`Self::assert_fact_with_id`].
    pub fn next_fact_id(&self) -> Result<u64, NibliError> {
        self.ensure_ready()?;
        let id = self.inner.borrow().fact_counter;
        id.checked_add(1).map(|_| id).ok_or_else(|| {
            NibliError::Reasoning(
                "fact-id space exhausted; assertion ids are monotonic semantic Skolem sources"
                    .to_string(),
            )
        })
    }

    /// Run the pure assertion-side structural preflight without allocating an id
    /// or mutating the knowledge base. Multi-root surfaces use this before
    /// installing any independently retractable root.
    pub fn validate_assertion(&self, logic: &LogicBuffer) -> Result<(), NibliError> {
        self.ensure_ready()?;
        let mut logic = logic.clone();
        preflight_assertion_buffer(&mut logic).map_err(NibliError::Reasoning)
    }

    /// A singleton can transfer its owned arena directly to normal assertion
    /// ingress, whose preflight still runs before allocating an ID. A multi-root
    /// statement retains the whole-buffer preflight before independent roots.
    fn checked_statement_roots(&self, buffer: LogicBuffer) -> Result<Vec<LogicBuffer>, NibliError> {
        if buffer.roots.len() <= 1 {
            return Ok(vec![buffer]);
        }
        self.validate_assertion(&buffer)?;
        Ok(buffer.split_roots())
    }

    /// Assert a compiled FOL formula into the knowledge base. Returns the fact ID.
    /// Exact-count and executable compute formulas in asserted position are
    /// query-only and cannot be installed as constraints/facts; opaque
    /// abstraction content remains quoted.
    pub fn assert_fact(&self, logic: LogicBuffer, label: String) -> Result<u64, NibliError> {
        // The assert IS the reasoning stage: by the time this runs the buffer has
        // already passed nibli-semantics, so every failure here (stratification, fail-closed
        // rule compilation, the zero-ingest guard, rebuild replay) is reasoning-layer.
        // The layer contract is Syntax=nibli-kr / Semantic=nibli-semantics / Reasoning=nibli-reason.
        self.transaction(|candidate| {
            candidate
                .assert_unpublished_fact(logic, label)
                .map_err(NibliError::Reasoning)
        })
    }

    /// Append ordered compiled statements atomically with one detached candidate.
    /// Normal per-statement guards and stratification still run. Each root has
    /// its own ID and label; any error discards the entire candidate.
    pub fn assert_compiled_batch(
        &self,
        statements: Vec<(LogicBuffer, String)>,
    ) -> Result<Vec<Vec<u64>>, NibliError> {
        self.transaction(|candidate| {
            let mut groups = Vec::with_capacity(statements.len());
            for (buffer, label) in statements {
                if candidate
                    .inner
                    .borrow()
                    .cancel
                    .as_ref()
                    .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                {
                    return Err(NibliError::Reasoning(
                        "fixture assertion cancelled".to_owned(),
                    ));
                }
                let mut ids = Vec::new();
                for root in candidate.checked_statement_roots(buffer)? {
                    ids.push(
                        candidate
                            .assert_unpublished_fact(root, label.clone())
                            .map_err(NibliError::Reasoning)?,
                    );
                }
                groups.push(ids);
            }
            Ok(groups)
        })
    }

    /// Build a fresh in-memory KB from ordered, separately compiled statements.
    ///
    /// Each root retains its own assertion ID and statement label. All normal
    /// assertion guards run in order, including vocabulary and derived-only
    /// declarations. The unpublished KB checks stratification once after the
    /// last statement instead of repeating the same whole-graph analysis after
    /// every rule. Any failure discards the entire new KB.
    pub fn from_compiled_batch(
        statements: Vec<(LogicBuffer, String)>,
    ) -> Result<(Self, Vec<Vec<u64>>), NibliError> {
        Self::from_compiled_batch_with_cancel(
            statements,
            Arc::new(std::sync::atomic::AtomicBool::new(false)),
        )
    }

    /// Cancellable counterpart of [`Self::from_compiled_batch`].
    pub fn from_compiled_batch_with_cancel(
        statements: Vec<(LogicBuffer, String)>,
        cancellation: Arc<std::sync::atomic::AtomicBool>,
    ) -> Result<(Self, Vec<Vec<u64>>), NibliError> {
        let kb = Self::new();
        kb.set_cancel_flag(Arc::clone(&cancellation));
        kb.inner.borrow_mut().deferred_stratification = true;
        let mut ids = Vec::with_capacity(statements.len());
        for (buffer, label) in statements {
            if cancellation.load(std::sync::atomic::Ordering::Relaxed) {
                return Err(NibliError::Reasoning(
                    "fixture construction cancelled".to_owned(),
                ));
            }
            let mut statement_ids = Vec::new();
            for root in kb.checked_statement_roots(buffer)? {
                // This KB is unpublished: a batch error discards it wholesale.
                // Avoid cloning its growing state for every individual root.
                statement_ids.push(
                    kb.assert_unpublished_fact(root, label.clone())
                        .map_err(NibliError::Reasoning)?,
                );
            }
            ids.push(statement_ids);
        }
        {
            if cancellation.load(std::sync::atomic::Ordering::Relaxed) {
                return Err(NibliError::Reasoning(
                    "fixture construction cancelled".to_owned(),
                ));
            }
            let mut inner = kb.inner.borrow_mut();
            for edges in inner.pred_dep_graph.values_mut() {
                edges.sort_unstable();
                edges.dedup();
            }
            rules::check_stratification(&inner.pred_dep_graph).map_err(NibliError::Reasoning)?;
            inner.deferred_stratification = false;
        }
        Ok((kb, ids))
    }

    /// Run a query under temporary assumptions without mutating the real KB.
    /// Clones the KB, asserts all assumptions into the clone, runs the callback,
    /// and discards the clone. The original KB is untouched.
    ///
    /// Assumptions use assertion semantics, so CountNode and executable
    /// ComputeNode formulas are rejected rather than treated as temporary
    /// constraints/facts. Supports multiple independent hypotheticals (each gets its own snapshot)
    /// and nesting (the callback receives a `&KnowledgeBase` with `with_assumptions`).
    pub fn with_assumptions<F, R>(&self, assumptions: &[LogicBuffer], f: F) -> Result<R, NibliError>
    where
        F: FnOnce(&KnowledgeBase) -> R,
    {
        self.ensure_ready()?;
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
    ///
    /// Shares the assertion guards with stored-fact semantics
    /// ([`kb::validate_constraint_conjunct`]): a conjunct naming a reference
    /// external-compute relation, or an operational numeric comparison, is
    /// REFUSED — such facts are refused at assertion ingress, so a constraint
    /// over them could never match anything and would be inert by
    /// construction while looking like a guarantee.
    pub fn register_constraint(
        &self,
        label: String,
        mut conjuncts: Vec<kb::StoredFact>,
    ) -> Result<(), NibliError> {
        self.ensure_ready()?;
        for conjunct in &mut conjuncts {
            kb::canonicalize_stored_fact_abstraction_marker(conjunct)
                .map_err(NibliError::Reasoning)?;
            kb::validate_constraint_conjunct(conjunct).map_err(NibliError::Reasoning)?;
        }
        let predicates: Vec<String> = conjuncts.iter().map(|c| c.relation().to_string()).collect();
        let mut inner = self.inner.borrow_mut();
        inner.integrity_constraints.push(kb::IntegrityConstraint {
            label,
            conjuncts,
            predicates,
        });
        Ok(())
    }

    /// Check whether a caller-supplied formula is entailed by the knowledge
    /// base (four-valued result). This is the native BYO-IR query boundary: an
    /// explicit [`LogicNode::ComputeNode`] may carry an arbitrary relation name
    /// and argument vector directly to the configured dispatcher. No text
    /// registration or arity inference occurs on this path; compute IR remains
    /// query-only at assertion ingress.
    pub fn query_entailment(&self, logic: LogicBuffer) -> Result<QueryResult, NibliError> {
        self.ensure_ready()?;
        self.query_entailment_inner(logic)
            .map_err(NibliError::Reasoning)
    }

    /// Find all satisfying witness binding sets for existential variables in the formula.
    /// Returns `NibliError::Reasoning` with `witness enumeration incomplete` when any
    /// evaluated candidate leaf is `Unknown(_)` or `ResourceExceeded(_)`.
    pub fn query_find(&self, logic: LogicBuffer) -> Result<Vec<Vec<WitnessBinding>>, NibliError> {
        self.ensure_ready()?;
        self.query_find_inner(logic).map_err(NibliError::Reasoning)
    }

    /// Count the number of distinct witness binding sets satisfying the formula.
    /// Inherits [`Self::query_find`]'s complete-or-error collection contract.
    pub fn count_witnesses(&self, logic: LogicBuffer) -> Result<usize, NibliError> {
        self.query_find(logic).map(|bindings| bindings.len())
    }

    /// Aggregate numeric values of a named variable across all witness binding
    /// sets — FAIL CLOSED. Inherits [`Self::query_find`]'s complete-or-error
    /// enumeration contract, then refuses (rather than silently dropping) every
    /// defective binding: a set that does not bind `variable`, a nonnumeric
    /// value, a non-finite operand, and a non-finite aggregate (overflow) are
    /// each a distinct [`NibliError::Reasoning`]. A definitive zero-witness
    /// enumeration is [`AggregateOutcome::Empty`]; a valid aggregate carries
    /// its contributing-witness count as provenance.
    pub fn aggregate(
        &self,
        logic: LogicBuffer,
        variable: &str,
        op: nibli_types::logic::AggregateOp,
    ) -> Result<nibli_types::logic::AggregateOutcome, NibliError> {
        use nibli_types::logic::{AggregateOp, AggregateOutcome};
        let bindings = self.query_find(logic)?;
        let mut values: Vec<f64> = Vec::with_capacity(bindings.len());
        for (i, binding_set) in bindings.iter().enumerate() {
            let Some(binding) = binding_set.iter().find(|b| b.variable == variable) else {
                return Err(NibliError::Reasoning(format!(
                    "aggregate over `{variable}` is undefined: witness binding set #{i} \
                     does not bind the variable — refusing a partial aggregate \
                     (fail closed, never a silent drop)"
                )));
            };
            let LogicalTerm::Number(n) = &binding.term else {
                return Err(NibliError::Reasoning(format!(
                    "aggregate over `{variable}` is undefined: witness binding set #{i} \
                     binds a non-numeric term ({:?}) — refusing a mixed aggregate \
                     (fail closed, never a silent drop)",
                    binding.term
                )));
            };
            if !n.is_finite() {
                return Err(NibliError::Reasoning(format!(
                    "aggregate over `{variable}` is undefined: witness binding set #{i} \
                     binds the non-finite value {n} — refusing (fail closed)"
                )));
            }
            values.push(*n);
        }
        if values.is_empty() {
            return Ok(AggregateOutcome::Empty);
        }
        let witnesses = values.len();
        let value = match op {
            AggregateOp::Sum => values.iter().sum(),
            AggregateOp::Min => values.iter().cloned().reduce(f64::min).unwrap_or(0.0),
            AggregateOp::Max => values.iter().cloned().reduce(f64::max).unwrap_or(0.0),
            AggregateOp::Avg => values.iter().sum::<f64>() / witnesses as f64,
        };
        if !value.is_finite() {
            return Err(NibliError::Reasoning(format!(
                "aggregate over `{variable}` overflowed: the {witnesses}-witness result \
                 is non-finite ({value}) — refusing (fail closed)"
            )));
        }
        Ok(AggregateOutcome::Value { value, witnesses })
    }

    /// Check entailment and return a proof trace showing the full derivation chain.
    pub fn query_entailment_with_proof(
        &self,
        logic: LogicBuffer,
    ) -> Result<(QueryResult, ProofTrace), NibliError> {
        self.ensure_ready()?;
        self.query_entailment_with_proof_inner(logic)
            .map_err(NibliError::Reasoning)
    }

    /// Clear all facts, rules, indexes, and derived state.
    pub fn reset(&self) -> Result<(), NibliError> {
        self.ensure_ready()?;
        let mut inner = self.inner.borrow_mut();
        inner.reset();
        invalidate_pred_cache(&inner); // Tabling: KB cleared.
        Ok(())
    }

    /// Retract a fact by ID — ONE path for every fact shape: mark the registry
    /// record retracted, rebuild from the survivors (retract ≡ never-asserted;
    /// see `retract_fact_inner`'s doc block and GUARANTEES §Retraction Model).
    pub fn retract_fact(&self, id: u64) -> Result<(), NibliError> {
        self.transaction(|candidate| {
            candidate
                .retract_fact_inner(id)
                .map_err(NibliError::Reasoning)
        })
    }

    /// List all active (non-retracted) facts with their IDs and labels.
    /// Snapshot of every fact currently in the truth store — asserted AND
    /// eagerly derived (forward chaining inserts conclusions here), in
    /// unspecified order. The TYPED read surface for exporters
    /// (nibli-import's N-Triples emitter): labels are display, these are the
    /// facts. Rules are not facts and are not included.
    pub fn active_typed_facts(&self) -> Result<Vec<kb::StoredFact>, NibliError> {
        self.ensure_ready()?;
        Ok(self
            .inner
            .borrow()
            .fact_store
            .all_facts()
            .cloned()
            .collect())
    }

    pub fn list_facts(&self) -> Result<Vec<FactSummary>, NibliError> {
        self.ensure_ready()?;
        self.list_facts_inner().map_err(NibliError::Reasoning)
    }

    /// Ids of LIVE (non-retracted) stored statements — facts AND rules ride the
    /// same registry — whose assertion-reachable content references `relation`.
    /// Role spellings (`foo_x1`) collapse onto the anchor; opaque quoted content
    /// and unreachable sibling-root arena entries do not count. Ascending order.
    ///
    /// This is the registration-guard primitive: a compute name may only be
    /// registered while this is empty (`CoreSession::register_compute_predicate`),
    /// because registration flips how future compiled queries SPELL the relation
    /// (`Predicate` → `ComputeNode`) and a stored extension would become
    /// unreachable-but-listed the moment the query side starts dispatching.
    pub fn stored_statement_ids_referencing(&self, relation: &str) -> Vec<u64> {
        let inner = self.inner.borrow();
        let mut ids: Vec<u64> = inner
            .fact_registry
            .values()
            .filter(|r| !r.retracted)
            .filter(|r| {
                r.buffer
                    .as_ref()
                    .is_some_and(|buffer| kb::buffer_references_relation(buffer, relation))
            })
            .map(|r| r.id)
            .collect();
        ids.sort_unstable();
        ids
    }

    /// Drop the stratum-ordered saturation. For mutations OUTSIDE KB content:
    /// compute-name registration changes how future compiled queries SPELL a
    /// relation (`Predicate` → `ComputeNode`), so the content-mutation
    /// invalidations never fire and `materialization_report` would keep listing
    /// the name as a complete stored extension — a stale report, not a wrong
    /// verdict (the saturator refuses `ComputeNode` conjuncts), but stale
    /// reports are how re-derivations come to disagree.
    pub fn invalidate_materialization(&self) {
        let inner = self.inner.borrow();
        reasoning::invalidate_materialization(&inner);
        *inner.materialization_plan.borrow_mut() = None;
    }

    /// Mark all rules concluding the given predicate as forward-chaining enabled.
    /// Forward-enabled rules fire eagerly on fact insertion when all conditions
    /// are already in the truth store (directly asserted or eagerly derived).
    ///
    /// FAIL CLOSED: a rule with a negation-as-failure condition (a flat negated
    /// condition or a `poi na <predicate>` group) is NOT forward-enabled — it stays
    /// backward-only, where it is sound (backward chaining re-evaluates `¬Q` at
    /// query time). Forward chaining + NAF has no truth maintenance: a
    /// forward-derived conclusion would never be retracted when a later assertion
    /// makes the negated dependency true. Positive (negation-free) rules enable
    /// normally; `forward = false` (disabling) always applies.
    ///
    /// SESSION CONFIGURATION (like `strict`): the setting is recorded per
    /// conclusion predicate and consulted at every rule REGISTRATION, so it
    /// applies to rules registered later and SURVIVES the rebuild a retraction
    /// (or rollback, or profile switch) performs — replay re-registers every
    /// surviving rule under the recorded overrides, re-checking the NAF refusal
    /// per rule. Enabling never fires retroactively: eager derivation happens on
    /// subsequent triggering insertions, and verdicts are unaffected either way
    /// (backward chaining derives the same conclusions at query time). Cleared
    /// by `reset()`.
    pub fn set_rule_forward(&self, conclusion_predicate: &str, forward: bool) {
        let mut inner = self.inner.borrow_mut();
        inner.query_domain.completed_at.set(None);
        *inner.materialization_plan.borrow_mut() = None;
        inner
            .rule_exec_overrides
            .entry(conclusion_predicate.to_string())
            .or_default()
            .forward = Some(forward);
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
    ///
    /// SESSION CONFIGURATION: recorded per conclusion predicate, consulted at
    /// every rule registration, survives rebuild (see [`Self::set_rule_forward`]).
    /// Cleared by `reset()`.
    pub fn set_rule_priority(&self, conclusion_predicate: &str, priority: u32) {
        let mut inner = self.inner.borrow_mut();
        inner.query_domain.completed_at.set(None);
        *inner.materialization_plan.borrow_mut() = None;
        inner
            .rule_exec_overrides
            .entry(conclusion_predicate.to_string())
            .or_default()
            .priority = Some(priority);
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

    /// The live execution settings of every rule concluding
    /// `conclusion_predicate`: `(label, forward, priority)` per bucket member,
    /// in bucket order (descending priority). Programmatic read twin of
    /// [`Self::set_rule_forward`] / [`Self::set_rule_priority`] — what the
    /// retraction differential compares across rebuilds. Empty when no rule
    /// concludes the predicate.
    pub fn rule_execution_settings(&self, conclusion_predicate: &str) -> Vec<(String, bool, u32)> {
        self.inner
            .borrow()
            .universal_rules
            .get(conclusion_predicate)
            .map(|rules| {
                rules
                    .iter()
                    .map(|r| (r.label.clone(), r.forward, r.priority))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Declare that an entity belongs to a sort.
    /// e.g., `declare_entity_sort("adam", "person")` means adam is a person.
    pub fn declare_entity_sort(&self, entity: &str, sort: &str) {
        let mut inner = self.inner.borrow_mut();
        inner.query_domain.completed_at.set(None);
        inner
            .entity_sorts
            .insert(entity.to_string(), sort.to_string());
    }

    /// Declare a subsort relationship: child ⊂ parent.
    /// e.g., `declare_subsort("person", "animal")` means every person is an animal.
    /// Transitive: if person ⊂ animal and animal ⊂ entity, then person is compatible with entity.
    pub fn declare_subsort(&self, child: &str, parent: &str) {
        let mut inner = self.inner.borrow_mut();
        inner.query_domain.completed_at.set(None);
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
        inner.query_domain.completed_at.set(None);
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

    /// Store-only fast path; the report method adds evaluator-based checks.
    fn check_contradictions_stored(&self) -> Vec<String> {
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
        //    counterpart holds. Each negation is a template group with event
        //    arguments generalized to pattern variables (see
        //    `record_negative_ground_fact`). Leg (a): one consistent binding
        //    satisfies EVERY template against the **asserted** fact store
        //    (whole-group requirement prevents false positives from unrelated
        //    events sharing a predicate). Leg (b): after this borrow ends, groups
        //    that miss the store are re-checked via `query_entailment` so a
        //    **derived** positive also flags. Flat `du` inequalities go to §5.
        //    Query semantics (NAF/CWA) are unaffected — negatives never enter
        //    the positive store.
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
        //    this fast path. The report subsequently evaluates antecedents using
        //    typed witness enumeration after this store borrow has ended.
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

/// Convert a negative-fact template group into a positive entailment query.
/// Pattern variables (generalized event Skolems) become existentially quantified
/// logic variables so a later contrary (or derived) positive with a different
/// event Skolem still matches — same intent as `negative_group_holds` over the store.
fn negative_group_to_query_buffer(group: &[StoredFact]) -> Option<LogicBuffer> {
    if group.is_empty() {
        return None;
    }
    fn ground_term_to_logical(t: &GroundTerm) -> Option<LogicalTerm> {
        match t {
            GroundTerm::Constant(s) => Some(LogicalTerm::Constant(s.clone())),
            GroundTerm::Number(bits) => Some(LogicalTerm::Number(f64::from_bits(*bits))),
            GroundTerm::Description(s) => Some(LogicalTerm::Description(s.clone())),
            GroundTerm::Unspecified => Some(LogicalTerm::Unspecified),
            GroundTerm::PatternVar(s) => Some(LogicalTerm::Variable(template_query_variable(s))),
            GroundTerm::Skolem(_)
            | GroundTerm::SkolemFn(_, _)
            | GroundTerm::DepPair(_, _)
            | GroundTerm::SkolemPlaceholder(_) => None,
        }
    }

    let mut nodes: Vec<LogicNode> = Vec::new();
    let mut pattern_vars: Vec<String> = Vec::new();
    let mut leaf_ids: Vec<u32> = Vec::new();

    for fact in group {
        let gf = fact.inner();
        for arg in &gf.args {
            if let GroundTerm::PatternVar(s) = arg {
                let variable = template_query_variable(s);
                if !pattern_vars.contains(&variable) {
                    pattern_vars.push(variable);
                }
            }
        }
        let args: Vec<LogicalTerm> = gf
            .args
            .iter()
            .map(ground_term_to_logical)
            .collect::<Option<Vec<_>>>()?;
        let pred_id = nodes.len() as u32;
        nodes.push(LogicNode::Predicate((gf.relation.clone(), args)));
        let wrapped = match fact {
            StoredFact::Bare(_) => pred_id,
            StoredFact::Past(_) => {
                let id = nodes.len() as u32;
                nodes.push(LogicNode::PastNode(pred_id));
                id
            }
            StoredFact::Present(_) => {
                let id = nodes.len() as u32;
                nodes.push(LogicNode::PresentNode(pred_id));
                id
            }
            StoredFact::Future(_) => {
                let id = nodes.len() as u32;
                nodes.push(LogicNode::FutureNode(pred_id));
                id
            }
            StoredFact::Obligatory(_) => {
                let id = nodes.len() as u32;
                nodes.push(LogicNode::ObligatoryNode(pred_id));
                id
            }
            StoredFact::Permitted(_) => {
                let id = nodes.len() as u32;
                nodes.push(LogicNode::PermittedNode(pred_id));
                id
            }
        };
        leaf_ids.push(wrapped);
    }

    let mut root = leaf_ids[0];
    for &id in &leaf_ids[1..] {
        let and_id = nodes.len() as u32;
        nodes.push(LogicNode::AndNode((root, id)));
        root = and_id;
    }
    // Outermost ∃ for each pattern var (event slots) so free variables are bound.
    for pvar in pattern_vars.into_iter().rev() {
        let ex_id = nodes.len() as u32;
        nodes.push(LogicNode::ExistsNode((pvar, root)));
        root = ex_id;
    }

    Some(LogicBuffer {
        nodes,
        roots: vec![root],
    })
}

/// Internal rule/negative-pattern event names are not user individual binders.
/// Normalize at this adapter boundary, keeping a reversible mapping for the
/// constraint substitution that consumes enumeration results.
fn template_query_variable(name: &str) -> String {
    if name.starts_with("ev__") || name.starts_with("__neg_ev") {
        format!("_ev__constraint_{name}")
    } else {
        name.to_string()
    }
}

fn restore_template_query_variable(name: String) -> String {
    name.strip_prefix("_ev__constraint_")
        .map(str::to_string)
        .unwrap_or(name)
}

#[cfg(test)]
mod tests;
