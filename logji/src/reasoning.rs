use super::*;

/// Temporarily bind `key` to `value` in `subs`, run `f`, then restore the
/// previous binding (or remove if there was none). Avoids the repeated
/// save/restore boilerplate across quantifier evaluation.
fn with_sub<T>(
    subs: &mut HashMap<String, GroundTerm>,
    key: &str,
    value: GroundTerm,
    f: impl FnOnce(&mut HashMap<String, GroundTerm>) -> T,
) -> T {
    let prev = subs.insert(key.to_string(), value);
    let result = f(subs);
    match prev {
        Some(p) => {
            subs.insert(key.to_string(), p);
        }
        None => {
            subs.remove(key);
        }
    }
    result
}

/// Build the full candidate vector for unbound event variable search:
/// all typed domain members + SkolemFn witness terms from the registry.
fn build_all_candidates(inner: &KnowledgeBaseInner) -> Vec<GroundTerm> {
    let members = inner.all_typed_domain_members();
    let mut candidates: Vec<GroundTerm> = members.to_vec();
    for entry in &inner.skolem_fn_registry {
        for combo in GroundTermCartesianProduct::new(members, entry.dep_count) {
            candidates.push(build_skolem_fn_term(&entry.base_name, &combo));
        }
    }
    candidates
}

/// Lazily build (at most once per backward-chaining frame) the unbound-event
/// candidate vector. The full members^dep_count product is only needed when a
/// matched rule actually has unbound `ev__` pattern variables; most frames
/// never reach that point, so the eager build was pure waste.
fn ensure_candidates<'a>(
    slot: &'a mut Option<Vec<GroundTerm>>,
    inner: &KnowledgeBaseInner,
) -> &'a [GroundTerm] {
    if slot.is_none() {
        *slot = Some(build_all_candidates(inner));
    }
    slot.as_deref().expect("slot was just filled")
}

/// A condition relation is "index-decidable" when backward chaining can never
/// prove it beyond a direct fact-store lookup: no rule concludes the relation
/// (temporal lifting consults the same relation-keyed bucket, so this covers
/// tensed goals too), it is not the special-cased `du` equality predicate, and
/// no du-equivalence classes exist (equivalence substitution could otherwise
/// rewrite the fact into an asserted variant via the recursive fallback).
///
/// For such relations `check_predicate_in_kb_typed` reduces to
/// `typed_fact_is_asserted` at ANY depth, so the unbound-event-variable filter
/// can evaluate them definitively without recursion — crucially, even at the
/// depth horizon, where the recursive check returns ResourceExceeded for
/// every candidate and would otherwise pessimistically keep the entire
/// members^k cartesian product alive.
fn condition_is_index_decidable(relation: &str, inner: &KnowledgeBaseInner) -> bool {
    relation != "du"
        && inner.equivalence_parent.is_empty()
        && !inner.universal_rules.contains_key(relation)
}

fn prefer_non_definitive(
    current: Option<QueryResult>,
    candidate: QueryResult,
) -> Option<QueryResult> {
    if candidate.is_definitive() {
        return current;
    }
    match (current, candidate) {
        (Some(QueryResult::ResourceExceeded(kind)), QueryResult::Unknown(_)) => {
            Some(QueryResult::ResourceExceeded(kind))
        }
        (Some(QueryResult::Unknown(_)), QueryResult::ResourceExceeded(kind)) => {
            Some(QueryResult::ResourceExceeded(kind))
        }
        (Some(existing), _) => Some(existing),
        (None, candidate) => Some(candidate),
    }
}

fn combine_conjunction(left: QueryResult, right: QueryResult) -> QueryResult {
    if left.is_false() || right.is_false() {
        QueryResult::False
    } else if left.is_true() && right.is_true() {
        QueryResult::True
    } else {
        prefer_non_definitive(None, left)
            .and_then(|acc| prefer_non_definitive(Some(acc), right))
            .unwrap_or(QueryResult::False)
    }
}

fn combine_disjunction(left: QueryResult, right: QueryResult) -> QueryResult {
    if left.is_true() || right.is_true() {
        QueryResult::True
    } else if left.is_false() && right.is_false() {
        QueryResult::False
    } else {
        prefer_non_definitive(None, left)
            .and_then(|acc| prefer_non_definitive(Some(acc), right))
            .unwrap_or(QueryResult::False)
    }
}

fn negate_result(result: QueryResult) -> QueryResult {
    match result {
        QueryResult::True => QueryResult::False,
        QueryResult::False => QueryResult::True,
        QueryResult::Unknown(reason) => QueryResult::Unknown(reason),
        QueryResult::ResourceExceeded(kind) => QueryResult::ResourceExceeded(kind),
    }
}

/// Cooperative cancellation checkpoint. Returns `Err` when an installed cancel
/// flag has been raised (by the native nibli-server request watchdog), aborting
/// the in-flight query through the existing `Result` error channel. A `None` flag
/// (gasnu/lasna/tests) makes this a single branch with no clock access.
#[inline]
pub(super) fn check_cancelled(inner: &KnowledgeBaseInner) -> Result<(), String> {
    if inner
        .cancel
        .as_ref()
        .is_some_and(|c| c.load(std::sync::atomic::Ordering::Relaxed))
    {
        return Err("reasoning cancelled: deadline exceeded".to_string());
    }
    Ok(())
}

pub(super) fn check_formula_holds(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
) -> Result<QueryResult, String> {
    // Check cancellation both BEFORE and AFTER the sub-evaluation. The pre-check
    // catches a flag that was already raised (e.g. before the query started); the
    // post-check converts a flag raised by the watchdog DURING a long backward-
    // chaining call into a clean `Err` rather than a discarded partial verdict.
    // Recursion runs through this wrapper, so the checks fire at every node.
    check_cancelled(inner)?;
    let result = check_formula_holds_inner(buffer, node_id, subs, inner, tense)?;
    check_cancelled(inner)?;
    Ok(result)
}

fn check_formula_holds_inner(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
) -> Result<QueryResult, String> {
    match get_node(buffer, node_id)? {
        LogicNode::AndNode((l, r)) => {
            let left = check_formula_holds(buffer, *l, subs, inner, tense)?;
            let right = check_formula_holds(buffer, *r, subs, inner, tense)?;
            Ok(combine_conjunction(left, right))
        }
        LogicNode::OrNode((l, r)) => {
            let left = check_formula_holds(buffer, *l, subs, inner, tense)?;
            let right = check_formula_holds(buffer, *r, subs, inner, tense)?;
            Ok(combine_disjunction(left, right))
        }
        // Negation-as-failure (NAF): ¬P holds when P cannot be proved.
        // Sound because stratification is enforced at rule registration time —
        // register_rule() rejects any rule that would create a negative cycle
        // in the predicate dependency graph.
        LogicNode::NotNode(inner_node) => Ok(negate_result(check_formula_holds(
            buffer,
            *inner_node,
            subs,
            inner,
            tense,
        )?)),
        LogicNode::PastNode(inner_node) => {
            check_formula_holds(buffer, *inner_node, subs, inner, Some("Past"))
        }
        LogicNode::PresentNode(inner_node) => {
            check_formula_holds(buffer, *inner_node, subs, inner, Some("Present"))
        }
        LogicNode::FutureNode(inner_node) => {
            check_formula_holds(buffer, *inner_node, subs, inner, Some("Future"))
        }
        LogicNode::ObligatoryNode(inner_node) | LogicNode::PermittedNode(inner_node) => {
            check_formula_holds(buffer, *inner_node, subs, inner, tense)
        }
        LogicNode::ExistsNode((v, body)) => {
            // Try batch compute fast path first (uses slice, no .to_vec()).
            if let Ok(body_node) = get_node(buffer, *body) {
                if let LogicNode::ComputeNode((rel, args)) = body_node {
                    let members = inner.all_typed_domain_members();
                    if let Some(batch) =
                        batch_evaluate_compute_for_members(rel, args, v, members, subs)
                    {
                        // Ingest deferred facts now that the slice borrow is released.
                        for fact in batch.deferred_facts {
                            assert_typed_fact(fact, inner);
                        }
                        if batch.results.iter().any(|r| *r) {
                            return Ok(QueryResult::True);
                        }
                    }
                }
            }
            // Decomposed numeric group (surface arithmetic/comparison): evaluate
            // the operands gathered from the role predicates directly — the
            // verdict is definitive, matching the flat ComputeNode arm.
            if let Some(verdict) = try_evaluate_numeric_group(buffer, v, *body, subs) {
                return Ok(if verdict.holds {
                    QueryResult::True
                } else {
                    QueryResult::False
                });
            }
            // Slow path: need owned Vec because check_formula_holds takes &mut inner.
            // Candidate narrowing (∃-heavy query blowup fix): when the body has
            // a mandatory positive anchor, enumerate only index/rule-derivable
            // candidates instead of the full domain × SkolemFn-registry
            // cartesian — completeness argument at collect_entailment_candidates.
            let candidates: Vec<GroundTerm> =
                match collect_entailment_candidates(buffer, *body, v, subs, inner, tense) {
                    Some(narrowed) => narrowed,
                    None => {
                        let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
                        let mut all = members.clone();
                        for entry in &inner.skolem_fn_registry {
                            for combo in GroundTermCartesianProduct::new(&members, entry.dep_count)
                            {
                                all.push(build_skolem_fn_term(&entry.base_name, &combo));
                            }
                        }
                        all
                    }
                };
            let mut best_result = None;
            for candidate in candidates {
                let result = with_sub(subs, v, candidate, |s| {
                    check_formula_holds(buffer, *body, s, inner, tense)
                })?;
                if result.is_true() {
                    return Ok(QueryResult::True);
                }
                best_result = prefer_non_definitive(best_result, result);
            }
            Ok(best_result.unwrap_or(QueryResult::False))
        }
        LogicNode::ForAllNode((v, body)) => {
            if inner.all_typed_domain_members().is_empty() {
                return Ok(QueryResult::True);
            }
            // Batch compute fast path (slice, no .to_vec()).
            if let Ok(body_node) = get_node(buffer, *body) {
                if let LogicNode::ComputeNode((rel, args)) = body_node {
                    let members = inner.all_typed_domain_members();
                    if let Some(batch) =
                        batch_evaluate_compute_for_members(rel, args, v, members, subs)
                    {
                        for fact in batch.deferred_facts {
                            assert_typed_fact(fact, inner);
                        }
                        return Ok(if batch.results.iter().all(|r| *r) {
                            QueryResult::True
                        } else {
                            QueryResult::False
                        });
                    }
                }
            }
            let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
            let mut best_result = None;
            for member in &members {
                let result = with_sub(subs, v, member.clone(), |s| {
                    check_formula_holds(buffer, *body, s, inner, tense)
                })?;
                if result.is_false() {
                    return Ok(QueryResult::False);
                }
                if !result.is_true() {
                    best_result = prefer_non_definitive(best_result, result);
                }
            }
            Ok(best_result.unwrap_or(QueryResult::True))
        }
        LogicNode::CountNode((v, count, body)) => {
            // Batch compute fast path (slice, no .to_vec()).
            if let Ok(body_node) = get_node(buffer, *body) {
                if let LogicNode::ComputeNode((rel, args)) = body_node {
                    let members = inner.all_typed_domain_members();
                    if let Some(batch) =
                        batch_evaluate_compute_for_members(rel, args, v, members, subs)
                    {
                        for fact in batch.deferred_facts {
                            assert_typed_fact(fact, inner);
                        }
                        let satisfying = batch.results.iter().filter(|r| **r).count() as u32;
                        return Ok(if satisfying == *count {
                            QueryResult::True
                        } else {
                            QueryResult::False
                        });
                    }
                }
            }
            let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
            let mut satisfying = 0u32;
            let mut unresolved = 0u32;
            let mut best_result = None;
            for member in &members {
                let result = with_sub(subs, v, member.clone(), |s| {
                    check_formula_holds(buffer, *body, s, inner, tense)
                })?;
                match result {
                    QueryResult::True => satisfying += 1,
                    QueryResult::False => {}
                    other => {
                        unresolved += 1;
                        best_result = prefer_non_definitive(best_result, other);
                    }
                }
            }
            if unresolved == 0 {
                Ok(if satisfying == *count {
                    QueryResult::True
                } else {
                    QueryResult::False
                })
            } else if satisfying > *count || satisfying + unresolved < *count {
                Ok(QueryResult::False)
            } else {
                Ok(best_result.unwrap_or(QueryResult::Unknown(UnknownReason::IncompleteKnowledge)))
            }
        }
        LogicNode::Predicate((rel, args)) => {
            if let Some(result) = try_numeric_comparison(rel, args, subs) {
                return Ok(if result {
                    QueryResult::True
                } else {
                    QueryResult::False
                });
            }
            // Build typed fact and query typed store.
            if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                let mut visited = HashSet::new();
                Ok(check_predicate_in_kb_typed(&fact, &*inner, 0, &mut visited))
            } else {
                Ok(QueryResult::False) // build_stored_fact_from_node failed — should not happen for Predicate
            }
        }
        LogicNode::ComputeNode((rel, args)) => {
            // Built-in arithmetic FIRST, then external dispatch — the
            // documented Layer-2 ordering (matches gasnu's evaluate() and the
            // batch path; the backend is only consulted for what the engine
            // cannot compute itself).
            if let Some(result) = try_arithmetic_evaluation(rel, args, subs) {
                if result {
                    if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                        assert_typed_fact(fact, inner);
                    }
                }
                return Ok(if result {
                    QueryResult::True
                } else {
                    QueryResult::False
                });
            }
            let resolved = resolve_args_for_dispatch(args, subs);
            if let Ok(result) = dispatch_to_backend(rel, &resolved) {
                if result {
                    if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                        assert_typed_fact(fact, inner);
                    }
                }
                return Ok(if result {
                    QueryResult::True
                } else {
                    QueryResult::False
                });
            }
            if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                let mut visited = HashSet::new();
                Ok(check_predicate_in_kb_typed(&fact, &*inner, 0, &mut visited))
            } else {
                Ok(QueryResult::False)
            }
        }
    }
}

pub(super) fn find_witnesses(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
) -> Result<Vec<Vec<(String, GroundTerm)>>, String> {
    match get_node(buffer, node_id)? {
        LogicNode::ExistsNode((v, body)) => {
            let mut results = Vec::new();

            // Index-driven candidate extraction: walk the body to find
            // positive predicates mentioning this variable, extract
            // candidates from the predicate index + backward-chain rule
            // conclusions. Falls back to full domain scan only when no
            // positive predicate anchor exists (pure negation body).
            let candidates: Vec<GroundTerm> =
                if let Some(indexed) = collect_candidates(buffer, *body, v, subs, inner, tense) {
                    // Also include SkolemFn witnesses — these may not appear
                    // in the index but are valid existential witnesses.
                    let members = inner.all_typed_domain_members();
                    let entries = &inner.skolem_fn_registry;
                    let mut all = indexed;
                    for entry in entries {
                        for combo in GroundTermCartesianProduct::new(members, entry.dep_count) {
                            all.push(build_skolem_fn_term(&entry.base_name, &combo));
                        }
                    }
                    all
                } else {
                    // No positive anchor — must enumerate all domain members.
                    // This only happens for bodies like ∃x.¬P(x).
                    let members = inner.all_typed_domain_members();
                    let entries = &inner.skolem_fn_registry;
                    let mut all: Vec<GroundTerm> = members.to_vec();
                    for entry in entries {
                        for combo in GroundTermCartesianProduct::new(members, entry.dep_count) {
                            all.push(build_skolem_fn_term(&entry.base_name, &combo));
                        }
                    }
                    all
                };

            for candidate in candidates {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), candidate.clone());
                let sub_results = find_witnesses(buffer, *body, &mut new_subs, inner, tense)?;
                for mut bindings in sub_results {
                    bindings.push((v.clone(), candidate.clone()));
                    results.push(bindings);
                }
            }

            Ok(results)
        }
        LogicNode::PastNode(inner_node) => {
            find_witnesses(buffer, *inner_node, subs, inner, Some("Past"))
        }
        LogicNode::PresentNode(inner_node) => {
            find_witnesses(buffer, *inner_node, subs, inner, Some("Present"))
        }
        LogicNode::FutureNode(inner_node) => {
            find_witnesses(buffer, *inner_node, subs, inner, Some("Future"))
        }
        LogicNode::AndNode((l, r)) => {
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
            let mut results = find_witnesses(buffer, *l, subs, inner, tense)?;
            results.extend(find_witnesses(buffer, *r, subs, inner, tense)?);
            Ok(results)
        }
        _ => {
            if check_formula_holds(buffer, node_id, subs, inner, tense)?.is_true() {
                Ok(vec![vec![]])
            } else {
                Ok(vec![])
            }
        }
    }
}

// ─── Typed Backward-Chaining (Phase 4-5b) ────────────────────────
//
// These functions mirror the fact_repr-based backward-chaining above but
// operate on StoredFact/GroundTerm directly, avoiding all string ops.

thread_local! {
    static TYPED_PRED_CACHE: RefCell<HashMap<StoredFact, QueryResult>> =
        RefCell::new(HashMap::new());
}

pub(super) fn clear_typed_pred_cache() {
    TYPED_PRED_CACHE.with(|c| c.borrow_mut().clear());
}

/// Check if a typed fact is asserted in the typed fact store.
pub(super) fn typed_fact_is_asserted(fact: &StoredFact, inner: &KnowledgeBaseInner) -> bool {
    // Fast path: exact match.
    if inner.fact_store.contains(fact) {
        return true;
    }
    // Equivalence path: try substitutions of equivalent terms in args.
    if inner.equivalence_parent.is_empty() {
        return false;
    }
    typed_fact_is_asserted_with_equivalence(fact, inner)
}

/// Check if a fact holds under any equivalence-class substitution of its arguments.
fn typed_fact_is_asserted_with_equivalence(fact: &StoredFact, inner: &KnowledgeBaseInner) -> bool {
    let gf = fact.inner();
    // For each arg position, get the equivalence class.
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

    // If no argument has equivalents beyond itself, nothing to try.
    if equiv_args.iter().all(|cls| cls.len() <= 1) {
        return false;
    }

    // Enumerate cartesian product of equivalence classes (skip original combo).
    for combo in CartesianProduct::new(&equiv_args) {
        let variant_gf = GroundFact::new(gf.relation.clone(), combo);
        let variant = StoredFact::with_tense_from(variant_gf, fact);
        if variant != *fact && inner.fact_store.contains(&variant) {
            return true;
        }
    }
    false
}

/// Simple cartesian product iterator over Vec<Vec<T>>.
struct CartesianProduct<'a> {
    sets: &'a [Vec<GroundTerm>],
    indices: Vec<usize>,
    done: bool,
}

impl<'a> CartesianProduct<'a> {
    fn new(sets: &'a [Vec<GroundTerm>]) -> Self {
        let done = sets.iter().any(|s| s.is_empty());
        Self {
            sets,
            indices: vec![0; sets.len()],
            done,
        }
    }
}

impl Iterator for CartesianProduct<'_> {
    type Item = Vec<GroundTerm>;

    fn next(&mut self) -> Option<Vec<GroundTerm>> {
        if self.done {
            return None;
        }
        let result: Vec<GroundTerm> = self
            .indices
            .iter()
            .enumerate()
            .map(|(i, &idx)| self.sets[i][idx].clone())
            .collect();

        // Advance indices (rightmost first).
        let mut carry = true;
        for i in (0..self.sets.len()).rev() {
            if carry {
                self.indices[i] += 1;
                if self.indices[i] < self.sets[i].len() {
                    carry = false;
                } else {
                    self.indices[i] = 0;
                }
            }
        }
        if carry {
            self.done = true;
        }
        Some(result)
    }
}

/// Collect rules whose conclusion templates match the given fact's relation name.
/// Returns rules sorted by priority descending (highest priority first).
fn collect_matching_rules_typed(
    fact: &StoredFact,
    universal_rules: &HashMap<String, Vec<Arc<UniversalRuleRecord>>>,
) -> Vec<Arc<UniversalRuleRecord>> {
    let rel = fact.relation();
    let mut rules = universal_rules.get(rel).cloned().unwrap_or_default();
    rules.sort_by_key(|r| std::cmp::Reverse(r.priority));
    rules
}

/// Check if a typed fact holds in the KB (direct assertion or backward-chaining).
pub(super) fn check_predicate_in_kb_typed(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
) -> QueryResult {
    // Cooperative cancellation: once the watchdog raises the flag, collapse every
    // predicate sub-check to False immediately so a candidates² backward-chaining
    // blowup unwinds in bounded time. Returns before any cache write, so no
    // cancelled verdict is memoized. The Result-returning callers (check_formula_
    // holds / _traced) convert the raised flag into the final `Err`.
    if check_cancelled(inner).is_err() {
        return QueryResult::False;
    }
    // Interactive trace: print when a traced predicate is encountered.
    let is_traced = inner.traced_predicates.contains(fact.relation());
    if is_traced {
        let indent = "  ".repeat(depth);
        eprintln!(
            "[Trace] {}depth={} check: {}",
            indent,
            depth,
            fact.to_display_string()
        );
    }

    // du reflexivity + transitivity: du(x,x) always holds; du(a,b) holds
    // if a and b are in the same equivalence class.
    if fact.relation() == "du" {
        let args = &fact.inner().args;
        if args.len() == 2 {
            if args[0] == args[1] {
                return QueryResult::True; // Reflexivity
            }
            if !inner.equivalence_parent.is_empty() {
                let canon_a = find_canonical_readonly(&inner.equivalence_parent, &args[0]);
                let canon_b = find_canonical_readonly(&inner.equivalence_parent, &args[1]);
                if canon_a == canon_b {
                    return QueryResult::True; // Symmetry + transitivity
                }
            }
        }
    }

    if typed_fact_is_asserted(fact, inner) {
        return QueryResult::True;
    }
    let cached = PRED_CACHE_ENABLED.with(|e| {
        if e.get() {
            TYPED_PRED_CACHE.with(|c| c.borrow().get(fact).cloned())
        } else {
            None
        }
    });
    if let Some(result) = cached {
        return result;
    }
    let mut result = try_backward_chain_typed(fact, inner, depth, visited);

    // If backward chaining failed, try equivalence variants.
    //
    // This fallback recurses through `check_predicate_in_kb_typed`. Without a
    // cycle guard it loops forever: `try_backward_chain_typed` removes its own
    // `visited` entry before returning, so by the time we get here `fact` is no
    // longer in `visited`, and checking an equivalence variant can regenerate
    // `fact` (du(a,b) makes `a` and `b` mutually substitutable). Asserting du(a,b)
    // then querying an unprovable predicate about `b` would otherwise stack-
    // overflow: `P(b)` → variant `P(a)` → variant `P(b)` → … .
    //
    // Cut the cycle with the shared `visited` set: re-insert `fact` for the
    // duration of the variant search and skip any variant already on the stack.
    // The recursion keeps the SAME `depth` (the variant is a lateral equality
    // rewrite, not a deeper proof step) so iterative deepening is unaffected —
    // gating this on `depth + 1 < max_chain_depth` would wrongly let a shallow
    // pass return a definitive (and cacheable) False before the fallback ever
    // runs. `visited` is removed by the inner backward chainer for the variant's
    // own derivation, but `fact` itself stays guarded until the loop ends.
    if result.is_false()
        && !inner.equivalence_parent.is_empty()
        && fact.relation() != "du"
        && !visited.contains(fact)
    {
        let gf = fact.inner();
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
        if equiv_args.iter().any(|cls| cls.len() > 1) {
            // Guard against re-deriving `fact` itself while exploring its
            // equivalence variants. Inserted here (not by the inner backward
            // chainer, which removes its own entry on return).
            let reinserted = visited.insert(fact.clone());
            for combo in CartesianProduct::new(&equiv_args) {
                let variant_gf = GroundFact::new(gf.relation.clone(), combo);
                let variant = StoredFact::with_tense_from(variant_gf, fact);
                if variant != *fact && !visited.contains(&variant) {
                    let variant_result =
                        check_predicate_in_kb_typed(&variant, inner, depth, visited);
                    if variant_result.is_true() {
                        result = QueryResult::True;
                        break;
                    }
                }
            }
            // Only remove `fact` if WE inserted it (don't clobber an entry an
            // outer frame is relying on for its own cycle guard).
            if reinserted {
                visited.remove(fact);
            }
        }
    }

    if is_traced {
        let indent = "  ".repeat(depth);
        eprintln!(
            "[Trace] {}depth={} result: {} → {}",
            indent,
            depth,
            fact.to_display_string(),
            result.status_label()
        );
    }

    // Only cache definitive (True/False) results. Non-definitive results
    // (Unknown(CycleCut), ResourceExceeded(Depth)) are context-dependent — they
    // depend on the current `visited` stack and `max_chain_depth` — so caching
    // them keyed by fact alone would poison sibling branches and later, deeper
    // iterative-deepening passes. True/False are context-independent for a fixed KB.
    PRED_CACHE_ENABLED.with(|e| {
        if e.get() && result.is_definitive() {
            TYPED_PRED_CACHE.with(|c| c.borrow_mut().insert(fact.clone(), result.clone()));
        }
    });
    result
}

/// Check if a StoredFact contains a specific pattern variable.
fn stored_fact_contains_var(fact: &StoredFact, var: &str) -> bool {
    fn term_contains_var(term: &GroundTerm, var: &str) -> bool {
        match term {
            GroundTerm::PatternVar(name) => name == var,
            GroundTerm::SkolemFn(_, dep) => term_contains_var(dep, var),
            GroundTerm::DepPair(a, b) => term_contains_var(a, var) || term_contains_var(b, var),
            _ => false,
        }
    }
    fact.inner().args.iter().any(|a| term_contains_var(a, var))
}

/// Sound one-step provability lookahead used at the depth horizon: a goal can
/// only be proved by (a) direct assertion (the caller checks that before
/// backward chaining) or (b) firing a rule whose conclusion template unifies
/// with it — for a tensed goal, temporal lifting strips the tense first, so
/// the tense-stripped goal is also tried against the (always-Bare) templates.
/// If no conclusion unifies, no amount of extra depth can ever prove the goal.
fn any_rule_conclusion_unifies(fact: &StoredFact, inner: &KnowledgeBaseInner) -> bool {
    let try_goal = |goal: &StoredFact| {
        inner
            .universal_rules
            .get(goal.relation())
            .is_some_and(|rules| {
                rules.iter().any(|r| {
                    r.typed_conclusions
                        .iter()
                        .any(|c| unify_facts(c, goal).is_some())
                })
            })
    };
    try_goal(fact) || strip_tense_from_fact(fact).as_ref().is_some_and(try_goal)
}

/// Typed backward-chaining — structural matching instead of fact_repr tokenization.
pub(super) fn try_backward_chain_typed(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
) -> QueryResult {
    // Cancellation fast-path: unwind the recursion immediately (see
    // check_predicate_in_kb_typed). The Result-returning formula entry surfaces
    // the raised flag as the final `Err`.
    if check_cancelled(inner).is_err() {
        return QueryResult::False;
    }
    if depth >= inner.max_chain_depth {
        // A goal that is not asserted (the caller already checked) and that no
        // rule conclusion can unify with is unprovable at ANY depth: return the
        // exact definitive False instead of ResourceExceeded, so the depth
        // horizon does not pessimistically keep dead candidates alive in the
        // unbound-event-variable search (the members^k cartesian blowup) — and
        // so the result becomes cacheable. Gated off for the special-cased `du`
        // relation, when du-equivalence classes exist (the equivalence fallback
        // could rewrite the goal into a provable variant), and when legacy
        // `__fallback__` rules exist (their conclusions are not relation-indexed).
        if fact.relation() != "du"
            && inner.equivalence_parent.is_empty()
            && !inner.universal_rules.contains_key("__fallback__")
            && !any_rule_conclusion_unifies(fact, inner)
        {
            return QueryResult::False;
        }
        return QueryResult::ResourceExceeded(ResourceKind::Depth);
    }
    if !visited.insert(fact.clone()) {
        return QueryResult::Unknown(UnknownReason::CycleCut);
    }

    // Candidate terms for unbound event variable search, built lazily: only a
    // matched rule with unbound `ev__` pattern variables needs them, and most
    // frames never reach that point. Shared across all rules in this frame.
    let mut candidates_slot: Option<Vec<GroundTerm>> = None;

    let rules_snapshot = collect_matching_rules_typed(fact, &inner.universal_rules);
    let is_traced = inner.traced_predicates.contains(fact.relation());
    if is_traced && !rules_snapshot.is_empty() {
        let indent = "  ".repeat(depth);
        eprintln!(
            "[Trace] {}depth={} backward-chain: {} ({} rule(s) to try)",
            indent,
            depth,
            fact.to_display_string(),
            rules_snapshot.len()
        );
    }
    let mut best_result = None;

    for rule in &rules_snapshot {
        for typed_concl in &rule.typed_conclusions {
            let Some(mut bindings) = unify_facts(typed_concl, fact) else {
                continue;
            };

            // Handle unbound event variables (same logic as fact_repr version).
            let unbound_event_vars: Vec<String> = rule
                .pattern_var_names
                .iter()
                .filter(|pv| pv.starts_with("ev__") && !bindings.contains_key(pv.as_str()))
                .cloned()
                .collect();

            if !unbound_event_vars.is_empty() {
                let mut per_var_candidates: Vec<Vec<GroundTerm>> = Vec::new();
                for ev_var in &unbound_event_vars {
                    let single_var_cond_indices: Vec<usize> = rule
                        .typed_conditions
                        .iter()
                        .enumerate()
                        .filter(|(_, ct)| {
                            stored_fact_contains_var(ct, ev_var)
                                && unbound_event_vars.iter().all(|other| {
                                    other == ev_var || !stored_fact_contains_var(ct, other)
                                })
                        })
                        .map(|(i, _)| i)
                        .collect();

                    if single_var_cond_indices.is_empty() {
                        per_var_candidates
                            .push(ensure_candidates(&mut candidates_slot, inner).to_vec());
                    } else {
                        // Index-decidable conditions are evaluated FIRST and
                        // definitively (their verdict cannot change at greater
                        // depth), pruning candidates without recursion. Only
                        // rule-backed conditions fall through to the recursive
                        // check, whose ResourceExceeded near the depth horizon
                        // must conservatively keep the candidate.
                        let (decidable_indices, recursive_indices): (Vec<usize>, Vec<usize>) =
                            single_var_cond_indices.iter().copied().partition(|&idx| {
                                condition_is_index_decidable(
                                    rule.typed_conditions[idx].relation(),
                                    inner,
                                )
                            });
                        let filtered: Vec<GroundTerm> =
                            ensure_candidates(&mut candidates_slot, inner)
                                .iter()
                                .filter(|candidate| {
                                    let mut test_bindings = bindings.clone();
                                    test_bindings.insert(ev_var.clone(), (*candidate).clone());
                                    decidable_indices.iter().all(|&idx| {
                                        let cs = substitute_fact(
                                            &rule.typed_conditions[idx],
                                            &test_bindings,
                                        );
                                        let asserted = typed_fact_is_asserted(&cs, inner);
                                        if rule.negated_condition_indices.contains(&idx) {
                                            !asserted
                                        } else {
                                            asserted
                                        }
                                    }) && recursive_indices.iter().all(|&idx| {
                                        let cs = substitute_fact(
                                            &rule.typed_conditions[idx],
                                            &test_bindings,
                                        );
                                        let result = check_predicate_in_kb_typed(
                                            &cs,
                                            inner,
                                            depth + 1,
                                            visited,
                                        );
                                        let verdict =
                                            if rule.negated_condition_indices.contains(&idx) {
                                                negate_result(result)
                                            } else {
                                                result
                                            };
                                        !verdict.is_false()
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
                let mut combo_pending = None;
                for combo in TypedMultiCartesian::new(&per_var_candidates, inner.cancel.clone()) {
                    for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                        bindings.insert(ev_var.clone(), combo[i].clone());
                    }
                    let mut all_hold = true;
                    let mut pending_here = None;
                    for (idx, ct) in rule.typed_conditions.iter().enumerate() {
                        let cs = substitute_fact(ct, &bindings);
                        let result = check_predicate_in_kb_typed(&cs, inner, depth + 1, visited);
                        let verdict = if rule.negated_condition_indices.contains(&idx) {
                            negate_result(result)
                        } else {
                            result
                        };
                        if verdict.is_false() {
                            all_hold = false;
                            pending_here = None;
                            break;
                        }
                        if !verdict.is_true() {
                            all_hold = false;
                            pending_here = prefer_non_definitive(pending_here, verdict);
                        }
                    }
                    if all_hold {
                        found = true;
                        break;
                    }
                    combo_pending = pending_here.or(combo_pending);
                    for ev_var in &unbound_event_vars {
                        bindings.remove(ev_var.as_str());
                    }
                }
                if !found {
                    // Merge any pending non-definitive result WITHOUT wiping an
                    // already-pending one: if combo_pending is None (every combo
                    // failed definitively), keep best_result intact. Using
                    // `and_then` here would erase a pending ResourceExceeded into
                    // None and cache a wrong definitive False.
                    if let Some(r) = combo_pending {
                        best_result = prefer_non_definitive(best_result, r);
                    }
                    continue;
                }
            }

            let mut all_conditions_hold = true;
            let mut rule_pending = None;
            for (idx, ct) in rule.typed_conditions.iter().enumerate() {
                let cs = substitute_fact(ct, &bindings);
                let result = check_predicate_in_kb_typed(&cs, inner, depth + 1, visited);
                // Negated antecedent conditions hold via negation-as-failure: invert
                // the verdict so ¬P holds iff P is unprovable (False), not iff P is True.
                let verdict = if rule.negated_condition_indices.contains(&idx) {
                    negate_result(result)
                } else {
                    result
                };
                if verdict.is_false() {
                    all_conditions_hold = false;
                    rule_pending = None;
                    break;
                }
                if !verdict.is_true() {
                    all_conditions_hold = false;
                    rule_pending = prefer_non_definitive(rule_pending, verdict);
                }
            }

            if all_conditions_hold {
                visited.remove(fact);
                return QueryResult::True;
            }
            // Never wipe an already-pending non-definitive result: when
            // rule_pending is None (this rule failed definitively), leave
            // best_result intact rather than erasing it via `and_then`.
            if let Some(r) = rule_pending {
                best_result = prefer_non_definitive(best_result, r);
            }
        }
    }

    // Temporal lifting: if querying a tensed fact, try bare (timeless) rules.
    if let Some(bare_fact) = strip_tense_from_fact(fact) {
        let bare_rules = collect_matching_rules_typed(&bare_fact, &inner.universal_rules);
        for rule in &bare_rules {
            for typed_concl in &rule.typed_conclusions {
                let Some(mut bindings) = unify_facts(typed_concl, &bare_fact) else {
                    continue;
                };

                let unbound_event_vars: Vec<String> = rule
                    .pattern_var_names
                    .iter()
                    .filter(|pv| pv.starts_with("ev__") && !bindings.contains_key(pv.as_str()))
                    .cloned()
                    .collect();

                if !unbound_event_vars.is_empty() {
                    let mut per_var_candidates: Vec<Vec<GroundTerm>> = Vec::new();
                    for ev_var in &unbound_event_vars {
                        let single_var_cond_indices: Vec<usize> = rule
                            .typed_conditions
                            .iter()
                            .enumerate()
                            .filter(|(_, ct)| {
                                stored_fact_contains_var(ct, ev_var)
                                    && unbound_event_vars.iter().all(|other| {
                                        other == ev_var || !stored_fact_contains_var(ct, other)
                                    })
                            })
                            .map(|(i, _)| i)
                            .collect();

                        if single_var_cond_indices.is_empty() {
                            per_var_candidates
                                .push(ensure_candidates(&mut candidates_slot, inner).to_vec());
                        } else {
                            // Same decidable-first split as the untensed block
                            // above; the asserted check runs on the TENSED fact
                            // (temporal lifting consults the same relation-keyed
                            // rule bucket, so decidability is tense-independent).
                            let (decidable_indices, recursive_indices): (Vec<usize>, Vec<usize>) =
                                single_var_cond_indices.iter().copied().partition(|&idx| {
                                    condition_is_index_decidable(
                                        rule.typed_conditions[idx].relation(),
                                        inner,
                                    )
                                });
                            let filtered: Vec<GroundTerm> =
                                ensure_candidates(&mut candidates_slot, inner)
                                    .iter()
                                    .filter(|candidate| {
                                        let mut test_bindings = bindings.clone();
                                        test_bindings.insert(ev_var.clone(), (*candidate).clone());
                                        decidable_indices.iter().all(|&idx| {
                                            let bare_cs = substitute_fact(
                                                &rule.typed_conditions[idx],
                                                &test_bindings,
                                            );
                                            let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                                            let asserted =
                                                typed_fact_is_asserted(&tensed_cs, inner);
                                            if rule.negated_condition_indices.contains(&idx) {
                                                !asserted
                                            } else {
                                                asserted
                                            }
                                        }) && recursive_indices.iter().all(|&idx| {
                                            let bare_cs = substitute_fact(
                                                &rule.typed_conditions[idx],
                                                &test_bindings,
                                            );
                                            let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                                            let result = check_predicate_in_kb_typed(
                                                &tensed_cs,
                                                inner,
                                                depth + 1,
                                                visited,
                                            );
                                            let verdict =
                                                if rule.negated_condition_indices.contains(&idx) {
                                                    negate_result(result)
                                                } else {
                                                    result
                                                };
                                            !verdict.is_false()
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
                    let mut combo_pending = None;
                    for combo in TypedMultiCartesian::new(&per_var_candidates, inner.cancel.clone())
                    {
                        for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                            bindings.insert(ev_var.clone(), combo[i].clone());
                        }
                        let mut all_hold = true;
                        let mut pending_here = None;
                        for (idx, ct) in rule.typed_conditions.iter().enumerate() {
                            let bare_cs = substitute_fact(ct, &bindings);
                            let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                            let result =
                                check_predicate_in_kb_typed(&tensed_cs, inner, depth + 1, visited);
                            let verdict = if rule.negated_condition_indices.contains(&idx) {
                                negate_result(result)
                            } else {
                                result
                            };
                            if verdict.is_false() {
                                all_hold = false;
                                pending_here = None;
                                break;
                            }
                            if !verdict.is_true() {
                                all_hold = false;
                                pending_here = prefer_non_definitive(pending_here, verdict);
                            }
                        }
                        if all_hold {
                            found = true;
                            break;
                        }
                        combo_pending = pending_here.or(combo_pending);
                        for ev_var in &unbound_event_vars {
                            bindings.remove(ev_var.as_str());
                        }
                    }
                    if !found {
                        // Preserve any already-pending non-definitive result; do
                        // not erase best_result when combo_pending is None.
                        if let Some(r) = combo_pending {
                            best_result = prefer_non_definitive(best_result, r);
                        }
                        continue;
                    }
                }

                let mut all_conditions_hold = true;
                let mut rule_pending = None;
                for (idx, ct) in rule.typed_conditions.iter().enumerate() {
                    let bare_cs = substitute_fact(ct, &bindings);
                    let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                    let result = check_predicate_in_kb_typed(&tensed_cs, inner, depth + 1, visited);
                    let verdict = if rule.negated_condition_indices.contains(&idx) {
                        negate_result(result)
                    } else {
                        result
                    };
                    if verdict.is_false() {
                        all_conditions_hold = false;
                        rule_pending = None;
                        break;
                    }
                    if !verdict.is_true() {
                        all_conditions_hold = false;
                        rule_pending = prefer_non_definitive(rule_pending, verdict);
                    }
                }

                if all_conditions_hold {
                    visited.remove(fact);
                    return QueryResult::True;
                }
                // Preserve any already-pending non-definitive result; do not
                // erase best_result when rule_pending is None.
                if let Some(r) = rule_pending {
                    best_result = prefer_non_definitive(best_result, r);
                }
            }
        }
    }

    visited.remove(fact);
    best_result.unwrap_or(QueryResult::False)
}

/// Strip tense wrapper from a StoredFact, returning the bare fact.
fn strip_tense_from_fact(fact: &StoredFact) -> Option<StoredFact> {
    match fact {
        StoredFact::Past(f) | StoredFact::Present(f) | StoredFact::Future(f) => {
            Some(StoredFact::Bare(f.clone()))
        }
        _ => None,
    }
}

/// Apply the tense of `source` to a bare fact.
fn apply_tense_to_fact(fact: &StoredFact, source: &StoredFact) -> StoredFact {
    match source {
        StoredFact::Past(_) => match fact {
            StoredFact::Bare(f) => StoredFact::Past(f.clone()),
            other => other.clone(),
        },
        StoredFact::Present(_) => match fact {
            StoredFact::Bare(f) => StoredFact::Present(f.clone()),
            other => other.clone(),
        },
        StoredFact::Future(_) => match fact {
            StoredFact::Bare(f) => StoredFact::Future(f.clone()),
            other => other.clone(),
        },
        _ => fact.clone(),
    }
}

/// Cartesian product over typed GroundTerm vectors.
struct TypedMultiCartesian<'a> {
    sets: &'a [Vec<GroundTerm>],
    indices: Vec<usize>,
    done: bool,
    /// Cooperative cancellation flag: when raised, the product stops yielding so
    /// a candidates^k backward-chaining blowup terminates promptly. `None` for
    /// every non-server caller, so iteration is unchanged there.
    cancel: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
}

impl<'a> TypedMultiCartesian<'a> {
    fn new(
        sets: &'a [Vec<GroundTerm>],
        cancel: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
    ) -> Self {
        let done = sets.iter().any(|s| s.is_empty());
        Self {
            sets,
            indices: vec![0; sets.len()],
            done,
            cancel,
        }
    }
}

impl<'a> Iterator for TypedMultiCartesian<'a> {
    type Item = Vec<GroundTerm>;

    fn next(&mut self) -> Option<Self::Item> {
        if self
            .cancel
            .as_ref()
            .is_some_and(|c| c.load(std::sync::atomic::Ordering::Relaxed))
        {
            return None;
        }
        if self.done || self.sets.is_empty() {
            if self.sets.is_empty() && !self.done {
                self.done = true;
                return Some(vec![]);
            }
            return None;
        }
        let combo: Vec<GroundTerm> = self
            .indices
            .iter()
            .enumerate()
            .map(|(set_idx, &item_idx)| self.sets[set_idx][item_idx].clone())
            .collect();
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

// ─── Typed Traced Backward-Chaining ──────────────────────────────
//
// Typed equivalents of trace_predicate_provenance() and try_backward_chain_traced()
// that use StoredFact and unify_facts() using structural unification.

/// Typed trace_predicate_provenance: check if fact holds and build proof step.
pub(super) fn trace_predicate_provenance_typed(
    fact: &StoredFact,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    depth: usize,
    memo: &mut HashMap<String, u32>,
) -> u32 {
    let display = fact.to_display_string();

    if let Some(&cached_idx) = memo.get(&display) {
        // Memo hit — emit a lightweight ProofRef leaf instead of
        // re-deriving the full proof sub-tree. The original derivation
        // lives at steps[cached_idx]. We store cached_idx in children
        // so consumers can follow the back-reference if needed.
        let idx = steps.len() as u32;
        steps.push(ProofStep {
            rule: ProofRule::ProofRef(display),
            holds: steps[cached_idx as usize].holds,
            children: vec![cached_idx],
        });
        return idx;
    }

    if typed_fact_is_asserted(fact, inner) {
        let idx = steps.len() as u32;
        steps.push(ProofStep {
            rule: ProofRule::Asserted(display.clone()),
            holds: true,
            children: vec![],
        });
        memo.insert(display, idx);
        return idx;
    }

    if depth < inner.max_chain_depth {
        if let Some(idx) = try_backward_chain_traced_typed(fact, inner, steps, depth, memo) {
            memo.insert(display, idx);
            return idx;
        }
    }

    // Equality substitution: the fact may hold only after replacing arguments with
    // du-equivalent terms (mirrors the untraced fallback in check_predicate_in_kb_typed).
    // Find a satisfying equivalent variant and record an EqualitySubstitution step whose
    // child is the variant's real derivation — never a holds:true leaf with no support.
    // The variant probe below recurses only into `check_predicate_in_kb_typed`,
    // whose own equivalence fallback now carries a `visited` cycle guard, so the
    // probe terminates (returns a definitive verdict) for every variant. A du-
    // cycle therefore yields `satisfying = None` rather than overflowing the
    // stack, and the recursive `trace_predicate_provenance_typed` below only fires
    // for a genuinely-provable variant (which bottoms out at an asserted fact /
    // rule), so it terminates as well. No extra depth gate is needed here, and
    // adding one would wrongly suppress the fallback on shallow iterative-
    // deepening passes.
    if !inner.equivalence_parent.is_empty() && fact.relation() != "du" {
        let gf = fact.inner();
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
        if equiv_args.iter().any(|cls| cls.len() > 1) {
            let mut satisfying: Option<StoredFact> = None;
            for combo in CartesianProduct::new(&equiv_args) {
                let variant_gf = GroundFact::new(gf.relation.clone(), combo);
                let variant = StoredFact::with_tense_from(variant_gf, fact);
                if variant != *fact
                    && check_predicate_in_kb_typed(&variant, &*inner, depth, &mut HashSet::new())
                        .is_true()
                {
                    satisfying = Some(variant);
                    break;
                }
            }
            if let Some(variant) = satisfying {
                let du_note = gf
                    .args
                    .iter()
                    .zip(variant.inner().args.iter())
                    .filter(|(o, v)| o != v)
                    .map(|(o, v)| format!("{} du {}", o.to_display_string(), v.to_display_string()))
                    .collect::<Vec<_>>()
                    .join(", ");
                let substituted = variant.to_display_string();
                let child = trace_predicate_provenance_typed(&variant, inner, steps, depth, memo);
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::EqualitySubstitution((display.clone(), du_note, substituted)),
                    holds: true,
                    children: vec![child],
                });
                memo.insert(display, idx);
                return idx;
            }
        }
    }

    // Final fallback: the traced path could not derive the fact. Report it honestly as
    // not-found (holds:false) rather than claiming truth with no supporting derivation.
    let idx = steps.len() as u32;
    steps.push(ProofStep {
        rule: ProofRule::PredicateNotFound(display.clone()),
        holds: false,
        children: vec![],
    });
    memo.insert(display, idx);
    idx
}

/// Typed try_backward_chain_traced: structural matching with proof step recording.
pub(super) fn try_backward_chain_traced_typed(
    fact: &StoredFact,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    depth: usize,
    memo: &mut HashMap<String, u32>,
) -> Option<u32> {
    // Cancellation fast-path: bail out of the traced backward chain immediately
    // once the watchdog raises the flag. check_formula_holds_traced surfaces the
    // raised flag as the final `Err`.
    if check_cancelled(inner).is_err() {
        return None;
    }
    // Candidate terms for unbound event variable search, built lazily (only a
    // matched rule with unbound `ev__` pattern variables needs them).
    let mut candidates_slot: Option<Vec<GroundTerm>> = None;

    let rules_snapshot = collect_matching_rules_typed(fact, &inner.universal_rules);
    let display = fact.to_display_string();

    for rule in &rules_snapshot {
        for typed_concl in &rule.typed_conclusions {
            let Some(mut bindings) = unify_facts(typed_concl, fact) else {
                continue;
            };

            let unbound_event_vars: Vec<String> = rule
                .pattern_var_names
                .iter()
                .filter(|pv| pv.starts_with("ev__") && !bindings.contains_key(pv.as_str()))
                .cloned()
                .collect();

            if !unbound_event_vars.is_empty() {
                let mut per_var_candidates: Vec<Vec<GroundTerm>> = Vec::new();
                for ev_var in &unbound_event_vars {
                    let single_var_cond_indices: Vec<usize> = rule
                        .typed_conditions
                        .iter()
                        .enumerate()
                        .filter(|(_, ct)| {
                            stored_fact_contains_var(ct, ev_var)
                                && unbound_event_vars.iter().all(|other| {
                                    other == ev_var || !stored_fact_contains_var(ct, other)
                                })
                        })
                        .map(|(i, _)| i)
                        .collect();

                    if single_var_cond_indices.is_empty() {
                        per_var_candidates
                            .push(ensure_candidates(&mut candidates_slot, inner).to_vec());
                    } else {
                        let filtered: Vec<GroundTerm> =
                            ensure_candidates(&mut candidates_slot, inner)
                                .iter()
                                .filter(|candidate| {
                                    let mut test_bindings = bindings.clone();
                                    test_bindings.insert(ev_var.clone(), (*candidate).clone());
                                    single_var_cond_indices.iter().all(|&idx| {
                                        let cs = substitute_fact(
                                            &rule.typed_conditions[idx],
                                            &test_bindings,
                                        );
                                        check_predicate_in_kb_typed(
                                            &cs,
                                            &*inner,
                                            depth + 1,
                                            &mut HashSet::new(),
                                        )
                                        .is_true()
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
                for combo in TypedMultiCartesian::new(&per_var_candidates, inner.cancel.clone()) {
                    for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                        bindings.insert(ev_var.clone(), combo[i].clone());
                    }
                    let all_hold = rule.typed_conditions.iter().enumerate().all(|(idx, ct)| {
                        let cs = substitute_fact(ct, &bindings);
                        let result = check_predicate_in_kb_typed(
                            &cs,
                            &*inner,
                            depth + 1,
                            &mut HashSet::new(),
                        );
                        if rule.negated_condition_indices.contains(&idx) {
                            result.is_false()
                        } else {
                            result.is_true()
                        }
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

            // Check all conditions hold, building provenance children inline. A negated
            // condition holds via negation-as-failure (¬P holds iff P is unprovable);
            // record it as a leaf Negation step rather than tracing the positive atom
            // (which does not hold). An empty condition list yields a childless Derived
            // step (ground material conditional).
            let mut all_conditions_hold = true;
            let mut child_indices = Vec::new();

            for (idx, cond_template) in rule.typed_conditions.iter().enumerate() {
                let cond_fact = substitute_fact(cond_template, &bindings);
                let negated = rule.negated_condition_indices.contains(&idx);
                let result = check_predicate_in_kb_typed(
                    &cond_fact,
                    &*inner,
                    depth + 1,
                    &mut HashSet::new(),
                );
                let holds = if negated {
                    result.is_false()
                } else {
                    result.is_true()
                };
                if !holds {
                    all_conditions_hold = false;
                    break;
                }
                if negated {
                    let leaf = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::Negation,
                        holds: true,
                        children: vec![],
                    });
                    child_indices.push(leaf);
                } else {
                    let child_idx =
                        trace_predicate_provenance_typed(&cond_fact, inner, steps, depth + 1, memo);
                    child_indices.push(child_idx);
                }
            }

            if !all_conditions_hold {
                continue;
            }

            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::Derived((rule.label.clone(), display.clone())),
                holds: true,
                children: child_indices,
            });
            return Some(idx);
        }
    }

    // Temporal lifting: if querying a tensed fact, try bare (timeless) rules.
    if let Some(bare_fact) = strip_tense_from_fact(fact) {
        let tense_label = match fact {
            StoredFact::Past(_) => "past",
            StoredFact::Present(_) => "present",
            StoredFact::Future(_) => "future",
            _ => "?",
        };
        let bare_rules = collect_matching_rules_typed(&bare_fact, &inner.universal_rules);
        for rule in &bare_rules {
            for typed_concl in &rule.typed_conclusions {
                let Some(mut bindings) = unify_facts(typed_concl, &bare_fact) else {
                    continue;
                };

                let unbound_event_vars: Vec<String> = rule
                    .pattern_var_names
                    .iter()
                    .filter(|pv| pv.starts_with("ev__") && !bindings.contains_key(pv.as_str()))
                    .cloned()
                    .collect();

                if !unbound_event_vars.is_empty() {
                    let mut per_var_candidates: Vec<Vec<GroundTerm>> = Vec::new();
                    for ev_var in &unbound_event_vars {
                        let single_var_cond_indices: Vec<usize> = rule
                            .typed_conditions
                            .iter()
                            .enumerate()
                            .filter(|(_, ct)| {
                                stored_fact_contains_var(ct, ev_var)
                                    && unbound_event_vars.iter().all(|other| {
                                        other == ev_var || !stored_fact_contains_var(ct, other)
                                    })
                            })
                            .map(|(i, _)| i)
                            .collect();

                        if single_var_cond_indices.is_empty() {
                            per_var_candidates
                                .push(ensure_candidates(&mut candidates_slot, inner).to_vec());
                        } else {
                            let filtered: Vec<GroundTerm> =
                                ensure_candidates(&mut candidates_slot, inner)
                                    .iter()
                                    .filter(|candidate| {
                                        let mut test_bindings = bindings.clone();
                                        test_bindings.insert(ev_var.clone(), (*candidate).clone());
                                        single_var_cond_indices.iter().all(|&idx| {
                                            let bare_cs = substitute_fact(
                                                &rule.typed_conditions[idx],
                                                &test_bindings,
                                            );
                                            let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                                            check_predicate_in_kb_typed(
                                                &tensed_cs,
                                                &*inner,
                                                depth + 1,
                                                &mut HashSet::new(),
                                            )
                                            .is_true()
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
                    for combo in TypedMultiCartesian::new(&per_var_candidates, inner.cancel.clone())
                    {
                        for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                            bindings.insert(ev_var.clone(), combo[i].clone());
                        }
                        let all_hold = rule.typed_conditions.iter().enumerate().all(|(idx, ct)| {
                            let bare_cs = substitute_fact(ct, &bindings);
                            let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                            let result = check_predicate_in_kb_typed(
                                &tensed_cs,
                                &*inner,
                                depth + 1,
                                &mut HashSet::new(),
                            );
                            if rule.negated_condition_indices.contains(&idx) {
                                result.is_false()
                            } else {
                                result.is_true()
                            }
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

                let mut all_conditions_hold = true;
                let mut child_indices = Vec::new();
                for (idx, cond_template) in rule.typed_conditions.iter().enumerate() {
                    let bare_cs = substitute_fact(cond_template, &bindings);
                    let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                    let negated = rule.negated_condition_indices.contains(&idx);
                    let result = check_predicate_in_kb_typed(
                        &tensed_cs,
                        &*inner,
                        depth + 1,
                        &mut HashSet::new(),
                    );
                    let holds = if negated {
                        result.is_false()
                    } else {
                        result.is_true()
                    };
                    if !holds {
                        all_conditions_hold = false;
                        break;
                    }
                    if negated {
                        let leaf = steps.len() as u32;
                        steps.push(ProofStep {
                            rule: ProofRule::Negation,
                            holds: true,
                            children: vec![],
                        });
                        child_indices.push(leaf);
                    } else {
                        let child_idx = trace_predicate_provenance_typed(
                            &tensed_cs,
                            inner,
                            steps,
                            depth + 1,
                            memo,
                        );
                        child_indices.push(child_idx);
                    }
                }

                if !all_conditions_hold {
                    continue;
                }

                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::Derived((
                        format!("{} [{}]", rule.label, tense_label),
                        display.clone(),
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

// ─── End Typed Backward-Chaining ─────────────────────────────────

pub(super) fn check_formula_holds_traced(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    tense: Option<&str>,
    memo: &mut HashMap<String, u32>,
) -> Result<(bool, u32), String> {
    check_cancelled(inner)?;
    match get_node(buffer, node_id)? {
        LogicNode::AndNode((l, r)) => {
            let (l_result, l_idx) =
                check_formula_holds_traced(buffer, *l, subs, inner, steps, tense, memo)?;
            if !l_result {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::Conjunction,
                    holds: false,
                    children: vec![l_idx],
                });
                return Ok((false, idx));
            }
            let (r_result, r_idx) =
                check_formula_holds_traced(buffer, *r, subs, inner, steps, tense, memo)?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::Conjunction,
                holds: r_result,
                children: vec![l_idx, r_idx],
            });
            Ok((r_result, idx))
        }
        LogicNode::OrNode((l, r)) => {
            let (l_result, l_idx) =
                check_formula_holds_traced(buffer, *l, subs, inner, steps, tense, memo)?;
            if l_result {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::DisjunctionIntro("left".to_string()),
                    holds: true,
                    children: vec![l_idx],
                });
                return Ok((true, idx));
            }
            let (r_result, r_idx) =
                check_formula_holds_traced(buffer, *r, subs, inner, steps, tense, memo)?;
            if r_result {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::DisjunctionIntro("right".to_string()),
                    holds: true,
                    children: vec![r_idx],
                });
                return Ok((true, idx));
            }
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
        LogicNode::PastNode(inner_node) => {
            let (result, child_idx) = check_formula_holds_traced(
                buffer,
                *inner_node,
                subs,
                inner,
                steps,
                Some("Past"),
                memo,
            )?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("past".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::PresentNode(inner_node) => {
            let (result, child_idx) = check_formula_holds_traced(
                buffer,
                *inner_node,
                subs,
                inner,
                steps,
                Some("Present"),
                memo,
            )?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("present".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::FutureNode(inner_node) => {
            let (result, child_idx) = check_formula_holds_traced(
                buffer,
                *inner_node,
                subs,
                inner,
                steps,
                Some("Future"),
                memo,
            )?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("future".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
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
            // Batch compute fast path (slice, no .to_vec()).
            if let Ok(body_node) = get_node(buffer, *body) {
                if let LogicNode::ComputeNode((rel, args)) = body_node {
                    let members = inner.all_typed_domain_members();
                    if let Some(batch) =
                        batch_evaluate_compute_for_members(rel, args, v, members, subs)
                    {
                        // Clone the winning member before releasing the slice borrow.
                        let winner = batch
                            .results
                            .iter()
                            .position(|r| *r)
                            .map(|i| members[i].clone());
                        // Ingest deferred facts.
                        for fact in batch.deferred_facts {
                            assert_typed_fact(fact, inner);
                        }
                        if let Some(winning_member) = winner {
                            let mut new_subs = subs.clone();
                            new_subs.insert(v.clone(), winning_member.clone());
                            let (_, body_idx) = check_formula_holds_traced(
                                buffer,
                                *body,
                                &mut new_subs,
                                inner,
                                steps,
                                tense,
                                memo,
                            )?;
                            let idx = steps.len() as u32;
                            steps.push(ProofStep {
                                rule: ProofRule::ExistsWitness((
                                    v.clone(),
                                    witness_term_to_logical_term(&winning_member),
                                )),
                                holds: true,
                                children: vec![body_idx],
                            });
                            return Ok((true, idx));
                        }
                    }
                }
            }

            // Decomposed numeric group — must mirror the untraced arm exactly
            // (run_entailment_check_with_proof runs both on the same roots, so
            // a one-sided hook would make verdict and trace disagree).
            if let Some(verdict) = try_evaluate_numeric_group(buffer, v, *body, subs) {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::ComputeCheck((verdict.method.to_string(), verdict.relation)),
                    holds: verdict.holds,
                    children: vec![],
                });
                return Ok((verdict.holds, idx));
            }
            // Candidate narrowing (∃-heavy query blowup fix) — same enumeration
            // as the untraced Exists arm; see collect_entailment_candidates.
            let candidates: Vec<GroundTerm> =
                match collect_entailment_candidates(buffer, *body, v, subs, inner, tense) {
                    Some(narrowed) => narrowed,
                    None => {
                        let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
                        let mut all = members.clone();
                        for entry in &inner.skolem_fn_registry {
                            for combo in GroundTermCartesianProduct::new(&members, entry.dep_count)
                            {
                                all.push(build_skolem_fn_term(&entry.base_name, &combo));
                            }
                        }
                        all
                    }
                };
            for candidate in &candidates {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), candidate.clone());
                if check_formula_holds(buffer, *body, &mut new_subs, inner, tense)?.is_true() {
                    let (_, body_idx) = check_formula_holds_traced(
                        buffer,
                        *body,
                        &mut new_subs,
                        inner,
                        steps,
                        tense,
                        memo,
                    )?;
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::ExistsWitness((
                            v.clone(),
                            witness_term_to_logical_term(candidate),
                        )),
                        holds: true,
                        children: vec![body_idx],
                    });
                    return Ok((true, idx));
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
            let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
            if members.is_empty() {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::ForallVacuous,
                    holds: true,
                    children: vec![],
                });
                return Ok((true, idx));
            }
            // Batch compute fast path.
            if let Ok(body_node) = get_node(buffer, *body) {
                if let LogicNode::ComputeNode((rel, args)) = body_node {
                    let members_slice = inner.all_typed_domain_members();
                    if let Some(batch) =
                        batch_evaluate_compute_for_members(rel, args, v, members_slice, subs)
                    {
                        // Clone the counterexample before releasing slice.
                        let fail_member = batch
                            .results
                            .iter()
                            .position(|r| !*r)
                            .map(|i| members_slice[i].clone());
                        for fact in batch.deferred_facts {
                            assert_typed_fact(fact, inner);
                        }
                        if let Some(counter) = fail_member {
                            let mut new_subs = subs.clone();
                            new_subs.insert(v.clone(), counter.clone());
                            let (_, body_idx) = check_formula_holds_traced(
                                buffer,
                                *body,
                                &mut new_subs,
                                inner,
                                steps,
                                tense,
                                memo,
                            )?;
                            let idx = steps.len() as u32;
                            steps.push(ProofStep {
                                rule: ProofRule::ForallCounterexample(ground_term_to_logical_term(
                                    &counter,
                                )),
                                holds: false,
                                children: vec![body_idx],
                            });
                            return Ok((false, idx));
                        }
                        // All passed — trace each member.
                        let members_owned: Vec<GroundTerm> =
                            inner.all_typed_domain_members().to_vec();
                        let mut child_indices = Vec::new();
                        let mut entity_terms = Vec::new();
                        for member in &members_owned {
                            let mut new_subs = subs.clone();
                            new_subs.insert(v.clone(), member.clone());
                            let (_, body_idx) = check_formula_holds_traced(
                                buffer,
                                *body,
                                &mut new_subs,
                                inner,
                                steps,
                                tense,
                                memo,
                            )?;
                            child_indices.push(body_idx);
                            entity_terms.push(ground_term_to_logical_term(member));
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
            }
            let mut child_indices = Vec::new();
            let mut entity_terms = Vec::new();
            for member in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), member.clone());
                let (holds, body_idx) = check_formula_holds_traced(
                    buffer,
                    *body,
                    &mut new_subs,
                    inner,
                    steps,
                    tense,
                    memo,
                )?;
                if !holds {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::ForallCounterexample(ground_term_to_logical_term(member)),
                        holds: false,
                        children: vec![body_idx],
                    });
                    return Ok((false, idx));
                }
                child_indices.push(body_idx);
                entity_terms.push(ground_term_to_logical_term(member));
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
            // Batch compute fast path.
            if let Ok(body_node) = get_node(buffer, *body) {
                if let LogicNode::ComputeNode((rel, args)) = body_node {
                    let members = inner.all_typed_domain_members();
                    if let Some(batch) =
                        batch_evaluate_compute_for_members(rel, args, v, members, subs)
                    {
                        for fact in batch.deferred_facts {
                            assert_typed_fact(fact, inner);
                        }
                        let satisfying = batch.results.iter().filter(|r| **r).count() as u32;
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
            }
            let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
            let mut satisfying = 0u32;
            for member in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), member.clone());
                if check_formula_holds(buffer, *body, &mut new_subs, inner, tense)?.is_true() {
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
            if let Some(result) = try_numeric_comparison(rel, args, subs) {
                let detail = format!(
                    "{}({}) = {}",
                    rel,
                    args.iter()
                        .map(|a| match a {
                            LogicalTerm::Number(n) => format!("{}", *n as i64),
                            LogicalTerm::Variable(v) => subs
                                .get(v.as_str())
                                .map(|gt| gt.to_display_string())
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
            if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                let mut visited = HashSet::new();
                let result = check_predicate_in_kb_typed(&fact, &*inner, 0, &mut visited);
                if result.is_true() {
                    let idx = trace_predicate_provenance_typed(&fact, inner, steps, 0, memo);
                    Ok((true, idx))
                } else {
                    // Record failure details: which rules were tried, which conditions failed.
                    let mut failed_children = Vec::new();

                    // Check if any rules could have matched this predicate.
                    let rules_snapshot =
                        collect_matching_rules_typed(&fact, &inner.universal_rules);
                    for rule in &rules_snapshot {
                        for concl in &rule.typed_conclusions {
                            if let Some(bindings) = unify_facts(concl, &fact) {
                                // Rule matched structurally. Check which condition failed.
                                for ct in &rule.typed_conditions {
                                    let cond_fact = substitute_fact(ct, &bindings);
                                    let cond_result = check_predicate_in_kb_typed(
                                        &cond_fact,
                                        inner,
                                        1,
                                        &mut HashSet::new(),
                                    );
                                    if !cond_result.is_true() {
                                        let child_idx = steps.len() as u32;
                                        steps.push(ProofStep {
                                            rule: ProofRule::RuleAttemptFailed((
                                                rule.label.clone(),
                                                cond_fact.to_display_string(),
                                            )),
                                            holds: false,
                                            children: vec![],
                                        });
                                        failed_children.push(child_idx);
                                        break; // First failed condition is enough.
                                    }
                                }
                            }
                        }
                    }

                    let idx = steps.len() as u32;
                    if failed_children.is_empty() {
                        // No rules matched at all — predicate simply not found.
                        steps.push(ProofStep {
                            rule: ProofRule::PredicateNotFound(fact.to_display_string()),
                            holds: false,
                            children: vec![],
                        });
                    } else {
                        // Rules were tried but conditions failed.
                        steps.push(ProofStep {
                            rule: ProofRule::PredicateNotFound(fact.to_display_string()),
                            holds: false,
                            children: failed_children,
                        });
                    }
                    Ok((false, idx))
                }
            } else {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::PredicateCheck(("build_failed".to_string(), String::new())),
                    holds: false,
                    children: vec![],
                });
                Ok((false, idx))
            }
        }
        LogicNode::ComputeNode((rel, args)) => {
            // Built-in arithmetic FIRST, then external dispatch — the
            // documented Layer-2 ordering (matches gasnu's evaluate() and the
            // batch path).
            if let Some(result) = try_arithmetic_evaluation(rel, args, subs) {
                if result {
                    if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                        assert_typed_fact(fact, inner);
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
            let resolved = resolve_args_for_dispatch(args, subs);
            if let Ok(result) = dispatch_to_backend(rel, &resolved) {
                if result {
                    if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                        assert_typed_fact(fact, inner);
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
            // Fallback: check typed store for compute predicate.
            let result =
                if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                    let mut visited = HashSet::new();
                    check_predicate_in_kb_typed(&fact, &*inner, 0, &mut visited)
                } else {
                    QueryResult::False
                };
            let holds = result.is_true();
            let method = match result {
                QueryResult::Unknown(UnknownReason::CycleCut) => "cycle_cut",
                QueryResult::Unknown(UnknownReason::IncompleteKnowledge) => "incomplete_knowledge",
                QueryResult::Unknown(UnknownReason::NafDependent) => "naf_dependent",
                QueryResult::ResourceExceeded(ResourceKind::Depth) => "depth_limit",
                QueryResult::ResourceExceeded(ResourceKind::Fuel) => "fuel_limit",
                QueryResult::ResourceExceeded(ResourceKind::Memory) => "memory_limit",
                QueryResult::False | QueryResult::True => "kb",
            };
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ComputeCheck((method.to_string(), rel.clone())),
                holds,
                children: vec![],
            });
            Ok((holds, idx))
        }
    }
}
