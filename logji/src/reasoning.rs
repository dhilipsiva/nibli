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

pub(super) fn check_formula_holds(
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
            // Slow path: need owned Vec because check_formula_holds takes &mut inner.
            let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
            let mut best_result = None;
            for member in &members {
                let result = with_sub(subs, v, member.clone(), |s| {
                    check_formula_holds(buffer, *body, s, inner, tense)
                })?;
                if result.is_true() {
                    return Ok(QueryResult::True);
                }
                best_result = prefer_non_definitive(best_result, result);
            }
            let sk_entries: Vec<(String, usize)> = inner
                .skolem_fn_registry
                .iter()
                .map(|e| (e.base_name.clone(), e.dep_count))
                .collect();
            for (base_name, dep_count) in &sk_entries {
                for combo in GroundTermCartesianProduct::new(&members, *dep_count) {
                    let witness = build_skolem_fn_term(base_name, &combo);
                    let result = with_sub(subs, v, witness, |s| {
                        check_formula_holds(buffer, *body, s, inner, tense)
                    })?;
                    if result.is_true() {
                        return Ok(QueryResult::True);
                    }
                    best_result = prefer_non_definitive(best_result, result);
                }
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
fn typed_fact_is_asserted_with_equivalence(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
) -> bool {
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
fn collect_matching_rules_typed(
    fact: &StoredFact,
    universal_rules: &HashMap<String, Vec<Arc<UniversalRuleRecord>>>,
) -> Vec<Arc<UniversalRuleRecord>> {
    let rel = fact.relation();
    universal_rules.get(rel).cloned().unwrap_or_default()
}

/// Check if a typed fact holds in the KB (direct assertion or backward-chaining).
pub(super) fn check_predicate_in_kb_typed(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
) -> QueryResult {
    // du reflexivity + transitivity: du(x,x) always holds; du(a,b) holds
    // if a and b are in the same equivalence class.
    if fact.relation() == "du" {
        let args = &fact.inner().args;
        if args.len() == 2 {
            if args[0] == args[1] {
                return QueryResult::True; // Reflexivity
            }
            if !inner.equivalence_parent.is_empty() {
                let canon_a =
                    find_canonical_readonly(&inner.equivalence_parent, &args[0]);
                let canon_b =
                    find_canonical_readonly(&inner.equivalence_parent, &args[1]);
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
    if result.is_false() && !inner.equivalence_parent.is_empty() && fact.relation() != "du" {
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
            for combo in CartesianProduct::new(&equiv_args) {
                let variant_gf = GroundFact::new(gf.relation.clone(), combo);
                let variant = StoredFact::with_tense_from(variant_gf, fact);
                if variant != *fact {
                    let variant_result =
                        check_predicate_in_kb_typed(&variant, inner, depth, visited);
                    if variant_result.is_true() {
                        result = QueryResult::True;
                        break;
                    }
                }
            }
        }
    }

    PRED_CACHE_ENABLED.with(|e| {
        if e.get() {
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

/// Typed backward-chaining — structural matching instead of fact_repr tokenization.
pub(super) fn try_backward_chain_typed(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
) -> QueryResult {
    if depth >= inner.max_chain_depth {
        return QueryResult::ResourceExceeded(ResourceKind::Depth);
    }
    if !visited.insert(fact.clone()) {
        return QueryResult::Unknown(UnknownReason::CycleCut);
    }

    // Pre-compute candidate terms for unbound event variable search.
    // Shared across all rules to avoid repeated allocation inside the per-rule loop.
    let all_candidates = build_all_candidates(inner);

    let rules_snapshot = collect_matching_rules_typed(fact, &inner.universal_rules);
    let mut best_result = None;

    for rule in &rules_snapshot {
        for typed_concl in &rule.typed_conclusions {
            let bindings_opt = unify_facts(typed_concl, fact);
            if bindings_opt.is_none() {
                continue;
            }
            let mut bindings = bindings_opt.unwrap();

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
                        per_var_candidates.push(all_candidates.clone());
                    } else {
                        let filtered: Vec<GroundTerm> = all_candidates
                            .iter()
                            .filter(|candidate| {
                                let mut test_bindings = bindings.clone();
                                test_bindings.insert(ev_var.clone(), (*candidate).clone());
                                single_var_cond_indices.iter().all(|&idx| {
                                    let cs = substitute_fact(
                                        &rule.typed_conditions[idx],
                                        &test_bindings,
                                    );
                                    !check_predicate_in_kb_typed(&cs, inner, depth + 1, visited)
                                        .is_false()
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
                for combo in TypedMultiCartesian::new(&per_var_candidates) {
                    for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                        bindings.insert(ev_var.clone(), combo[i].clone());
                    }
                    let mut all_hold = true;
                    let mut pending_here = None;
                    for ct in &rule.typed_conditions {
                        let cs = substitute_fact(ct, &bindings);
                        let result = check_predicate_in_kb_typed(&cs, inner, depth + 1, visited);
                        if result.is_false() {
                            all_hold = false;
                            pending_here = None;
                            break;
                        }
                        if !result.is_true() {
                            all_hold = false;
                            pending_here = prefer_non_definitive(pending_here, result);
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
                    best_result = combo_pending.and_then(|r| prefer_non_definitive(best_result, r));
                    continue;
                }
            }

            let mut all_conditions_hold = true;
            let mut rule_pending = None;
            for ct in &rule.typed_conditions {
                let cs = substitute_fact(ct, &bindings);
                let result = check_predicate_in_kb_typed(&cs, inner, depth + 1, visited);
                if result.is_false() {
                    all_conditions_hold = false;
                    rule_pending = None;
                    break;
                }
                if !result.is_true() {
                    all_conditions_hold = false;
                    rule_pending = prefer_non_definitive(rule_pending, result);
                }
            }

            if all_conditions_hold {
                visited.remove(fact);
                return QueryResult::True;
            }
            best_result = rule_pending.and_then(|r| prefer_non_definitive(best_result, r));
        }
    }

    // Temporal lifting: if querying a tensed fact, try bare (timeless) rules.
    if let Some(bare_fact) = strip_tense_from_fact(fact) {
        let bare_rules = collect_matching_rules_typed(&bare_fact, &inner.universal_rules);
        for rule in &bare_rules {
            for typed_concl in &rule.typed_conclusions {
                let bindings_opt = unify_facts(typed_concl, &bare_fact);
                if bindings_opt.is_none() {
                    continue;
                }
                let mut bindings = bindings_opt.unwrap();

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
                            per_var_candidates.push(all_candidates.clone());
                        } else {
                            let filtered: Vec<GroundTerm> = all_candidates
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
                                        !check_predicate_in_kb_typed(
                                            &tensed_cs,
                                            inner,
                                            depth + 1,
                                            visited,
                                        )
                                        .is_false()
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
                    for combo in TypedMultiCartesian::new(&per_var_candidates) {
                        for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                            bindings.insert(ev_var.clone(), combo[i].clone());
                        }
                        let mut all_hold = true;
                        let mut pending_here = None;
                        for ct in &rule.typed_conditions {
                            let bare_cs = substitute_fact(ct, &bindings);
                            let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                            let result =
                                check_predicate_in_kb_typed(&tensed_cs, inner, depth + 1, visited);
                            if result.is_false() {
                                all_hold = false;
                                pending_here = None;
                                break;
                            }
                            if !result.is_true() {
                                all_hold = false;
                                pending_here = prefer_non_definitive(pending_here, result);
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
                        best_result =
                            combo_pending.and_then(|r| prefer_non_definitive(best_result, r));
                        continue;
                    }
                }

                let mut all_conditions_hold = true;
                let mut rule_pending = None;
                for ct in &rule.typed_conditions {
                    let bare_cs = substitute_fact(ct, &bindings);
                    let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                    let result = check_predicate_in_kb_typed(&tensed_cs, inner, depth + 1, visited);
                    if result.is_false() {
                        all_conditions_hold = false;
                        rule_pending = None;
                        break;
                    }
                    if !result.is_true() {
                        all_conditions_hold = false;
                        rule_pending = prefer_non_definitive(rule_pending, result);
                    }
                }

                if all_conditions_hold {
                    visited.remove(fact);
                    return QueryResult::True;
                }
                best_result = rule_pending.and_then(|r| prefer_non_definitive(best_result, r));
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
}

impl<'a> TypedMultiCartesian<'a> {
    fn new(sets: &'a [Vec<GroundTerm>]) -> Self {
        let done = sets.iter().any(|s| s.is_empty());
        Self {
            sets,
            indices: vec![0; sets.len()],
            done,
        }
    }
}

impl<'a> Iterator for TypedMultiCartesian<'a> {
    type Item = Vec<GroundTerm>;

    fn next(&mut self) -> Option<Self::Item> {
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

    let idx = steps.len() as u32;
    steps.push(ProofStep {
        rule: ProofRule::PredicateCheck(("unknown".to_string(), display.clone())),
        holds: true,
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
    // Pre-compute candidate terms for unbound event variable search.
    let all_candidates = build_all_candidates(inner);

    let rules_snapshot = collect_matching_rules_typed(fact, &inner.universal_rules);
    let display = fact.to_display_string();

    for rule in &rules_snapshot {
        for typed_concl in &rule.typed_conclusions {
            let bindings_opt = unify_facts(typed_concl, fact);
            if bindings_opt.is_none() {
                continue;
            }
            let mut bindings = bindings_opt.unwrap();

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
                        per_var_candidates.push(all_candidates.clone());
                    } else {
                        let filtered: Vec<GroundTerm> = all_candidates
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
                for combo in TypedMultiCartesian::new(&per_var_candidates) {
                    for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                        bindings.insert(ev_var.clone(), combo[i].clone());
                    }
                    let all_hold = rule.typed_conditions.iter().all(|ct| {
                        let cs = substitute_fact(ct, &bindings);
                        check_predicate_in_kb_typed(&cs, &*inner, depth + 1, &mut HashSet::new())
                            .is_true()
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

            // Check all conditions hold and collect their StoredFacts for provenance.
            let mut all_conditions_hold = true;
            let mut condition_facts = Vec::new();

            for cond_template in &rule.typed_conditions {
                let cond_fact = substitute_fact(cond_template, &bindings);
                if check_predicate_in_kb_typed(&cond_fact, &*inner, depth + 1, &mut HashSet::new())
                    .is_true()
                {
                    condition_facts.push(cond_fact);
                } else {
                    all_conditions_hold = false;
                    break;
                }
            }

            if !all_conditions_hold {
                continue;
            }

            if rule.typed_conditions.is_empty() {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::Derived((rule.label.clone(), display.clone())),
                    holds: true,
                    children: vec![],
                });
                return Some(idx);
            }

            let mut child_indices = Vec::new();
            for cond_fact in &condition_facts {
                let child_idx =
                    trace_predicate_provenance_typed(cond_fact, inner, steps, depth + 1, memo);
                child_indices.push(child_idx);
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
                let bindings_opt = unify_facts(typed_concl, &bare_fact);
                if bindings_opt.is_none() {
                    continue;
                }
                let mut bindings = bindings_opt.unwrap();

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
                            per_var_candidates.push(all_candidates.clone());
                        } else {
                            let filtered: Vec<GroundTerm> = all_candidates
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
                    for combo in TypedMultiCartesian::new(&per_var_candidates) {
                        for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                            bindings.insert(ev_var.clone(), combo[i].clone());
                        }
                        let all_hold = rule.typed_conditions.iter().all(|ct| {
                            let bare_cs = substitute_fact(ct, &bindings);
                            let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                            check_predicate_in_kb_typed(
                                &tensed_cs,
                                &*inner,
                                depth + 1,
                                &mut HashSet::new(),
                            )
                            .is_true()
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
                let mut condition_facts = Vec::new();
                for cond_template in &rule.typed_conditions {
                    let bare_cs = substitute_fact(cond_template, &bindings);
                    let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                    if check_predicate_in_kb_typed(
                        &tensed_cs,
                        &*inner,
                        depth + 1,
                        &mut HashSet::new(),
                    )
                    .is_true()
                    {
                        condition_facts.push(tensed_cs);
                    } else {
                        all_conditions_hold = false;
                        break;
                    }
                }

                if !all_conditions_hold {
                    continue;
                }

                if rule.typed_conditions.is_empty() {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::Derived((
                            format!("{} [{}]", rule.label, tense_label),
                            display.clone(),
                        )),
                        holds: true,
                        children: vec![],
                    });
                    return Some(idx);
                }

                let mut child_indices = Vec::new();
                for cond_fact in &condition_facts {
                    let child_idx =
                        trace_predicate_provenance_typed(cond_fact, inner, steps, depth + 1, memo);
                    child_indices.push(child_idx);
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
                                    ground_term_to_logical_term(&winning_member),
                                )),
                                holds: true,
                                children: vec![body_idx],
                            });
                            return Ok((true, idx));
                        }
                    }
                }
            }

            let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
            for member in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), member.clone());
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
                            ground_term_to_logical_term(member),
                        )),
                        holds: true,
                        children: vec![body_idx],
                    });
                    return Ok((true, idx));
                }
            }
            let sk_entries: Vec<(String, usize)> = inner
                .skolem_fn_registry
                .iter()
                .map(|e| (e.base_name.clone(), e.dep_count))
                .collect();
            for (base_name, dep_count) in &sk_entries {
                for combo in GroundTermCartesianProduct::new(&members, *dep_count) {
                    let witness = build_skolem_fn_term(base_name, &combo);
                    let mut new_subs = subs.clone();
                    new_subs.insert(v.clone(), witness.clone());
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
                                ground_term_to_logical_term(&witness),
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
