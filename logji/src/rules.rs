use super::*;
use std::hash::{Hash, Hasher};

/// Compute a structural hash for rule dedup. `tag` distinguishes rule kinds.
fn rule_dedup_hash(tag: u8, conditions: &[StoredFact], conclusions: &[StoredFact]) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    tag.hash(&mut hasher);
    conditions.hash(&mut hasher);
    conclusions.hash(&mut hasher);
    hasher.finish()
}

/// Check if a GroundTerm represents a dependent Skolem placeholder.
pub(super) fn is_skdep(gt: &GroundTerm) -> bool {
    matches!(gt, GroundTerm::PatternVar(s) if s.starts_with(SKDEP_PREFIX))
}

/// Extract the base Skolem name from a dependent Skolem placeholder.
pub(super) fn skdep_base_name(gt: &GroundTerm) -> Option<&str> {
    match gt {
        GroundTerm::PatternVar(s) => s.strip_prefix(SKDEP_PREFIX),
        _ => None,
    }
}

pub(super) fn collect_exists_for_skolem(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, GroundTerm>,
    enclosing_universals: &mut Vec<String>,
    counter: &mut usize,
) {
    let Ok(node) = get_node(buffer, node_id) else {
        return;
    };
    match node {
        LogicNode::ExistsNode((v, body)) => {
            if !subs.contains_key(v.as_str()) {
                if enclosing_universals.is_empty() {
                    let sk = format!("sk_{}", *counter);
                    *counter += 1;
                    subs.insert(v.clone(), GroundTerm::Constant(sk));
                } else {
                    let base = format!("sk_{}", *counter);
                    *counter += 1;
                    let placeholder = format!("{}{}", SKDEP_PREFIX, base);
                    subs.insert(v.clone(), GroundTerm::PatternVar(placeholder));
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
                    subs.insert(v.clone(), GroundTerm::Constant(sk));
                } else {
                    let base = format!("sk_{}", *counter);
                    *counter += 1;
                    let placeholder = format!("{}{}", SKDEP_PREFIX, base);
                    subs.insert(v.clone(), GroundTerm::PatternVar(placeholder));
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

pub(super) fn decompose_implication(buffer: &LogicBuffer, body_id: u32) -> Option<(Vec<u32>, u32)> {
    let mut conditions = Vec::new();
    let mut current = body_id;

    loop {
        let Ok(node) = get_node(buffer, current) else {
            break;
        };
        match node {
            LogicNode::OrNode((left, right)) => {
                let Ok(left_node) = get_node(buffer, *left) else {
                    break;
                };
                match left_node {
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

#[allow(dead_code)]
pub(super) fn flatten_conjuncts(buffer: &LogicBuffer, node_id: u32) -> Vec<u32> {
    let Ok(node) = get_node(buffer, node_id) else {
        return vec![node_id];
    };
    match node {
        LogicNode::AndNode((l, r)) => {
            let mut result = flatten_conjuncts(buffer, *l);
            result.extend(flatten_conjuncts(buffer, *r));
            result
        }
        _ => vec![node_id],
    }
}

pub(super) fn collect_condition_exists(
    buffer: &LogicBuffer,
    node_id: u32,
    exists_vars: &mut HashSet<String>,
) {
    let Ok(node) = get_node(buffer, node_id) else {
        return;
    };
    match node {
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

pub(super) fn flatten_conjuncts_through_exists(
    buffer: &LogicBuffer,
    node_id: u32,
    condition_exists: &HashSet<String>,
) -> Vec<u32> {
    let Ok(node) = get_node(buffer, node_id) else {
        return vec![node_id];
    };
    match node {
        LogicNode::AndNode((l, r)) => {
            let mut result = flatten_conjuncts_through_exists(buffer, *l, condition_exists);
            result.extend(flatten_conjuncts_through_exists(
                buffer,
                *r,
                condition_exists,
            ));
            result
        }
        LogicNode::ExistsNode((v, body)) if condition_exists.contains(v.as_str()) => {
            flatten_conjuncts_through_exists(buffer, *body, condition_exists)
        }
        _ => vec![node_id],
    }
}

fn flatten_consequent(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, GroundTerm>,
) -> Vec<u32> {
    let Ok(node) = get_node(buffer, node_id) else {
        return vec![node_id];
    };
    match node {
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

pub(super) fn collect_and_note_constants(
    buffer: &LogicBuffer,
    node_id: u32,
    inner: &mut KnowledgeBaseInner,
) {
    let Ok(node) = get_node(buffer, node_id) else {
        return;
    };
    match node {
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

pub(super) fn register_rule(
    inner: &mut KnowledgeBaseInner,
    label: String,
    pattern_var_names: Vec<String>,
    typed_conditions: Vec<StoredFact>,
    typed_conclusions: Vec<StoredFact>,
    negated_condition_indices: Vec<usize>,
    forward: bool,
) -> Result<(), String> {
    // Update predicate dependency graph before inserting the rule.
    for concl in &typed_conclusions {
        let concl_rel = concl.relation().to_string();
        for (idx, cond) in typed_conditions.iter().enumerate() {
            let is_neg = negated_condition_indices.contains(&idx);
            inner
                .pred_dep_graph
                .entry(concl_rel.clone())
                .or_default()
                .push((cond.relation().to_string(), is_neg));
        }
    }

    // Check stratification (skip during rebuild — same rules passed before).
    if !inner.rebuilding {
        if let Err(e) = check_stratification(&inner.pred_dep_graph) {
            // Rollback: remove the edges we just added.
            for concl in &typed_conclusions {
                let concl_rel = concl.relation();
                if let Some(edges) = inner.pred_dep_graph.get_mut(concl_rel) {
                    for _ in 0..typed_conditions.len() {
                        edges.pop();
                    }
                    if edges.is_empty() {
                        inner.pred_dep_graph.remove(concl_rel);
                    }
                }
            }
            return Err(e);
        }
    }

    let rule = UniversalRuleRecord {
        label,
        typed_conditions,
        typed_conclusions,
        pattern_var_names,
        negated_condition_indices,
        forward,
        priority: 0, // Default priority; can be changed via set_rule_priority.
    };
    let rc = Arc::new(rule);
    let mut indexed = false;
    for concl in &rc.typed_conclusions {
        inner
            .universal_rules
            .entry(concl.relation().to_string())
            .or_default()
            .push(Arc::clone(&rc));
        indexed = true;
    }
    if !indexed {
        inner
            .universal_rules
            .entry("__fallback__".to_string())
            .or_default()
            .push(rc.clone());
    }

    // Track which assertion ID produced this rule (for incremental retraction).
    if let Some(assertion_id) = inner.current_assertion_id {
        let pred_keys: Vec<String> = rc
            .typed_conclusions
            .iter()
            .map(|c| c.relation().to_string())
            .collect();
        inner
            .rule_source_map
            .entry(assertion_id)
            .or_default()
            .extend(pred_keys);
    }

    Ok(())
}

/// Compute the strongly-connected components of the predicate dependency graph.
///
/// Iterative (explicit-stack) Tarjan — a recursive DFS would risk a stack
/// overflow on a long positive dependency chain. The node set is the graph keys
/// PLUS every edge target (a condition-only leaf predicate is never a key but is
/// still a node), and both the node scan and each node's neighbor list are taken
/// in SORTED order, so the partition is canonical regardless of HashMap layout or
/// rule-registration order.
pub(super) fn compute_sccs(graph: &HashMap<String, Vec<(String, bool)>>) -> Vec<Vec<String>> {
    use std::collections::{BTreeSet, HashSet};

    let mut node_set: BTreeSet<&str> = BTreeSet::new();
    for (k, edges) in graph {
        node_set.insert(k.as_str());
        for (dep, _) in edges {
            node_set.insert(dep.as_str());
        }
    }
    let nodes: Vec<&str> = node_set.into_iter().collect();

    let neighbors = |n: &str| -> Vec<&str> {
        match graph.get(n) {
            Some(edges) => {
                let mut out: Vec<&str> = edges.iter().map(|(d, _)| d.as_str()).collect();
                out.sort_unstable();
                out
            }
            None => Vec::new(),
        }
    };

    let mut index_of: HashMap<&str, usize> = HashMap::new();
    let mut lowlink: HashMap<&str, usize> = HashMap::new();
    let mut on_stack: HashSet<&str> = HashSet::new();
    let mut tarjan_stack: Vec<&str> = Vec::new();
    let mut next_index = 0usize;
    let mut sccs: Vec<Vec<String>> = Vec::new();

    for &start in &nodes {
        if index_of.contains_key(start) {
            continue;
        }
        index_of.insert(start, next_index);
        lowlink.insert(start, next_index);
        next_index += 1;
        tarjan_stack.push(start);
        on_stack.insert(start);
        // Each work frame is (node, neighbor cursor, sorted neighbors).
        let mut work: Vec<(&str, usize, Vec<&str>)> = vec![(start, 0, neighbors(start))];

        while let Some(&(node, _, _)) = work.last() {
            let cursor = work.last().unwrap().1;
            let nlen = work.last().unwrap().2.len();
            if cursor < nlen {
                let w = work.last().unwrap().2[cursor];
                work.last_mut().unwrap().1 += 1;
                if !index_of.contains_key(w) {
                    index_of.insert(w, next_index);
                    lowlink.insert(w, next_index);
                    next_index += 1;
                    tarjan_stack.push(w);
                    on_stack.insert(w);
                    work.push((w, 0, neighbors(w)));
                } else if on_stack.contains(w) {
                    let wi = index_of[w];
                    let cur = lowlink[node];
                    lowlink.insert(node, cur.min(wi));
                }
            } else {
                // `node` is fully explored; if it roots an SCC, pop the component.
                if lowlink[node] == index_of[node] {
                    let mut comp: Vec<String> = Vec::new();
                    while let Some(w) = tarjan_stack.pop() {
                        on_stack.remove(w);
                        comp.push(w.to_string());
                        if w == node {
                            break;
                        }
                    }
                    comp.sort();
                    sccs.push(comp);
                }
                work.pop();
                if let Some(&(parent, _, _)) = work.last() {
                    let cur = lowlink[parent];
                    let child = lowlink[node];
                    lowlink.insert(parent, cur.min(child));
                }
            }
        }
    }
    sccs
}

/// Check the predicate dependency graph for negative cycles.
///
/// A program is unstratifiable iff some strongly-connected component contains a
/// negative edge — negation-as-failure over a recursive cycle is unsound. This
/// is order-independent (SCCs are a graph invariant) and position-aware: only
/// edges whose BOTH endpoints lie inside one SCC are counted, so a negative edge
/// feeding INTO a cycle from outside cannot flip the verdict, and a negative
/// self-loop (a size-1 SCC) is caught uniformly.
fn check_stratification(graph: &HashMap<String, Vec<(String, bool)>>) -> Result<(), String> {
    for scc in compute_sccs(graph) {
        let members: std::collections::HashSet<&str> = scc.iter().map(|s| s.as_str()).collect();
        for node in &scc {
            if let Some(edges) = graph.get(node.as_str()) {
                for (dep, is_neg) in edges {
                    if *is_neg && members.contains(dep.as_str()) {
                        return Err(format!(
                            "Unstratifiable negation: strongly-connected component \
                             containing '{}' -> '{}' (negative)",
                            node, dep
                        ));
                    }
                }
            }
        }
    }
    Ok(())
}

/// Assert a typed fact into the fact store.
/// Validates predicate arity against the registry (permissive mode: warns on mismatch).
pub(super) fn assert_typed_fact(fact: StoredFact, inner: &mut KnowledgeBaseInner) {
    let rel = fact.relation();
    let arity = fact.inner().args.len();

    if let Some(sig) = inner.predicate_registry.get(rel) {
        // Known predicate — check arity.
        if sig.arity != arity {
            eprintln!(
                "[Arity Warning] '{}': expected {} args, got {} ({})",
                rel,
                sig.arity,
                arity,
                match sig.source {
                    SignatureSource::Dictionary => "dictionary",
                    SignatureSource::Inferred => "inferred from first use",
                }
            );
        }
    } else {
        // First time seeing this predicate — register it.
        let source = if smuni_dictionary::get_arity(rel).is_some() {
            SignatureSource::Dictionary
        } else {
            SignatureSource::Inferred
        };
        inner.predicate_registry.insert(
            rel.to_string(),
            PredicateSignature {
                arity,
                source,
                arg_sorts: vec![],
            },
        );
    }

    // Sort validation (permissive mode: warn on mismatch).
    if let Some(sig) = inner.predicate_registry.get(rel) {
        if !sig.arg_sorts.is_empty() && !inner.rebuilding {
            let gf_check = fact.inner();
            for (pos, arg) in gf_check.args.iter().enumerate() {
                if pos >= sig.arg_sorts.len() {
                    break;
                }
                let expected_sort = &sig.arg_sorts[pos];
                if expected_sort.is_empty() {
                    continue; // No sort constraint for this position.
                }
                if let GroundTerm::Constant(name) = arg {
                    if let Some(actual_sort) = inner.entity_sorts.get(name.as_str()) {
                        if !is_sort_compatible(&inner.sort_hierarchy, actual_sort, expected_sort) {
                            eprintln!(
                                "[Sort Warning] '{}' arg {}: entity '{}' has sort '{}', expected '{}'",
                                rel, pos, name, actual_sort, expected_sort
                            );
                        }
                    }
                }
            }
        }
    }

    let rel_owned = rel.to_string();

    // Populate argument-position index before inserting (need fact reference).
    let gf = fact.inner();
    for (pos, arg) in gf.args.iter().enumerate() {
        inner
            .arg_position_index
            .entry((gf.relation.clone(), pos))
            .or_default()
            .entry(arg.clone())
            .or_default()
            .push(fact.clone());
    }

    inner.fact_store.insert(fact);

    // The fact store just changed. Clear the predicate result cache so no
    // subsequent lookup in the SAME query returns a stale verdict — the most
    // important trigger is mid-query compute auto-ingestion (an external/
    // arithmetic result asserted here that a downstream rule then chains on).
    // Structural invariant at the mutation point, not call-site discipline.
    // CLEARS entries but KEEPS the cache enabled (preserves cross-depth
    // tabling); cycle-cutting is a separate `visited` set, so this is
    // termination-safe. During normal assertion the cache is disabled+empty,
    // so this is a free no-op there.
    clear_typed_pred_cache();

    // Check integrity constraints (permissive mode: warn, don't reject).
    if !inner.integrity_constraints.is_empty() && !inner.rebuilding {
        if let Some(violation) = check_constraints_for_predicate(&rel_owned, inner) {
            eprintln!("[Constraint] {}", violation);
        }
    }

    // Selective forward chaining: fire forward-enabled rules triggered by this fact.
    if !inner.rebuilding {
        trigger_forward_rules(&rel_owned, inner);
    }
}

/// Fire forward-enabled rules whose conditions are fully satisfied after a new
/// fact insertion. Only checks directly asserted facts (not backward chaining)
/// to keep forward chaining cheap. Depth-limited to prevent infinite loops.
const MAX_FORWARD_DEPTH: usize = 10;

fn trigger_forward_rules(new_rel: &str, inner: &mut KnowledgeBaseInner) {
    if inner.forward_depth >= MAX_FORWARD_DEPTH {
        return;
    }

    // Collect forward rules whose conditions mention the newly-asserted predicate.
    let mut forward_rules: Vec<Arc<UniversalRuleRecord>> = inner
        .universal_rules
        .values()
        .flat_map(|v| v.iter())
        .filter(|r| r.forward && r.typed_conditions.iter().any(|c| c.relation() == new_rel))
        .cloned()
        .collect();
    forward_rules.sort_by_key(|r| std::cmp::Reverse(r.priority));

    if forward_rules.is_empty() {
        return;
    }

    inner.forward_depth += 1;

    // For each forward rule, try to match the new fact against each condition.
    let mut to_derive: Vec<StoredFact> = Vec::new();
    for rule in &forward_rules {
        for (cond_idx, cond_template) in rule.typed_conditions.iter().enumerate() {
            if cond_template.relation() != new_rel {
                continue;
            }
            // A forward rule cannot be triggered by ASSERTING a fact that matches a
            // negated (absence) condition — asserting the fact makes ¬P false, not true.
            if rule.negated_condition_indices.contains(&cond_idx) {
                continue;
            }
            // Try all facts matching this predicate to find full condition satisfaction.
            let matching_facts: Vec<StoredFact> = inner
                .fact_store
                .lookup_predicate(new_rel)
                .map(|set| set.iter().cloned().collect())
                .unwrap_or_default();

            for fact in &matching_facts {
                let Some(bindings) = unify_facts(cond_template, fact) else {
                    continue;
                };
                // Check all OTHER conditions hold against the fact store: positive
                // conditions must be asserted; negated conditions hold via NAF (absent).
                // TODO(naf-forward): no truth maintenance when a negated condition flips
                // after a forward derivation; forward rules are off by default. See todo.md.
                let all_others = rule
                    .typed_conditions
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != cond_idx)
                    .all(|(i, other)| {
                        let sub = substitute_fact(other, &bindings);
                        if rule.negated_condition_indices.contains(&i) {
                            !inner.fact_store.contains(&sub)
                        } else {
                            inner.fact_store.contains(&sub)
                        }
                    });
                if all_others {
                    for concl in &rule.typed_conclusions {
                        let derived = substitute_fact(concl, &bindings);
                        if !inner.fact_store.contains(&derived) {
                            to_derive.push(derived);
                        }
                    }
                }
            }
        }
    }

    // Assert derived facts (may trigger further forward chaining recursively).
    for fact in to_derive {
        if !inner.rebuilding {
            eprintln!("[Forward] Derived: {}", fact.to_display_string());
        }
        assert_typed_fact(fact, inner);
    }

    inner.forward_depth -= 1;
}

/// Collect the variable names appearing as arguments of a flat predicate/compute
/// atom. Used to compute precise dependent-skolem dependencies (which universals
/// a conclusion existential actually references).
fn atom_var_args(buffer: &LogicBuffer, node_id: u32) -> Vec<String> {
    match get_node(buffer, node_id) {
        Ok(LogicNode::Predicate((_, args))) | Ok(LogicNode::ComputeNode((_, args))) => args
            .iter()
            .filter_map(|t| match t {
                LogicalTerm::Variable(v) => Some(v.clone()),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

pub(super) fn compile_forall_to_rule(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
) -> Result<(), String> {
    let mut universals: Vec<String> = Vec::new();
    let mut current = node_id;
    loop {
        let Ok(node) = get_node(buffer, current) else {
            return Ok(());
        };
        match node {
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

    // For fail-closed diagnostics: how to refer to this rule in an error message.
    let rule_desc = if universals.is_empty() {
        "ground conditional".to_string()
    } else {
        format!("∀{}", universals.join(","))
    };

    let mut pattern_vars: HashMap<String, String> = universals
        .iter()
        .enumerate()
        .map(|(i, v)| (v.clone(), format!("x__v{}", i)))
        .collect();

    let mut ground_skolems: HashMap<String, String> = skolem_subs
        .iter()
        .filter(|(_, gt)| !is_skdep(gt))
        .filter_map(|(k, gt)| {
            if let GroundTerm::Constant(s) = gt {
                Some((k.clone(), s.clone()))
            } else {
                None
            }
        })
        .collect();

    let pattern_var_names: Vec<String> =
        universals.iter().map(|v| pattern_vars[v].clone()).collect();
    let mut dependent_skolems: HashMap<String, (String, Vec<String>)> = skolem_subs
        .iter()
        .filter_map(|(k, gt)| {
            skdep_base_name(gt)
                .map(|base| (k.clone(), (base.to_string(), pattern_var_names.clone())))
        })
        .collect();

    match decompose_implication(buffer, inner_body_id) {
        Some((condition_ids, consequent_id)) => {
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

            let consequent_atoms = flatten_consequent(buffer, consequent_id, skolem_subs);

            // DepPair precision: a conclusion existential depends only on the
            // universals it is CONNECTED to, not on ALL enclosing universals.
            // Over-approximating inflates `dep_count`, which drives a
            // `members^dep_count` witness cartesian during firing and witness
            // search. Connectivity is TRANSITIVE over the consequent's
            // variable-sharing graph (two vars are adjacent iff they appear in
            // the same atom): direct co-occurrence is the 1-hop case, but a
            // Neo-Davidsonian existential reaches its universal THROUGH a shared
            // event variable — e.g. the cat `_v1` connects to the dog universal
            // `_v0` only via the nelci event `_ev0` (`nelci_x1(ev, dog)` and
            // `nelci_x2(ev, cat)` share `ev`). Restricting deps to the universals
            // in the existential's connected component keeps them minimal (no
            // blowup), while a 1-hop-only rule would mis-register the cat as
            // INDEPENDENT (`sk_N(_)`): distinct dogs would then share one cat (a
            // soundness bug) and find witnesses would render unbound. (`zdani(x,
            // y, z)` still yields both x and y; `zenba(de)` still yields only
            // `de` — both are single-atom, so 1-hop and transitive agree.)
            let mut var_adjacency: HashMap<String, HashSet<String>> = HashMap::new();
            for &aid in &consequent_atoms {
                let vars = atom_var_args(buffer, aid);
                for a in &vars {
                    for b in &vars {
                        if a != b {
                            var_adjacency
                                .entry(a.clone())
                                .or_default()
                                .insert(b.clone());
                        }
                    }
                }
            }
            for (k, val) in dependent_skolems.iter_mut() {
                // Variables reachable from `k` over the sharing graph (its
                // connected component), found by iterative DFS.
                let mut reached: HashSet<String> = HashSet::new();
                reached.insert(k.clone());
                let mut stack = vec![k.clone()];
                while let Some(node) = stack.pop() {
                    if let Some(neighbors) = var_adjacency.get(&node) {
                        for n in neighbors {
                            if reached.insert(n.clone()) {
                                stack.push(n.clone());
                            }
                        }
                    }
                }
                // Keep `universals` order so DepPair nesting stays deterministic.
                let precise: Vec<String> = universals
                    .iter()
                    .filter(|u| reached.contains(*u))
                    .map(|u| pattern_vars[u].clone())
                    .collect();
                val.1 = precise;
            }

            if !dependent_skolems.is_empty() {
                for (_, (base, pvars)) in &dependent_skolems {
                    if !inner
                        .skolem_fn_registry
                        .iter()
                        .any(|e| e.base_name == *base)
                    {
                        inner.skolem_fn_registry.push(SkolemFnEntry {
                            base_name: base.clone(),
                            dep_count: pvars.len(),
                        });
                    }
                }
            }

            let all_pattern_var_names: Vec<String> = {
                let mut names = pattern_var_names.clone();
                for var in &condition_exists_vars {
                    if let Some(pvar) = pattern_vars.get(var) {
                        names.push(pvar.clone());
                    }
                }
                names
            };

            let mut all_conditions = Vec::new();
            for cid in &condition_ids {
                all_conditions.extend(flatten_conjuncts_through_exists(
                    buffer,
                    *cid,
                    &condition_exists_vars,
                ));
            }

            let mut typed_conds: Vec<StoredFact> = Vec::new();
            let mut negated_condition_indices: Vec<usize> = Vec::new();
            for &cid in &all_conditions {
                match build_rule_template_fact_with_negation(
                    buffer,
                    cid,
                    &pattern_vars,
                    &ground_skolems,
                    &dependent_skolems,
                ) {
                    Some((fact, is_negated)) => {
                        if is_negated {
                            negated_condition_indices.push(typed_conds.len());
                        }
                        typed_conds.push(fact);
                    }
                    // FAIL CLOSED: an antecedent atom we cannot represent as a flat
                    // backward-chaining template (a tense wrapper, disjunction, nested
                    // quantifier, or negated-complex form) would otherwise be silently
                    // dropped — leaving an UNDER-CONDITIONED rule that fires when it
                    // should not. That is exactly the fail-open unsoundness the
                    // zero-hallucination contract forbids. Reject the assertion instead.
                    None => {
                        return Err(format!(
                            "cannot compile rule antecedent for {rule_desc}: an atom is not a \
                             flat predicate (tense, disjunction, nested quantifier, or \
                             negated-complex antecedents are unsupported). Rejecting the \
                             assertion to preserve soundness rather than registering an \
                             under-conditioned rule."
                        ));
                    }
                }
            }
            let mut typed_concls: Vec<StoredFact> = Vec::new();
            for &aid in &consequent_atoms {
                match build_rule_template_fact(
                    buffer,
                    aid,
                    &pattern_vars,
                    &ground_skolems,
                    &dependent_skolems,
                ) {
                    Some(fact) => typed_concls.push(fact),
                    // FAIL CLOSED: a conclusion atom we cannot template (negated,
                    // disjunctive, or nested) would make the rule conclude less than
                    // written — a dead `__fallback__` rule or silently-lost negative
                    // information. Reject rather than register a misleading rule.
                    None => {
                        return Err(format!(
                            "cannot compile rule conclusion for {rule_desc}: a consequent \
                             atom is not a flat predicate. Rejecting the assertion to \
                             preserve soundness."
                        ));
                    }
                }
            }

            let dedup_key = rule_dedup_hash(0, &typed_conds, &typed_concls);
            if !inner.known_rules.insert(dedup_key) {
                if !inner.rebuilding {
                    println!("[Rule] ∀{} already present, skipping", universals.join(","));
                }
            } else {
                if !inner.rebuilding {
                    println!(
                        "[Rule] Compiled ∀{} to backward-chaining rule",
                        universals.join(",")
                    );
                }

                let label = build_typed_rule_label(&typed_conds, &typed_concls);
                if let Err(e) = register_rule(
                    inner,
                    label,
                    all_pattern_var_names.clone(),
                    typed_conds,
                    typed_concls,
                    negated_condition_indices,
                    false, // forward chaining disabled by default
                ) {
                    eprintln!("[Stratification Error] {}", e);
                    return Err(e);
                }

                // xorlo presupposition applies only to genuine universals (ro lo / ro le):
                // a ground material conditional (zero universals, e.g. `ganai A gi B`) carries
                // no existential import and must NOT assert its antecedent/consequent witnesses.
                if !universals.is_empty() {
                    let xp_name = inner.fresh_skolem();
                    inner.note_entity(&xp_name);
                    let mut xp_subs: HashMap<String, GroundTerm> = HashMap::new();
                    for v in &universals {
                        xp_subs.insert(v.clone(), GroundTerm::Constant(xp_name.clone()));
                    }
                    for (k, v) in &ground_skolems {
                        xp_subs
                            .entry(k.clone())
                            .or_insert_with(|| GroundTerm::Constant(v.clone()));
                    }
                    for var in &condition_exists_vars {
                        let ev_sk = inner.fresh_skolem();
                        if var.starts_with("_ev") {
                            inner.note_event_entity(&ev_sk);
                        } else {
                            inner.note_entity(&ev_sk);
                        }
                        xp_subs.insert(var.clone(), GroundTerm::Constant(ev_sk));
                    }
                    for &cid in &all_conditions {
                        if let Some(fact) = build_stored_fact_from_node(buffer, cid, &xp_subs, None)
                        {
                            assert_typed_fact(fact, inner);
                        }
                    }
                }
            }
        }
        None => {
            if !dependent_skolems.is_empty() {
                for (_, (base, pvars)) in &dependent_skolems {
                    if !inner
                        .skolem_fn_registry
                        .iter()
                        .any(|e| e.base_name == *base)
                    {
                        inner.skolem_fn_registry.push(SkolemFnEntry {
                            base_name: base.clone(),
                            dep_count: pvars.len(),
                        });
                    }
                }
            }

            let typed_concls: Vec<StoredFact> = match build_rule_template_fact(
                buffer,
                inner_body_id,
                &pattern_vars,
                &ground_skolems,
                &dependent_skolems,
            ) {
                Some(fact) => vec![fact],
                // FAIL CLOSED: a bare universal whose body is conjunctive/complex would
                // otherwise collapse to an empty conclusion list (a dead rule). Reject.
                None => {
                    return Err(format!(
                        "cannot compile bare universal {rule_desc}: its body is not a flat \
                         predicate. Rejecting the assertion to preserve soundness."
                    ));
                }
            };

            let dedup_key = rule_dedup_hash(1, &[], &typed_concls);
            if !inner.known_rules.insert(dedup_key) {
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

                let label = build_typed_rule_label(&[], &typed_concls);
                if let Err(e) = register_rule(
                    inner,
                    label,
                    pattern_var_names.clone(),
                    vec![],
                    typed_concls,
                    vec![], // bare universal — no conditions, no negation
                    false,  // forward chaining disabled by default
                ) {
                    eprintln!("[Stratification Error] {}", e);
                    return Err(e);
                }
            }
        }
    }

    Ok(())
}

pub(super) fn generate_count_extra_witnesses(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
) {
    let Ok(node) = get_node(buffer, node_id) else {
        return;
    };
    match node {
        LogicNode::CountNode((v, count, body)) => {
            if *count > 1 {
                for _ in 1..*count {
                    let extra_sk = inner.fresh_skolem();
                    inner.note_entity(&extra_sk);

                    let mut typed_extra_subs: HashMap<String, GroundTerm> = skolem_subs
                        .iter()
                        .filter(|(_, gt)| !is_skdep(gt))
                        .map(|(k, gt)| (k.clone(), gt.clone()))
                        .collect();
                    typed_extra_subs.insert(v.clone(), GroundTerm::Constant(extra_sk.clone()));
                    if let Some(fact) =
                        build_stored_fact_from_node(buffer, *body, &typed_extra_subs, None)
                    {
                        assert_typed_fact(fact, inner);
                    }
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

/// Convert a LogicalTerm + substitutions to a GroundTerm.
/// `subs` maps variable names to GroundTerm values directly — no string parsing needed.
pub(super) fn build_ground_term(
    term: &LogicalTerm,
    subs: &HashMap<String, GroundTerm>,
) -> GroundTerm {
    match term {
        LogicalTerm::Variable(v) => {
            if let Some(gt) = subs.get(v.as_str()) {
                if is_skdep(gt) {
                    // Dependent Skolem — left as a variable (handled by rule compilation)
                    GroundTerm::PatternVar(v.clone())
                } else {
                    gt.clone()
                }
            } else {
                // Unsubstituted variable — either a pattern var in rules or an error.
                GroundTerm::PatternVar(v.clone())
            }
        }
        LogicalTerm::Constant(c) => GroundTerm::Constant(c.clone()),
        LogicalTerm::Description(d) => GroundTerm::Description(d.clone()),
        LogicalTerm::Unspecified => GroundTerm::Unspecified,
        LogicalTerm::Number(n) => GroundTerm::from_f64(*n),
    }
}

/// Build a StoredFact from a Predicate/ComputeNode in a LogicBuffer.
/// Returns None if the node isn't a predicate-like node.
pub(super) fn build_stored_fact_from_node(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
    tense: Option<&str>,
) -> Option<StoredFact> {
    let Ok(node) = get_node(buffer, node_id) else {
        return None;
    };
    match node {
        LogicNode::Predicate((rel, args)) | LogicNode::ComputeNode((rel, args)) => {
            let ground_args: Vec<GroundTerm> =
                args.iter().map(|a| build_ground_term(a, subs)).collect();
            let fact = GroundFact::new(rel.clone(), ground_args);
            Some(StoredFact::with_tense(fact, tense))
        }
        LogicNode::ExistsNode((v, body)) => {
            // If variable is Skolemized, skip the quantifier wrapper.
            if subs.contains_key(v.as_str()) {
                build_stored_fact_from_node(buffer, *body, subs, tense)
            } else {
                None // Unskolemized existential — not a ground fact.
            }
        }
        LogicNode::PastNode(inner) => {
            build_stored_fact_from_node(buffer, *inner, subs, Some("Past"))
        }
        LogicNode::PresentNode(inner) => {
            build_stored_fact_from_node(buffer, *inner, subs, Some("Present"))
        }
        LogicNode::FutureNode(inner) => {
            build_stored_fact_from_node(buffer, *inner, subs, Some("Future"))
        }
        LogicNode::ObligatoryNode(inner) | LogicNode::PermittedNode(inner) => {
            // Deontic wrappers are transparent — same as fact_repr path.
            build_stored_fact_from_node(buffer, *inner, subs, tense)
        }
        _ => None, // And/Or/Not/ForAll/Count — not a leaf fact.
    }
}

/// Collect leaf StoredFacts from an And-tree (typed equivalent of collect_ground_leaves + reconstruct_repr).
pub(super) fn collect_ground_facts(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
    tense: Option<&str>,
    out: &mut Vec<StoredFact>,
) {
    let Ok(node) = get_node(buffer, node_id) else {
        return;
    };
    match node {
        LogicNode::AndNode((l, r)) => {
            collect_ground_facts(buffer, *l, subs, tense, out);
            collect_ground_facts(buffer, *r, subs, tense, out);
        }
        LogicNode::ExistsNode((v, body)) => {
            if subs.contains_key(v.as_str()) {
                collect_ground_facts(buffer, *body, subs, tense, out);
            }
        }
        LogicNode::PastNode(inner) => {
            collect_ground_facts(buffer, *inner, subs, Some("Past"), out);
        }
        LogicNode::PresentNode(inner) => {
            collect_ground_facts(buffer, *inner, subs, Some("Present"), out);
        }
        LogicNode::FutureNode(inner) => {
            collect_ground_facts(buffer, *inner, subs, Some("Future"), out);
        }
        LogicNode::ObligatoryNode(inner) | LogicNode::PermittedNode(inner) => {
            // Deontic wrappers are transparent — same as fact_repr path.
            collect_ground_facts(buffer, *inner, subs, tense, out);
        }
        _ => {
            if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                out.push(fact);
            }
        }
    }
}

/// Build a typed rule template fact from a LogicBuffer node.
/// `pattern_vars` maps variable names → pattern var names (e.g., "_v0" → "x__v0").
/// `ground_skolems` maps variable names → Skolem constant names.
/// `dependent_skolems` maps variable names → (base_name, [pattern_var_names]).
/// Like `build_rule_template_fact`, but also returns whether the atom was
/// originally under negation. Used for stratification tracking.
pub(super) fn build_rule_template_fact_with_negation(
    buffer: &LogicBuffer,
    node_id: u32,
    pattern_vars: &HashMap<String, String>,
    ground_skolems: &HashMap<String, String>,
    dependent_skolems: &HashMap<String, (String, Vec<String>)>,
) -> Option<(StoredFact, bool)> {
    let Ok(node) = get_node(buffer, node_id) else {
        return None;
    };
    match node {
        LogicNode::NotNode(inner_node) => {
            // Recurse into the negated body and mark as negated.
            build_rule_template_fact(
                buffer,
                *inner_node,
                pattern_vars,
                ground_skolems,
                dependent_skolems,
            )
            .map(|fact| (fact, true))
        }
        _ => build_rule_template_fact(
            buffer,
            node_id,
            pattern_vars,
            ground_skolems,
            dependent_skolems,
        )
        .map(|fact| (fact, false)),
    }
}

pub(super) fn build_rule_template_fact(
    buffer: &LogicBuffer,
    node_id: u32,
    pattern_vars: &HashMap<String, String>,
    ground_skolems: &HashMap<String, String>,
    dependent_skolems: &HashMap<String, (String, Vec<String>)>,
) -> Option<StoredFact> {
    let Ok(node) = get_node(buffer, node_id) else {
        return None;
    };
    match node {
        LogicNode::Predicate((rel, args)) | LogicNode::ComputeNode((rel, args)) => {
            let ground_args: Vec<GroundTerm> = args
                .iter()
                .map(|arg| match arg {
                    LogicalTerm::Variable(v) => {
                        if let Some(pvar) = pattern_vars.get(v.as_str()) {
                            GroundTerm::PatternVar(pvar.clone())
                        } else if let Some(sk) = ground_skolems.get(v.as_str()) {
                            GroundTerm::Constant(sk.clone())
                        } else if let Some((base, pvars)) = dependent_skolems.get(v.as_str()) {
                            let deps: Vec<GroundTerm> = pvars
                                .iter()
                                .map(|pv| GroundTerm::PatternVar(pv.clone()))
                                .collect();
                            build_skolem_fn_term(base, &deps)
                        } else {
                            GroundTerm::PatternVar(v.clone())
                        }
                    }
                    LogicalTerm::Constant(c) => GroundTerm::Constant(c.clone()),
                    LogicalTerm::Description(d) => GroundTerm::Description(d.clone()),
                    LogicalTerm::Unspecified => GroundTerm::Unspecified,
                    LogicalTerm::Number(n) => GroundTerm::from_f64(*n),
                })
                .collect();
            Some(StoredFact::Bare(GroundFact::new(rel.clone(), ground_args)))
        }
        LogicNode::ExistsNode((v, body)) => {
            // Skip Exists wrapper if variable is Skolemized or a pattern var
            if pattern_vars.contains_key(v.as_str())
                || ground_skolems.contains_key(v.as_str())
                || dependent_skolems.contains_key(v.as_str())
            {
                build_rule_template_fact(
                    buffer,
                    *body,
                    pattern_vars,
                    ground_skolems,
                    dependent_skolems,
                )
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Build a GroundTerm representing a SkolemFn with given dependencies.
pub(super) fn build_skolem_fn_term(base_name: &str, deps: &[GroundTerm]) -> GroundTerm {
    let dep_term = match deps.len() {
        0 => GroundTerm::Unspecified,
        1 => deps[0].clone(),
        _ => {
            // Right-nested DepPair encoding: [a, b, c] → DepPair(a, DepPair(b, c))
            let mut acc = deps.last().unwrap().clone();
            for dep in deps[..deps.len() - 1].iter().rev() {
                acc = GroundTerm::DepPair(Box::new(dep.clone()), Box::new(acc));
            }
            acc
        }
    };
    GroundTerm::SkolemFn(base_name.to_string(), Box::new(dep_term))
}
