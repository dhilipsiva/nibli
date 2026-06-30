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

/// Prenex-normalize an OBJECT-POSITION universal. `ro lo gerku cu pendo ro lo
/// mlatu` ("every dog befriends every cat") lowers to
/// `Or(Not(gerku(x)), ForAll(y, Or(Not(mlatu(y)), <pendo>)))` — the inner `∀y`
/// sits in the CONSEQUENT of the outer `∀x` material conditional. Starting from a
/// rule body (after the leading `ForAll`s are stripped), this INTERLEAVES
/// `decompose_implication` (harvest `Or(Not(cond), rest)` conditions) with peeling
/// a nested `ForAll(y, body)` out of the resulting consequent, lifting each `y` +
/// its restrictor into the universals + conditions — producing the SAME
/// `(universals += [y], conditions = [gerku(x), mlatu(y)], consequent = <pendo>)`
/// the prenex form `ro da ro de zo'u …` yields. Sound: `∀x.(P → ∀y.(Q → R)) ≡
/// ∀x∀y.(P ∧ Q → R)` (y not free in P). Only a BARE `ForAllNode` consequent is
/// peeled — a `Count`/`Exists`/tense-wrapped consequent is left intact (it fails
/// closed downstream). A no-op for the existing single-universal and prenex
/// shapes (nothing nested to peel → returns `([], conditions, consequent)`).
/// Returns `(peeled universal vars outer→inner, condition node ids, final
/// consequent node id)`.
fn prenex_flatten(buffer: &LogicBuffer, body_id: u32) -> (Vec<String>, Vec<u32>, u32) {
    let mut extra_universals = Vec::new();
    let mut conditions = Vec::new();
    let mut current = body_id;
    loop {
        if let Some((conds, rest)) = decompose_implication(buffer, current) {
            conditions.extend(conds);
            current = rest;
        }
        if let Ok(LogicNode::ForAllNode((y, inner_body))) = get_node(buffer, current) {
            extra_universals.push(y.clone());
            current = *inner_body;
            continue;
        }
        break;
    }
    (extra_universals, conditions, current)
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
        // Descend tense/deontic wrappers so an event ∃ var living UNDER a tensed
        // condition (`poi pu broda` → `Past(Exists(ev, ...))`) is still
        // registered (and becomes a pattern var). Tense is irrelevant to WHICH
        // vars exist — just recurse.
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner)
        | LogicNode::ObligatoryNode(inner)
        | LogicNode::PermittedNode(inner) => {
            collect_condition_exists(buffer, *inner, exists_vars);
        }
        _ => {}
    }
}

/// Flatten an And-tree of condition atoms, descending condition-∃, tense wrappers,
/// AND deontic wrappers. Each returned leaf carries the tense accumulated on the
/// path to it (`Some("Past")` etc.), so a tensed antecedent atom (`poi pu broda` →
/// `Past(Exists(ev, And(broda(ev), broda_x1(ev, x))))`) flattens to tensed leaf
/// atoms instead of one opaque `Past(...)` node that would be rejected. Deontic
/// `Obligatory/Permitted` are descended TRANSPARENTLY (tense unchanged) — a deontic
/// antecedent compiles as its bare inner, matching the transparent-deontic
/// semantics (asserting `ei P` stores bare `P`).
pub(super) fn flatten_conjuncts_through_exists(
    buffer: &LogicBuffer,
    node_id: u32,
    condition_exists: &HashSet<String>,
    tense: Option<&'static str>,
) -> Vec<(u32, Option<&'static str>)> {
    let Ok(node) = get_node(buffer, node_id) else {
        return vec![(node_id, tense)];
    };
    match node {
        LogicNode::AndNode((l, r)) => {
            let mut result = flatten_conjuncts_through_exists(buffer, *l, condition_exists, tense);
            result.extend(flatten_conjuncts_through_exists(
                buffer,
                *r,
                condition_exists,
                tense,
            ));
            result
        }
        LogicNode::ExistsNode((v, body)) if condition_exists.contains(v.as_str()) => {
            flatten_conjuncts_through_exists(buffer, *body, condition_exists, tense)
        }
        LogicNode::PastNode(inner) => {
            flatten_conjuncts_through_exists(buffer, *inner, condition_exists, Some("Past"))
        }
        LogicNode::PresentNode(inner) => {
            flatten_conjuncts_through_exists(buffer, *inner, condition_exists, Some("Present"))
        }
        LogicNode::FutureNode(inner) => {
            flatten_conjuncts_through_exists(buffer, *inner, condition_exists, Some("Future"))
        }
        // Deontic wrappers (ei/e'e → Obligatory/Permitted) are transparent: descend
        // to the inner condition keeping tense unchanged, mirroring the assert path
        // (`collect_ground_facts`). Surface-unreachable today (attitudinals only wrap
        // whole bridi), so this is raw-FOL completeness, consistent with the documented
        // transparent-deontic semantics.
        LogicNode::ObligatoryNode(inner) | LogicNode::PermittedNode(inner) => {
            flatten_conjuncts_through_exists(buffer, *inner, condition_exists, tense)
        }
        _ => vec![(node_id, tense)],
    }
}

/// Upper bound on the number of conjunctive clauses a disjunctive antecedent may
/// DNF-expand to. A pathological `(A∨B)∧(C∨D)∧…` blows up combinatorially; cap it
/// and fail closed rather than register thousands of rules from one assertion.
pub(super) const MAX_DNF_CLAUSES: usize = 32;

/// Cross-product two clause lists (conjunction distributes over disjunction):
/// `{c1,c2} × {d1,d2}` → `{c1∪d1, c1∪d2, c2∪d1, c2∪d2}`. Deterministic (left
/// outer, right inner). Fails closed if the product would exceed `cap`.
fn dnf_cross_product(
    a: Vec<Vec<u32>>,
    b: &[Vec<u32>],
    cap: usize,
) -> Result<Vec<Vec<u32>>, String> {
    let count = a.len().saturating_mul(b.len());
    if count > cap {
        return Err(format!(
            "disjunctive rule antecedent expands to {count} conjunctive clauses, exceeding the \
             cap of {cap}; restate with fewer alternations (ja/ga) to keep rule compilation \
             bounded."
        ));
    }
    let mut out = Vec::with_capacity(count);
    for x in &a {
        for y in b {
            let mut clause = x.clone();
            clause.extend(y.iter().copied());
            out.push(clause);
        }
    }
    Ok(out)
}

/// DNF-expand a single condition node into a list of conjunctive clauses (each a
/// list of leaf node ids). `Or` → the union of its branches' clause lists; `And` →
/// the cross product; ANY other node (`Not`/`Exists`/tense/deontic/`Predicate`) →
/// a single one-leaf clause — NOT descended, so the per-clause pipeline
/// (`flatten_conjuncts_through_exists` + negated-exists-group detection +
/// deontic-strip + template building) handles it. Distributing under `Not`/`∃`
/// would be unsound, so those stay opaque. Deterministic (left-first); capped.
fn dnf_of_node(buffer: &LogicBuffer, id: u32, cap: usize) -> Result<Vec<Vec<u32>>, String> {
    match get_node(buffer, id) {
        Ok(LogicNode::OrNode((l, r))) => {
            let mut out = dnf_of_node(buffer, *l, cap)?;
            out.extend(dnf_of_node(buffer, *r, cap)?);
            if out.len() > cap {
                return Err(format!(
                    "disjunctive rule antecedent expands to {} conjunctive clauses, exceeding \
                     the cap of {cap}; restate with fewer alternations (ja/ga).",
                    out.len()
                ));
            }
            Ok(out)
        }
        Ok(LogicNode::AndNode((l, r))) => {
            let lc = dnf_of_node(buffer, *l, cap)?;
            let rc = dnf_of_node(buffer, *r, cap)?;
            dnf_cross_product(lc, &rc, cap)
        }
        _ => Ok(vec![vec![id]]),
    }
}

/// DNF-expand the antecedent condition forest into conjunctive clauses, conjoining
/// the top-level `condition_ids` and distributing `And` over `Or`. One clause for a
/// pure conjunction (byte-identical to the pre-split path), one clause per disjunct
/// for a disjunctive antecedent. Each clause is a list of condition LEAF node ids
/// with the `Or`s removed; the caller registers one backward-chaining rule per clause.
pub(super) fn dnf_condition_clauses(
    buffer: &LogicBuffer,
    condition_ids: &[u32],
    cap: usize,
) -> Result<Vec<Vec<u32>>, String> {
    let mut clauses: Vec<Vec<u32>> = vec![Vec::new()];
    for &cid in condition_ids {
        let node_clauses = dnf_of_node(buffer, cid, cap)?;
        clauses = dnf_cross_product(clauses, &node_clauses, cap)?;
    }
    Ok(clauses)
}

/// Detect a NEGATED event-decomposed restrictor condition `Not(Exists(ev, And-tree
/// of flat leaves))` (the antecedent shape of `ro lo X poi na <selbri> cu …`) and
/// return `(ev_var_name, leaf_node_ids)`. Returns `None` for any other shape — a
/// flat negated atom `Not(P)` (handled by `negated_condition_indices`), a
/// `Not(Or(..))`, a nested foreign quantifier, or a tensed inner — so the caller
/// stays fail-closed.
fn detect_negated_exists_group(buffer: &LogicBuffer, cond_id: u32) -> Option<(String, Vec<u32>)> {
    let LogicNode::NotNode(inner) = get_node(buffer, cond_id).ok()? else {
        return None;
    };
    let LogicNode::ExistsNode((ev, body)) = get_node(buffer, *inner).ok()? else {
        return None;
    };
    let mut leaves = Vec::new();
    if !flatten_group_leaves(buffer, *body, ev.as_str(), &mut leaves) || leaves.is_empty() {
        return None;
    }
    Some((ev.clone(), leaves))
}

/// Walk the inner conjunction of a negated existential group, collecting only flat
/// `Predicate`/`ComputeNode` leaf node ids. Descends `And` and the group's OWN
/// existential (`Exists(ev)`); any `Or`/`Not`/foreign quantifier/tense wrapper
/// returns `false`, so the whole group is rejected (fail-closed compilation
/// preserved — no under-conditioned rule is registered).
fn flatten_group_leaves(buffer: &LogicBuffer, id: u32, ev: &str, out: &mut Vec<u32>) -> bool {
    match get_node(buffer, id) {
        Ok(LogicNode::AndNode((l, r))) => {
            flatten_group_leaves(buffer, *l, ev, out) && flatten_group_leaves(buffer, *r, ev, out)
        }
        Ok(LogicNode::ExistsNode((v, b))) if v.as_str() == ev => {
            flatten_group_leaves(buffer, *b, ev, out)
        }
        Ok(LogicNode::Predicate(_)) | Ok(LogicNode::ComputeNode(_)) => {
            out.push(id);
            true
        }
        _ => false,
    }
}

/// Flatten the consequent to leaf atom node ids, descending skolemized `Exists` +
/// `And`, threading tense through `Past`/`Present`/`Future` wrappers (so a tensed
/// conclusion `→ pu Q` becomes a `StoredFact::Past` template via the same mechanism
/// as a tensed antecedent), and descending deontic `Obligatory`/`Permitted`
/// transparently (tense unchanged — this also flattens an event-decomposed deontic
/// conclusion that `build_rule_template_fact`'s deontic arm alone cannot reach
/// through the inner `And`). Each returned leaf carries the tense accumulated on the
/// path to it. A top-level `Or` is returned opaque (one leaf with its tense) — the
/// caller detects it for the disjunctive-conclusion-constraint path.
fn flatten_consequent(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, GroundTerm>,
    tense: Option<&'static str>,
) -> Vec<(u32, Option<&'static str>)> {
    let Ok(node) = get_node(buffer, node_id) else {
        return vec![(node_id, tense)];
    };
    match node {
        LogicNode::ExistsNode((v, body)) if skolem_subs.contains_key(v.as_str()) => {
            flatten_consequent(buffer, *body, skolem_subs, tense)
        }
        LogicNode::AndNode((l, r)) => {
            let mut result = flatten_consequent(buffer, *l, skolem_subs, tense);
            result.extend(flatten_consequent(buffer, *r, skolem_subs, tense));
            result
        }
        LogicNode::PastNode(inner) => flatten_consequent(buffer, *inner, skolem_subs, Some("Past")),
        LogicNode::PresentNode(inner) => {
            flatten_consequent(buffer, *inner, skolem_subs, Some("Present"))
        }
        LogicNode::FutureNode(inner) => {
            flatten_consequent(buffer, *inner, skolem_subs, Some("Future"))
        }
        LogicNode::ObligatoryNode(inner) | LogicNode::PermittedNode(inner) => {
            flatten_consequent(buffer, *inner, skolem_subs, tense)
        }
        _ => vec![(node_id, tense)],
    }
}

/// Flatten an `Or`-tree of a disjunctive conclusion into its branch node ids
/// (descending `Or`, collecting any non-`Or` node as one branch). `Or(A, B)` → `[A,
/// B]`; `Or(Or(A, B), C)` → `[A, B, C]`.
fn collect_disjunct_branches(buffer: &LogicBuffer, node_id: u32, out: &mut Vec<u32>) {
    match get_node(buffer, node_id) {
        Ok(LogicNode::OrNode((l, r))) => {
            collect_disjunct_branches(buffer, *l, out);
            collect_disjunct_branches(buffer, *r, out);
        }
        _ => out.push(node_id),
    }
}

/// Build the POSITIVE flat condition templates for one antecedent DNF clause — the
/// `P` of a disjunctive-conclusion constraint `¬(P ∧ ¬Q ∧ ¬R)`. Fails closed (v1) if
/// the clause carries a negated atom or a negated-exists group: "P holds" is checked
/// by store-membership in `check_contradictions`, which a negated/NAF antecedent
/// condition would not soundly support.
fn build_positive_clause_conditions(
    buffer: &LogicBuffer,
    clause: &[u32],
    pattern_vars: &HashMap<String, String>,
    ground_skolems: &HashMap<String, String>,
    dependent_skolems: &HashMap<String, (String, Vec<String>)>,
    rule_desc: &str,
) -> Result<Vec<StoredFact>, String> {
    let mut clause_exists: HashSet<String> = HashSet::new();
    for &lid in clause {
        collect_condition_exists(buffer, lid, &mut clause_exists);
    }
    let mut conds = Vec::new();
    for &lid in clause {
        for (cid, tense) in flatten_conjuncts_through_exists(buffer, lid, &clause_exists, None) {
            if detect_negated_exists_group(buffer, cid).is_some() {
                return Err(format!(
                    "cannot represent disjunctive conclusion for {rule_desc}: a negated \
                     restrictor in the antecedent is unsupported. Rejecting to preserve soundness."
                ));
            }
            match build_rule_template_fact_with_negation(
                buffer,
                cid,
                pattern_vars,
                ground_skolems,
                dependent_skolems,
                tense,
            ) {
                Some((fact, false)) => conds.push(fact),
                Some((_, true)) => {
                    return Err(format!(
                        "cannot represent disjunctive conclusion for {rule_desc}: a negated \
                         antecedent condition is unsupported. Rejecting to preserve soundness."
                    ));
                }
                None => {
                    return Err(format!(
                        "cannot represent disjunctive conclusion for {rule_desc}: an antecedent \
                         atom is not a flat predicate. Rejecting to preserve soundness."
                    ));
                }
            }
        }
    }
    Ok(conds)
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
    negated_exists_groups: Vec<NegatedExistsGroup>,
    forward: bool,
) -> Result<(), String> {
    // Each negated-exists group contributes one negative edge per inner condition
    // relation (added below alongside the flat-condition edges), so the rollback
    // must pop that many extra edges per conclusion.
    let group_edge_count: usize = negated_exists_groups
        .iter()
        .map(|g| g.conditions.len())
        .sum();

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
        // A negated event-decomposed restrictor (`poi na <selbri>`) reads its inner
        // conjuncts under negation-as-failure, so each is a NEGATIVE dependency: a
        // rule whose conclusion recurses through the negated existential (e.g.
        // `ro lo X poi na danlu cu danlu`) becomes a negative self-loop and is
        // rejected as unstratifiable by `check_stratification`.
        for group in &negated_exists_groups {
            for cond in &group.conditions {
                inner
                    .pred_dep_graph
                    .entry(concl_rel.clone())
                    .or_default()
                    .push((cond.relation().to_string(), true));
            }
        }
    }

    // Check stratification (skip during rebuild — same rules passed before).
    if !inner.rebuilding {
        if let Err(e) = check_stratification(&inner.pred_dep_graph) {
            // Rollback: remove the edges we just added.
            for concl in &typed_conclusions {
                let concl_rel = concl.relation();
                if let Some(edges) = inner.pred_dep_graph.get_mut(concl_rel) {
                    for _ in 0..(typed_conditions.len() + group_edge_count) {
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
        negated_exists_groups,
        forward,
        priority: 0, // Default priority; can be changed via set_rule_priority.
    };
    let rc = Arc::new(rule);
    let mut indexed = false;
    for concl in &rc.typed_conclusions {
        let bucket = inner
            .universal_rules
            .entry(concl.relation().to_string())
            .or_default();
        bucket.push(Arc::clone(&rc));
        // Keep the bucket descending-sorted by priority so the backward-chain
        // read path (`matching_rules_typed`) can borrow it without re-sorting.
        // (A new rule has priority 0, the minimum, so this is order-preserving
        // today; the explicit sort makes the invariant robust to future changes.)
        sort_rule_bucket(bucket);
        indexed = true;
    }
    if !indexed {
        let bucket = inner
            .universal_rules
            .entry("__fallback__".to_string())
            .or_default();
        bucket.push(rc.clone());
        sort_rule_bucket(bucket);
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

    // Populate the argument-position index only for a fact not already in the
    // store (the store is a HashSet, so this keeps the index consistent with it
    // — exactly one index entry per fact). Re-ingesting an identical ground fact
    // (e.g. compute auto-assert firing on every query) is then a no-op for the
    // index, not a duplicate append; duplicates would both grow the index
    // unboundedly and inflate `bind_join_vars_from_index`'s `matching.len() == 1`
    // uniqueness check, suppressing a valid join binding. `fact_store.insert` is
    // the only insert site, so "in the store" ⟺ "indexed". The leaf stays a Vec
    // in insertion order (the consumer iterates it; output determinism depends on
    // that order).
    let gf = fact.inner();
    if !inner.fact_store.contains(&fact) {
        for (pos, arg) in gf.args.iter().enumerate() {
            inner
                .arg_position_index
                .entry((gf.relation.clone(), pos))
                .or_default()
                .entry(arg.clone())
                .or_default()
                .push(fact.clone());
        }
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
    clear_typed_pred_cache(inner);

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
    // FAIL CLOSED: a NAF-bearing rule (a flat negated condition or a `poi na
    // <selbri>` group) must never forward-fire — a forward-derived conclusion would
    // go stale when a later assertion makes the negated dependency true, and there
    // is no truth maintenance to retract it. `set_rule_forward` refuses to enable
    // these, but exclude them here too so the invariant holds regardless of how
    // `forward` was set; they stay sound via backward chaining (re-evaluates `¬Q`
    // at query time).
    let mut forward_rules: Vec<Arc<UniversalRuleRecord>> = inner
        .universal_rules
        .values()
        .flat_map(|v| v.iter())
        .filter(|r| {
            r.forward
                && r.negated_condition_indices.is_empty()
                && r.negated_exists_groups.is_empty()
                && r.typed_conditions.iter().any(|c| c.relation() == new_rel)
        })
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
                // A NAF-bearing rule is excluded by the filter above (kept
                // backward-only — forward chaining + NAF has no truth maintenance), so
                // the negated branch here is dead for forward firing; retained as
                // defensive code (a forwarded rule has no negated indices).
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

    // Determinism: `to_derive` is built from a `lookup_predicate` HashSet clone,
    // so its order (driving the `[Forward] Derived:` print + the assertion order)
    // is otherwise hasher-seed dependent. Sort by canonical display — the SET of
    // derived facts is unchanged (forward chaining is monotonic). This also makes
    // the output independent of the equal-priority `forward_rules` tie-break.
    to_derive.sort_by(|a, b| a.to_display_string().cmp(&b.to_display_string()));

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

/// Register ONE backward-chaining rule for a single DNF clause of a (possibly
/// disjunctive) rule antecedent. The clause-independent work (consequent templates
/// `typed_concls`, universals, pattern vars, and the precise `dependent_skolems`)
/// is computed once by the caller and passed in; this builds the clause's condition
/// templates, dedups, registers, and (for `branch_idx == 0`) asserts the xorlo
/// presupposition. Returns `Err` (fail-closed, aborting the whole assertion) on any
/// untemplatable condition atom or stratification violation.
#[allow(clippy::too_many_arguments)]
fn register_clause_rule(
    buffer: &LogicBuffer,
    clause: &[u32],
    branch_idx: usize,
    clause_count: usize,
    universals: &[String],
    pattern_vars: &HashMap<String, String>,
    pattern_var_names: &[String],
    ground_skolems: &HashMap<String, String>,
    dependent_skolems: &HashMap<String, (String, Vec<String>)>,
    typed_concls: &[StoredFact],
    rule_desc: &str,
    inner: &mut KnowledgeBaseInner,
) -> Result<(), String> {
    // This clause's own condition ∃ vars (sorted → deterministic pattern-var order),
    // a subset of the caller's union. Drives which `Exists` flatten descends and the
    // clause's event pattern-var list.
    let clause_exists: Vec<String> = {
        let mut s: HashSet<String> = HashSet::new();
        for &lid in clause {
            collect_condition_exists(buffer, lid, &mut s);
        }
        let mut v: Vec<String> = s.into_iter().collect();
        v.sort();
        v
    };
    let clause_exists_set: HashSet<String> = clause_exists.iter().cloned().collect();

    let all_pattern_var_names: Vec<String> = {
        let mut names = pattern_var_names.to_vec();
        for var in &clause_exists {
            if let Some(pvar) = pattern_vars.get(var) {
                names.push(pvar.clone());
            }
        }
        names
    };

    let mut all_conditions: Vec<(u32, Option<&str>)> = Vec::new();
    for &lid in clause {
        all_conditions.extend(flatten_conjuncts_through_exists(
            buffer,
            lid,
            &clause_exists_set,
            None,
        ));
    }

    let mut typed_conds: Vec<StoredFact> = Vec::new();
    let mut negated_condition_indices: Vec<usize> = Vec::new();
    let mut negated_exists_groups: Vec<NegatedExistsGroup> = Vec::new();
    for &(cid, tense) in &all_conditions {
        // A NEGATED event-decomposed restrictor `Not(Exists(ev, And(..)))`
        // (`poi na <selbri>`) is compiled as a NAF-over-existential group, NOT a flat
        // condition: collect the inner conjuncts as templates with the universal's
        // `x__vN` (shared) and a group-local event pvar. It is excluded from
        // `typed_conditions` AND from the xorlo presupposition (a `poi na zanru`
        // person must NOT get an asserted consent witness).
        if let Some((ev_var, leaf_ids)) = detect_negated_exists_group(buffer, cid) {
            let ev_pvar = format!("ev__{}", ev_var);
            let mut group_pattern_vars: HashMap<String, String> = pattern_vars.clone();
            group_pattern_vars.insert(ev_var.clone(), ev_pvar.clone());
            let mut group_conditions = Vec::new();
            for &lid in &leaf_ids {
                match build_rule_template_fact(
                    buffer,
                    lid,
                    &group_pattern_vars,
                    ground_skolems,
                    dependent_skolems,
                    None,
                ) {
                    Some(f) => group_conditions.push(f),
                    None => {
                        return Err(format!(
                            "cannot compile negated restrictor group for {rule_desc}: an \
                             inner atom is not a flat predicate. Rejecting the assertion \
                             to preserve soundness."
                        ));
                    }
                }
            }
            negated_exists_groups.push(NegatedExistsGroup {
                conditions: group_conditions,
                event_var: ev_pvar,
            });
            continue;
        }
        match build_rule_template_fact_with_negation(
            buffer,
            cid,
            pattern_vars,
            ground_skolems,
            dependent_skolems,
            tense,
        ) {
            Some((fact, is_negated)) => {
                if is_negated {
                    negated_condition_indices.push(typed_conds.len());
                }
                typed_conds.push(fact);
            }
            // FAIL CLOSED: an antecedent atom we cannot represent as a flat
            // backward-chaining template (a tense wrapper, nested quantifier, or
            // negated-complex form) would otherwise be silently dropped — leaving an
            // UNDER-CONDITIONED rule that fires when it should not. (Disjunction is now
            // handled by DNF rule-splitting; deontic wrappers are transparently
            // stripped.) Reject the assertion instead.
            None => {
                return Err(format!(
                    "cannot compile rule antecedent for {rule_desc}: an atom is not a \
                     flat predicate (tense, nested quantifier, or negated-complex \
                     antecedents are unsupported). Rejecting the assertion to preserve \
                     soundness rather than registering an under-conditioned rule."
                ));
            }
        }
    }

    let dedup_key = rule_dedup_hash(0, &typed_conds, typed_concls);
    if !inner.known_rules.insert(dedup_key) {
        if inner.diag_enabled() {
            println!("[Rule] ∀{} already present, skipping", universals.join(","));
        }
        return Ok(());
    }
    if inner.diag_enabled() {
        println!(
            "[Rule] Compiled ∀{} to backward-chaining rule",
            universals.join(",")
        );
    }

    let base_label = build_typed_rule_label(&typed_conds, typed_concls);
    let label = if clause_count > 1 {
        format!(
            "[branch {}/{}] {}",
            branch_idx + 1,
            clause_count,
            base_label
        )
    } else {
        base_label
    };
    if let Err(e) = register_rule(
        inner,
        label,
        all_pattern_var_names,
        typed_conds,
        typed_concls.to_vec(),
        negated_condition_indices,
        negated_exists_groups,
        false, // forward chaining disabled by default
    ) {
        eprintln!("[Stratification Error] {}", e);
        return Err(e);
    }

    // xorlo presupposition applies ONLY to DESCRIPTION universals (`ro lo` / `ro le`),
    // which carry existential import — "there is such a thing" — so a fresh witness
    // satisfying the restrictor is asserted. Asserted ONCE, for branch 0 only: for a
    // disjunctive antecedent the import only needs the restricted domain non-empty, so
    // a witness for the FIRST disjunct is a sound minimal choice (asserting every
    // branch would over-commit, injecting a witness for each disjunct the author never
    // stated). It must NOT fire for a ground material conditional (zero universals) or
    // a PRENEX universal (`ro da zo'u …`, no existential import). smuni names
    // description universals `_v{n}` and prenex universals `da`/`de`/`di`.
    let is_description_universal =
        !universals.is_empty() && universals.iter().all(|v| v.starts_with("_v"));
    if branch_idx == 0 && is_description_universal {
        // One FRESH witness PER universal. `ro lo gerku cu pendo ro lo mlatu`
        // presupposes ≥1 dog AND ≥1 cat as DISTINCT entities; a single shared
        // witness would assert `gerku(xp) ∧ mlatu(xp)` — a phantom dog-cat (an
        // unsoundness reachable only once object-position multi-`_v`-universal
        // rules compile). Behavior-identical for the single-universal case (one
        // universal → one witness).
        let mut xp_subs: HashMap<String, GroundTerm> = HashMap::new();
        for v in universals {
            let xp_name = inner.fresh_skolem();
            inner.note_entity(&xp_name);
            xp_subs.insert(v.clone(), GroundTerm::Constant(xp_name));
        }
        for (k, v) in ground_skolems {
            xp_subs
                .entry(k.clone())
                .or_insert_with(|| GroundTerm::Constant(v.clone()));
        }
        for var in &clause_exists {
            let ev_sk = inner.fresh_skolem();
            if var.starts_with("_ev") {
                inner.note_event_entity(&ev_sk);
            } else {
                inner.note_entity(&ev_sk);
            }
            xp_subs.insert(var.clone(), GroundTerm::Constant(ev_sk));
        }
        for &(cid, tense) in &all_conditions {
            if let Some(fact) = build_stored_fact_from_node(buffer, cid, &xp_subs, tense) {
                assert_typed_fact(fact, inner);
            }
        }
    }

    Ok(())
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
            // FAIL CLOSED: a tense (pu/ca/ba) or deontic attitudinal (ei/e'e)
            // wrapping a WHOLE universal/conditional rule (`pu ro lo gerku cu
            // danlu` → Past(ForAll(...))) cannot be soundly represented as a
            // timeless backward-chaining rule. Stripping it (the old behavior)
            // compiled the rule TIMELESS, so it fired on present/future/bare
            // facts the tensed input never licensed — an over-claim. The engine
            // has no interval/modal temporal semantics to thread whole-rule tense
            // or modality, so reject rather than register an over-general rule.
            //
            // A tensed ANTECEDENT (`ro lo gerku poi pu citka cu xagji` →
            // ForAll(_, Or(Not(Past(...)), ...))) keeps its tense INSIDE the Or's
            // Not, off this spine; the loop breaks at the Or via the `_` arm
            // below, so the per-condition tense threading
            // (`flatten_conjuncts_through_exists` + `build_rule_template_fact`)
            // still handles it. This rejection only fires for a tense/deontic
            // node ON the spine, i.e. wrapping the whole rule.
            LogicNode::PastNode(_)
            | LogicNode::PresentNode(_)
            | LogicNode::FutureNode(_)
            | LogicNode::ObligatoryNode(_)
            | LogicNode::PermittedNode(_) => {
                return Err("cannot compile a tense (pu/ca/ba) or deontic (ei/e'e) \
                     wrapping a whole universal/conditional rule: a timeless \
                     backward-chaining rule cannot carry whole-rule tense or \
                     modality without over-claiming on untensed facts. Rejecting \
                     the assertion to preserve soundness; restate the \
                     temporal/deontic scope on the relevant predicate instead."
                    .to_string());
            }
            _ => break,
        }
    }
    let inner_body_id = current;

    // Prenex-flatten an OBJECT-POSITION universal (`ro lo gerku cu pendo ro lo
    // mlatu`): lift a nested `∀y` + its restrictor from the consequent into the
    // rule's universals + conditions, producing the SAME rule the prenex
    // `ro da ro de zo'u …` form does. A no-op for single-universal / prenex
    // shapes. `pattern_vars` etc. below are then built from the COMPLETE
    // `universals`, and the DepPair connected-component gives the conclusion
    // event-Skolem `dep_count 2` (co-occurs with x AND y).
    let (extra_universals, pf_conditions, pf_consequent) = prenex_flatten(buffer, inner_body_id);
    universals.extend(extra_universals);

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

    let implication = if pf_conditions.is_empty() {
        None
    } else {
        Some((pf_conditions, pf_consequent))
    };
    match implication {
        Some((condition_ids, consequent_id)) => {
            // DNF-split the antecedent into conjunctive clauses and register ONE
            // backward-chaining rule per clause: `∀x.(P(x)∨Q(x))→R(x)` is the
            // conjunction of `∀x.P(x)→R(x)` and `∀x.Q(x)→R(x)`. A pure conjunction
            // yields a single clause (byte-identical to the pre-split path); a
            // disjunctive antecedent (`ro lo X poi P ja Q cu R`, `ganai ga P gi Q gi R`)
            // yields one clause per disjunct.
            let clauses = dnf_condition_clauses(buffer, &condition_ids, MAX_DNF_CLAUSES)?;

            // The condition event ∃ vars across ALL clauses become pattern vars (not
            // skolems); what remains in `dependent_skolems` are the CONCLUSION
            // existentials, shared by every clause. (collect_condition_exists does not
            // descend `Or`, so this union mirrors the pre-split single-condition set.)
            let mut all_condition_exists: HashSet<String> = HashSet::new();
            for clause in &clauses {
                for &lid in clause {
                    collect_condition_exists(buffer, lid, &mut all_condition_exists);
                }
            }
            for var in &all_condition_exists {
                dependent_skolems.remove(var);
                ground_skolems.remove(var);
                let pvar = format!("ev__{}", var);
                pattern_vars.insert(var.clone(), pvar);
            }

            let mut consequent_atoms = flatten_consequent(buffer, consequent_id, skolem_subs, None);

            // DISJUNCTIVE CONCLUSION: a top-level `Or` consequent atom is not a Horn
            // clause (deriving a disjunct would be unsound), so it is registered as the
            // integrity constraint `¬(P ∧ ¬Q ∧ ¬R)` — `check_contradictions` flags it
            // when P holds and every disjunct is explicitly denied (`na`); the positive
            // use is a disjunctive QUERY. A MIXED head `∀x. P → (A ∧ (Q∨R))` SPLITS:
            // `≡ [∀x.P→A]` (the Horn conclusion A, registered by the fall-through below)
            // `∧ [∀x.P→(Q∨R)]` (this constraint). So register a constraint per Or atom,
            // then keep the non-Or atoms for the Horn path. `dependent_skolems` still
            // carries the over-approximated deps here (DepPair precision runs after this)
            // — fine, the disjunct templates only ever unify against `na` groups, never
            // fired, and the event term is existential on both sides.
            let or_atom_ids: Vec<u32> = consequent_atoms
                .iter()
                .filter(|&&(aid, _)| matches!(get_node(buffer, aid), Ok(LogicNode::OrNode(_))))
                .map(|&(aid, _)| aid)
                .collect();
            if !or_atom_ids.is_empty() {
                for &or_id in &or_atom_ids {
                    let mut branches = Vec::new();
                    collect_disjunct_branches(buffer, or_id, &mut branches);
                    let mut disjuncts: Vec<Vec<StoredFact>> = Vec::new();
                    for &br in &branches {
                        let mut leaves = Vec::new();
                        for (aid, tense) in flatten_consequent(buffer, br, skolem_subs, None) {
                            match build_rule_template_fact(
                                buffer,
                                aid,
                                &pattern_vars,
                                &ground_skolems,
                                &dependent_skolems,
                                tense,
                            ) {
                                Some(fact) => leaves.push(fact),
                                None => {
                                    return Err(format!(
                                        "cannot represent disjunctive conclusion for {rule_desc}: \
                                         a disjunct atom is not a flat predicate. Rejecting to \
                                         preserve soundness."
                                    ));
                                }
                            }
                        }
                        disjuncts.push(leaves);
                    }
                    // One constraint per antecedent DNF clause (a disjunctive antecedent
                    // splits P into clauses, exactly as the rule path does).
                    for clause in &clauses {
                        let conditions = build_positive_clause_conditions(
                            buffer,
                            clause,
                            &pattern_vars,
                            &ground_skolems,
                            &dependent_skolems,
                            &rule_desc,
                        )?;
                        let cond_label = conditions
                            .iter()
                            .map(|c| c.relation().to_string())
                            .collect::<Vec<_>>()
                            .join(" ∧ ");
                        let disj_label = disjuncts
                            .iter()
                            .map(|d| {
                                d.iter()
                                    .map(|f| f.relation().to_string())
                                    .collect::<Vec<_>>()
                                    .join(" ∧ ")
                            })
                            .collect::<Vec<_>>()
                            .join(" ∨ ");
                        inner.disjunctive_constraints.push(DisjunctiveConstraint {
                            label: format!("{cond_label} → {disj_label}"),
                            conditions,
                            disjuncts: disjuncts.clone(),
                        });
                    }
                }
                // Record the assertion id so retracting a (possibly skolem-free)
                // disjunctive conclusion triggers a rebuild that drops the constraint.
                if let Some(aid) = inner.current_assertion_id {
                    inner.rule_source_map.entry(aid).or_default();
                }
                if inner.diag_enabled() {
                    println!(
                        "[Constraint] Registered disjunctive conclusion {} as ¬(P ∧ ¬Q ∧ ¬R)",
                        rule_desc
                    );
                }
                // Keep only the non-Or atoms for the Horn path. A PURE disjunctive head
                // has none (done); a MIXED `And(P, Or)` head registers P below.
                consequent_atoms
                    .retain(|&(aid, _)| !matches!(get_node(buffer, aid), Ok(LogicNode::OrNode(_))));
                if consequent_atoms.is_empty() {
                    return Ok(());
                }
                // MIXED head: drop the Or-part's conclusion existentials from
                // `dependent_skolems` — they appear ONLY in the Or subtree (a fresh
                // `_evN` per operand), so without this they would DepPair-refine to
                // dep_count 0 and register spurious entries into the GLOBAL
                // skolem_fn_registry (polluting `members^k` witness enumeration for
                // unrelated queries). The constraint templates above already captured
                // them with the over-approximated deps. No-op for a pure-conjunction
                // head (every conclusion existential appears in a retained atom).
                let retained_vars: HashSet<String> = consequent_atoms
                    .iter()
                    .flat_map(|&(aid, _)| atom_var_args(buffer, aid))
                    .collect();
                dependent_skolems.retain(|k, _| retained_vars.contains(k));
            }

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
            for &(aid, _) in &consequent_atoms {
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

            // Conclusion templates are clause-independent — build + validate once.
            // Each leaf carries its own tense (threaded by `flatten_consequent`), so a
            // tensed conclusion (`ganai A gi pu B` → `Past(B)`) becomes a `Past` template.
            let mut typed_concls: Vec<StoredFact> = Vec::new();
            for &(aid, tense) in &consequent_atoms {
                match build_rule_template_fact(
                    buffer,
                    aid,
                    &pattern_vars,
                    &ground_skolems,
                    &dependent_skolems,
                    tense,
                ) {
                    Some(fact) => typed_concls.push(fact),
                    None => {
                        return Err(format!(
                            "cannot compile rule conclusion for {rule_desc}: a consequent \
                             atom is not a flat predicate. Rejecting the assertion to \
                             preserve soundness."
                        ));
                    }
                }
            }

            // One rule per DNF clause; all clauses share the consequent + universals
            // + dependent-Skolem analysis, only the conditions differ.
            let clause_count = clauses.len();
            for (branch_idx, clause) in clauses.iter().enumerate() {
                register_clause_rule(
                    buffer,
                    clause,
                    branch_idx,
                    clause_count,
                    &universals,
                    &pattern_vars,
                    &pattern_var_names,
                    &ground_skolems,
                    &dependent_skolems,
                    &typed_concls,
                    &rule_desc,
                    inner,
                )?;
            }
        }
        None => {
            // BARE-UNIVERSAL branch: a restrictor-less ∀ (a bare prenex
            // `ro da zo'u da broda`, no `lo`/`le` gadri). Unlike the implication
            // branch above, it asserts NO xorlo presupposition witness — and that
            // is correct: a prenex `ro da`/`de`/`di` is a plain logical universal
            // with no existential import (vacuously true on an empty domain),
            // whereas the DESCRIPTION universals that carry import (`ro lo`/`ro le`,
            // smuni-named `_v{n}`) ALWAYS compile to `∀x. R(x) → C(x)` and route
            // through `register_clause_rule`, whose `is_description_universal` guard
            // asserts the witness. So a description universal never reaches here.
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
                pf_consequent,
                &pattern_vars,
                &ground_skolems,
                &dependent_skolems,
                None, // conclusions stay bare (tensed conclusions out of scope)
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
                if inner.diag_enabled() {
                    println!(
                        "[Rule] bare ∀{} already present, skipping",
                        universals.join(",")
                    );
                }
            } else {
                if inner.diag_enabled() {
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
                    vec![], // bare universal — no negated-exists groups
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
        LogicNode::ObligatoryNode(inner) => {
            // Deontic context is preserved (mirrors the tense arms) so the leaf becomes a
            // `StoredFact::Obligatory`. Reached only via a direct deontic node — the
            // assert (collect_ground_facts) and query (reasoning.rs) paths strip the
            // wrapper first; kept here so the "deontic is opaque" invariant is uniform.
            build_stored_fact_from_node(buffer, *inner, subs, Some("Obligatory"))
        }
        LogicNode::PermittedNode(inner) => {
            build_stored_fact_from_node(buffer, *inner, subs, Some("Permitted"))
        }
        _ => None, // And/Or/Not/ForAll/Count — not a leaf fact.
    }
}

/// Collect leaf StoredFacts from an And-tree (the typed structural walk that
/// flattens a conjunction down to its ground leaf facts).
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
            // Abstraction opacity: `And(__abs_<hash>(referent), body)` — collect the
            // marker (its content identity matters) but SKIP the body so its inner
            // predicates never become free-standing ground facts.
            if is_abstraction_marker(buffer, *l) {
                collect_ground_facts(buffer, *l, subs, tense, out);
            } else {
                collect_ground_facts(buffer, *l, subs, tense, out);
                collect_ground_facts(buffer, *r, subs, tense, out);
            }
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
        LogicNode::ObligatoryNode(inner) => {
            // Deontic context is preserved (mirrors the tense arms): a ground `ei`
            // fact is stored as `StoredFact::Obligatory`, kept distinct from actuality.
            collect_ground_facts(buffer, *inner, subs, Some("Obligatory"), out);
        }
        LogicNode::PermittedNode(inner) => {
            collect_ground_facts(buffer, *inner, subs, Some("Permitted"), out);
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
    tense: Option<&str>,
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
                tense,
            )
            .map(|fact| (fact, true))
        }
        _ => build_rule_template_fact(
            buffer,
            node_id,
            pattern_vars,
            ground_skolems,
            dependent_skolems,
            tense,
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
    tense: Option<&str>,
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
            // Carry the antecedent's tense (threaded from the flatten walk) so a
            // tensed condition becomes a `StoredFact::Past/Present/Future` template
            // that unify_facts matches only against the same-tense stored fact.
            Some(StoredFact::with_tense(
                GroundFact::new(rel.clone(), ground_args),
                tense,
            ))
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
                    tense,
                )
            } else {
                None
            }
        }
        // Deontic wrappers are transparent — descend to the inner atom (mirrors the
        // assert path `build_stored_fact_from_node`). Handles a flat or `Not(..)`-wrapped
        // deontic antecedent atom; the And/∃ case is pre-stripped by
        // `flatten_conjuncts_through_exists`.
        LogicNode::ObligatoryNode(inner) | LogicNode::PermittedNode(inner) => {
            build_rule_template_fact(
                buffer,
                *inner,
                pattern_vars,
                ground_skolems,
                dependent_skolems,
                tense,
            )
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

#[cfg(test)]
mod stratification_conformance {
    //! Bridge from the mechanized criterion proof (`proofs/Stratification.lean`) to the real
    //! Tarjan-based check. `proofs/Stratification.lean` PROVES the criterion — "no negative edge
    //! whose target reaches back to its source" ⟺ a valid stratification exists. Here we check
    //! that the production `check_stratification` (which decides that via `compute_sccs`) agrees
    //! with a naive reachability implementation of the *same* criterion, over a corpus of
    //! hand-crafted + deterministically-randomized graphs. Honest scope: graphs are unbounded, so
    //! this is a corpus conformance test (not exhaustive, unlike the finite combiner), and it
    //! conformance-tests `compute_sccs` rather than proving it.

    use super::*;
    use std::collections::{BTreeSet, HashSet};

    /// Reachable-set per node (reflexive-transitive closure of the edges, ignoring sign),
    /// computed by a naive fixpoint — the independent reference for "tgt reaches src".
    fn reachable_sets(
        graph: &HashMap<String, Vec<(String, bool)>>,
    ) -> HashMap<String, HashSet<String>> {
        let mut nodes: BTreeSet<String> = BTreeSet::new();
        for (k, edges) in graph {
            nodes.insert(k.clone());
            for (d, _) in edges {
                nodes.insert(d.clone());
            }
        }
        let mut reach: HashMap<String, HashSet<String>> = nodes
            .iter()
            .map(|n| (n.clone(), HashSet::from([n.clone()])))
            .collect();
        let mut changed = true;
        while changed {
            changed = false;
            for u in &nodes {
                let Some(edges) = graph.get(u) else { continue };
                let mut additions: Vec<String> = Vec::new();
                for (v, _) in edges {
                    if let Some(rv) = reach.get(v) {
                        additions.extend(rv.iter().cloned());
                    }
                }
                let ru = reach.get_mut(u).unwrap();
                for w in additions {
                    if ru.insert(w) {
                        changed = true;
                    }
                }
            }
        }
        reach
    }

    /// Naive criterion: stratifiable iff NO negative edge `u → v` has `v` reaching `u`.
    /// (An edge already gives `u` reaches `v`, so "v reaches u" ⟺ same SCC.) Mirrors the Lean
    /// `RejectsByCriterion` / `NoNegCycle`.
    fn stratifiable_naive(graph: &HashMap<String, Vec<(String, bool)>>) -> bool {
        let reach = reachable_sets(graph);
        for (u, edges) in graph {
            for (v, is_neg) in edges {
                if *is_neg && reach.get(v).is_some_and(|rv| rv.contains(u)) {
                    return false;
                }
            }
        }
        true
    }

    fn graph_of(edges: &[(&str, &str, bool)]) -> HashMap<String, Vec<(String, bool)>> {
        let mut g: HashMap<String, Vec<(String, bool)>> = HashMap::new();
        for (u, v, neg) in edges {
            g.entry(u.to_string())
                .or_default()
                .push((v.to_string(), *neg));
        }
        g
    }

    /// Deterministic small pseudo-random graph (LCG seeded by `seed`); used for differential
    /// coverage beyond the hand-crafted cases — includes self-loops, cycles, and negative cycles.
    fn pseudo_random_graph(seed: u64, num_nodes: usize) -> HashMap<String, Vec<(String, bool)>> {
        let mut state = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let mut next = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            state >> 33
        };
        let names: Vec<String> = (0..num_nodes).map(|i| format!("p{i}")).collect();
        let mut g: HashMap<String, Vec<(String, bool)>> = HashMap::new();
        for u in 0..num_nodes {
            for v in 0..num_nodes {
                if next() % 5 < 2 {
                    let is_neg = next() % 2 == 0;
                    g.entry(names[u].clone())
                        .or_default()
                        .push((names[v].clone(), is_neg));
                }
            }
        }
        g
    }

    /// The real Tarjan-based `check_stratification` must agree with the naive criterion
    /// (proven correct in `proofs/Stratification.lean`) on every corpus graph.
    #[test]
    fn check_stratification_matches_proven_criterion() {
        let mut corpus: Vec<(String, HashMap<String, Vec<(String, bool)>>)> = vec![
            ("empty".into(), graph_of(&[])),
            ("neg_self_loop".into(), graph_of(&[("a", "a", true)])),
            ("pos_self_loop".into(), graph_of(&[("a", "a", false)])),
            (
                "positive_cycle".into(),
                graph_of(&[("a", "b", false), ("b", "c", false), ("c", "a", false)]),
            ),
            (
                "neg_cycle".into(),
                graph_of(&[("a", "b", true), ("b", "c", true), ("c", "b", false)]),
            ),
            (
                "stratified_with_negation".into(),
                graph_of(&[("a", "b", true), ("b", "c", false)]),
            ),
            (
                "neg_edge_into_cycle_ok".into(),
                // a negative edge feeding INTO a positive cycle (but not inside it) is fine.
                graph_of(&[("x", "a", true), ("a", "b", false), ("b", "a", false)]),
            ),
            (
                "dag".into(),
                graph_of(&[("a", "b", true), ("a", "c", false), ("b", "d", true)]),
            ),
        ];
        // Deterministic randomized small graphs for differential coverage.
        for seed in 0u64..300 {
            let num_nodes = 2 + (seed as usize % 4); // 2..=5 nodes
            corpus.push((
                format!("rand_seed{seed}_n{num_nodes}"),
                pseudo_random_graph(seed, num_nodes),
            ));
        }

        let mut checked = 0usize;
        for (name, g) in &corpus {
            let check_ok = check_stratification(g).is_ok();
            let naive_ok = stratifiable_naive(g);
            assert_eq!(
                check_ok, naive_ok,
                "check_stratification disagreed with the proven criterion on '{name}': \
                 check_ok={check_ok}, naive_ok={naive_ok}, graph={g:?}"
            );
            checked += 1;
        }
        assert!(
            checked >= 300,
            "corpus too small ({checked}); gate near-vacuous"
        );
    }
}
