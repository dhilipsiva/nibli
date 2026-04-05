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
    let Ok(node) = get_node(buffer, node_id) else { return };
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

pub(super) fn decompose_implication(
    buffer: &LogicBuffer,
    body_id: u32,
) -> Option<(Vec<u32>, u32)> {
    let mut conditions = Vec::new();
    let mut current = body_id;

    loop {
        let Ok(node) = get_node(buffer, current) else { break };
        match node {
            LogicNode::OrNode((left, right)) => {
                let Ok(left_node) = get_node(buffer, *left) else { break };
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
    let Ok(node) = get_node(buffer, node_id) else { return vec![node_id] };
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
    let Ok(node) = get_node(buffer, node_id) else { return };
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
    let Ok(node) = get_node(buffer, node_id) else { return vec![node_id] };
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
    let Ok(node) = get_node(buffer, node_id) else { return vec![node_id] };
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
    let Ok(node) = get_node(buffer, node_id) else { return };
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

/// Check the predicate dependency graph for negative cycles.
/// A negative cycle exists when a cycle in the graph contains at least one
/// edge marked as negative (from a negated condition). NAF is unsound in
/// the presence of negative cycles.
fn check_stratification(graph: &HashMap<String, Vec<(String, bool)>>) -> Result<(), String> {
    #[derive(Clone, Copy, PartialEq)]
    enum Color {
        White,
        Gray,
        Black,
    }

    let mut color: HashMap<&str, Color> = HashMap::new();
    // Track whether the path from root to this Gray node includes a negative edge.
    let mut neg_on_path: HashMap<&str, bool> = HashMap::new();

    fn dfs<'a>(
        node: &'a str,
        has_neg: bool,
        graph: &'a HashMap<String, Vec<(String, bool)>>,
        color: &mut HashMap<&'a str, Color>,
        neg_on_path: &mut HashMap<&'a str, bool>,
    ) -> Result<(), String> {
        color.insert(node, Color::Gray);
        neg_on_path.insert(node, has_neg);

        if let Some(edges) = graph.get(node) {
            for (dep, is_neg) in edges {
                let new_neg = has_neg || *is_neg;
                match color.get(dep.as_str()).copied().unwrap_or(Color::White) {
                    Color::Gray => {
                        // Back-edge → cycle found. Check if the cycle has any
                        // negative edge: either this edge is negative, or the
                        // path from dep to here already had one.
                        let dep_neg = neg_on_path.get(dep.as_str()).copied().unwrap_or(false);
                        let cycle_has_neg = *is_neg || (has_neg && !dep_neg);
                        if cycle_has_neg {
                            return Err(format!(
                                "Unstratifiable negation: cycle involving '{}' and \
                                 '{}' contains a negative dependency",
                                node, dep
                            ));
                        }
                    }
                    Color::Black => {} // already fully explored
                    Color::White => {
                        dfs(dep, new_neg, graph, color, neg_on_path)?;
                    }
                }
            }
        }

        color.insert(node, Color::Black);
        neg_on_path.remove(node);
        Ok(())
    }

    for node in graph.keys() {
        if color.get(node.as_str()).copied().unwrap_or(Color::White) == Color::White {
            dfs(node, false, graph, &mut color, &mut neg_on_path)?;
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
            PredicateSignature { arity, source },
        );
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

    // Check integrity constraints (permissive mode: warn, don't reject).
    if !inner.integrity_constraints.is_empty() && !inner.rebuilding {
        if let Some(violation) = check_constraints_for_predicate(&rel_owned, inner) {
            eprintln!("[Constraint] {}", violation);
        }
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
        let Ok(node) = get_node(buffer, current) else { return Ok(()) };
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

            let consequent_atoms = flatten_consequent(buffer, consequent_id, skolem_subs);

            let mut typed_conds: Vec<StoredFact> = Vec::new();
            let mut negated_condition_indices: Vec<usize> = Vec::new();
            for &cid in &all_conditions {
                if let Some((fact, is_negated)) = build_rule_template_fact_with_negation(
                    buffer, cid, &pattern_vars, &ground_skolems, &dependent_skolems,
                ) {
                    if is_negated {
                        negated_condition_indices.push(typed_conds.len());
                    }
                    typed_conds.push(fact);
                }
            }
            let typed_concls: Vec<StoredFact> = consequent_atoms
                .iter()
                .filter_map(|&aid| {
                    build_rule_template_fact(
                        buffer, aid, &pattern_vars, &ground_skolems, &dependent_skolems,
                    )
                })
                .collect();

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
                ) {
                    eprintln!("[Stratification Error] {}", e);
                    return Err(e);
                }

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
                    if let Some(fact) = build_stored_fact_from_node(buffer, cid, &xp_subs, None) {
                        assert_typed_fact(fact, inner);
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

            let typed_concls: Vec<StoredFact> = vec![inner_body_id]
                .iter()
                .filter_map(|&aid| {
                    build_rule_template_fact(
                        buffer, aid, &pattern_vars, &ground_skolems, &dependent_skolems,
                    )
                })
                .collect();

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
    let Ok(node) = get_node(buffer, node_id) else { return };
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
                    if let Some(fact) = build_stored_fact_from_node(buffer, *body, &typed_extra_subs, None) {
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
    let Ok(node) = get_node(buffer, node_id) else { return None };
    match node {
        LogicNode::Predicate((rel, args)) | LogicNode::ComputeNode((rel, args)) => {
            let ground_args: Vec<GroundTerm> = args
                .iter()
                .map(|a| build_ground_term(a, subs))
                .collect();
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
    let Ok(node) = get_node(buffer, node_id) else { return };
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
            build_rule_template_fact(buffer, *inner_node, pattern_vars, ground_skolems, dependent_skolems)
                .map(|fact| (fact, true))
        }
        _ => build_rule_template_fact(buffer, node_id, pattern_vars, ground_skolems, dependent_skolems)
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
    let Ok(node) = get_node(buffer, node_id) else { return None };
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
                build_rule_template_fact(buffer, *body, pattern_vars, ground_skolems, dependent_skolems)
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
