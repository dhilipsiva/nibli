use super::*;

pub(super) fn wrap_with_tense(tense: Option<&str>, sexp: &str) -> String {
    match tense {
        Some(t) => format!("({} {})", t, sexp),
        None => sexp.to_string(),
    }
}

pub(super) fn check_formula_holds(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
) -> Result<bool, String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => Ok(check_formula_holds(buffer, *l, subs, inner, tense)?
            && check_formula_holds(buffer, *r, subs, inner, tense)?),
        LogicNode::OrNode((l, r)) => Ok(check_formula_holds(buffer, *l, subs, inner, tense)?
            || check_formula_holds(buffer, *r, subs, inner, tense)?),
        LogicNode::NotNode(inner_node) => Ok(!check_formula_holds(
            buffer,
            *inner_node,
            subs,
            inner,
            tense,
        )?),
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
            let members: Vec<(String, LogicalTerm)> = inner.all_domain_members().to_vec();
            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) =
                    batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner)
                {
                    if batch_results.iter().any(|r| *r) {
                        return Ok(true);
                    }
                }
            }
            let v_key = v.clone();
            let prev = subs.remove(&v_key);
            for (member_sexp, _) in &members {
                subs.insert(v_key.clone(), member_sexp.clone());
                if check_formula_holds(buffer, *body, subs, inner, tense)? {
                    match prev {
                        Some(p) => {
                            subs.insert(v_key, p);
                        }
                        None => {
                            subs.remove(&v_key);
                        }
                    }
                    return Ok(true);
                }
            }
            let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
            for entry in &entries {
                let dep_sexps: Vec<String> = members.iter().map(|(s, _)| s.clone()).collect();
                for combo in CartesianProduct::new(&dep_sexps, entry.dep_count) {
                    let witness_sexp = build_skolem_fn_sexp(&entry.base_name, &combo);
                    subs.insert(v_key.clone(), witness_sexp);
                    if check_formula_holds(buffer, *body, subs, inner, tense)? {
                        match prev {
                            Some(p) => {
                                subs.insert(v_key, p);
                            }
                            None => {
                                subs.remove(&v_key);
                            }
                        }
                        return Ok(true);
                    }
                }
            }
            match prev {
                Some(p) => {
                    subs.insert(v_key, p);
                }
                None => {
                    subs.remove(&v_key);
                }
            }
            Ok(false)
        }
        LogicNode::ForAllNode((v, body)) => {
            let members: Vec<(String, LogicalTerm)> = inner.all_domain_members().to_vec();
            if members.is_empty() {
                return Ok(true);
            }
            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) =
                    batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner)
                {
                    return Ok(batch_results.iter().all(|r| *r));
                }
            }
            let v_key = v.clone();
            let prev = subs.remove(&v_key);
            for (member_sexp, _) in &members {
                subs.insert(v_key.clone(), member_sexp.clone());
                if !check_formula_holds(buffer, *body, subs, inner, tense)? {
                    match prev {
                        Some(p) => {
                            subs.insert(v_key, p);
                        }
                        None => {
                            subs.remove(&v_key);
                        }
                    }
                    return Ok(false);
                }
            }
            match prev {
                Some(p) => {
                    subs.insert(v_key, p);
                }
                None => {
                    subs.remove(&v_key);
                }
            }
            Ok(true)
        }
        LogicNode::CountNode((v, count, body)) => {
            let members: Vec<(String, LogicalTerm)> = inner.all_domain_members().to_vec();
            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) =
                    batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner)
                {
                    let satisfying = batch_results.iter().filter(|r| **r).count() as u32;
                    return Ok(satisfying == *count);
                }
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
                Some(p) => {
                    subs.insert(v_key, p);
                }
                None => {
                    subs.remove(&v_key);
                }
            }
            Ok(satisfying == *count)
        }
        LogicNode::Predicate((rel, args)) => {
            if let Some(result) = try_numeric_comparison(rel, args, subs) {
                return Ok(result);
            }
            // Build typed fact and query typed store.
            if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                let mut visited = HashSet::new();
                Ok(check_predicate_in_kb_typed(&fact, &*inner, 0, &mut visited))
            } else {
                // Fallback to sexp path if typed build fails.
                let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
                let wrapped = wrap_with_tense(tense, &sexp);
                let mut visited = HashSet::new();
                Ok(check_predicate_in_kb(&wrapped, &*inner, 0, &mut visited))
            }
        }
        LogicNode::ComputeNode((rel, args)) => {
            let resolved = resolve_args_for_dispatch(args, subs);
            if let Ok(result) = dispatch_to_backend(rel, &resolved) {
                if result {
                    if let Some(sexp) = build_ground_predicate_sexp(rel, &resolved) {
                        assert_sexp(sexp.clone(), inner);
                    }
                    // Also assert into typed store.
                    if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                        assert_typed_fact(fact, inner);
                    }
                }
                return Ok(result);
            }
            if let Some(result) = try_arithmetic_evaluation(rel, args, subs) {
                if result {
                    if let Some(sexp) = build_ground_predicate_sexp(rel, &resolved) {
                        assert_sexp(sexp.clone(), inner);
                    }
                    if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                        assert_typed_fact(fact, inner);
                    }
                }
                return Ok(result);
            }
            // Build typed fact and query typed store.
            if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                let mut visited = HashSet::new();
                Ok(check_predicate_in_kb_typed(&fact, &*inner, 0, &mut visited))
            } else {
                let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
                let wrapped = wrap_with_tense(tense, &sexp);
                let mut visited = HashSet::new();
                Ok(check_predicate_in_kb(&wrapped, &*inner, 0, &mut visited))
            }
        }
    }
}

pub(super) fn find_witnesses(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
) -> Result<Vec<Vec<(String, String)>>, String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) => {
            let mut results = Vec::new();
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
            if check_formula_holds(buffer, node_id, subs, inner, tense)? {
                Ok(vec![vec![]])
            } else {
                Ok(vec![])
            }
        }
    }
}

const MAX_BACKWARD_CHAIN_DEPTH: usize = 10;

pub(super) fn try_backward_chain_traced(
    sexp: &str,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    depth: usize,
    memo: &mut HashMap<String, u32>,
) -> Option<u32> {
    let rules = collect_matching_rules(sexp, &inner.universal_rules);
    let sexp_tokens = sexp_tokenize(sexp);

    for rule in &rules {
        for concl_tree in &rule.conclusion_trees {
            if let Some(mut bindings) = concl_tree.match_against_tokens(&sexp_tokens) {
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
                        let single_var_cond_indices: Vec<usize> = rule
                            .condition_trees
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
                                        let cs =
                                            rule.condition_trees[idx].substitute(&test_bindings);
                                        check_predicate_in_kb(
                                            &cs,
                                            &*inner,
                                            depth + 1,
                                            &mut HashSet::new(),
                                        )
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

                if rule.condition_templates.is_empty() {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::Derived((rule.label.clone(), sexp.to_string())),
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
                    rule: ProofRule::Derived((rule.label.clone(), sexp.to_string())),
                    holds: true,
                    children: child_indices,
                });
                return Some(idx);
            }
        }
    }

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
                        let single_var_cond_indices: Vec<usize> = rule
                            .condition_trees
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
                                        let bare_cs =
                                            rule.condition_trees[idx].substitute(&test_bindings);
                                        let tensed_cs = wrap_tense(tense, &bare_cs);
                                        check_predicate_in_kb(
                                            &tensed_cs,
                                            &*inner,
                                            depth + 1,
                                            &mut HashSet::new(),
                                        )
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
                            check_predicate_in_kb(
                                &tensed_cs,
                                &*inner,
                                depth + 1,
                                &mut HashSet::new(),
                            )
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

pub(super) fn check_predicate_in_kb(
    sexp: &str,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<String>,
) -> bool {
    if sexp_is_asserted(sexp, inner) {
        return true;
    }
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
    PRED_CACHE_ENABLED.with(|e| {
        if e.get() {
            PRED_CACHE.with(|c| c.borrow_mut().insert(sexp.to_string(), result));
        }
    });
    result
}

const MAX_BACKWARD_CHAIN_DEPTH_UNTRACED: usize = 10;

pub(super) fn try_backward_chain(
    sexp: &str,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<String>,
) -> bool {
    if depth >= MAX_BACKWARD_CHAIN_DEPTH_UNTRACED {
        return false;
    }
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
                    let single_var_cond_indices: Vec<usize> = rule
                        .condition_trees
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
                    for entry in &inner.skolem_fn_registry {
                        for combo in CartesianProduct::new(&member_sexps, entry.dep_count) {
                            all_candidates.push(build_skolem_fn_sexp(&entry.base_name, &combo));
                        }
                    }

                    let mut per_var_candidates: Vec<Vec<String>> = Vec::new();
                    for ev_var in &unbound_event_vars {
                        let single_var_cond_indices: Vec<usize> = rule
                            .condition_trees
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
                                        let bare_cs =
                                            rule.condition_trees[idx].substitute(&test_bindings);
                                        let tensed_cs = wrap_with_tense(Some(tense), &bare_cs);
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
                            let tensed_cs = wrap_with_tense(Some(tense), &bare_cs);
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

                let all_conditions_hold = rule.condition_trees.iter().all(|ct| {
                    let bare_cs = ct.substitute(&bindings);
                    let tensed_cs = wrap_with_tense(Some(tense), &bare_cs);
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

// ─── Typed Backward-Chaining (Phase 4-5b) ────────────────────────
//
// These functions mirror the sexp-based backward-chaining above but
// operate on StoredFact/GroundTerm directly, avoiding all string ops.

thread_local! {
    static TYPED_PRED_CACHE: RefCell<HashMap<StoredFact, bool>> = RefCell::new(HashMap::new());
}

pub(super) fn clear_typed_pred_cache() {
    TYPED_PRED_CACHE.with(|c| c.borrow_mut().clear());
}

/// Check if a typed fact is asserted in the typed fact store.
pub(super) fn typed_fact_is_asserted(fact: &StoredFact, inner: &KnowledgeBaseInner) -> bool {
    let rel = fact.relation();
    if let Some(set) = inner.typed_predicate_facts.get(rel) {
        set.contains(fact)
    } else {
        false
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
) -> bool {
    if typed_fact_is_asserted(fact, inner) {
        return true;
    }
    let cached = PRED_CACHE_ENABLED.with(|e| {
        if e.get() {
            TYPED_PRED_CACHE.with(|c| c.borrow().get(fact).copied())
        } else {
            None
        }
    });
    if let Some(result) = cached {
        return result;
    }
    let result = try_backward_chain_typed(fact, inner, depth, visited);
    PRED_CACHE_ENABLED.with(|e| {
        if e.get() {
            TYPED_PRED_CACHE.with(|c| c.borrow_mut().insert(fact.clone(), result));
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

/// Typed backward-chaining — structural matching instead of sexp tokenization.
pub(super) fn try_backward_chain_typed(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
) -> bool {
    if depth >= MAX_BACKWARD_CHAIN_DEPTH_UNTRACED {
        return false;
    }
    if !visited.insert(fact.clone()) {
        return false;
    }

    let rules_snapshot = collect_matching_rules_typed(fact, &inner.universal_rules);

    for rule in &rules_snapshot {
        for typed_concl in &rule.typed_conclusions {
            let bindings_opt = unify_facts(typed_concl, fact);
            if bindings_opt.is_none() {
                continue;
            }
            let mut bindings = bindings_opt.unwrap();

            // Handle unbound event variables (same logic as sexp version).
            let unbound_event_vars: Vec<String> = rule
                .pattern_var_names
                .iter()
                .filter(|pv| pv.starts_with("ev__") && !bindings.contains_key(pv.as_str()))
                .cloned()
                .collect();

            if !unbound_event_vars.is_empty() {
                let members = inner.all_typed_domain_members();
                let mut all_candidates: Vec<GroundTerm> = members.to_vec();
                for entry in &inner.skolem_fn_registry {
                    for combo in CartesianProduct::new(
                        // CartesianProduct works with &[String] — need member names.
                        // Reuse sexp domain members for candidate generation.
                        &inner.all_domain_members().iter().map(|(s, _)| s.clone()).collect::<Vec<_>>(),
                        entry.dep_count,
                    ) {
                        let dep_terms: Vec<GroundTerm> = combo
                            .iter()
                            .map(|s| parse_sexp_to_ground_term(s))
                            .collect();
                        all_candidates.push(build_skolem_fn_term(&entry.base_name, &dep_terms));
                    }
                }

                let mut per_var_candidates: Vec<Vec<GroundTerm>> = Vec::new();
                for ev_var in &unbound_event_vars {
                    let single_var_cond_indices: Vec<usize> = rule
                        .typed_conditions
                        .iter()
                        .enumerate()
                        .filter(|(_, ct)| {
                            stored_fact_contains_var(ct, ev_var)
                                && unbound_event_vars
                                    .iter()
                                    .all(|other| other == ev_var || !stored_fact_contains_var(ct, other))
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
                                    let cs = substitute_fact(&rule.typed_conditions[idx], &test_bindings);
                                    check_predicate_in_kb_typed(&cs, inner, depth + 1, visited)
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
                        check_predicate_in_kb_typed(&cs, inner, depth + 1, visited)
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

            let all_conditions_hold = rule.typed_conditions.iter().all(|ct| {
                let cs = substitute_fact(ct, &bindings);
                check_predicate_in_kb_typed(&cs, inner, depth + 1, visited)
            });

            if all_conditions_hold {
                visited.remove(fact);
                return true;
            }
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
                    let members = inner.all_typed_domain_members();
                    let mut all_candidates: Vec<GroundTerm> = members.to_vec();
                    for entry in &inner.skolem_fn_registry {
                        for combo in CartesianProduct::new(
                            &inner.all_domain_members().iter().map(|(s, _)| s.clone()).collect::<Vec<_>>(),
                            entry.dep_count,
                        ) {
                            let dep_terms: Vec<GroundTerm> = combo
                                .iter()
                                .map(|s| parse_sexp_to_ground_term(s))
                                .collect();
                            all_candidates.push(build_skolem_fn_term(&entry.base_name, &dep_terms));
                        }
                    }

                    let mut per_var_candidates: Vec<Vec<GroundTerm>> = Vec::new();
                    for ev_var in &unbound_event_vars {
                        let single_var_cond_indices: Vec<usize> = rule
                            .typed_conditions
                            .iter()
                            .enumerate()
                            .filter(|(_, ct)| {
                                stored_fact_contains_var(ct, ev_var)
                                    && unbound_event_vars
                                        .iter()
                                        .all(|other| other == ev_var || !stored_fact_contains_var(ct, other))
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
                                        let bare_cs = substitute_fact(&rule.typed_conditions[idx], &test_bindings);
                                        let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                                        check_predicate_in_kb_typed(&tensed_cs, inner, depth + 1, visited)
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
                            check_predicate_in_kb_typed(&tensed_cs, inner, depth + 1, visited)
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

                let all_conditions_hold = rule.typed_conditions.iter().all(|ct| {
                    let bare_cs = substitute_fact(ct, &bindings);
                    let tensed_cs = apply_tense_to_fact(&bare_cs, fact);
                    check_predicate_in_kb_typed(&tensed_cs, inner, depth + 1, visited)
                });

                if all_conditions_hold {
                    visited.remove(fact);
                    return true;
                }
            }
        }
    }

    visited.remove(fact);
    false
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

// ─── End Typed Backward-Chaining ─────────────────────────────────

pub(super) fn trace_predicate_provenance(
    sexp: &str,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    depth: usize,
    memo: &mut HashMap<String, u32>,
) -> u32 {
    if memo.contains_key(sexp) {
        let idx = steps.len() as u32;
        steps.push(ProofStep {
            rule: ProofRule::ProofRef(sexp.to_string()),
            holds: true,
            children: vec![],
        });
        return idx;
    }

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

    if depth < MAX_BACKWARD_CHAIN_DEPTH {
        if let Some(idx) = try_backward_chain_traced(sexp, inner, steps, depth, memo) {
            memo.insert(sexp.to_string(), idx);
            return idx;
        }
    }

    let idx = steps.len() as u32;
    steps.push(ProofStep {
        rule: ProofRule::PredicateCheck(("unknown".to_string(), sexp.to_string())),
        holds: true,
        children: vec![],
    });
    memo.insert(sexp.to_string(), idx);
    idx
}

pub(super) fn check_formula_holds_traced(
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
            let members: Vec<(String, LogicalTerm)> = inner.all_domain_members().to_vec();

            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) =
                    batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner)
                {
                    if let Some(winner_idx) = batch_results.iter().position(|r| *r) {
                        let mut new_subs = subs.clone();
                        new_subs.insert(v.clone(), members[winner_idx].0.clone());
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
                                members[winner_idx].1.clone(),
                            )),
                            holds: true,
                            children: vec![body_idx],
                        });
                        return Ok((true, idx));
                    }
                }
            }

            for (sexp, term) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                if check_formula_holds(buffer, *body, &mut new_subs, inner, tense)? {
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
                        rule: ProofRule::ExistsWitness((v.clone(), term.clone())),
                        holds: true,
                        children: vec![body_idx],
                    });
                    return Ok((true, idx));
                }
            }
            let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
            for entry in &entries {
                let dep_sexps: Vec<String> = members.iter().map(|(s, _)| s.clone()).collect();
                for combo in CartesianProduct::new(&dep_sexps, entry.dep_count) {
                    let witness_sexp = build_skolem_fn_sexp(&entry.base_name, &combo);
                    let mut new_subs = subs.clone();
                    new_subs.insert(v.clone(), witness_sexp.clone());
                    if check_formula_holds(buffer, *body, &mut new_subs, inner, tense)? {
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
            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) =
                    batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner)
                {
                    if let Some(fail_idx) = batch_results.iter().position(|r| !*r) {
                        let mut new_subs = subs.clone();
                        new_subs.insert(v.clone(), members[fail_idx].0.clone());
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
                            rule: ProofRule::ForallCounterexample(members[fail_idx].1.clone()),
                            holds: false,
                            children: vec![body_idx],
                        });
                        return Ok((false, idx));
                    }
                    let mut child_indices = Vec::new();
                    let mut entity_terms = Vec::new();
                    for (sexp, term) in &members {
                        let mut new_subs = subs.clone();
                        new_subs.insert(v.clone(), sexp.clone());
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
            if let LogicNode::ComputeNode((rel, args)) = &buffer.nodes[*body as usize] {
                if let Some(batch_results) =
                    batch_evaluate_compute_for_members(rel, args, v, &members, subs, inner)
                {
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
            if let Some(result) = try_numeric_comparison(rel, args, subs) {
                let detail = format!(
                    "{}({}) = {}",
                    rel,
                    args.iter()
                        .map(|a| match a {
                            LogicalTerm::Number(n) => format!("{}", *n as i64),
                            LogicalTerm::Variable(v) =>
                                subs.get(v.as_str()).cloned().unwrap_or_else(|| v.clone()),
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
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let wrapped = wrap_with_tense(tense, &sexp);
            let mut visited = HashSet::new();
            if check_predicate_in_kb(&wrapped, &*inner, 0, &mut visited) {
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
