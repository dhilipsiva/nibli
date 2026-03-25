use super::*;

pub(super) fn collect_exists_for_skolem(
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

pub(super) fn decompose_implication(
    buffer: &LogicBuffer,
    body_id: u32,
) -> Option<(Vec<u32>, u32)> {
    let mut conditions = Vec::new();
    let mut current = body_id;

    loop {
        match &buffer.nodes[current as usize] {
            LogicNode::OrNode((left, right)) => match &buffer.nodes[*left as usize] {
                LogicNode::NotNode(inner) => {
                    conditions.push(*inner);
                    current = *right;
                }
                _ => break,
            },
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
    match &buffer.nodes[node_id as usize] {
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

pub(super) fn flatten_conjuncts_through_exists(
    buffer: &LogicBuffer,
    node_id: u32,
    condition_exists: &HashSet<String>,
) -> Vec<u32> {
    match &buffer.nodes[node_id as usize] {
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

pub(super) fn collect_and_note_constants(
    buffer: &LogicBuffer,
    node_id: u32,
    inner: &mut KnowledgeBaseInner,
) {
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

pub(super) fn reconstruct_rule_sexp(
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
                reconstruct_rule_sexp(
                    buffer,
                    *body,
                    pattern_vars,
                    ground_skolems,
                    dependent_skolems,
                )
            } else {
                format!(
                    "(Exists \"{}\" {})",
                    v,
                    reconstruct_rule_sexp(
                        buffer,
                        *body,
                        pattern_vars,
                        ground_skolems,
                        dependent_skolems
                    )
                )
            }
        }
        LogicNode::ForAllNode((v, body)) => {
            if pattern_vars.contains_key(v.as_str()) {
                reconstruct_rule_sexp(
                    buffer,
                    *body,
                    pattern_vars,
                    ground_skolems,
                    dependent_skolems,
                )
            } else {
                format!(
                    "(ForAll \"{}\" {})",
                    v,
                    reconstruct_rule_sexp(
                        buffer,
                        *body,
                        pattern_vars,
                        ground_skolems,
                        dependent_skolems
                    )
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
                reconstruct_rule_sexp(
                    buffer,
                    *inner,
                    pattern_vars,
                    ground_skolems,
                    dependent_skolems
                )
            )
        }
        LogicNode::CountNode((v, count, body)) => {
            if *count == 0 {
                let body_sexp = reconstruct_rule_sexp(
                    buffer,
                    *body,
                    pattern_vars,
                    ground_skolems,
                    dependent_skolems,
                );
                format!("(ForAll \"{}\" (Not {}))", v, body_sexp)
            } else if ground_skolems.contains_key(v.as_str()) {
                reconstruct_rule_sexp(
                    buffer,
                    *body,
                    pattern_vars,
                    ground_skolems,
                    dependent_skolems,
                )
            } else {
                let body_sexp = reconstruct_rule_sexp(
                    buffer,
                    *body,
                    pattern_vars,
                    ground_skolems,
                    dependent_skolems,
                );
                format!("(Exists \"{}\" {})", v, body_sexp)
            }
        }
        LogicNode::PastNode(inner) => {
            format!(
                "(Past {})",
                reconstruct_rule_sexp(
                    buffer,
                    *inner,
                    pattern_vars,
                    ground_skolems,
                    dependent_skolems
                )
            )
        }
        LogicNode::PresentNode(inner) => {
            format!(
                "(Present {})",
                reconstruct_rule_sexp(
                    buffer,
                    *inner,
                    pattern_vars,
                    ground_skolems,
                    dependent_skolems
                )
            )
        }
        LogicNode::FutureNode(inner) => {
            format!(
                "(Future {})",
                reconstruct_rule_sexp(
                    buffer,
                    *inner,
                    pattern_vars,
                    ground_skolems,
                    dependent_skolems
                )
            )
        }
        LogicNode::ObligatoryNode(inner) | LogicNode::PermittedNode(inner) => {
            reconstruct_rule_sexp(
                buffer,
                *inner,
                pattern_vars,
                ground_skolems,
                dependent_skolems,
            )
        }
    }
}

pub(super) fn extract_pred_name(sexp: &str) -> Option<&str> {
    let rest = sexp.strip_prefix("(Pred \"")?;
    let end = rest.find('"')?;
    Some(&rest[..end])
}

pub(super) fn extract_pred_name_deep(sexp: &str) -> Option<&str> {
    if let Some(name) = extract_pred_name(sexp) {
        return Some(name);
    }
    for prefix in &[
        "(Past ",
        "(Present ",
        "(Future ",
        "(Obligation ",
        "(Permission ",
    ] {
        if let Some(rest) = sexp.strip_prefix(prefix) {
            if let Some(inner) = rest.strip_suffix(')') {
                return extract_pred_name(inner);
            }
        }
    }
    None
}

pub(super) fn collect_matching_rules(
    sexp: &str,
    rules: &HashMap<String, Vec<Arc<UniversalRuleRecord>>>,
) -> Vec<Arc<UniversalRuleRecord>> {
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

pub(super) fn sexp_is_asserted(sexp: &str, inner: &KnowledgeBaseInner) -> bool {
    if let Some(pred_name) = extract_pred_name_deep(sexp) {
        if !inner.predicate_facts.contains_key(pred_name) {
            return false;
        }
    }
    inner
        .interner
        .get(sexp)
        .is_some_and(|key| inner.asserted_sexps.contains(&key))
}

fn intern_vec(strings: &[String], interner: &mut SexpInterner) -> Vec<u32> {
    strings.iter().map(|s| interner.intern(s)).collect()
}

pub(super) fn register_rule(
    inner: &mut KnowledgeBaseInner,
    label: String,
    condition_strings: Vec<String>,
    conclusion_strings: Vec<String>,
    pattern_var_names: Vec<String>,
) {
    let cond_keys = intern_vec(&condition_strings, &mut inner.interner);
    let concl_keys = intern_vec(&conclusion_strings, &mut inner.interner);
    let condition_trees: Vec<SexpTree> = condition_strings
        .iter()
        .map(|s| SexpTree::parse(s, &pattern_var_names))
        .collect();
    let conclusion_trees: Vec<SexpTree> = conclusion_strings
        .iter()
        .map(|s| SexpTree::parse(s, &pattern_var_names))
        .collect();
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

pub(super) fn assert_sexp(sexp: String, inner: &mut KnowledgeBaseInner) {
    let pred_name = extract_pred_name_deep(&sexp).map(|s| s.to_string());
    let key = inner.interner.intern_owned(sexp);
    inner.asserted_sexps.insert(key);
    if let Some(name) = pred_name {
        inner.predicate_facts.entry(name).or_default().insert(key);
    }
}

pub(super) fn facts_for_predicate<'a>(
    pred: &str,
    inner: &'a KnowledgeBaseInner,
) -> Option<&'a SortedU32Vec> {
    inner.predicate_facts.get(pred)
}

fn add_universal_rule(
    rules: &mut HashMap<String, Vec<Arc<UniversalRuleRecord>>>,
    rule: UniversalRuleRecord,
    interner: &SexpInterner,
) {
    let rc = Arc::new(rule);
    let mut indexed = false;
    for &concl_key in &rc.conclusion_templates {
        let concl_str = interner.resolve(concl_key);
        if let Some(pred_name) = extract_pred_name_deep(concl_str) {
            rules
                .entry(pred_name.to_string())
                .or_default()
                .push(Arc::clone(&rc));
            indexed = true;
        }
    }
    if !indexed {
        rules
            .entry("__fallback__".to_string())
            .or_default()
            .push(rc);
    }
}

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

pub(super) fn compile_forall_to_rule(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
) -> Result<(), String> {
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

    let pattern_var_names: Vec<String> =
        universals.iter().map(|v| pattern_vars[v].clone()).collect();
    let mut dependent_skolems: HashMap<String, (String, Vec<String>)> = skolem_subs
        .iter()
        .filter_map(|(k, v)| {
            v.strip_prefix(SKDEP_PREFIX)
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

            let bare_condition_sexps: Vec<String> = all_conditions
                .iter()
                .map(|&cid| {
                    reconstruct_rule_sexp(
                        buffer,
                        cid,
                        &pattern_vars,
                        &ground_skolems,
                        &dependent_skolems,
                    )
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
                    reconstruct_rule_sexp(
                        buffer,
                        aid,
                        &pattern_vars,
                        &ground_skolems,
                        &dependent_skolems,
                    )
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
                    println!("[Rule] ∀{} already present, skipping", universals.join(","));
                }
            } else {
                if !inner.rebuilding {
                    println!(
                        "[Rule] Compiled ∀{} to backward-chaining rule",
                        universals.join(",")
                    );
                }

                let label = build_rule_label(&bare_condition_sexps, &bare_conclusion_sexps);
                register_rule(
                    inner,
                    label,
                    bare_condition_sexps.clone(),
                    bare_conclusion_sexps.clone(),
                    all_pattern_var_names.clone(),
                );

                let xp_name = inner.fresh_skolem();
                inner.note_entity(&xp_name);
                let mut xp_subs: HashMap<String, String> = HashMap::new();
                for v in &universals {
                    xp_subs.insert(v.clone(), format!("(Const \"{}\")", xp_name));
                }
                for (k, v) in &ground_skolems {
                    xp_subs
                        .entry(k.clone())
                        .or_insert_with(|| format!("(Const \"{}\")", v));
                }
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
                    assert_sexp(presup, inner);
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

            let body_sexp = reconstruct_rule_sexp(
                buffer,
                inner_body_id,
                &pattern_vars,
                &ground_skolems,
                &dependent_skolems,
            );

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

                let label = build_rule_label(&[], &[body_sexp.clone()]);
                register_rule(
                    inner,
                    label,
                    vec![],
                    vec![body_sexp.clone()],
                    pattern_var_names.clone(),
                );
            }
        }
    }

    Ok(())
}

pub(super) fn strip_tense_wrapper(sexp: &str) -> Option<(&str, &str)> {
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

pub(super) fn wrap_tense(tense: &str, sexp: &str) -> String {
    format!("({} {})", tense, sexp)
}

pub(super) fn sexp_tokenize(s: &str) -> Vec<String> {
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
                chars.next();
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

pub(super) fn extract_sexp_at(tokens: &[String], start: usize) -> Option<(usize, String)> {
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

pub(super) fn reconstruct_sexp_with_subs(
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
            } else if subs.contains_key(v.as_str()) {
                reconstruct_sexp_with_subs(buffer, *body, subs)
            } else {
                let body_sexp = reconstruct_sexp_with_subs(buffer, *body, subs);
                format!("(Exists \"{}\" {})", v, body_sexp)
            }
        }
        LogicNode::PastNode(inner) => {
            format!(
                "(Past {})",
                reconstruct_sexp_with_subs(buffer, *inner, subs)
            )
        }
        LogicNode::PresentNode(inner) => {
            format!(
                "(Present {})",
                reconstruct_sexp_with_subs(buffer, *inner, subs)
            )
        }
        LogicNode::FutureNode(inner) => {
            format!(
                "(Future {})",
                reconstruct_sexp_with_subs(buffer, *inner, subs)
            )
        }
        LogicNode::ObligatoryNode(inner) | LogicNode::PermittedNode(inner) => {
            reconstruct_sexp_with_subs(buffer, *inner, subs)
        }
    }
}

pub(super) fn generate_count_extra_witnesses(
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

// ─── Typed Fact Builders (Phase 2 — parallel path) ───────────────
//
// These functions build StoredFact/GroundTerm directly from LogicBuffer,
// bypassing the s-expression string layer entirely.

/// Convert a LogicalTerm + Skolem substitutions to a GroundTerm.
/// `subs` maps variable names to their Skolem constant names (e.g., "_v0" → "sk_0").
pub(super) fn build_ground_term(
    term: &LogicalTerm,
    subs: &HashMap<String, String>,
) -> GroundTerm {
    match term {
        LogicalTerm::Variable(v) => {
            if let Some(sk) = subs.get(v.as_str()) {
                if sk.starts_with(SKDEP_PREFIX) {
                    // Dependent Skolem — left as a variable (handled by rule compilation)
                    GroundTerm::PatternVar(v.clone())
                } else {
                    GroundTerm::SkolemConst(sk.clone())
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
    subs: &HashMap<String, String>,
    tense: Option<&str>,
) -> Option<StoredFact> {
    match &buffer.nodes[node_id as usize] {
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
        LogicNode::ObligatoryNode(inner) => {
            build_stored_fact_from_node(buffer, *inner, subs, Some("Obligatory"))
        }
        LogicNode::PermittedNode(inner) => {
            build_stored_fact_from_node(buffer, *inner, subs, Some("Permitted"))
        }
        _ => None, // And/Or/Not/ForAll/Count — not a leaf fact.
    }
}

/// Collect leaf StoredFacts from an And-tree (typed equivalent of collect_ground_leaves + reconstruct_sexp).
pub(super) fn collect_ground_facts(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
    tense: Option<&str>,
    out: &mut Vec<StoredFact>,
) {
    match &buffer.nodes[node_id as usize] {
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
        LogicNode::ObligatoryNode(inner) => {
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

/// Build a GroundTerm representing a SkolemFn with given dependencies.
/// Typed equivalent of `build_skolem_fn_sexp()`.
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
