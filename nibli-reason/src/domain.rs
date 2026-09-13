//! Query-local closure of activated individual witnesses. Rule templates are
//! candidates; only a satisfied originating rule establishes domain membership.
use super::*;

pub(super) const MAX_INFERENCE_RECORDS: usize = 2_000_000;

#[cfg(test)]
thread_local! {
    pub(super) static TEST_CLOSURE_LIMIT: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
    pub(super) static TEST_CLOSURE_RUNS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    pub(super) static TEST_DOMAIN_IDENTITY_CHECKS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn closure_limit() -> usize {
    #[cfg(test)]
    if let Some(limit) = TEST_CLOSURE_LIMIT.with(std::cell::Cell::get) {
        return limit;
    }
    MAX_INFERENCE_RECORDS
}

#[derive(Default)]
pub(super) struct QueryDomain {
    pub(super) incomplete: Option<QueryResult>,
    /// Reuse only a fully closed domain, at no smaller reasoning budget and in
    /// the same proof/lookup mode. Every logical mutation clears this stamp.
    pub(super) completed_at: std::cell::Cell<Option<(usize, bool, usize)>>,
    /// The actual rule/bindings licensing each member. Kept query-local, never
    /// inserted into the asserted fact store or its provenance sidecar.
    activations: HashMap<GroundTerm, (Arc<UniversalRuleRecord>, HashMap<String, GroundTerm>)>,
    conclusions: HashMap<StoredFact, Arc<WitnessActivationEvidence>>,
    tracing: RefCell<HashSet<StoredFact>>,
}

pub(super) struct WitnessActivationEvidence {
    pub(super) rule: Arc<UniversalRuleRecord>,
    pub(super) bindings: HashMap<String, GroundTerm>,
    pub(super) conclusion: StoredFact,
}

fn canonical_fact(fact: &StoredFact, inner: &KnowledgeBaseInner) -> StoredFact {
    StoredFact::with_tense_from(
        GroundFact::new(
            fact.relation(),
            fact.inner()
                .args
                .iter()
                .map(|term| canonical_witness_term(&inner.equivalence_parent, term))
                .collect(),
        ),
        fact,
    )
}

pub(super) fn witness_activation_evidence<'a>(
    fact: &StoredFact,
    inner: &'a KnowledgeBaseInner,
) -> Option<&'a Arc<WitnessActivationEvidence>> {
    if inner.query_domain.conclusions.is_empty() {
        return None;
    }
    inner
        .query_domain
        .conclusions
        .get(&canonical_fact(fact, inner))
}

pub(super) fn activation_is_being_traced(fact: &StoredFact, inner: &KnowledgeBaseInner) -> bool {
    !inner.query_domain.tracing.borrow().is_empty()
        && inner
            .query_domain
            .tracing
            .borrow()
            .contains(&canonical_fact(fact, inner))
}

pub(super) fn mark_activation_trace(fact: &StoredFact, inner: &KnowledgeBaseInner, active: bool) {
    let key = canonical_fact(fact, inner);
    if active {
        inner.query_domain.tracing.borrow_mut().insert(key);
    } else {
        inner.query_domain.tracing.borrow_mut().remove(&key);
    }
}

fn individual_templates(term: &GroundTerm, out: &mut Vec<GroundTerm>) {
    match term {
        GroundTerm::Skolem(symbol) if symbol.sort() == SkolemSort::Individual => {
            out.push(term.clone())
        }
        GroundTerm::SkolemFn(symbol, dependency) => {
            if symbol.sort() == SkolemSort::Individual {
                out.push(term.clone());
            }
            individual_templates(dependency, out);
        }
        GroundTerm::DepPair(left, right) => {
            individual_templates(left, out);
            individual_templates(right, out);
        }
        _ => {}
    }
}

fn dependency_height(term: &GroundTerm) -> usize {
    match term {
        GroundTerm::SkolemFn(_, dep) => 1 + dependency_height(dep),
        GroundTerm::DepPair(left, right) => dependency_height(left).max(dependency_height(right)),
        _ => 0,
    }
}

fn collect_pattern_variables<'a>(term: &'a GroundTerm, names: &mut HashSet<&'a str>) {
    match term {
        GroundTerm::PatternVar(name) => {
            names.insert(name);
        }
        GroundTerm::SkolemFn(_, dependency) => collect_pattern_variables(dependency, names),
        GroundTerm::DepPair(left, right) => {
            collect_pattern_variables(left, names);
            collect_pattern_variables(right, names);
        }
        _ => {}
    }
}

/// Preserve first-seen semantic identity order without repeatedly comparing a
/// shared identity's entire body through every conclusion-index reference.
/// Distinct allocations still receive the ordinary full-value equality check.
pub(super) fn distinct_domain_rules(
    inner: &KnowledgeBaseInner,
) -> impl Iterator<Item = &Arc<UniversalRuleRecord>> {
    let mut pointers = HashSet::new();
    let mut identities = HashSet::new();
    inner
        .universal_rules
        .values()
        .flatten()
        .filter(move |rule| {
            if !pointers.insert(Arc::as_ptr(&rule.identity)) {
                return false;
            }
            #[cfg(test)]
            TEST_DOMAIN_IDENTITY_CHECKS.set(TEST_DOMAIN_IDENTITY_CHECKS.get() + 1);
            identities.insert(rule.identity.as_ref())
        })
}

/// Predicate stratification alone omits the implicit domain read of an
/// unguarded universal. Generating a new member can then invalidate the very
/// absence that generated it. Include that dependency before accepting any
/// activation; a negative cycle is incomplete, never a growing approximation.
fn domain_dependency_graph(inner: &KnowledgeBaseInner) -> HashMap<String, Vec<(String, bool)>> {
    const DOMAIN: &str = "__nibli_activated_individual_domain";
    let mut graph = inner.pred_dep_graph.clone();
    for rule in distinct_domain_rules(inner) {
        // Collect guarded names once. Re-scanning every condition separately
        // for every variable is quadratic in large compiled constitutional rules.
        let mut guarded = HashSet::new();
        for (index, condition) in rule.typed_conditions.iter().enumerate() {
            if !rule.negated_condition_indices.contains(&index)
                && !is_non_indexable_relation(condition.relation())
            {
                for term in &condition.inner().args {
                    collect_pattern_variables(term, &mut guarded);
                }
            }
        }
        let has_unguarded_variable = rule
            .pattern_var_names
            .iter()
            .filter(|name| !name.starts_with("ev__"))
            .any(|name| !guarded.contains(name.as_str()));
        if has_unguarded_variable {
            for head in &rule.typed_conclusions {
                graph
                    .entry(head.relation().to_string())
                    .or_default()
                    .push((DOMAIN.into(), false));
            }
        }
        let mut generated = Vec::new();
        for head in &rule.typed_conclusions {
            for term in &head.inner().args {
                individual_templates(term, &mut generated);
            }
        }
        if generated
            .iter()
            .all(|term| inner.known_entities.contains(term))
        {
            continue;
        }
        let dependencies = graph.entry(DOMAIN.into()).or_default();
        for (index, condition) in rule.typed_conditions.iter().enumerate() {
            dependencies.push((
                condition.relation().to_string(),
                rule.negated_condition_indices.contains(&index),
            ));
        }
        for group in &rule.negated_exists_groups {
            for condition in &group.conditions {
                dependencies.push((condition.relation().to_string(), true));
            }
        }
        if has_unguarded_variable {
            dependencies.push((DOMAIN.into(), false));
        }
    }
    graph
}

/// Immutable rule/domain planning. Ground facts do not change this plan unless
/// they change whether a generated individual template is already asserted.
/// Rule/profile/equality changes invalidate the enclosing materialization plan.
pub(super) struct DomainPlan {
    known_individuals: Vec<(GroundTerm, bool)>,
    incomplete: bool,
    rules: Vec<(usize, Arc<UniversalRuleRecord>, Vec<GroundTerm>)>,
}

impl DomainPlan {
    pub(super) fn new(inner: &KnowledgeBaseInner) -> Self {
        let mut templates = Vec::new();
        for rule in materialize::distinct_rules(inner) {
            for head in &rule.typed_conclusions {
                for term in &head.inner().args {
                    individual_templates(term, &mut templates);
                }
            }
        }
        templates.sort();
        templates.dedup();
        let known_individuals = templates
            .into_iter()
            .map(|term| {
                let known = inner.known_entities.contains(&term);
                (term, known)
            })
            .collect();
        let graph = domain_dependency_graph(inner);
        if check_stratification(&graph).is_err() {
            return Self {
                known_individuals,
                incomplete: true,
                rules: Vec::new(),
            };
        }
        let strata = materialize::compute_strata(&graph);
        let mut rules = Vec::new();
        for rule in distinct_domain_rules(inner) {
            let mut terms = Vec::new();
            for fact in &rule.typed_conclusions {
                for term in &fact.inner().args {
                    individual_templates(term, &mut terms);
                }
            }
            terms.sort();
            terms.dedup();
            terms.retain(|term| !inner.known_entities.contains(term));
            if terms.is_empty() {
                continue;
            }
            // Schedule by this rule's prerequisites. An unrelated writer can
            // raise one of a multi-head rule's predicates without raising the
            // rule's other head predicates; scheduling by max(head) would delay
            // a lower-stratum witness until its negative readers are already running.
            let level = rule
                .typed_conditions
                .iter()
                .enumerate()
                .map(|(index, fact)| {
                    strata.get(fact.relation()).copied().unwrap_or(0)
                        + usize::from(rule.negated_condition_indices.contains(&index))
                })
                .chain(rule.negated_exists_groups.iter().flat_map(|group| {
                    group
                        .conditions
                        .iter()
                        .map(|fact| strata.get(fact.relation()).copied().unwrap_or(0) + 1)
                }))
                .max()
                .unwrap_or(0);
            rules.push((level, rule.clone(), terms));
        }
        rules.sort_by(|a, b| (a.0, &a.1.label, &a.2).cmp(&(b.0, &b.1.label, &b.2)));
        Self {
            known_individuals,
            incomplete: false,
            rules,
        }
    }

    fn applies(&self, inner: &KnowledgeBaseInner) -> bool {
        self.known_individuals
            .iter()
            .all(|(term, was_known)| inner.known_entities.contains(term) == *was_known)
    }
}

/// A complete fixed point can be reused while facts, rules and profile remain
/// unchanged. Incomplete or shallower-budget closures are always recomputed.
pub(super) fn prepare_query_domain(inner: &mut KnowledgeBaseInner) -> Result<(), String> {
    check_cancelled(inner)?;
    if let Some((depth, lookup, limit)) = inner.query_domain.completed_at.get()
        && depth <= inner.max_chain_depth
        && lookup == inner.positive_lookup.get()
        && limit == closure_limit()
    {
        return Ok(());
    }
    #[cfg(test)]
    TEST_CLOSURE_RUNS.set(TEST_CLOSURE_RUNS.get() + 1);
    inner.query_domain = QueryDomain::default();
    inner.domain_members_dirty = true;
    inner.ensure_domain_members_cached();
    let shared = materialize::materialization_plan(inner);
    let rebuilt;
    let plan = if shared.domain.applies(inner) {
        &shared.domain
    } else {
        rebuilt = DomainPlan::new(inner);
        &rebuilt
    };
    if plan.incomplete {
        inner.query_domain.incomplete = Some(QueryResult::Unknown(UnknownReason::NafDependent));
        return Ok(());
    }
    let rules = &plan.rules;
    if rules.is_empty() {
        inner.query_domain.completed_at.set(Some((
            inner.max_chain_depth,
            inner.positive_lookup.get(),
            closure_limit(),
        )));
        return Ok(());
    }
    clear_and_enable_pred_cache(inner);
    let mut levels: Vec<_> = rules.iter().map(|(level, _, _)| *level).collect();
    levels.dedup();
    let mut attempts = 0usize;
    for level in levels {
        loop {
            check_cancelled(inner)?;
            let mut members: Vec<_> = inner
                .all_non_event_domain_members()
                .iter()
                .map(|term| canonical_witness_term(&inner.equivalence_parent, term))
                .collect();
            members.sort();
            members.dedup();
            let mut additions = Vec::new();
            let mut pending = None;
            // Finish lower positive closures before evaluating a higher NAF
            // stratum. New individuals also revisit previously finished rules.
            for (_, rule, templates) in rules.iter().filter(|(s, _, _)| *s <= level) {
                let variables: Vec<_> = rule
                    .pattern_var_names
                    .iter()
                    .filter(|name| !name.starts_with("ev__"))
                    .cloned()
                    .collect();
                // Most asserted names cannot satisfy a unary guard such as
                // person($x). A completed guard supplies an exact candidate
                // filter; unsupported shapes retain the full domain sweep.
                let restricted = if variables.len() == 1 {
                    materialize::complete_unary_condition_members(inner, rule, &variables[0]).map(
                        |allowed| {
                            members
                                .iter()
                                .filter(|term| allowed.contains(*term))
                                .cloned()
                                .collect::<Vec<_>>()
                        },
                    )
                } else {
                    None
                };
                let candidates = restricted.as_deref().unwrap_or(&members);
                for combo in GroundTermCartesianProduct::new(candidates, variables.len()) {
                    attempts += 1;
                    if attempts > closure_limit() {
                        inner.query_domain.incomplete =
                            Some(QueryResult::ResourceExceeded(ResourceKind::Memory));
                        return Ok(());
                    }
                    check_cancelled(inner)?;
                    let mut bindings: HashMap<_, _> =
                        variables.iter().cloned().zip(combo).collect();
                    let terms: Vec<_> = templates
                        .iter()
                        .map(|term| {
                            canonical_witness_term(
                                &inner.equivalence_parent,
                                &substitute_term(term, &bindings),
                            )
                        })
                        .collect();
                    if terms
                        .iter()
                        .all(|term| inner.query_domain.activations.contains_key(term))
                    {
                        continue;
                    }
                    let verdict = witness_activation_holds(rule, &mut bindings, inner);
                    if !verdict.is_true() {
                        if !verdict.is_false() {
                            pending = Some(match pending {
                                Some(previous) => combine_indeterminate(previous, verdict),
                                None => verdict,
                            });
                        }
                        continue;
                    }
                    for term in terms {
                        if term.contains_compiler_only_term() {
                            return Err("witness activation retained an unbound dependency".into());
                        }
                        if dependency_height(&term) > inner.max_chain_depth {
                            let exhausted = QueryResult::ResourceExceeded(ResourceKind::Depth);
                            pending = Some(match pending {
                                Some(previous) => combine_indeterminate(previous, exhausted),
                                None => exhausted,
                            });
                        } else if !inner.query_domain.activations.contains_key(&term) {
                            if additions.len() + inner.query_domain.activations.len()
                                >= closure_limit()
                            {
                                inner.query_domain.incomplete =
                                    Some(QueryResult::ResourceExceeded(ResourceKind::Memory));
                                return Ok(());
                            }
                            additions.push((term, rule.clone(), bindings.clone()));
                        }
                    }
                }
            }
            if additions.is_empty() {
                if pending.is_some() {
                    inner.query_domain.incomplete = pending;
                    return Ok(()); // no higher-stratum NAF on unfinished closure
                }
                break;
            }
            for (term, rule, bindings) in additions {
                // Keep complete activation bindings as query-local lemmas. A
                // body-only variable may have been bound to a generated
                // individual; the older index-only join cannot rediscover it.
                // First evidence wins, preserving the acyclic activation order.
                for template in &rule.typed_conclusions {
                    let conclusion = substitute_fact(template, &bindings);
                    let key = canonical_fact(&conclusion, inner);
                    if inner.query_domain.conclusions.len() + inner.query_domain.activations.len()
                        >= closure_limit()
                    {
                        inner.query_domain.incomplete =
                            Some(QueryResult::ResourceExceeded(ResourceKind::Memory));
                        return Ok(());
                    }
                    inner
                        .query_domain
                        .conclusions
                        .entry(key)
                        .or_insert_with(|| {
                            Arc::new(WitnessActivationEvidence {
                                rule: rule.clone(),
                                bindings: bindings.clone(),
                                conclusion,
                            })
                        });
                }
                if inner
                    .query_domain
                    .activations
                    .insert(term.clone(), (rule, bindings))
                    .is_none()
                {
                    inner.typed_domain_members_cache.push(term.clone());
                    inner.typed_non_event_members_cache.push(term);
                }
            }
            inner.typed_domain_members_cache.sort();
            inner.typed_domain_members_cache.dedup();
            inner.typed_non_event_members_cache.sort();
            inner.typed_non_event_members_cache.dedup();
            clear_and_enable_pred_cache(inner);
        }
    }
    inner.query_domain.completed_at.set(Some((
        inner.max_chain_depth,
        inner.positive_lookup.get(),
        closure_limit(),
    )));
    Ok(())
}

/// Share domain membership across verdict and enumeration paths. Event
/// variables still use the indexed event search; non-finite numeric witnesses
/// retain their separately documented index-only behavior.
pub(super) fn restrict_to_activated_individuals(
    candidates: &mut Vec<GroundTerm>,
    variable: &str,
    inner: &KnowledgeBaseInner,
) {
    if variable.starts_with("_ev") {
        return;
    }
    candidates.retain(|term| match term {
        GroundTerm::Skolem(symbol) | GroundTerm::SkolemFn(symbol, _) => {
            symbol.sort() == SkolemSort::Individual
        }
        GroundTerm::Unspecified
        | GroundTerm::PatternVar(_)
        | GroundTerm::SkolemPlaceholder(_)
        | GroundTerm::DepPair(_, _) => false,
        _ => true,
    });
    candidates.retain(|term| {
        !is_generated_individual(term)
            || inner.known_entities.contains(term)
            || inner
                .query_domain
                .activations
                .contains_key(&canonical_witness_term(&inner.equivalence_parent, term))
    });
    let mut seen = HashSet::new();
    candidates.retain(|term| seen.insert(canonical_witness_term(&inner.equivalence_parent, term)));
}

fn is_generated_individual(term: &GroundTerm) -> bool {
    matches!(term, GroundTerm::Skolem(symbol) | GroundTerm::SkolemFn(symbol, _) if symbol.sort() == SkolemSort::Individual)
}
