use super::*;

// ── Query-local compute lifecycle ──────────────────────────────────────────

fn external_flat_query() -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = compute(
        &mut nodes,
        "exponential",
        vec![
            LogicalTerm::Number(8.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

fn external_surface_query() -> LogicBuffer {
    compile_external_surface_query("exponential(8, 2, 3).")
}

fn compile_external_surface_query(text: &str) -> LogicBuffer {
    let ast = nibli_kr::parse_checked(text).unwrap();
    let mut buf = nibli_semantics::compile_from_ast(ast).unwrap();
    let mut predicates = default_compute_predicates();
    predicates.insert("exponential".to_string());
    transform_compute_nodes(&mut buf, &predicates);
    buf
}

fn external_flat_public_terms_query() -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = compute(
        &mut nodes,
        "exponential",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Description("dog".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

fn backend_accepts_public_terms(rel: &str, args: &[LogicalTerm]) -> Result<bool, String> {
    if rel == "exponential"
        && matches!(
            args,
            [
                LogicalTerm::Constant(name),
                LogicalTerm::Description(description),
                LogicalTerm::Unspecified,
            ] if name == "alis" && description == "dog"
        )
    {
        Ok(true)
    } else {
        Err(format!("unexpected compute request: {rel}{args:?}"))
    }
}

fn backend_true(_rel: &str, _args: &[LogicalTerm]) -> Result<bool, String> {
    Ok(true)
}

fn backend_false(_rel: &str, _args: &[LogicalTerm]) -> Result<bool, String> {
    Ok(false)
}

fn backend_error(_rel: &str, _args: &[LogicalTerm]) -> Result<bool, String> {
    Err("backend unreachable".to_string())
}

fn batch_true(reqs: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    reqs.iter().map(|_| Ok(true)).collect()
}

fn batch_false(reqs: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    reqs.iter().map(|_| Ok(false)).collect()
}

fn batch_error(reqs: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    reqs.iter()
        .map(|_| Err("backend unreachable".to_string()))
        .collect()
}

#[derive(Clone, Copy, Debug)]
enum QuantifiedCompute {
    Exists,
    ForAll,
    Count,
}

#[derive(Debug, PartialEq)]
struct RuleState {
    index_relation: String,
    label: String,
    conditions: Vec<StoredFact>,
    conclusions: Vec<StoredFact>,
    pattern_vars: Vec<String>,
    negated_condition_indices: Vec<usize>,
    negated_groups: Vec<(String, Vec<StoredFact>)>,
    forward: bool,
    priority: u32,
}

#[derive(Debug, PartialEq)]
struct MaterializedState {
    extensions: std::collections::HashMap<String, std::collections::HashSet<Vec<GroundTerm>>>,
    complete: std::collections::HashSet<String>,
    refused: std::collections::HashMap<String, String>,
    arity: std::collections::HashMap<String, usize>,
}

/// Durable/derived logical state only. Per-query memo tables and proof caches are
/// intentionally excluded; all stores, registries, domains, rules, indexes, and
/// the already-built materialisation snapshot must remain byte-for-byte equal.
#[derive(Debug, PartialEq)]
struct LogicalStateSnapshot {
    skolem_counter: u64,
    skolem_local_counter: u32,
    fact_counter: u64,
    fact_registry: Vec<(u64, Option<LogicBuffer>, String, bool)>,
    facts: std::collections::HashSet<StoredFact>,
    arg_position_index: std::collections::HashMap<
        (String, usize),
        std::collections::HashMap<GroundTerm, Vec<StoredFact>>,
    >,
    known_entities: std::collections::HashSet<GroundTerm>,
    known_event_entities: std::collections::HashSet<GroundTerm>,
    known_descriptions: std::collections::HashSet<String>,
    known_numbers: std::collections::HashSet<u64>,
    typed_domain_members_cache: Vec<GroundTerm>,
    typed_non_event_members_cache: Vec<GroundTerm>,
    domain_members_dirty: bool,
    known_rule_count: usize,
    skolem_functions: Vec<(String, usize)>,
    universal_rules: Vec<RuleState>,
    predicate_dependencies: std::collections::HashMap<String, Vec<(String, bool)>>,
    predicate_registry: Vec<(String, usize, String, Vec<String>)>,
    equivalence_parent: std::collections::HashMap<GroundTerm, GroundTerm>,
    equivalence_classes: std::collections::HashMap<GroundTerm, Vec<GroundTerm>>,
    negative_facts: std::collections::HashSet<Vec<StoredFact>>,
    integrity_constraints: Vec<(String, Vec<StoredFact>, Vec<String>)>,
    disjunctive_constraints: Vec<(String, Vec<StoredFact>, Vec<Vec<StoredFact>>)>,
    derived_only: std::collections::HashSet<String>,
    admitted: std::collections::HashSet<String>,
    materialized: Option<MaterializedState>,
}

fn logical_state_snapshot(kb: &KnowledgeBase) -> LogicalStateSnapshot {
    let inner = kb.inner.borrow();
    let mut fact_registry = inner
        .fact_registry
        .values()
        .map(|record| {
            (
                record.id,
                record.buffer.clone(),
                record.label.clone(),
                record.retracted,
            )
        })
        .collect::<Vec<_>>();
    fact_registry.sort_by_key(|row| row.0);

    let mut universal_rules = inner
        .universal_rules
        .iter()
        .flat_map(|(index_relation, rules)| {
            rules.iter().map(|rule| RuleState {
                index_relation: index_relation.clone(),
                label: rule.label.clone(),
                conditions: rule.typed_conditions.clone(),
                conclusions: rule.typed_conclusions.clone(),
                pattern_vars: rule.pattern_var_names.clone(),
                negated_condition_indices: rule.negated_condition_indices.clone(),
                negated_groups: rule
                    .negated_exists_groups
                    .iter()
                    .map(|group| (group.event_var.clone(), group.conditions.clone()))
                    .collect(),
                forward: rule.forward,
                priority: rule.priority,
            })
        })
        .collect::<Vec<_>>();
    universal_rules.sort_by(|a, b| {
        (&a.index_relation, &a.label, a.priority).cmp(&(&b.index_relation, &b.label, b.priority))
    });

    let mut predicate_registry = inner
        .predicate_registry
        .iter()
        .map(|(relation, signature)| {
            (
                relation.clone(),
                signature.arity,
                format!("{:?}", signature.source),
                signature.arg_sorts.clone(),
            )
        })
        .collect::<Vec<_>>();
    predicate_registry.sort_by(|a, b| a.0.cmp(&b.0));

    let materialized = inner
        .materialized
        .borrow()
        .as_ref()
        .map(|state| MaterializedState {
            extensions: state.ext.clone(),
            complete: state.complete.clone(),
            refused: state
                .refused
                .iter()
                .map(|(relation, reason)| (relation.clone(), reason.reason()))
                .collect(),
            arity: state.arity.clone(),
        });

    LogicalStateSnapshot {
        skolem_counter: inner.skolem_counter,
        skolem_local_counter: inner.skolem_local_counter,
        fact_counter: inner.fact_counter,
        fact_registry,
        facts: inner.fact_store.all_facts().cloned().collect(),
        arg_position_index: inner.arg_position_index.clone(),
        known_entities: inner.known_entities.clone(),
        known_event_entities: inner.known_event_entities.clone(),
        known_descriptions: inner.known_descriptions.clone(),
        known_numbers: inner.known_numbers.clone(),
        typed_domain_members_cache: inner.typed_domain_members_cache.clone(),
        typed_non_event_members_cache: inner.typed_non_event_members_cache.clone(),
        domain_members_dirty: inner.domain_members_dirty,
        known_rule_count: inner.known_rules.identity_count(),
        skolem_functions: inner
            .skolem_fn_registry
            .iter()
            .map(|entry| (format!("{:?}", entry.symbol.id()), entry.dep_count))
            .collect(),
        universal_rules,
        predicate_dependencies: inner.pred_dep_graph.clone(),
        predicate_registry,
        equivalence_parent: inner.equivalence_parent.clone(),
        equivalence_classes: inner.equivalence_classes.clone(),
        negative_facts: inner.negative_facts.clone(),
        integrity_constraints: inner
            .integrity_constraints
            .iter()
            .map(|constraint| {
                (
                    constraint.label.clone(),
                    constraint.conjuncts.clone(),
                    constraint.predicates.clone(),
                )
            })
            .collect(),
        disjunctive_constraints: inner
            .disjunctive_constraints
            .iter()
            .map(|constraint| {
                (
                    constraint.label.clone(),
                    constraint.conditions.clone(),
                    constraint.disjuncts.clone(),
                )
            })
            .collect(),
        derived_only: inner.derived_only.clone(),
        admitted: inner.admitted.clone(),
        materialized,
    }
}

fn flat_term_assertion(term: LogicalTerm) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = pred(&mut nodes, "seed", vec![term, LogicalTerm::Unspecified]);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

fn quantified_compute_fixture() -> KnowledgeBase {
    let kb = new_kb();
    for term in [
        LogicalTerm::Constant("alis".to_string()),
        LogicalTerm::Description("dog".to_string()),
        LogicalTerm::Number(5.0),
    ] {
        assert_buf(&kb, flat_term_assertion(term));
    }
    assert_buf(&kb, make_universal("seed", "derived"));
    assert!(query(&kb, make_query("alis", "derived")));
    // Stabilize the read-derived domain caches before taking the snapshot.
    kb.inner.borrow_mut().ensure_domain_members_cached();
    assert!(kb.inner.borrow().materialized.borrow().is_some());
    kb
}

fn quantified_external_query(kind: QuantifiedCompute, exact_count: u32) -> LogicBuffer {
    let mut nodes = Vec::new();
    let body = compute(
        &mut nodes,
        "exponential",
        vec![
            LogicalTerm::Variable("member".to_string()),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    let root = match kind {
        QuantifiedCompute::Exists => exists(&mut nodes, "member", body),
        QuantifiedCompute::ForAll => forall(&mut nodes, "member", body),
        QuantifiedCompute::Count => count(&mut nodes, "member", exact_count, body),
    };
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

static SUCCESS_BATCH_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static SUCCESS_SCALAR_CALLS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

fn counted_backend_true(_rel: &str, _args: &[LogicalTerm]) -> Result<bool, String> {
    SUCCESS_SCALAR_CALLS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    Ok(true)
}

fn counted_batch_true(reqs: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    SUCCESS_BATCH_CALLS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    reqs.iter().map(|_| Ok(true)).collect()
}

#[test]
fn built_in_compute_is_query_local_and_does_not_grow_kb_state() {
    let kb = new_kb();
    let query_buf = make_compute_query("product", 6.0, 2.0, 3.0);
    assert!(query(&kb, query_buf));

    assert!(kb.list_facts().unwrap().is_empty());
    assert_eq!(
        kb.next_fact_id().unwrap(),
        0,
        "a query cannot consume an id"
    );
    {
        let inner = kb.inner.borrow();
        assert!(inner.known_numbers.is_empty());
        assert!(
            inner
                .fact_store
                .lookup_predicate("product")
                .map(|facts| facts.is_empty())
                .unwrap_or(true),
            "local arithmetic must not become a stored logical fact"
        );
        assert!(inner.arg_position_index.is_empty());
    }

    // A plain Predicate is store-backed and must not see the earlier compute
    // result. The same ComputeNode would simply recompute.
    let mut plain_nodes = Vec::new();
    let plain_root = pred(
        &mut plain_nodes,
        "product",
        vec![
            LogicalTerm::Number(6.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    assert!(query_false(
        &kb,
        LogicBuffer {
            nodes: plain_nodes,
            roots: vec![plain_root],
        }
    ));

    // Query evaluation must not manufacture quantifier-domain members. With
    // no asserted entities/numbers this universal remains vacuously true.
    let mut universal_nodes = Vec::new();
    let body = compute(
        &mut universal_nodes,
        "product",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(2.0),
        ],
    );
    let root = forall(&mut universal_nodes, "_v0", body);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: universal_nodes,
            roots: vec![root],
        }
    ));
}

#[test]
fn quantified_compute_fast_paths_leave_all_logical_state_unchanged() {
    for kind in [
        QuantifiedCompute::Exists,
        QuantifiedCompute::ForAll,
        QuantifiedCompute::Count,
    ] {
        let kb = quantified_compute_fixture();
        kb.set_compute_dispatch(counted_backend_true, counted_batch_true);
        let exact_count = kb.inner.borrow().typed_domain_members_cache.len() as u32;
        let query_buf = quantified_external_query(kind, exact_count);
        let before = logical_state_snapshot(&kb);

        SUCCESS_BATCH_CALLS.store(0, std::sync::atomic::Ordering::SeqCst);
        SUCCESS_SCALAR_CALLS.store(0, std::sync::atomic::Ordering::SeqCst);
        assert_eq!(
            query_result(&kb, query_buf),
            QueryResult::True,
            "{kind:?}: all three seeded members satisfy the external batch"
        );
        assert!(
            SUCCESS_BATCH_CALLS.load(std::sync::atomic::Ordering::SeqCst) > 0,
            "{kind:?}: the quantified batch fast path must actually execute"
        );
        assert_eq!(
            SUCCESS_SCALAR_CALLS.load(std::sync::atomic::Ordering::SeqCst),
            0,
            "{kind:?}: a well-formed batch must not fall back to scalar dispatch"
        );
        assert_eq!(
            logical_state_snapshot(&kb),
            before,
            "{kind:?}: a query-local batch result changed logical KB state"
        );
    }
}

#[test]
fn external_compute_is_query_local_on_flat_and_surface_paths() {
    for (shape, compute_query) in [
        ("flat", external_flat_query()),
        ("surface", external_surface_query()),
    ] {
        let kb = new_kb();
        kb.set_compute_dispatch(backend_true, batch_true);

        let (result, trace) = kb
            .query_entailment_with_proof_inner(compute_query.clone())
            .unwrap();
        assert!(
            result.is_true(),
            "{shape}: working backend must answer true"
        );
        assert!(
            trace.steps.iter().any(|step| matches!(
                &step.rule,
                ProofRule::ComputeCheck { method, .. } if method == "backend"
            )),
            "{shape}: backend evidence must remain a ComputeCheck"
        );
        assert!(
            !trace
                .steps
                .iter()
                .any(|step| matches!(step.rule, ProofRule::Asserted { .. })),
            "{shape}: a backend result must never be rendered as asserted"
        );

        assert!(
            kb.list_facts().unwrap().is_empty(),
            "{shape}: no registry row"
        );
        assert_eq!(
            kb.next_fact_id().unwrap(),
            0,
            "{shape}: no fact id allocation"
        );
        {
            let inner = kb.inner.borrow();
            assert!(inner.known_numbers.is_empty(), "{shape}: no domain growth");
            assert!(
                inner
                    .fact_store
                    .lookup_predicate("exponential")
                    .map(|facts| facts.is_empty())
                    .unwrap_or(true),
                "{shape}: no typed-store insertion"
            );
        }

        // A healthy false is definitive, equally non-mutating, and must not be
        // mislabeled as a closed-world absence in proof metadata.
        kb.set_compute_dispatch(backend_false, batch_false);
        let (false_result, false_trace) = kb
            .query_entailment_with_proof_inner(compute_query.clone())
            .unwrap();
        assert!(false_result.is_false(), "{shape}: backend false");
        assert!(
            !false_trace.cwa_false,
            "{shape}: a definitive backend false is not a CWA false"
        );
        assert!(
            false_trace.steps.iter().any(|step| matches!(
                &step.rule,
                ProofRule::ComputeCheck { method, .. }
                    if method == "backend" && !step.holds
            )),
            "{shape}: false proof must retain definitive backend evidence"
        );

        // A previous true is never an outage-time axiom. Flat and ordinary KR
        // surface paths both fail closed after the backend becomes unavailable.
        kb.set_compute_dispatch(backend_error, batch_error);
        assert_eq!(
            query_result(&kb, compute_query),
            QueryResult::Unknown(UnknownReason::BackendUnavailable),
            "{shape}: outage after success must be UNKNOWN"
        );
        assert!(kb.list_facts().unwrap().is_empty());
    }
}

#[test]
fn external_compute_accepts_public_constants_and_descriptions_on_both_shapes() {
    for (shape, compute_query) in [
        ("flat", external_flat_public_terms_query()),
        (
            "surface",
            compile_external_surface_query("exponential(Alis, the dog)."),
        ),
    ] {
        let kb = new_kb();
        kb.set_compute_dispatch(backend_accepts_public_terms, batch_error);
        assert_eq!(
            query_result(&kb, compute_query),
            QueryResult::True,
            "{shape}: public constant/description terms must reach the backend unchanged"
        );
        assert!(kb.list_facts().unwrap().is_empty(), "{shape}: query-local");
    }
}

fn short_batch(_reqs: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    Vec::new()
}

fn long_batch(reqs: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    (0..=reqs.len()).map(|_| Ok(true)).collect()
}

static MALFORMED_BATCH_CALLS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

fn counted_short_batch(_reqs: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    MALFORMED_BATCH_CALLS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    Vec::new()
}

fn counted_long_batch(reqs: &[ComputeRequest]) -> Vec<Result<bool, String>> {
    MALFORMED_BATCH_CALLS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    (0..=reqs.len()).map(|_| Ok(true)).collect()
}

#[test]
fn malformed_batch_cardinality_falls_back_instead_of_fabricating_a_verdict() {
    let members = vec![GroundTerm::from_f64(1.0), GroundTerm::from_f64(2.0)];
    let args = vec![LogicalTerm::Variable("x".to_string())];
    let subs = std::collections::HashMap::new();

    for batch in [short_batch as BatchEvalFn, long_batch as BatchEvalFn] {
        let kb = new_kb();
        kb.set_compute_dispatch(backend_error, batch);
        let inner = kb.inner.borrow();
        assert!(
            batch_evaluate_compute_for_members(&inner, "zzoracle", &args, "x", &members, &subs,)
                .is_none(),
            "a short or long backend response must fall back to scalar evaluation"
        );
        assert!(inner.fact_store.is_empty());
    }
}

#[test]
fn malformed_quantified_batches_are_non_definitive_and_non_mutating_end_to_end() {
    for (malformation, batch) in [
        ("short", counted_short_batch as BatchEvalFn),
        ("long", counted_long_batch as BatchEvalFn),
    ] {
        for kind in [
            QuantifiedCompute::Exists,
            QuantifiedCompute::ForAll,
            QuantifiedCompute::Count,
        ] {
            let kb = quantified_compute_fixture();
            kb.set_compute_dispatch(backend_error, batch);
            let exact_count = kb.inner.borrow().typed_domain_members_cache.len() as u32;
            let before = logical_state_snapshot(&kb);

            MALFORMED_BATCH_CALLS.store(0, std::sync::atomic::Ordering::SeqCst);
            assert_eq!(
                query_result(&kb, quantified_external_query(kind, exact_count)),
                QueryResult::Unknown(UnknownReason::BackendUnavailable),
                "{kind:?}/{malformation}: malformed cardinality must fail closed"
            );
            assert!(
                MALFORMED_BATCH_CALLS.load(std::sync::atomic::Ordering::SeqCst) > 0,
                "{kind:?}/{malformation}: the malformed batch seam was not exercised"
            );
            assert_eq!(
                logical_state_snapshot(&kb),
                before,
                "{kind:?}/{malformation}: malformed batch changed logical KB state"
            );
        }
    }
}

// ── Typed predicate-cache mutation invariants ──────────────────────────────

#[test]
fn assert_typed_fact_invalidates_pred_cache() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));

    let danlu_adam = StoredFact::Bare(GroundFact::new(
        "danlu",
        vec![
            GroundTerm::Constant("adam".to_string()),
            GroundTerm::Unspecified,
        ],
    ));
    let dog_adam = StoredFact::Bare(GroundFact::new(
        "gerku",
        vec![
            GroundTerm::Constant("adam".to_string()),
            GroundTerm::Unspecified,
        ],
    ));

    clear_and_enable_pred_cache(&kb.inner.borrow());
    {
        let inner = kb.inner.borrow();
        let mut visited = std::collections::HashSet::new();
        assert!(check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited).is_false());
    }
    {
        let mut inner = kb.inner.borrow_mut();
        assert_typed_fact(dog_adam, &mut inner);
    }
    {
        let inner = kb.inner.borrow();
        let mut visited = std::collections::HashSet::new();
        assert!(
            check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited).is_true(),
            "a structural fact insertion must invalidate a stale false"
        );
    }
}

#[test]
fn pred_cache_is_per_instance_no_cross_kb_leak() {
    let danlu_adam = StoredFact::Bare(GroundFact::new(
        "danlu",
        vec![
            GroundTerm::Constant("adam".to_string()),
            GroundTerm::Unspecified,
        ],
    ));

    let kb_a = new_kb();
    assert_buf(&kb_a, make_universal("gerku", "danlu"));
    {
        let inner = kb_a.inner.borrow();
        clear_and_enable_pred_cache(&inner);
        let mut visited = std::collections::HashSet::new();
        assert!(check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited).is_false());
    }

    let kb_b = new_kb();
    assert_buf(&kb_b, make_universal("gerku", "danlu"));
    assert_buf(&kb_b, make_assertion("adam", "gerku"));
    {
        let inner = kb_b.inner.borrow();
        let mut visited = std::collections::HashSet::new();
        assert!(
            check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited).is_true(),
            "KB-A's cached false must not leak into KB-B"
        );
    }
}
