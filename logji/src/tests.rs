use super::*;
use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm, ProofRule, ProofTrace};

/// Helper: build a Predicate node with the given relation and args.
fn pred(nodes: &mut Vec<LogicNode>, rel: &str, args: Vec<LogicalTerm>) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::Predicate((rel.to_string(), args)));
    id
}

/// Helper: build a NotNode wrapping the given node.
fn not(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::NotNode(inner));
    id
}

/// Helper: build an OrNode.
fn or(nodes: &mut Vec<LogicNode>, left: u32, right: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::OrNode((left, right)));
    id
}

/// Helper: build a ForAllNode.
fn forall(nodes: &mut Vec<LogicNode>, var: &str, body: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::ForAllNode((var.to_string(), body)));
    id
}

/// Helper: build an ExistsNode.
fn exists(nodes: &mut Vec<LogicNode>, var: &str, body: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::ExistsNode((var.to_string(), body)));
    id
}

/// Helper: build an AndNode.
fn and(nodes: &mut Vec<LogicNode>, left: u32, right: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::AndNode((left, right)));
    id
}

fn new_kb() -> KnowledgeBase {
    KnowledgeBase {
        inner: RefCell::new(KnowledgeBaseInner::new()),
    }
}

fn assert_buf(kb: &KnowledgeBase, buf: LogicBuffer) {
    kb.assert_fact_inner(buf, String::new()).unwrap();
}

/// Test helper: assert and return the fact ID (unwraps Result).
fn assert_id(kb: &KnowledgeBase, buf: LogicBuffer, label: impl Into<String>) -> u64 {
    kb.assert_fact_inner(buf, label.into()).unwrap()
}

fn query(kb: &KnowledgeBase, buf: LogicBuffer) -> bool {
    kb.query_entailment_inner(buf).unwrap().is_true()
}

fn query_result(kb: &KnowledgeBase, buf: LogicBuffer) -> QueryResult {
    kb.query_entailment_inner(buf).unwrap()
}

/// Build "la .X. P" -> Pred("P", [Const("X"), Zoe])
fn make_assertion(entity: &str, predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        predicate,
        vec![
            LogicalTerm::Constant(entity.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Build "ro lo P cu Q" -> ForAll("_v0", Or(Not(Pred("P", [Var("_v0"), Zoe])), Pred("Q", [Var("_v0"), Zoe])))
fn make_universal(restrictor: &str, consequent: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let restrict = pred(
        &mut nodes,
        restrictor,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let body = pred(
        &mut nodes,
        consequent,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg = not(&mut nodes, restrict);
    let disj = or(&mut nodes, neg, body);
    let root = forall(&mut nodes, "_v0", disj);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

fn make_query(entity: &str, predicate: &str) -> LogicBuffer {
    make_assertion(entity, predicate)
}

#[test]
fn test_native_rule_simple_universal() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert!(query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_native_rule_entity_after_rule() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_native_rule_selective_application() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "mlatu"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert!(query(&kb, make_query("alis", "danlu")));
    assert!(!query(&kb, make_query("bob", "danlu")));
}

// ─── Cooperative cancellation (server watchdog) ──────────────

#[test]
fn cancelled_query_returns_err() {
    use std::sync::atomic::{AtomicBool, Ordering};
    // A pre-set cancel flag makes any query abort via the Err channel
    // rather than running to completion. The native server's watchdog
    // sets this flag when the request timeout elapses.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));

    let flag = std::sync::Arc::new(AtomicBool::new(true));
    kb.set_cancel_flag(flag.clone());

    let result = kb.query_entailment_inner(make_query("alis", "danlu"));
    assert!(
        result.is_err(),
        "cancelled query must return Err, got {result:?}"
    );
    assert!(
        result.unwrap_err().to_lowercase().contains("cancel"),
        "cancellation error should mention 'cancel'"
    );

    // Clearing the flag restores normal evaluation.
    flag.store(false, Ordering::Relaxed);
    kb.clear_cancel_flag();
    assert!(query(&kb, make_query("alis", "danlu")));
}

// ─── Existential introduction (xorlo presupposition) ─────────

#[test]
fn test_xorlo_presupposition_basic() {
    // ro lo gerku cu danlu → presupposition: ∃x. gerku(x)
    // Query ∃x. gerku(x) should find the presupposition Skolem
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));

    // Query: ∃x. gerku(x)
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_xorlo_presupposition_consequent() {
    // ro lo gerku cu danlu → presupposition creates sk entity → rule fires
    // Query ∃x. danlu(x) should find the derived fact
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_xorlo_presupposition_conjunction() {
    // THE BUG FIX: ro lo gerku cu danlu, then ? lo gerku cu danlu
    // (∃x. gerku(x) ∧ danlu(x)) should be TRUE
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));

    let mut nodes = Vec::new();
    let p1 = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let p2 = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let conj = and(&mut nodes, p1, p2);
    let root = exists(&mut nodes, "x", conj);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_xorlo_presupposition_with_real_entity() {
    // Real entity + presupposition Skolem both satisfy the query
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // Both alis and the presupposition Skolem are in the KB
    assert!(query(&kb, make_query("alis", "danlu")));

    // Witness search should find both alis and the presupposition Skolem
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    assert!(results.len() >= 2); // alis + presupposition Skolem
}

#[test]
fn test_xorlo_presupposition_transitive() {
    // ro lo gerku cu danlu, ro lo danlu cu xanlu
    // Each universal creates its own presupposition Skolem
    // Query ∃x. xanlu(x) should find witnesses via chain
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "xanlu"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "xanlu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_xorlo_presupposition_no_false_positives() {
    // ro lo gerku cu danlu should NOT make mlatu(x) exist
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_native_rule_transitive_chain() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "xanlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(query(&kb, make_query("alis", "xanlu")));
}

#[test]
fn test_native_rule_multiple_entities() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert!(query(&kb, make_query("alis", "danlu")));
    assert!(query(&kb, make_query("bob", "danlu")));
}

#[test]
fn test_native_rule_negated_universal() {
    // A universal with a NEGATED conclusion — ∀x. gerku(x) → ¬danlu(x), encoded as
    // ∀x. ¬gerku(x) ∨ ¬danlu(x). The conclusion atom ¬danlu(x) is not a flat
    // predicate, so it cannot be compiled into a backward-chaining template.
    //
    // This used to be silently dropped to an empty-conclusion `__fallback__` rule
    // (dead, never matched), and the test "passed for the wrong reason": danlu(alis)
    // was simply never derivable. The compiler now FAILS CLOSED (todo.md: "Negated
    // conclusions silently dropped to __fallback__") — the assertion is rejected
    // rather than registering a misleading dead rule.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));

    let mut nodes = Vec::new();
    let restrict = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let body_pred = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_body = not(&mut nodes, body_pred);
    let neg_restrict = not(&mut nodes, restrict);
    let disj = or(&mut nodes, neg_restrict, neg_body);
    let root = forall(&mut nodes, "_v0", disj);
    let result = kb.assert_fact_inner(
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
        String::new(),
    );
    assert!(
        result.is_err(),
        "negated-conclusion universal must be rejected (fail-closed), got {result:?}"
    );

    // danlu(alis) must not be derivable either way.
    assert!(!query(&kb, make_query("alis", "danlu")));
}

/// Build the rule ∀x. (gerku(x) ∧ ¬mlatu(x)) → danlu(x)
/// encoded as ∀x. ¬(gerku(x) ∧ ¬mlatu(x)) ∨ danlu(x).
fn make_negated_antecedent_rule() -> LogicBuffer {
    let mut nodes = Vec::new();
    let gerku = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let mlatu = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_mlatu = not(&mut nodes, mlatu);
    let antecedent = and(&mut nodes, gerku, neg_mlatu);
    let danlu = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_antecedent = not(&mut nodes, antecedent);
    let disj = or(&mut nodes, neg_antecedent, danlu);
    let root = forall(&mut nodes, "_v0", disj);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Regression: a negated antecedent condition must be evaluated via
/// negation-as-failure, not as a positive requirement. Untraced path.
#[test]
fn test_naf_negated_antecedent_untraced() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_negated_antecedent_rule());

    // mlatu(alis) is unprovable → ¬mlatu holds (NAF) → the rule fires.
    assert!(
        query(&kb, make_query("alis", "danlu")),
        "danlu(alis) should hold: gerku true and mlatu unprovable (NAF)"
    );

    // Asserting mlatu(alis) makes ¬mlatu false → the rule must no longer fire.
    assert_buf(&kb, make_assertion("alis", "mlatu"));
    assert!(
        matches!(
            query_result(&kb, make_query("alis", "danlu")),
            QueryResult::False
        ),
        "danlu(alis) should be FALSE once mlatu(alis) is asserted"
    );
}

/// Regression: the traced (proof) path must agree with the untraced verdict
/// and record the negated condition as a negation-as-failure dependency.
#[test]
fn test_naf_negated_antecedent_traced() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_negated_antecedent_rule());

    let (result, trace) = kb
        .query_entailment_with_proof_inner(make_query("alis", "danlu"))
        .unwrap();
    assert!(
        result.is_true(),
        "traced verdict should be TRUE before mlatu"
    );
    assert!(
        trace.has_naf_dependency(),
        "proof should record a negation-as-failure dependency for ¬mlatu"
    );

    assert_buf(&kb, make_assertion("alis", "mlatu"));
    let (result2, _trace2) = kb
        .query_entailment_with_proof_inner(make_query("alis", "danlu"))
        .unwrap();
    assert!(
        result2.is_false(),
        "traced verdict should be FALSE after mlatu(alis) is asserted"
    );
}

/// White-box guard for the And-flattening prerequisite: the negated-antecedent
/// rule must register with two conditions [gerku, mlatu], mlatu (index 1) flagged
/// negated, and a positive danlu conclusion.
#[test]
fn test_naf_negated_antecedent_rule_shape() {
    let kb = new_kb();
    assert_buf(&kb, make_negated_antecedent_rule());

    let inner = kb.inner.borrow();
    let rule = inner
        .universal_rules
        .values()
        .flatten()
        .find(|r| r.typed_conclusions.iter().any(|c| c.relation() == "danlu"))
        .expect("a rule concluding danlu should be registered");

    let cond_rels: Vec<&str> = rule.typed_conditions.iter().map(|c| c.relation()).collect();
    assert_eq!(
        cond_rels,
        vec!["gerku", "mlatu"],
        "antecedent And should flatten into two conditions"
    );
    assert_eq!(
        rule.negated_condition_indices,
        vec![1],
        "mlatu (index 1) should be the negated condition"
    );
}

#[test]
fn test_native_rule_duplicate_rule_no_panic() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_query_result_false_for_missing_fact() {
    let kb = new_kb();
    let result = query_result(&kb, make_query("alis", "gerku"));
    assert!(matches!(result, QueryResult::False));
}

#[test]
fn test_query_result_unknown_for_cycle_cut() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "gerku"));

    let result = query_result(&kb, make_query("alis", "gerku"));
    assert!(matches!(
        result,
        QueryResult::Unknown(UnknownReason::CycleCut)
    ));

    let (result, _) = kb
        .query_entailment_with_proof_inner(make_query("alis", "gerku"))
        .unwrap();
    assert!(matches!(
        result,
        QueryResult::Unknown(UnknownReason::CycleCut)
    ));
}

#[test]
fn test_query_result_resource_exceeded_for_depth_limit() {
    let kb = new_kb();
    kb.inner.borrow_mut().max_chain_depth = 1;

    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "xanlu"));

    let result = query_result(&kb, make_query("alis", "xanlu"));
    assert!(matches!(
        result,
        QueryResult::ResourceExceeded(ResourceKind::Depth)
    ));

    let (result, _) = kb
        .query_entailment_with_proof_inner(make_query("alis", "xanlu"))
        .unwrap();
    assert!(matches!(
        result,
        QueryResult::ResourceExceeded(ResourceKind::Depth)
    ));
}

// ─── Proof-trace / verdict consistency (EG-M2 + LP-M3 display half) ──
//
// The displayed proof must never contradict the authoritative four-valued
// verdict: under Unknown/ResourceExceeded the trace must NOT assert a decided
// FALSE (ForallCounterexample / ExistsFailed / PredicateNotFound) or a NAF-true
// negation. A genuine definitive False MUST still show its counterexample.

/// Assert the proof trace's root step is consistent with the four-valued verdict.
fn assert_trace_consistent(result: &QueryResult, trace: &ProofTrace) {
    let root = &trace.steps[trace.root as usize];
    match result {
        QueryResult::True => assert!(root.holds, "True verdict but root step holds=false"),
        QueryResult::False => assert!(!root.holds, "False verdict but root step holds=true"),
        QueryResult::Unknown(_) | QueryResult::ResourceExceeded(_) => {
            assert!(
                !root.holds,
                "non-definitive verdict {result:?} but root step holds=true"
            );
            assert!(
                !matches!(
                    root.rule,
                    ProofRule::ForallCounterexample(_)
                        | ProofRule::ExistsFailed
                        | ProofRule::PredicateNotFound(_)
                ),
                "non-definitive verdict {result:?} but root asserts a decided failure: {:?}",
                root.rule
            );
        }
    }
    assert_proof_refs_resolve_to_holds_true(trace);
}

/// Stage 2d invariant: the proof memo only caches `holds:true` derivations (the
/// depth-relative `PredicateNotFound` is no longer memoized), so EVERY `ProofRef`
/// leaf must resolve to a `holds:true` step. A `ProofRef` pointing at a `holds:false`
/// step is the cross-recursion-depth not-found poisoning this stage removed.
fn assert_proof_refs_resolve_to_holds_true(trace: &ProofTrace) {
    for (i, step) in trace.steps.iter().enumerate() {
        if matches!(step.rule, ProofRule::ProofRef(_)) {
            let target = step.children[0] as usize;
            assert!(
                trace.steps[target].holds,
                "ProofRef step #{i} resolves to a holds:false step #{target} ({:?}) — \
                 stale not-found memo poisoning",
                trace.steps[target].rule
            );
        }
    }
}

#[test]
fn trace_does_not_contradict_unknown_cyclecut() {
    // gerku ⟸ danlu ⟸ gerku: querying gerku(alis) cuts the cycle → Unknown.
    // The trace must not display a decided "predicate not found" under Unknown.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "gerku"));
    let (result, trace) = kb
        .query_entailment_with_proof_inner(make_query("alis", "gerku"))
        .unwrap();
    assert!(matches!(
        result,
        QueryResult::Unknown(UnknownReason::CycleCut)
    ));
    assert_trace_consistent(&result, &trace);
}

#[test]
fn backchain_cycle_cut_trace_parity() {
    // Regression LOCK (GREEN before+after the 2b core merge): over a cyclic rule
    // set (gerku ⟸ danlu ⟸ gerku), the untraced verdict path and the
    // proof-recording path must reach the SAME Unknown(CycleCut) verdict. The
    // merged `try_backward_chain_core` threads ONE shared `visited` through both
    // walks (closing the former traced-path per-condition fresh-`HashSet` cycle
    // asymmetry, LP-L2), so the recording walk can no longer re-expand a cycle
    // that the untraced walk cut. The trace root must stay non-committal.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "gerku"));

    // Untraced (authoritative) verdict.
    let untraced = kb
        .query_entailment_inner(make_query("alis", "gerku"))
        .unwrap();
    assert!(
        matches!(untraced, QueryResult::Unknown(UnknownReason::CycleCut)),
        "untraced verdict over a cycle should be Unknown(CycleCut), got {untraced:?}"
    );

    // Recording (proof) path — same KB, same query: must agree.
    let (traced, trace) = kb
        .query_entailment_with_proof_inner(make_query("alis", "gerku"))
        .unwrap();
    assert!(
        matches!(traced, QueryResult::Unknown(UnknownReason::CycleCut)),
        "recording-path verdict should match the untraced Unknown(CycleCut), got {traced:?}"
    );
    assert_trace_consistent(&traced, &trace);
}

#[test]
fn unknown_left_and_evaluates_right_conjunct() {
    // 2c: the merged And short-circuits ONLY on a definitively-False left. With a
    // non-definitive (Unknown(CycleCut)) left conjunct, the right is still
    // evaluated and BOTH children are recorded — where the former boolean traced
    // evaluator short-circuited on any falsy (incl. Unknown) left and recorded
    // only the left. The verdict (Unknown) is unchanged. This trace change is
    // confined to non-definitive queries (book proofs are all-True, so it is
    // invisible to verify-book-capture); pinned here instead.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "gerku")); // gerku ⟸ danlu ⟸ gerku cycle
    assert_buf(&kb, make_assertion("rex", "mlatu")); // a definitively-True conjunct

    let mut nodes = Vec::new();
    let gerku_rex = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("rex".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let mlatu_rex = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("rex".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = and(&mut nodes, gerku_rex, mlatu_rex);
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };

    let (result, trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    assert!(
        matches!(result, QueryResult::Unknown(UnknownReason::CycleCut)),
        "Unknown(CycleCut) ∧ True should be Unknown(CycleCut), got {result:?}"
    );
    assert_trace_consistent(&result, &trace);
    let root_step = &trace.steps[trace.root as usize];
    assert!(
        matches!(root_step.rule, ProofRule::Conjunction),
        "root should be a Conjunction, got {:?}",
        root_step.rule
    );
    assert_eq!(
        root_step.children.len(),
        2,
        "the right conjunct must be evaluated and recorded even though the left is non-definitive"
    );
}

#[test]
fn trace_does_not_show_counterexample_under_depth_exceeded() {
    // max depth 1, chain gerku→danlu→xanlu, gerku(alis). ∀x. xanlu(x) over the
    // singleton domain {alis} exceeds the depth budget → ResourceExceeded(Depth);
    // the trace must NOT show a decided ForallCounterexample.
    let kb = new_kb();
    kb.inner.borrow_mut().max_chain_depth = 1;
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "xanlu"));
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "xanlu",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = forall(&mut nodes, "x", body);
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };
    let (result, trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    assert!(
        matches!(result, QueryResult::ResourceExceeded(ResourceKind::Depth)),
        "got {result:?}"
    );
    assert_trace_consistent(&result, &trace);
    assert!(
        !trace
            .steps
            .iter()
            .any(|s| matches!(s.rule, ProofRule::ForallCounterexample(_))),
        "depth-exceeded ForAll must not display a decided counterexample"
    );
}

#[test]
fn trace_naf_flag_false_when_inner_is_unknown() {
    // ¬gerku(alis) where gerku(alis) is Unknown(CycleCut), NOT definitively False.
    // negate_result preserves Unknown, so the verdict is Unknown and the trace
    // must NOT claim a NAF dependency (a boolean !false would wrongly do so).
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "gerku"));
    let mut nodes = Vec::new();
    let inner = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = not(&mut nodes, inner);
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };
    let (result, trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    assert!(matches!(result, QueryResult::Unknown(_)), "got {result:?}");
    assert!(
        !trace.has_naf_dependency(),
        "NAF flag must be false when the negated inner is Unknown, not definitively False"
    );
}

#[test]
fn trace_exists_failed_only_when_all_definitively_false() {
    // Ground material conditionals gerku(x)⟸danlu(x) and danlu(x)⟸gerku(x) form a
    // positive cycle WITHOUT xorlo witnesses (unlike `ro lo` universals), so
    // gerku(x) is Unknown(CycleCut) and ∃y.gerku(y) — whose only candidate is the
    // rule-derivable `x` — has no satisfying witness. Verdict Unknown → the trace
    // must NOT show a decided ExistsFailed.
    let kb = new_kb();
    assert_buf(&kb, make_material_cond("gerku", "danlu", false));
    assert_buf(&kb, make_material_cond("danlu", "gerku", false));
    let mut nodes = Vec::new();
    let body = pred(&mut nodes, "gerku", vec![LogicalTerm::Variable("y".into())]);
    let root = exists(&mut nodes, "y", body);
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };
    let (result, trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    assert!(matches!(result, QueryResult::Unknown(_)), "got {result:?}");
    assert_trace_consistent(&result, &trace);
    assert!(
        !trace
            .steps
            .iter()
            .any(|s| matches!(s.rule, ProofRule::ExistsFailed)),
        "Exists over an Unknown candidate must not display a decided ExistsFailed"
    );
}

#[test]
fn forall_genuine_counterexample_still_traced() {
    // Positive guard against over-suppression: a genuinely-False member (bob,
    // known but not mlatu) under a definitive False verdict MUST still be shown
    // as a ForallCounterexample.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "mlatu")); // mlatu(alis) true; alis known
    assert_buf(&kb, make_assertion("bob", "gerku")); // bob known, not mlatu
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "mlatu",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = forall(&mut nodes, "x", body);
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };
    let (result, trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    assert!(matches!(result, QueryResult::False), "got {result:?}");
    assert_trace_consistent(&result, &trace);
    assert!(
        trace
            .steps
            .iter()
            .any(|s| matches!(s.rule, ProofRule::ForallCounterexample(_))),
        "a genuine False member must still be shown as a counterexample"
    );
}

// ─── Dependent Skolem (Phase B) Tests ────────────────────────────

fn make_dependent_skolem_universal(restrictor: &str, consequent: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let restrict = pred(
        &mut nodes,
        restrictor,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let body = pred(
        &mut nodes,
        consequent,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Variable("_v1".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let ex = exists(&mut nodes, "_v1", body);
    let neg = not(&mut nodes, restrict);
    let disj = or(&mut nodes, neg, ex);
    let root = forall(&mut nodes, "_v0", disj);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

fn make_exists_query(entity: &str, predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        predicate,
        vec![
            LogicalTerm::Constant(entity.to_string()),
            LogicalTerm::Variable("_v1".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "_v1", body);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_dependent_skolem_native_rule() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
    assert!(query(&kb, make_exists_query("alis", "zdani")));
}

#[test]
fn test_dependent_skolem_entity_after_rule() {
    let kb = new_kb();
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert!(query(&kb, make_exists_query("alis", "zdani")));
}

#[test]
fn test_dependent_skolem_query_existential() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
    assert!(query(&kb, make_exists_query("alis", "zdani")));
    assert!(!query(&kb, make_exists_query("bob", "zdani")));
}

#[test]
fn test_skolem_fn_multiple_entities() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_assertion("bob", "prenu"));
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
    assert!(query(&kb, make_exists_query("alis", "zdani")));
    assert!(query(&kb, make_exists_query("bob", "zdani")));
}

#[test]
fn test_skolem_fn_registry_populated() {
    let kb = new_kb();
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
    let inner = kb.inner.borrow();
    assert!(
        !inner.skolem_fn_registry.is_empty(),
        "SkolemFn registry should have entries"
    );
    assert_eq!(inner.skolem_fn_registry[0].base_name, "sk_0");
    assert_eq!(inner.skolem_fn_registry[0].dep_count, 1);
}

// ─── Multi-Dependency SkolemFn Tests ─────────────────────────

/// Build: ∀_v0. ∀_v1. (¬(prenu(_v0, zo'e) ∧ mlatu(_v1, zo'e)) ∨ ∃_v2. zdani(_v0, _v1, _v2))
/// Meaning: for all persons x and cats y, there exists a z such that zdani(x, y, z).
fn make_multi_dep_skolem_universal() -> LogicBuffer {
    let mut nodes = Vec::new();
    let p = pred(
        &mut nodes,
        "prenu",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let q = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Variable("_v1".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let conj = and(&mut nodes, p, q);
    let body = pred(
        &mut nodes,
        "zdani",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Variable("_v1".to_string()),
            LogicalTerm::Variable("_v2".to_string()),
        ],
    );
    let ex = exists(&mut nodes, "_v2", body);
    let neg = not(&mut nodes, conj);
    let disj = or(&mut nodes, neg, ex);
    let inner_forall = forall(&mut nodes, "_v1", disj);
    let root = forall(&mut nodes, "_v0", inner_forall);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Query: ∃_v2. zdani(entity_a, entity_b, _v2)
fn make_multi_dep_exists_query(entity_a: &str, entity_b: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "zdani",
        vec![
            LogicalTerm::Constant(entity_a.to_string()),
            LogicalTerm::Constant(entity_b.to_string()),
            LogicalTerm::Variable("_v2".to_string()),
        ],
    );
    let root = exists(&mut nodes, "_v2", body);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_multi_dep_skolem_two_universals() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_assertion("felix", "mlatu"));
    assert_buf(&kb, make_multi_dep_skolem_universal());
    // ∃z. zdani(alis, felix, z) should be TRUE via SkolemFn with 2 deps
    assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
}

#[test]
fn test_multi_dep_skolem_registry() {
    let kb = new_kb();
    assert_buf(&kb, make_multi_dep_skolem_universal());
    let inner = kb.inner.borrow();
    assert!(!inner.skolem_fn_registry.is_empty());
    assert_eq!(inner.skolem_fn_registry[0].dep_count, 2);
}

/// CYP-shape: ∀_v0. ∀_v1. ∀_v3. ¬(prenu(_v0) ∧ mlatu(_v1) ∧ gerku(_v3)) ∨ ∃_v2. zdani(_v1, _v2)
/// The conclusion existential _v2 references ONLY _v1, so its dependent Skolem depends on a
/// single universal even though 3 universals are in scope (dependency precision).
fn make_cyp_shape_universal() -> LogicBuffer {
    let mut nodes = Vec::new();
    let p = pred(
        &mut nodes,
        "prenu",
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let q = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Variable("_v1".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let r = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("_v3".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let conj_pq = and(&mut nodes, p, q);
    let conj = and(&mut nodes, conj_pq, r);
    let body = pred(
        &mut nodes,
        "zdani",
        vec![
            LogicalTerm::Variable("_v1".to_string()),
            LogicalTerm::Variable("_v2".to_string()),
        ],
    );
    let ex = exists(&mut nodes, "_v2", body);
    let neg = not(&mut nodes, conj);
    let disj = or(&mut nodes, neg, ex);
    let f3 = forall(&mut nodes, "_v3", disj);
    let f1 = forall(&mut nodes, "_v1", f3);
    let root = forall(&mut nodes, "_v0", f1);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_dependent_skolem_precise_deps_single_universal() {
    let kb = new_kb();
    assert_buf(&kb, make_cyp_shape_universal());
    let inner = kb.inner.borrow();
    assert!(!inner.skolem_fn_registry.is_empty());
    // The conclusion existential references only _v1, so dep_count is 1 — NOT 3, even though
    // three universals are in scope. The old over-approximation gave 3, inflating the firing
    // candidate cartesian to members^3 (the prenex CYP-join blowup).
    assert_eq!(inner.skolem_fn_registry[0].dep_count, 1);
}

#[test]
fn test_multi_dep_skolem_different_entities() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_assertion("bob", "prenu"));
    assert_buf(&kb, make_assertion("felix", "mlatu"));
    assert_buf(&kb, make_assertion("garfield", "mlatu"));
    assert_buf(&kb, make_multi_dep_skolem_universal());
    // All combinations of person × cat should have zdani witnesses
    assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
    assert!(query(&kb, make_multi_dep_exists_query("alis", "garfield")));
    assert!(query(&kb, make_multi_dep_exists_query("bob", "felix")));
    assert!(query(&kb, make_multi_dep_exists_query("bob", "garfield")));
    // Non-prenu or non-mlatu entities should NOT have zdani witnesses
    assert!(!query(&kb, make_multi_dep_exists_query("felix", "alis")));
}

#[test]
fn test_multi_dep_skolem_rule_before_facts() {
    let kb = new_kb();
    // Rule first, then facts
    assert_buf(&kb, make_multi_dep_skolem_universal());
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_assertion("felix", "mlatu"));
    assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
}

// ─── Numeric Comparison Tests ────────────────────────────────

/// Build a comparison predicate: Pred(rel, [Num(a), Num(b), Zoe, ...])
fn make_numeric_pred(nodes: &mut Vec<LogicNode>, relation: &str, a: f64, b: f64) -> u32 {
    let mut args = vec![
        LogicalTerm::Number(a),
        LogicalTerm::Number(b),
        LogicalTerm::Unspecified,
    ];
    // zmadu and mleca have arity 4; dunli has arity 3
    if relation == "zmadu" || relation == "mleca" {
        args.push(LogicalTerm::Unspecified);
    }
    pred(nodes, relation, args)
}

fn make_numeric_query(relation: &str, a: f64, b: f64) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = make_numeric_pred(&mut nodes, relation, a, b);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_zmadu_numeric_true() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("zmadu", 2.0, 1.0)));
}

#[test]
fn test_zmadu_numeric_false() {
    let kb = new_kb();
    assert!(!query(&kb, make_numeric_query("zmadu", 1.0, 2.0)));
}

#[test]
fn test_zmadu_numeric_equal_false() {
    let kb = new_kb();
    assert!(!query(&kb, make_numeric_query("zmadu", 2.0, 2.0)));
}

#[test]
fn test_mleca_numeric_true() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("mleca", 1.0, 2.0)));
}

#[test]
fn test_mleca_numeric_false() {
    let kb = new_kb();
    assert!(!query(&kb, make_numeric_query("mleca", 2.0, 1.0)));
}

#[test]
fn test_dunli_numeric_true() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("dunli", 5.0, 5.0)));
}

#[test]
fn test_dunli_numeric_false() {
    let kb = new_kb();
    assert!(!query(&kb, make_numeric_query("dunli", 5.0, 3.0)));
}

#[test]
fn test_zmadu_negated() {
    let kb = new_kb();
    // NOT (1 > 2) should be TRUE
    let mut nodes = Vec::new();
    let cmp = make_numeric_pred(&mut nodes, "zmadu", 1.0, 2.0);
    let root = not(&mut nodes, cmp);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_zmadu_non_numeric_fallback() {
    let kb = new_kb();
    // Non-numeric zmadu: assert then query via standard KB path
    let mut a_nodes = Vec::new();
    let a_root = pred(
        &mut a_nodes,
        "zmadu",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Unspecified,
            LogicalTerm::Unspecified,
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![a_root],
        },
    );

    let mut q_nodes = Vec::new();
    let q_root = pred(
        &mut q_nodes,
        "zmadu",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Unspecified,
            LogicalTerm::Unspecified,
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_zmadu_large_numbers() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_numeric_query("zmadu", 1_000_000.0, 999_999.0)
    ));
}

#[test]
fn test_zmadu_negative_numbers() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("zmadu", -1.0, -2.0)));
    assert!(!query(&kb, make_numeric_query("zmadu", -2.0, -1.0)));
}

// ─── ComputeNode Tests ───────────────────────────────────────

/// Helper: build a ComputeNode with the given relation and args.
fn compute(nodes: &mut Vec<LogicNode>, rel: &str, args: Vec<LogicalTerm>) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::ComputeNode((rel.to_string(), args)));
    id
}

/// Helper: build a ComputeNode query buffer for arithmetic predicates.
fn make_compute_query(rel: &str, x1: f64, x2: f64, x3: f64) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = compute(
        &mut nodes,
        rel,
        vec![
            LogicalTerm::Number(x1),
            LogicalTerm::Number(x2),
            LogicalTerm::Number(x3),
        ],
    );
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_compute_pilji_true() {
    let kb = new_kb();
    // 6 = 2 * 3
    assert!(query(&kb, make_compute_query("pilji", 6.0, 2.0, 3.0)));
}

#[test]
fn test_compute_pilji_false() {
    let kb = new_kb();
    // 7 != 2 * 3
    assert!(!query(&kb, make_compute_query("pilji", 7.0, 2.0, 3.0)));
}

#[test]
fn test_compute_sumji_true() {
    let kb = new_kb();
    // 5 = 2 + 3
    assert!(query(&kb, make_compute_query("sumji", 5.0, 2.0, 3.0)));
}

#[test]
fn test_compute_sumji_false() {
    let kb = new_kb();
    // 4 != 2 + 3
    assert!(!query(&kb, make_compute_query("sumji", 4.0, 2.0, 3.0)));
}

#[test]
fn test_compute_dilcu_true() {
    let kb = new_kb();
    // 3 = 6 / 2
    assert!(query(&kb, make_compute_query("dilcu", 3.0, 6.0, 2.0)));
}

#[test]
fn test_compute_dilcu_division_by_zero() {
    let kb = new_kb();
    // x / 0 is always false
    assert!(!query(&kb, make_compute_query("dilcu", 0.0, 5.0, 0.0)));
}

// ─── Decomposed numeric groups (surface-Lojban shape) ─────────────
//
// Surface numeric bridi event-decompose to ∃ev. head(ev) ∧ rel_x1(ev, a) ∧
// rel_x2(ev, b) ∧ ... — a LEFT-nested And where the head carries only the
// event variable and the operands live in sibling role predicates. These
// tests build that exact shape (mirroring smuni's event_decompose output)
// and pin that the numeric evaluators reach the operands.

/// Decomposed compute group: ∃_ev0. (((Compute(rel,[ev]) ∧ rel_x1(ev,x1))
/// ∧ rel_x2(ev,x2)) ∧ rel_x3(ev,x3)) — the surface shape for pilji/sumji/dilcu.
fn make_decomposed_compute_query(rel: &str, x1: f64, x2: f64, x3: f64) -> LogicBuffer {
    let mut nodes = Vec::new();
    let ev = || LogicalTerm::Variable("_ev0".to_string());
    let head = compute(&mut nodes, rel, vec![ev()]);
    let mut acc = head;
    for (i, v) in [x1, x2, x3].iter().enumerate() {
        let role = pred(
            &mut nodes,
            &format!("{rel}_x{}", i + 1),
            vec![ev(), LogicalTerm::Number(*v)],
        );
        acc = and(&mut nodes, acc, role);
    }
    let root = exists(&mut nodes, "_ev0", acc);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Decomposed comparison group: ∃_ev0. head Pred(rel,[ev]) ∧ rel_x1(ev,a) ∧
/// rel_x2(ev,b) ∧ Zoe-padded trailing roles (zmadu/mleca arity 4, dunli 3).
fn make_decomposed_comparison_query(rel: &str, a: f64, b: f64) -> LogicBuffer {
    let mut nodes = Vec::new();
    let ev = || LogicalTerm::Variable("_ev0".to_string());
    let head = pred(&mut nodes, rel, vec![ev()]);
    let arity = if rel == "dunli" { 3 } else { 4 };
    let mut acc = head;
    for i in 1..=arity {
        let arg = match i {
            1 => LogicalTerm::Number(a),
            2 => LogicalTerm::Number(b),
            _ => LogicalTerm::Unspecified,
        };
        let role = pred(&mut nodes, &format!("{rel}_x{i}"), vec![ev(), arg]);
        acc = and(&mut nodes, acc, role);
    }
    let root = exists(&mut nodes, "_ev0", acc);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_decomposed_pilji_true() {
    let kb = new_kb();
    // 10 = 2 * 5 through the decomposed surface shape
    assert!(query(
        &kb,
        make_decomposed_compute_query("pilji", 10.0, 2.0, 5.0)
    ));
}

#[test]
fn test_decomposed_pilji_false() {
    let kb = new_kb();
    assert!(!query(
        &kb,
        make_decomposed_compute_query("pilji", 11.0, 2.0, 5.0)
    ));
}

#[test]
fn test_decomposed_sumji_true_false() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_decomposed_compute_query("sumji", 5.0, 2.0, 3.0)
    ));
    assert!(!query(
        &kb,
        make_decomposed_compute_query("sumji", 6.0, 2.0, 3.0)
    ));
}

#[test]
fn test_decomposed_dilcu_true_and_division_by_zero() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_decomposed_compute_query("dilcu", 3.0, 6.0, 2.0)
    ));
    // Division by zero is a definitive FALSE, not an error or fall-through.
    assert!(!query(
        &kb,
        make_decomposed_compute_query("dilcu", 3.0, 6.0, 0.0)
    ));
}

#[test]
fn test_decomposed_zmadu_true_false() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_decomposed_comparison_query("zmadu", 5.0, 3.0)
    ));
    assert!(!query(
        &kb,
        make_decomposed_comparison_query("zmadu", 3.0, 5.0)
    ));
}

#[test]
fn test_decomposed_mleca_true_false() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_decomposed_comparison_query("mleca", 2.0, 3.0)
    ));
    assert!(!query(
        &kb,
        make_decomposed_comparison_query("mleca", 3.0, 2.0)
    ));
}

#[test]
fn test_decomposed_dunli_true_false() {
    let kb = new_kb();
    assert!(query(
        &kb,
        make_decomposed_comparison_query("dunli", 3.0, 3.0)
    ));
    assert!(!query(
        &kb,
        make_decomposed_comparison_query("dunli", 3.0, 2.0)
    ));
}

#[test]
fn test_decomposed_negated() {
    // Not(∃ev. group) — the Not arm recurses into the Exists arm, so the
    // group verdict flips with no special handling.
    let kb = new_kb();
    let mut buf = make_decomposed_comparison_query("zmadu", 3.0, 5.0);
    let inner_root = buf.roots[0];
    let neg = {
        let id = buf.nodes.len() as u32;
        buf.nodes.push(LogicNode::NotNode(inner_root));
        id
    };
    buf.roots = vec![neg];
    assert!(query(&kb, buf), "NOT(3 > 5) must be TRUE");
}

#[test]
fn test_decomposed_extra_conjunct_falls_through() {
    // A group with an unrelated conjunct must NOT shortcut: the strict
    // same-relation rule bails, normal evaluation runs, and the unprovable
    // extra conjunct makes the query FALSE even though the arithmetic is true.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let ev = || LogicalTerm::Variable("_ev0".to_string());
    let head = compute(&mut nodes, "pilji", vec![ev()]);
    let x1 = pred(
        &mut nodes,
        "pilji_x1",
        vec![ev(), LogicalTerm::Number(10.0)],
    );
    let x2 = pred(&mut nodes, "pilji_x2", vec![ev(), LogicalTerm::Number(2.0)]);
    let x3 = pred(&mut nodes, "pilji_x3", vec![ev(), LogicalTerm::Number(5.0)]);
    let extra = pred(&mut nodes, "broda", vec![ev()]);
    let a1 = and(&mut nodes, head, x1);
    let a2 = and(&mut nodes, a1, x2);
    let a3 = and(&mut nodes, a2, x3);
    let body = and(&mut nodes, a3, extra);
    let root = exists(&mut nodes, "_ev0", body);
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };
    assert!(
        !query(&kb, buf),
        "an unrelated conjunct must disable the numeric-group shortcut"
    );
}

#[test]
fn test_decomposed_non_numeric_falls_through_to_store() {
    // Non-numeric operands can't compute; the group must fall through to
    // normal evaluation, where the asserted decomposed facts satisfy it.
    let kb = new_kb();
    let make = || {
        let mut nodes = Vec::new();
        let ev = || LogicalTerm::Variable("_ev0".to_string());
        let head = pred(&mut nodes, "zmadu", vec![ev()]);
        let x1 = pred(
            &mut nodes,
            "zmadu_x1",
            vec![ev(), LogicalTerm::Constant("alis".to_string())],
        );
        let x2 = pred(
            &mut nodes,
            "zmadu_x2",
            vec![ev(), LogicalTerm::Constant("bob".to_string())],
        );
        let a1 = and(&mut nodes, head, x1);
        let body = and(&mut nodes, a1, x2);
        let root = exists(&mut nodes, "_ev0", body);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    };
    assert_buf(&kb, make());
    assert!(
        query(&kb, make()),
        "asserted non-numeric zmadu group must stay queryable via the store"
    );
}

#[test]
fn test_decomposed_asserted_true_group_still_true() {
    // Asserting an arithmetically-true group then querying it: the computed
    // verdict agrees with the store, so shadowing is invisible for true facts.
    let kb = new_kb();
    assert_buf(&kb, make_decomposed_compute_query("pilji", 10.0, 2.0, 5.0));
    assert!(query(
        &kb,
        make_decomposed_compute_query("pilji", 10.0, 2.0, 5.0)
    ));
}

#[test]
fn test_decomposed_traced_compute_check() {
    // The traced evaluator must agree with the untraced verdict and record
    // a ComputeCheck step for the group.
    let kb = new_kb();
    let (result, trace) =
        query_with_proof(&kb, make_decomposed_compute_query("pilji", 10.0, 2.0, 5.0));
    assert!(result, "traced 10 = 2 × 5 must be TRUE");
    assert!(
        trace
            .steps
            .iter()
            .any(|s| matches!(&s.rule, ProofRule::ComputeCheck(_)) && s.holds),
        "trace must contain a holding ComputeCheck step"
    );

    let (result_f, trace_f) =
        query_with_proof(&kb, make_decomposed_comparison_query("zmadu", 3.0, 5.0));
    assert!(!result_f, "traced 3 > 5 must be FALSE");
    assert!(
        trace_f
            .steps
            .iter()
            .any(|s| matches!(&s.rule, ProofRule::ComputeCheck(_)) && !s.holds),
        "trace must contain a non-holding ComputeCheck step"
    );
}

#[test]
fn test_compute_negated() {
    let kb = new_kb();
    // NOT(7 = 2 * 3) → TRUE (because 7 != 6)
    let mut nodes = Vec::new();
    let inner = compute(
        &mut nodes,
        "pilji",
        vec![
            LogicalTerm::Number(7.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    let root = not(&mut nodes, inner);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_compute_node_kb_fallback() {
    // ComputeNode with non-arithmetic predicate falls back to KB lookup
    let kb = new_kb();

    // Assert: klama(alis, zarci) as a regular fact
    let mut a_nodes = Vec::new();
    let a_root = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Constant("zarci".to_string()),
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![a_root],
        },
    );

    // Query as ComputeNode — unknown to arithmetic, should fall through to KB lookup
    let mut q_nodes = Vec::new();
    let q_root = compute(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Constant("zarci".to_string()),
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

// ── Material conditional / modus ponens tests ──

/// Helper: build "ganai la .X. P gi la .X. Q" as Or(Not(Pred(P, [X])), Pred(Q, [X]))
/// This is the logic IR that sentence connective `ganai...gi` produces.
fn make_material_conditional(entity: &str, antecedent: &str, consequent: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let ante = pred(
        &mut nodes,
        antecedent,
        vec![
            LogicalTerm::Constant(entity.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let cons = pred(
        &mut nodes,
        consequent,
        vec![
            LogicalTerm::Constant(entity.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_ante = not(&mut nodes, ante);
    let root = or(&mut nodes, neg_ante, cons);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_material_conditional_modus_ponens() {
    // ganai la .sol. barda gi la .sol. tsali
    // + la .sol. barda
    // → la .sol. tsali should be TRUE via modus ponens
    let kb = new_kb();
    assert_buf(&kb, make_assertion("sol", "barda"));
    assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
    assert!(query(&kb, make_query("sol", "tsali")));
}

#[test]
fn test_material_conditional_modus_ponens_reversed_order() {
    // Assert the conditional FIRST, then the antecedent
    let kb = new_kb();
    assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
    assert_buf(&kb, make_assertion("sol", "barda"));
    assert!(query(&kb, make_query("sol", "tsali")));
}

#[test]
fn test_material_conditional_modus_tollens() {
    // ganai la .sol. barda gi la .sol. tsali
    // + la .sol. na tsali (Not tsali)
    // → la .sol. na barda (Not barda) via modus tollens
    let kb = new_kb();
    assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));

    // Assert Not(tsali(sol))
    let mut neg_nodes = Vec::new();
    let inner = pred(
        &mut neg_nodes,
        "tsali",
        vec![
            LogicalTerm::Constant("sol".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = not(&mut neg_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: neg_nodes,
            roots: vec![root],
        },
    );

    // Query: barda(sol) should be FALSE (modus tollens derives Not(barda(sol)))
    assert!(!query(&kb, make_query("sol", "barda")));
}

#[test]
fn test_material_conditional_antecedent_not_satisfied() {
    // ganai la .sol. barda gi la .sol. tsali
    // (no barda assertion)
    // → la .sol. tsali should be FALSE (antecedent not satisfied)
    let kb = new_kb();
    assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
    assert!(!query(&kb, make_query("sol", "tsali")));
}

#[test]
fn test_material_conditional_chain() {
    // ganai A gi B, ganai B gi C, assert A → derive C
    let kb = new_kb();
    assert_buf(&kb, make_assertion("sol", "tarci"));
    assert_buf(&kb, make_material_conditional("sol", "tarci", "gusni"));
    assert_buf(&kb, make_material_conditional("sol", "gusni", "melbi"));
    assert!(query(&kb, make_query("sol", "melbi")));
}

// ── Deontic predicate tests ──

/// Helper: build a 3-place deontic assertion: Pred(rel, [Const(entity), Const(action), Zoe])
fn make_deontic_assertion(entity: &str, relation: &str, action: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        relation,
        vec![
            LogicalTerm::Constant(entity.to_string()),
            LogicalTerm::Constant(action.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_deontic_bilga_assert_query() {
    // bilga(alis, klama, Zoe) — Alice is obligated to go
    let kb = new_kb();
    assert_buf(&kb, make_deontic_assertion("alis", "bilga", "klama"));
    assert!(query(&kb, make_deontic_assertion("alis", "bilga", "klama")));
    assert!(!query(&kb, make_deontic_assertion("bob", "bilga", "klama")));
}

#[test]
fn test_deontic_curmi_assert_query() {
    // curmi(alis, klama, Zoe) — Alice is permitted to go
    let kb = new_kb();
    assert_buf(&kb, make_deontic_assertion("alis", "curmi", "klama"));
    assert!(query(&kb, make_deontic_assertion("alis", "curmi", "klama")));
    assert!(!query(
        &kb,
        make_deontic_assertion("alis", "curmi", "tavla")
    ));
}

#[test]
fn test_deontic_nitcu_assert_query() {
    // nitcu(alis, klama, Zoe) — Alice needs to go
    let kb = new_kb();
    assert_buf(&kb, make_deontic_assertion("alis", "nitcu", "klama"));
    assert!(query(&kb, make_deontic_assertion("alis", "nitcu", "klama")));
    assert!(!query(
        &kb,
        make_deontic_assertion("alis", "nitcu", "tavla")
    ));
}

#[test]
fn test_deontic_universal_obligation() {
    // ∀x. prenu(x) → bilga(x, Zoe, Zoe) — all people are obligated
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_universal("prenu", "bilga"));
    assert!(query(&kb, make_query("alis", "bilga")));
    assert!(!query(&kb, make_query("bob", "bilga")));
}

#[test]
fn test_deontic_conditional_chain() {
    // ganai bilga(sol) gi nitcu(sol) — if obligated then needed
    // + bilga(sol) → nitcu(sol) via modus ponens
    let kb = new_kb();
    assert_buf(&kb, make_assertion("sol", "bilga"));
    assert_buf(&kb, make_material_conditional("sol", "bilga", "nitcu"));
    assert!(query(&kb, make_query("sol", "nitcu")));
}

// ── Deontic attitudinal tests ──

/// Helper: build an ObligatoryNode wrapping the given node.
fn obligatory(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::ObligatoryNode(inner));
    id
}

/// Helper: build a PermittedNode wrapping the given node.
fn permitted(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::PermittedNode(inner));
    id
}

#[test]
fn test_obligatory_assert_query() {
    // Assert Obligatory(klama(alis, zo'e)) then query exact → TRUE
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = obligatory(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = obligatory(&mut q_nodes, q_inner);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_permitted_assert_query() {
    // Assert Permitted(klama(alis, zo'e)) then query exact → TRUE
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = permitted(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = permitted(&mut q_nodes, q_inner);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_obligatory_transparent() {
    // Assert Obligatory(klama(alis, zo'e)) then query without wrapper → TRUE (transparent)
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = obligatory(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    // Query without obligatory wrapper → still TRUE (pass-through)
    assert!(query(&kb, make_query("alis", "klama")));
}

// ── Compute result ingestion tests ──

#[test]
fn test_compute_result_ingested_into_kb() {
    let kb = new_kb();

    // Query pilji(6, 2, 3) via ComputeNode → TRUE (built-in arithmetic)
    // This should auto-ingest the fact into the KB
    let mut q_nodes = Vec::new();
    let q_root = compute(
        &mut q_nodes,
        "pilji",
        vec![
            LogicalTerm::Number(6.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));

    // Now query the SAME fact as a plain Predicate (not ComputeNode)
    // It should be found directly in the KB because of auto-ingestion
    let mut p_nodes = Vec::new();
    let p_root = pred(
        &mut p_nodes,
        "pilji",
        vec![
            LogicalTerm::Number(6.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: p_nodes,
            roots: vec![p_root]
        }
    ));
}

#[test]
fn test_compute_false_not_ingested() {
    let kb = new_kb();

    // Query pilji(7, 2, 3) via ComputeNode → FALSE (7 != 2*3)
    let mut q_nodes = Vec::new();
    let q_root = compute(
        &mut q_nodes,
        "pilji",
        vec![
            LogicalTerm::Number(7.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));

    // Verify the false fact was NOT ingested as a plain Predicate
    let mut p_nodes = Vec::new();
    let p_root = pred(
        &mut p_nodes,
        "pilji",
        vec![
            LogicalTerm::Number(7.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes: p_nodes,
            roots: vec![p_root]
        }
    ));
}

#[test]
fn test_ingested_result_available_for_reasoning() {
    let kb = new_kb();

    // Step 1: Query sumji(5, 2, 3) via ComputeNode → TRUE, auto-ingests
    let mut q_nodes = Vec::new();
    let q_root = compute(
        &mut q_nodes,
        "sumji",
        vec![
            LogicalTerm::Number(5.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));

    // Step 2: Assert another fact
    assert_buf(&kb, make_assertion("ok", "derived"));

    // Step 3: Query conjunction: And(sumji(5,2,3), derived("ok", Zoe))
    // Both facts should be in KB: sumji from compute ingestion, derived from assertion
    let mut q2_nodes = Vec::new();
    let left = pred(
        &mut q2_nodes,
        "sumji",
        vec![
            LogicalTerm::Number(5.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    let right = pred(
        &mut q2_nodes,
        "derived",
        vec![
            LogicalTerm::Constant("ok".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = and(&mut q2_nodes, left, right);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q2_nodes,
            roots: vec![root]
        }
    ));

    // Step 4: Conjunctive query with a non-ingested compute fact fails
    let mut q3_nodes = Vec::new();
    let l2 = pred(
        &mut q3_nodes,
        "sumji",
        vec![
            LogicalTerm::Number(99.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    let r2 = pred(
        &mut q3_nodes,
        "derived",
        vec![
            LogicalTerm::Constant("ok".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root2 = and(&mut q3_nodes, l2, r2);
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes: q3_nodes,
            roots: vec![root2]
        }
    ));
}

#[test]
fn assert_typed_fact_invalidates_pred_cache() {
    // The cache-freshness invariant AT THE MUTATION POINT: cache a derived
    // predicate as False, then assert (via `assert_typed_fact` — the path ALL
    // five mid-query compute auto-ingestion sites funnel through) the base fact
    // that makes it derivable. The stale False must NOT survive. Pre-fix the
    // re-check returned the cached False (order-dependent wrong answers);
    // post-fix `assert_typed_fact` clears the cache so the re-check re-derives.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu")); // ∀x. gerku(x) → danlu(x)

    let danlu_adam = StoredFact::Bare(GroundFact::new(
        "danlu",
        vec![
            GroundTerm::Constant("adam".to_string()),
            GroundTerm::Unspecified,
        ],
    ));
    let gerku_adam = StoredFact::Bare(GroundFact::new(
        "gerku",
        vec![
            GroundTerm::Constant("adam".to_string()),
            GroundTerm::Unspecified,
        ],
    ));

    clear_and_enable_pred_cache(&kb.inner.borrow());

    // (1) danlu(adam) is not derivable yet (gerku(adam) absent) → caches False.
    {
        let inner = kb.inner.borrow();
        let mut visited = std::collections::HashSet::new();
        let r = check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited);
        assert!(
            r.is_false(),
            "danlu(adam) is not derivable before gerku(adam)"
        );
    }

    // (2) Assert gerku(adam) through the mutation point.
    {
        let mut inner = kb.inner.borrow_mut();
        assert_typed_fact(gerku_adam, &mut inner);
    }

    // (3) Re-check: a stale cached False here means the cache was NOT invalidated.
    {
        let inner = kb.inner.borrow();
        let mut visited = std::collections::HashSet::new();
        let r = check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited);
        assert!(
            r.is_true(),
            "danlu(adam) must derive True once gerku(adam) is asserted — a stale \
             cached False means assert_typed_fact failed to invalidate the cache"
        );
    }
}

#[test]
fn pred_cache_is_per_instance_no_cross_kb_leak() {
    // Two KBs on the same thread. KB-A enables its cache and caches a False for
    // danlu(adam) (gerku(adam) absent). KB-B has gerku(adam), so danlu(adam) IS
    // derivable. With the old THREAD-LOCAL cache, KB-A's enabled+cached False
    // leaked to KB-B on the same thread; per-instance caches keep them isolated.
    let danlu_adam = StoredFact::Bare(GroundFact::new(
        "danlu",
        vec![
            GroundTerm::Constant("adam".to_string()),
            GroundTerm::Unspecified,
        ],
    ));

    let kb_a = new_kb();
    assert_buf(&kb_a, make_universal("gerku", "danlu")); // ∀x. gerku(x) → danlu(x)
    {
        let inner = kb_a.inner.borrow();
        clear_and_enable_pred_cache(&inner);
        let mut visited = std::collections::HashSet::new();
        let r = check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited);
        assert!(
            r.is_false(),
            "KB-A: danlu(adam) is not derivable (no gerku) → caches False"
        );
    }

    let kb_b = new_kb();
    assert_buf(&kb_b, make_universal("gerku", "danlu"));
    assert_buf(&kb_b, make_assertion("adam", "gerku")); // gerku(adam)
    {
        let inner = kb_b.inner.borrow();
        let mut visited = std::collections::HashSet::new();
        let r = check_predicate_in_kb_typed(&danlu_adam, &inner, 0, &mut visited);
        assert!(
            r.is_true(),
            "KB-B: danlu(adam) IS derivable (gerku(adam) present); KB-A's cached \
             False must not leak across per-instance caches"
        );
    }
}

#[test]
fn compute_autoassert_invalidates_stale_cache() {
    // End-to-end through the actual compute auto-assert caller, in a SINGLE query
    // (the bug window — the cache is cleared once at query entry, then persists).
    // Rule `sumji(5,2,3) ⇒ derived(c)` (a ground material conditional), with
    // sumji NOT stored. One query: a probe that returns True but caches
    // derived(c)=False, then a compute conjunct that auto-asserts sumji(5,2,3),
    // then a re-check of derived(c). Pre-fix the re-check reads the stale False
    // (query wrongly False); post-fix the auto-assert clears the cache and
    // derived(c) re-derives True.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("c", "marker")); // always-true right branch

    // Material conditional: Or(Not(sumji(5,2,3)), derived(c)) ⇒ zero-var rule.
    let mut r_nodes = Vec::new();
    let cond = pred(
        &mut r_nodes,
        "sumji",
        vec![
            LogicalTerm::Number(5.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    let concl = pred(
        &mut r_nodes,
        "derived",
        vec![
            LogicalTerm::Constant("c".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let ncond = not(&mut r_nodes, cond);
    let rule_root = or(&mut r_nodes, ncond, concl);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: r_nodes,
            roots: vec![rule_root],
        },
    );

    // Query: And( Or(derived(c), marker(c)) , And( sumji(5,2,3)[compute] , derived(c) ) )
    let mut q = Vec::new();
    let derived_probe = pred(
        &mut q,
        "derived",
        vec![
            LogicalTerm::Constant("c".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let marker = pred(
        &mut q,
        "marker",
        vec![
            LogicalTerm::Constant("c".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let probe = or(&mut q, derived_probe, marker); // True overall, caches derived(c)=False
    let compute_node = compute(
        &mut q,
        "sumji",
        vec![
            LogicalTerm::Number(5.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    ); // computes True, auto-asserts sumji(5,2,3)
    let derived_final = pred(
        &mut q,
        "derived",
        vec![
            LogicalTerm::Constant("c".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let inner_and = and(&mut q, compute_node, derived_final);
    let root = and(&mut q, probe, inner_and);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes: q,
                roots: vec![root]
            }
        ),
        "derived(c) must re-derive True after the compute conjunct auto-asserts \
         sumji(5,2,3) — a stale cached False makes this query wrongly False"
    );
}

// ─── Witness extraction tests ────────────────────────────────

fn query_find(kb: &KnowledgeBase, buf: LogicBuffer) -> Vec<Vec<WitnessBinding>> {
    kb.query_find_inner(buf).unwrap()
}

#[test]
fn test_find_witnesses_single() {
    // Assert klama(mi), query ∃x.klama(x) → x = mi
    let kb = new_kb();
    assert_buf(&kb, make_assertion("mi", "klama"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "klama",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].len(), 1);
    assert_eq!(results[0][0].variable, "x");
    assert!(matches!(&results[0][0].term, LogicalTerm::Constant(c) if c == "mi"));
}

#[test]
fn test_find_witnesses_multiple() {
    // Assert klama(mi) + klama(do), query ∃x.klama(x) → x = mi, x = do
    let kb = new_kb();
    assert_buf(&kb, make_assertion("mi", "klama"));
    assert_buf(&kb, make_assertion("do", "klama"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "klama",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert_eq!(results.len(), 2);
    let mut found: Vec<String> = results
        .iter()
        .map(|bs| {
            assert_eq!(bs.len(), 1);
            assert_eq!(bs[0].variable, "x");
            match &bs[0].term {
                LogicalTerm::Constant(c) => c.clone(),
                _ => panic!("expected Constant"),
            }
        })
        .collect();
    found.sort();
    assert_eq!(found, vec!["do", "mi"]);
}

#[test]
fn test_find_witnesses_conjunction() {
    // Assert klama(mi), prami(mi), klama(do)
    // Query ∃x.(klama(x) ∧ prami(x)) → only x = mi satisfies both
    let kb = new_kb();
    assert_buf(&kb, make_assertion("mi", "klama"));
    assert_buf(&kb, make_assertion("mi", "prami"));
    assert_buf(&kb, make_assertion("do", "klama"));

    let mut nodes = Vec::new();
    let p1 = pred(
        &mut nodes,
        "klama",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let p2 = pred(
        &mut nodes,
        "prami",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let conj = and(&mut nodes, p1, p2);
    let root = exists(&mut nodes, "x", conj);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].len(), 1);
    assert_eq!(results[0][0].variable, "x");
    assert!(matches!(&results[0][0].term, LogicalTerm::Constant(c) if c == "mi"));
}

#[test]
fn test_find_witnesses_multi_root_join_merges_fresh_bindings() {
    // Assert nelci(bob, alis).
    // Query across two roots:
    //   ∃x. nelci(x, alis)
    //   ∃x. ∃y. nelci(x, y)
    // The root join should preserve the fresh y binding from the second root.
    let kb = new_kb();

    let mut anodes = Vec::new();
    let aidx = pred(
        &mut anodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("alis".to_string()),
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: anodes,
            roots: vec![aidx],
        },
    );

    let mut nodes = Vec::new();
    let left_body = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Constant("alis".to_string()),
        ],
    );
    let left_root = exists(&mut nodes, "x", left_body);

    let right_body = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Variable("y".to_string()),
        ],
    );
    let right_inner = exists(&mut nodes, "y", right_body);
    let right_root = exists(&mut nodes, "x", right_inner);

    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![left_root, right_root],
        },
    );

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].len(), 2);
    let vars: std::collections::HashMap<&str, &LogicalTerm> = results[0]
        .iter()
        .map(|binding| (binding.variable.as_str(), &binding.term))
        .collect();
    assert!(matches!(vars["x"], LogicalTerm::Constant(c) if c == "bob"));
    assert!(matches!(vars["y"], LogicalTerm::Constant(c) if c == "alis"));
}

#[test]
fn test_find_witnesses_no_match() {
    // No facts, query ∃x.klama(x) → empty
    let kb = new_kb();

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "klama",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(results.is_empty());
}

#[test]
fn test_find_witnesses_via_universal_rule() {
    // Assert gerku(alis), ∀x.(gerku(x)→danlu(x))
    // Query ∃x.danlu(x) → should find alis (+ presupposition Skolem)
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    // At least alis + presupposition Skolem
    assert!(results.len() >= 1);
    let found: Vec<String> = results
        .iter()
        .filter_map(|bs| match &bs[0].term {
            LogicalTerm::Constant(c) => Some(c.clone()),
            _ => None,
        })
        .collect();
    assert!(
        found.contains(&"alis".to_string()),
        "alis should be a witness"
    );
}

#[test]
fn test_find_witnesses_dependent_skolem_terms_stay_distinct() {
    // Two persons; ∀x. prenu(x) → ∃y. zdani(x, y, _). Each person's witness
    // is a dependent Skolem FUNCTION — sk_N(alis) vs sk_N(bob) — and the
    // WitnessBinding surface must keep them distinguishable. Regression:
    // SkolemFn(name, dep) was collapsed to Constant(name) on conversion,
    // so different entities' witnesses printed identically (`sk_0`).
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_assertion("bob", "prenu"));
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));

    let witnesses_for = |entity: &str| -> Vec<String> {
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "zdani",
            vec![
                LogicalTerm::Constant(entity.to_string()),
                LogicalTerm::Variable("y".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = exists(&mut nodes, "y", body);
        query_find(
            &kb,
            LogicBuffer {
                nodes,
                roots: vec![root],
            },
        )
        .iter()
        .flat_map(|bs| bs.iter())
        .filter(|b| b.variable == "y")
        .filter_map(|b| match &b.term {
            LogicalTerm::Constant(c) => Some(c.clone()),
            _ => None,
        })
        .collect()
    };

    let alis_w = witnesses_for("alis");
    let bob_w = witnesses_for("bob");
    assert!(
        alis_w.iter().any(|w| w.contains("alis")),
        "alis's dependent witness must mention its dependency, got {alis_w:?}"
    );
    assert!(
        bob_w.iter().any(|w| w.contains("bob")),
        "bob's dependent witness must mention its dependency, got {bob_w:?}"
    );
}

#[test]
fn find_dependent_skolem_witness_is_bound_and_unique() {
    // gerku(adam) + ∀x. gerku(x) → ∃y. nelci(x, y, _). The find `?? nelci(adam, y)`
    // must return EXACTLY ONE binding set whose y witness is the BOUND dependent
    // Skolem `sk_N(adam)` — not the unbound conclusion template `sk_N(_)` and not
    // a duplicated binding. Regression (Ch9 verify-book-capture RED): the find
    // path's old candidate collector inserted the raw template
    // `SkolemFn("sk_N", PatternVar)` and appended a generic non-anchored registry
    // cartesian, so the witness rendered `sk_N(_)` and the binding appeared twice,
    // nondeterministically. Now find shares the verdict path's anchored,
    // Unspecified-stripped collector.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert_buf(&kb, make_dependent_skolem_universal("gerku", "nelci"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("adam".to_string()),
            LogicalTerm::Variable("y".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "y", body);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert_eq!(
        results.len(),
        1,
        "exactly one binding set (no duplicate), got {results:?}"
    );
    let y_term = results[0]
        .iter()
        .find(|b| b.variable == "y")
        .map(|b| match &b.term {
            LogicalTerm::Constant(c) => c.clone(),
            other => format!("{other:?}"),
        })
        .expect("a binding for y");
    assert!(
        y_term.contains("(adam)"),
        "dependent witness must be bound to its dependency `(adam)`, got {y_term:?}"
    );
    assert!(
        !y_term.contains("(_)") && !y_term.contains('?'),
        "dependent witness must not be unbound (`sk_N(_)` / `sk_N(?..)`), got {y_term:?}"
    );
}

#[test]
fn count_witnesses_dedups_or_overlap() {
    // ∃x. (gerku(x) ∨ mlatu(x)) with adam satisfying BOTH disjuncts and bob only
    // one. The OrNode arm concatenates left+right witnesses, so adam arrives
    // twice; the return-boundary dedup must collapse it so the count is the
    // number of DISTINCT entities (2), not the raw enumeration (3). An inflated
    // count would be a hallucinated quantity.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert_buf(&kb, make_assertion("adam", "mlatu"));
    assert_buf(&kb, make_assertion("bob", "gerku"));

    let mut nodes = Vec::new();
    let g = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let m = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let disj = or(&mut nodes, g, m);
    let root = exists(&mut nodes, "x", disj);
    let count = kb
        .count_witnesses(LogicBuffer {
            nodes,
            roots: vec![root],
        })
        .unwrap();
    assert_eq!(count, 2, "adam (both disjuncts) counts once; bob once → 2");
}

#[test]
fn find_dependent_skolem_deterministic_across_instances() {
    // Two fresh KBs, opposite assertion orders, same dependent-Skolem find. The
    // deduped+canonically-sorted output must be byte-identical (hasher-seed
    // independent) — locks determinism and dedup together for the dependent
    // witness path.
    let find_query = || {
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("adam".to_string()),
                LogicalTerm::Variable("y".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = exists(&mut nodes, "y", body);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    };

    let kb1 = new_kb();
    assert_buf(&kb1, make_assertion("adam", "gerku"));
    assert_buf(&kb1, make_dependent_skolem_universal("gerku", "nelci"));

    let kb2 = new_kb();
    assert_buf(&kb2, make_dependent_skolem_universal("gerku", "nelci"));
    assert_buf(&kb2, make_assertion("adam", "gerku"));

    let r1 = query_find(&kb1, find_query());
    let r2 = query_find(&kb2, find_query());
    assert_eq!(
        r1, r2,
        "dependent-Skolem find must be identical across assertion orders"
    );
    assert_eq!(r1.len(), 1, "exactly one deduped binding set");
}

#[test]
fn test_proof_trace_exists_witness_renders_dependent_skolem() {
    // ∀x. prenu(x) → ∃y. zdani(x, y, _); query ∃y. zdani(alis, y, _) with
    // proof. The ExistsWitness step's term must render the dependent Skolem
    // functionally (sk_N(alis)), not as its bare base name.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "zdani",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Variable("y".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "y", body);
    let (result, trace) = query_with_proof(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(result);
    let witness_terms: Vec<String> = trace
        .steps
        .iter()
        .filter_map(|s| match &s.rule {
            ProofRule::ExistsWitness((_, LogicalTerm::Constant(c))) => Some(c.clone()),
            _ => None,
        })
        .collect();
    assert!(
        witness_terms.iter().any(|w| w.contains("alis")),
        "ExistsWitness must render the dependent Skolem functionally, got {witness_terms:?}"
    );
}

#[test]
fn test_find_witnesses_two_variables() {
    // Assert nelci(bob, alis), query ∃x.∃y.nelci(x, y)
    // Should find x=bob, y=alis
    let kb = new_kb();

    let mut anodes = Vec::new();
    let aidx = pred(
        &mut anodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("alis".to_string()),
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: anodes,
            roots: vec![aidx],
        },
    );

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Variable("y".to_string()),
        ],
    );
    let inner = exists(&mut nodes, "y", body);
    let root = exists(&mut nodes, "x", inner);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].len(), 2);
    let vars: std::collections::HashMap<&str, &LogicalTerm> = results[0]
        .iter()
        .map(|b| (b.variable.as_str(), &b.term))
        .collect();
    assert!(matches!(vars["x"], LogicalTerm::Constant(c) if c == "bob"));
    assert!(matches!(vars["y"], LogicalTerm::Constant(c) if c == "alis"));
}

#[test]
fn test_find_witnesses_transitive_chain() {
    // Assert gerku(alis), ∀x.(gerku→danlu), ∀x.(danlu→xanlu)
    // Query ∃x.xanlu(x) → should find alis (+ presupposition Skolems)
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "xanlu"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "xanlu",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(results.len() >= 1);
    let found: Vec<String> = results
        .iter()
        .filter_map(|bs| match &bs[0].term {
            LogicalTerm::Constant(c) => Some(c.clone()),
            _ => None,
        })
        .collect();
    assert!(
        found.contains(&"alis".to_string()),
        "alis should be a witness"
    );
}

// ─── Proof trace tests ───────────────────────────────────────

fn query_with_proof(kb: &KnowledgeBase, buf: LogicBuffer) -> (bool, ProofTrace) {
    let (result, trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    (result.is_true(), trace)
}

#[test]
fn test_proof_trace_simple_predicate() {
    // Assert klama(mi), query it → single asserted step, result true
    let kb = new_kb();
    assert_buf(&kb, make_assertion("mi", "klama"));
    let (result, trace) = query_with_proof(&kb, make_query("mi", "klama"));

    assert!(result);
    assert!(!trace.steps.is_empty());
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
}

#[test]
fn test_proof_trace_false_predicate() {
    // Query non-existent fact → PredicateNotFound with result false
    let kb = new_kb();
    let (result, trace) = query_with_proof(&kb, make_query("mi", "klama"));

    assert!(!result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(!root_step.holds);
    assert!(
        matches!(&root_step.rule, ProofRule::PredicateNotFound(_)),
        "expected PredicateNotFound, got {:?}",
        root_step.rule
    );
}

#[test]
fn test_proof_trace_conjunction() {
    // Assert klama(mi), prami(mi), query conjunction → conjunction root with two children
    let kb = new_kb();
    assert_buf(&kb, make_assertion("mi", "klama"));
    assert_buf(&kb, make_assertion("mi", "prami"));

    let mut nodes = Vec::new();
    let p1 = pred(
        &mut nodes,
        "klama",
        vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
    );
    let p2 = pred(
        &mut nodes,
        "prami",
        vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
    );
    let root = and(&mut nodes, p1, p2);
    let (result, trace) = query_with_proof(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Conjunction));
    assert_eq!(root_step.children.len(), 2);
    // Both children should be asserted with result true
    for &child in &root_step.children {
        let child_step = &trace.steps[child as usize];
        assert!(child_step.holds);
        assert!(matches!(&child_step.rule, ProofRule::Asserted(_)));
    }
}

#[test]
fn test_proof_trace_negation() {
    // Query negation of non-existent fact → negation root with result true
    let kb = new_kb();
    let mut nodes = Vec::new();
    let inner = pred(
        &mut nodes,
        "klama",
        vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
    );
    let root = not(&mut nodes, inner);
    let (result, trace) = query_with_proof(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Negation));
    assert_eq!(root_step.children.len(), 1);
    // Inner should be predicate-check with result false
    let inner_step = &trace.steps[root_step.children[0] as usize];
    assert!(!inner_step.holds);
}

#[test]
fn test_proof_trace_exists_witness() {
    // Assert klama(alis), query ∃x.klama(x) → exists-witness with x = alis
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "klama"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "klama",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = exists(&mut nodes, "x", body);
    let (result, trace) = query_with_proof(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::ExistsWitness(_)));
    if let ProofRule::ExistsWitness((var, term)) = &root_step.rule {
        assert_eq!(var, "x");
        assert!(matches!(term, LogicalTerm::Constant(c) if c == "alis"));
    }
}

#[test]
fn test_proof_trace_exists_failed() {
    // Query ∃x.klama(x) with no facts → exists-failed
    let kb = new_kb();

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "klama",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = exists(&mut nodes, "x", body);
    let (result, trace) = query_with_proof(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(!result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(!root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::ExistsFailed));
}

#[test]
fn test_proof_trace_forall() {
    // Assert gerku(alis), gerku(bob), query ∀x.gerku(x)→gerku(x) [trivially true]
    // Actually: assert gerku for both entities, query ∀x.(gerku(x)→gerku(x))
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));

    // Query: ∀x. gerku(x) — should be ForAll verified for both entities
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = forall(&mut nodes, "x", body);
    let (result, trace) = query_with_proof(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::ForallVerified(_)));
    if let ProofRule::ForallVerified(entities) = &root_step.rule {
        assert_eq!(entities.len(), 2);
    }
    // Each child should be a predicate-check with result true
    for &child in &root_step.children {
        let child_step = &trace.steps[child as usize];
        assert!(child_step.holds);
    }
}

// ─── Derivation Provenance Tests ──────────────────────────────────

#[test]
fn test_proof_trace_asserted_fact() {
    // Directly asserted fact should show Asserted, not PredicateCheck
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let (result, trace) = query_with_proof(&kb, make_query("alis", "gerku"));
    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
    if let ProofRule::Asserted(fact) = &root_step.rule {
        assert!(fact.contains("gerku"));
        assert!(fact.contains("alis"));
    }
}

#[test]
fn test_proof_trace_single_hop_derived() {
    // gerku(alis) + rule gerku→danlu → danlu(alis) should show Derived with Asserted child
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    let (result, trace) = query_with_proof(&kb, make_query("alis", "danlu"));
    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Derived(_)));
    if let ProofRule::Derived((label, fact)) = &root_step.rule {
        assert!(fact.contains("danlu"));
        assert!(label.contains("gerku"));
        assert!(label.contains("danlu"));
    }
    assert_eq!(root_step.children.len(), 1);
    // The child should be Asserted (gerku(alis))
    let child_step = &trace.steps[root_step.children[0] as usize];
    assert!(child_step.holds);
    assert!(matches!(&child_step.rule, ProofRule::Asserted(_)));
}

#[test]
fn test_proof_trace_multi_hop_derived() {
    // Chain: gerku(alis) → danlu(alis) → xanlu(alis) via two rules
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "xanlu"));
    let (result, trace) = query_with_proof(&kb, make_query("alis", "xanlu"));
    assert!(result);

    // Root: Derived(danlu → xanlu)
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Derived(_)));
    if let ProofRule::Derived((label, _)) = &root_step.rule {
        assert!(label.contains("xanlu"));
    }
    assert_eq!(root_step.children.len(), 1);

    // Child: Derived(gerku → danlu)
    let mid_step = &trace.steps[root_step.children[0] as usize];
    assert!(mid_step.holds);
    assert!(matches!(&mid_step.rule, ProofRule::Derived(_)));
    assert_eq!(mid_step.children.len(), 1);

    // Grandchild: Asserted(gerku(alis))
    let leaf_step = &trace.steps[mid_step.children[0] as usize];
    assert!(leaf_step.holds);
    assert!(matches!(&leaf_step.rule, ProofRule::Asserted(_)));
}

#[test]
fn test_proof_trace_derived_depth_limit() {
    // Self-referencing rule: gerku → gerku. Asserted fact should be found first,
    // preventing infinite backward-chaining.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "gerku"));
    let (result, trace) = query_with_proof(&kb, make_query("alis", "gerku"));
    assert!(result);
    // Should not panic or infinite-loop. Asserted is checked first.
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
}

#[test]
fn test_proof_trace_xorlo_presup_is_asserted() {
    // Universal "ro lo gerku cu danlu" creates xorlo presupposition Skolem.
    // That fact should show as Asserted, not trigger backward-chaining.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    // xorlo presupposition creates sk_0 as a gerku
    let (result, trace) = query_with_proof(&kb, make_query("sk_0", "gerku"));
    assert!(result);
    let root_step = &trace.steps[trace.root as usize];
    assert!(root_step.holds);
    assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
}

// ─── Conjunction Introduction (Guarded) Tests ────────────────────

/// Helper: query whether And(pred1(entity1), pred2(entity2)) holds in the KB.
fn query_conjunction(
    kb: &KnowledgeBase,
    pred1: &str,
    entity1: &str,
    pred2: &str,
    entity2: &str,
) -> bool {
    let mut nodes = Vec::new();
    let p1 = pred(
        &mut nodes,
        pred1,
        vec![
            LogicalTerm::Constant(entity1.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let p2 = pred(
        &mut nodes,
        pred2,
        vec![
            LogicalTerm::Constant(entity2.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = and(&mut nodes, p1, p2);
    query(
        kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    )
}

#[test]
fn test_conjunction_introduction_basic() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("alis", "barda"));

    // Both share entity "alis" in x1 → conjunction should hold
    assert!(
        query_conjunction(&kb, "gerku", "alis", "barda", "alis"),
        "And(gerku(alis), barda(alis)) should hold"
    );
    // Commutativity: reversed order should also hold
    assert!(
        query_conjunction(&kb, "barda", "alis", "gerku", "alis"),
        "And(barda(alis), gerku(alis)) should hold (commutativity)"
    );
}

#[test]
fn test_conjunction_both_individually_true() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "mlatu"));

    // Both are individually true, so their conjunction holds
    // (no shared entity requirement in demand-driven reasoning)
    assert!(
        query_conjunction(&kb, "gerku", "alis", "mlatu", "bob"),
        "And(gerku(alis), mlatu(bob)) should hold when both are individually true"
    );
}

#[test]
fn test_conjunction_introduction_with_derived() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu")); // All dogs are animals
    assert_buf(&kb, make_assertion("alis", "gerku")); // Alice is a dog
    assert_buf(&kb, make_assertion("alis", "barda")); // Alice is big

    // Rule derives danlu(alis). Conjunction should combine derived + asserted.
    assert!(
        query_conjunction(&kb, "danlu", "alis", "barda", "alis"),
        "And(danlu(alis), barda(alis)) should hold via rule + conjunction"
    );
    // Also: gerku(alis) ∧ danlu(alis) (asserted + derived)
    assert!(
        query_conjunction(&kb, "gerku", "alis", "danlu", "alis"),
        "And(gerku(alis), danlu(alis)) should hold"
    );
}

#[test]
fn test_conjunction_introduction_cross_position() {
    // nelci(bob, alis) and gerku(alis) share "alis" across x2 and x1
    let kb = new_kb();

    // gerku(alis, _)
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // nelci(bob, alis, _)
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    // Check: And(gerku(alis,_), nelci(bob,alis,_)) should hold
    let mut nodes2 = Vec::new();
    let p1 = pred(
        &mut nodes2,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let p2 = pred(
        &mut nodes2,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root2 = and(&mut nodes2, p1, p2);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes: nodes2,
                roots: vec![root2]
            }
        ),
        "Cross-position entity sharing should allow conjunction query"
    );
}

// ─── SE-conversion + universal rule + targeted witness tests ────

/// Build a 2-arg universal rule with different argument structures:
/// ∀x. restrictor(x, _) → consequent(fixed_entity, x, _)
/// This simulates "ro lo gerku cu se nelci la .bob." where SE swaps x1↔x2,
/// producing: ∀x. gerku(x) → nelci(bob, x)
fn make_universal_2arg(restrictor: &str, consequent: &str, fixed_entity: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    // restrictor(x, _)
    let restrict = pred(
        &mut nodes,
        restrictor,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    // consequent(fixed_entity, x, _)
    let body = pred(
        &mut nodes,
        consequent,
        vec![
            LogicalTerm::Constant(fixed_entity.to_string()),
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg = not(&mut nodes, restrict);
    let disj = or(&mut nodes, neg, body);
    let root = forall(&mut nodes, "_v0", disj);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_se_conversion_universal_rule() {
    // Simulates the REPL demo:
    //   la .alis. gerku          → gerku(alis)
    //   ro lo gerku cu se nelci la .bob.  → ∀x. gerku(x) → nelci(bob, x)
    //   ? la .bob. nelci la .alis.        → nelci(bob, alis) = TRUE
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

    // Query: nelci(bob, alis) — should be TRUE via universal rule
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_se_conversion_universal_multiple_entities() {
    // Two dogs: both should be liked by bob via universal rule
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("rex", "gerku"));
    assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

    // nelci(bob, alis) = TRUE
    let mut n1 = Vec::new();
    let r1 = pred(
        &mut n1,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: n1,
            roots: vec![r1]
        }
    ));

    // nelci(bob, rex) = TRUE
    let mut n2 = Vec::new();
    let r2 = pred(
        &mut n2,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("rex".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: n2,
            roots: vec![r2]
        }
    ));

    // nelci(bob, carol) = FALSE (carol is not a dog)
    let mut n3 = Vec::new();
    let r3 = pred(
        &mut n3,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Constant("carol".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes: n3,
            roots: vec![r3]
        }
    ));
}

#[test]
fn test_targeted_witness_search_with_fixed_entity() {
    // Simulates the REPL demo:
    //   la .alis. gerku          → gerku(alis)
    //   ro lo gerku cu se nelci la .bob.  → ∀x. gerku(x) → nelci(bob, x)
    //   ?? ma se nelci la .bob.           → ∃x. nelci(bob, x) → includes alis
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

    // Query: ∃x. nelci(bob, x) — should find alis (+ presupposition Skolem)
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(results.len() >= 1);
    let found: Vec<String> = results
        .iter()
        .filter_map(|bs| match &bs[0].term {
            LogicalTerm::Constant(c) => Some(c.clone()),
            _ => None,
        })
        .collect();
    assert!(
        found.contains(&"alis".to_string()),
        "alis should be a witness"
    );
}

#[test]
fn test_targeted_witness_search_multiple_matches() {
    // Two dogs → both should appear as witnesses for "who does bob like?"
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("rex", "gerku"));
    assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

    // Query: ∃x. nelci(bob, x) — should find alis AND rex (+ presupposition Skolem)
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    assert!(results.len() >= 2);
    let found: Vec<String> = results
        .iter()
        .filter_map(|bs| match &bs[0].term {
            LogicalTerm::Constant(c) => Some(c.clone()),
            _ => None,
        })
        .collect();
    assert!(
        found.contains(&"alis".to_string()),
        "alis should be a witness"
    );
    assert!(
        found.contains(&"rex".to_string()),
        "rex should be a witness"
    );
}

#[test]
fn test_conjunction_introduction_multiple_entities() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("alis", "barda"));
    assert_buf(&kb, make_assertion("bob", "mlatu"));
    assert_buf(&kb, make_assertion("bob", "cmalu"));

    // alis predicates should conjoin with each other
    assert!(query_conjunction(&kb, "gerku", "alis", "barda", "alis"));
    // bob predicates should conjoin with each other
    assert!(query_conjunction(&kb, "mlatu", "bob", "cmalu", "bob"));
    // cross-entity conjunction also holds (both sides individually true)
    assert!(query_conjunction(&kb, "gerku", "alis", "mlatu", "bob"));
}

// ─── KB Reset Tests ──────────────────────────────────────────

#[test]
fn test_kb_reset_clears_facts() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(query(&kb, make_query("alis", "gerku")));

    // Reset the knowledge base
    kb.inner.borrow_mut().reset();

    // After reset, previously asserted fact should no longer hold
    assert!(!query(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_kb_reset_clears_rules() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert!(query(&kb, make_query("alis", "danlu")));

    kb.inner.borrow_mut().reset();

    // After reset, re-assert the fact but not the rule
    assert_buf(&kb, make_assertion("alis", "gerku"));
    // Rule should not exist anymore
    assert!(!query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_kb_reset_resets_skolem_counter() {
    let kb = new_kb();
    // Assert a universal to trigger Skolem generation
    assert_buf(&kb, make_universal("gerku", "danlu"));
    let counter_before = kb.inner.borrow().skolem_counter;
    assert!(counter_before > 0);

    kb.inner.borrow_mut().reset();
    assert_eq!(kb.inner.borrow().skolem_counter, 0);
}

// ─── Empty buffer / edge case tests ──────────────────────────

#[test]
fn test_query_with_no_facts() {
    let kb = new_kb();
    assert!(!query(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_assert_and_query_same_fact_twice() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    // Should still hold and not cause issues
    assert!(query(&kb, make_query("alis", "gerku")));
}

// ─── Disjunction query tests ─────────────────────────────────

#[test]
fn test_disjunction_left_true() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));

    let mut nodes = Vec::new();
    let left = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let right = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = or(&mut nodes, left, right);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_disjunction_right_true() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "mlatu"));

    let mut nodes = Vec::new();
    let left = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let right = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = or(&mut nodes, left, right);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_disjunction_both_false() {
    let kb = new_kb();

    let mut nodes = Vec::new();
    let left = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let right = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = or(&mut nodes, left, right);
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

// ─── Double negation tests ───────────────────────────────────

#[test]
fn test_double_negation_elimination() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // Query Not(Not(gerku(alis))) → should be TRUE
    let mut nodes = Vec::new();
    let inner = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg1 = not(&mut nodes, inner);
    let root = not(&mut nodes, neg1);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

// ─── Tense wrapper tests ─────────────────────────────────────

fn past(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::PastNode(inner));
    id
}

fn present(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::PresentNode(inner));
    id
}

fn future(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::FutureNode(inner));
    id
}

#[test]
fn test_past_tense_wrapper_assert_query() {
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = past(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    // Query same tense wrapper → TRUE
    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = past(&mut q_nodes, q_inner);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_tense_not_transparent() {
    // Assert Past(klama(alis)), query klama(alis) without tense → FALSE
    // (tense is NOT transparent — tensed assertion ≠ timeless query)
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = past(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    assert!(!query(&kb, make_query("alis", "klama")));
}

#[test]
fn test_tense_discrimination_past_vs_future() {
    // Assert Past(klama(alis)), query Future(klama(alis)) → FALSE
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = past(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = future(&mut q_nodes, q_inner);
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_tense_discrimination_present_vs_past() {
    // Assert Present(klama(alis)), query Past(klama(alis)) → FALSE
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = present(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = past(&mut q_nodes, q_inner);
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_untensed_assert_tensed_query() {
    // Assert klama(alis) (bare/timeless), query Past(klama(alis)) → FALSE
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "klama"));

    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = past(&mut q_nodes, q_inner);
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_temporal_rule_lifting() {
    // Assert: ∀x. gerku(x) → danlu(x) (timeless rule)
    // Assert: Past(gerku(alis))
    // Query: Past(danlu(alis)) → TRUE (temporal lifting)
    let kb = new_kb();

    // Compile the universal rule: ForAll(x, Or(Not(gerku(x)), danlu(x)))
    let mut r_nodes = Vec::new();
    let gerku = pred(
        &mut r_nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let danlu = pred(
        &mut r_nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_gerku = not(&mut r_nodes, gerku);
    let impl_body = or(&mut r_nodes, neg_gerku, danlu);
    let forall = {
        let id = r_nodes.len() as u32;
        r_nodes.push(LogicNode::ForAllNode(("_v0".into(), impl_body)));
        id
    };
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: r_nodes,
            roots: vec![forall],
        },
    );

    // Assert Past(gerku(alis))
    let mut a_nodes = Vec::new();
    let gerku_alis = pred(
        &mut a_nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let past_gerku = past(&mut a_nodes, gerku_alis);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![past_gerku],
        },
    );

    // Query Past(danlu(alis)) → TRUE (lifted rule fires on Past premises)
    let mut q_nodes = Vec::new();
    let danlu_alis = pred(
        &mut q_nodes,
        "danlu",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let past_danlu = past(&mut q_nodes, danlu_alis);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![past_danlu]
        }
    ));
}

#[test]
fn test_temporal_rule_no_cross_tense() {
    // Assert: ∀x. gerku(x) → danlu(x) (timeless rule)
    // Assert: Past(gerku(alis))
    // Query: Future(danlu(alis)) → FALSE (no cross-tense derivation)
    let kb = new_kb();

    // Universal rule
    let mut r_nodes = Vec::new();
    let gerku = pred(
        &mut r_nodes,
        "gerku",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let danlu = pred(
        &mut r_nodes,
        "danlu",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_gerku = not(&mut r_nodes, gerku);
    let impl_body = or(&mut r_nodes, neg_gerku, danlu);
    let forall = {
        let id = r_nodes.len() as u32;
        r_nodes.push(LogicNode::ForAllNode(("_v0".into(), impl_body)));
        id
    };
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: r_nodes,
            roots: vec![forall],
        },
    );

    // Assert Past(gerku(alis))
    let mut a_nodes = Vec::new();
    let gerku_alis = pred(
        &mut a_nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let past_gerku = past(&mut a_nodes, gerku_alis);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![past_gerku],
        },
    );

    // Query Future(danlu(alis)) → FALSE (Past ≠ Future)
    let mut q_nodes = Vec::new();
    let danlu_alis = pred(
        &mut q_nodes,
        "danlu",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let future_danlu = future(&mut q_nodes, danlu_alis);
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![future_danlu]
        }
    ));
}

// ─── Tensed rule antecedents (compile + fire) ────────────────

/// Assert the tensed-antecedent rule `∀x. Past(citka(x)) → xagji(x)`
/// ("everything that ATE is hungry"). Pre-fix this panics (the rule is
/// rejected at compile time because the tensed condition cannot be templated).
fn assert_pu_citka_then_xagji(kb: &KnowledgeBase) {
    let mut r = Vec::new();
    let citka = pred(
        &mut r,
        "citka",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let past_citka = past(&mut r, citka);
    let neg = not(&mut r, past_citka);
    let xagji = pred(
        &mut r,
        "xagji",
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let body = or(&mut r, neg, xagji);
    let forall = {
        let id = r.len() as u32;
        r.push(LogicNode::ForAllNode(("_v0".into(), body)));
        id
    };
    assert_buf(
        kb,
        LogicBuffer {
            nodes: r,
            roots: vec![forall],
        },
    );
}

/// Query bare `xagji(rex)`.
fn query_xagji_rex(kb: &KnowledgeBase) -> bool {
    let mut q = Vec::new();
    let xagji = pred(
        &mut q,
        "xagji",
        vec![
            LogicalTerm::Constant("rex".into()),
            LogicalTerm::Unspecified,
        ],
    );
    query(
        kb,
        LogicBuffer {
            nodes: q,
            roots: vec![xagji],
        },
    )
}

/// Assert a `citka(rex)` fact under the given tense wrapper (`None` = bare).
fn assert_citka_rex(kb: &KnowledgeBase, tense: Option<&str>) {
    let mut a = Vec::new();
    let citka_rex = pred(
        &mut a,
        "citka",
        vec![
            LogicalTerm::Constant("rex".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = match tense {
        Some("Past") => past(&mut a, citka_rex),
        Some("Future") => future(&mut a, citka_rex),
        Some("Present") => present(&mut a, citka_rex),
        _ => citka_rex,
    };
    assert_buf(
        kb,
        LogicBuffer {
            nodes: a,
            roots: vec![root],
        },
    );
}

#[test]
fn test_tensed_antecedent_rule_compiles_and_fires() {
    // ∀x. Past(citka(x)) → xagji(x); given Past(citka(rex)), derive bare xagji(rex).
    let kb = new_kb();
    assert_pu_citka_then_xagji(&kb);
    assert_citka_rex(&kb, Some("Past"));
    assert!(
        query_xagji_rex(&kb),
        "tensed-antecedent rule must fire on a matching Past premise"
    );
}

#[test]
fn test_tensed_antecedent_no_premise_does_not_fire() {
    // The rule compiles, but with no premise the tensed condition fails.
    let kb = new_kb();
    assert_pu_citka_then_xagji(&kb);
    assert!(
        !query_xagji_rex(&kb),
        "tensed-antecedent rule must NOT fire with no supporting premise"
    );
}

#[test]
fn test_tensed_antecedent_wrong_tense_does_not_fire() {
    // A Future premise must not satisfy a Past antecedent (strict tense).
    let kb = new_kb();
    assert_pu_citka_then_xagji(&kb);
    assert_citka_rex(&kb, Some("Future"));
    assert!(
        !query_xagji_rex(&kb),
        "Past antecedent must NOT fire on a Future premise"
    );
}

#[test]
fn test_tensed_antecedent_bare_premise_does_not_fire() {
    // A bare premise must not satisfy a Past antecedent.
    let kb = new_kb();
    assert_pu_citka_then_xagji(&kb);
    assert_citka_rex(&kb, None);
    assert!(
        !query_xagji_rex(&kb),
        "Past antecedent must NOT fire on a bare premise"
    );
}

// ─── Multiple roots test ─────────────────────────────────────

#[test]
fn test_assert_multiple_roots() {
    let kb = new_kb();
    let mut nodes = Vec::new();
    let r1 = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let r2 = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("bob".into()),
            LogicalTerm::Unspecified,
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![r1, r2],
        },
    );

    assert!(query(&kb, make_query("alis", "gerku")));
    assert!(query(&kb, make_query("bob", "mlatu")));
}

// ─── Assertion atomicity (rebuild-on-failure) ────────────────

#[test]
fn multi_root_partial_failure_is_atomic() {
    // A 2-root assertion: root0 is a valid ground fact, root1 fails (a bare
    // disjunction ingests no fact and registers no rule → "no representable
    // content" Err). The whole assertion must roll back — root0's fact must NOT
    // survive, and no orphan FactRecord may be left behind.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let root0 = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("adam".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let g = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("zelda".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let m = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("zelda".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root1 = or(&mut nodes, g, m); // bare disjunction → process_assertion Err

    let result = kb.assert_fact_inner(
        LogicBuffer {
            nodes,
            roots: vec![root0, root1],
        },
        String::new(),
    );
    assert!(result.is_err(), "the assertion must fail on root1");
    assert!(
        !query(&kb, make_query("adam", "gerku")),
        "root0's fact must be rolled back, not orphaned"
    );
    assert!(
        kb.list_facts_inner().unwrap().is_empty(),
        "a failed assertion must leave no FactRecord"
    );
}

#[test]
fn failed_assertion_does_not_leak_assertion_id() {
    // The error path must clear current_assertion_id; a stale id would
    // mis-attribute the NEXT assertion's rules in rule_source_map.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let g = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("zelda".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let m = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("zelda".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let bad = or(&mut nodes, g, m);
    let result = kb.assert_fact_inner(
        LogicBuffer {
            nodes,
            roots: vec![bad],
        },
        String::new(),
    );
    assert!(result.is_err());
    assert!(
        kb.inner.borrow().current_assertion_id.is_none(),
        "current_assertion_id must be cleared after a failed assertion"
    );
}

#[test]
fn rebuild_preserves_user_arg_sorts() {
    // User-declared arg sorts (set_predicate_sorts) must survive a rebuild.
    let kb = new_kb();
    kb.set_predicate_sorts("gerku", vec!["animal".to_string(), String::new()]);
    // Retracting a ForAll record takes the full-rebuild path (a ground-fact
    // retraction is incremental and would not rebuild).
    let throwaway = assert_id(&kb, make_universal("foo", "bar"), "throwaway");
    assert_buf(&kb, make_assertion("adam", "gerku"));
    kb.retract_fact_inner(throwaway).unwrap(); // forces rebuild_inner

    let inner = kb.inner.borrow();
    let sig = inner
        .predicate_registry
        .get("gerku")
        .expect("gerku should be registered after rebuild");
    assert_eq!(
        sig.arg_sorts,
        vec!["animal".to_string(), String::new()],
        "user-declared arg sorts must survive a rebuild"
    );
}

// ─── Count quantifier test ───────────────────────────────────

fn count(nodes: &mut Vec<LogicNode>, var: &str, cnt: u32, body: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::CountNode((var.to_string(), cnt, body)));
    id
}

#[test]
fn test_count_exact_match() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));

    // Count(x, 2, gerku(x, _)) → exactly 2 dogs
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = count(&mut nodes, "x", 2, body);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn test_count_mismatch() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // Count(x, 2, gerku(x, _)) → only 1 dog, not 2
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = count(&mut nodes, "x", 2, body);
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root]
        }
    ));
}

#[test]
fn retract_count_quantified_fact_removes_witnesses() {
    // `Count(x, 2, gerku(x, _))` generates count-1 = 1 extra Skolem dog and
    // asserts gerku(sk) for it. Retracting the count assertion must remove that
    // generated witness — pre-fix a flat CountNode buffer took the incremental
    // path (has_skolems matched only Exists/ForAll), leaking the witness fact +
    // entity. Now CountNode routes to rebuild, which excludes the retracted
    // assertion and never regenerates its witnesses.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
    );
    let root = count(&mut nodes, "x", 2, body);
    let id = assert_id(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
        "count",
    );
    assert!(
        kb.count_witnesses(make_find_query("gerku")).unwrap() >= 1,
        "the count assertion should have generated a witness dog"
    );

    kb.retract_fact_inner(id).unwrap();
    assert_eq!(
        kb.count_witnesses(make_find_query("gerku")).unwrap(),
        0,
        "count-generated witnesses must not survive retraction"
    );
}

// ─── Compute builtin arithmetic tests ────────────────────────

#[test]
fn test_compute_pilji_correct() {
    let kb = new_kb();
    let buf = make_compute_query("pilji", 6.0, 2.0, 3.0);
    assert!(query(&kb, buf));
}

#[test]
fn test_compute_pilji_incorrect() {
    let kb = new_kb();
    let buf = make_compute_query("pilji", 7.0, 2.0, 3.0);
    assert!(!query(&kb, buf));
}

#[test]
fn test_compute_sumji_correct() {
    let kb = new_kb();
    let buf = make_compute_query("sumji", 5.0, 2.0, 3.0);
    assert!(query(&kb, buf));
}

#[test]
fn test_compute_sumji_incorrect() {
    let kb = new_kb();
    let buf = make_compute_query("sumji", 6.0, 2.0, 3.0);
    assert!(!query(&kb, buf));
}

#[test]
fn test_compute_dilcu_correct() {
    let kb = new_kb();
    let buf = make_compute_query("dilcu", 2.0, 6.0, 3.0);
    assert!(query(&kb, buf));
}

#[test]
fn test_compute_dilcu_incorrect() {
    let kb = new_kb();
    let buf = make_compute_query("dilcu", 3.0, 6.0, 3.0);
    assert!(!query(&kb, buf));
}

// ─── Numerical comparison predicate tests ────────────────────

#[test]
fn test_zmadu_greater_than() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("zmadu", 5.0, 3.0)));
}

#[test]
fn test_zmadu_not_greater() {
    let kb = new_kb();
    assert!(!query(&kb, make_numeric_query("zmadu", 3.0, 5.0)));
}

#[test]
fn test_mleca_less_than() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("mleca", 3.0, 5.0)));
}

#[test]
fn test_dunli_equal() {
    let kb = new_kb();
    assert!(query(&kb, make_numeric_query("dunli", 5.0, 5.0)));
}

#[test]
fn test_dunli_not_equal() {
    let kb = new_kb();
    assert!(!query(&kb, make_numeric_query("dunli", 5.0, 3.0)));
}

// ─── Assert fact with various term types ──────────────────────

#[test]
fn test_assert_fact_with_number_terms() {
    let kb = new_kb();
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "pilji",
        vec![
            LogicalTerm::Number(6.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    // Query the same fact back
    let mut q_nodes = Vec::new();
    let q_root = pred(
        &mut q_nodes,
        "pilji",
        vec![
            LogicalTerm::Number(6.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_assert_fact_with_description_terms() {
    let kb = new_kb();
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Description("lo_gerku".to_string()),
        ],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );

    // Query back
    let mut q_nodes = Vec::new();
    let q_root = pred(
        &mut q_nodes,
        "nelci",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Description("lo_gerku".to_string()),
        ],
    );
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

// ─── Fact Registry / Retraction Tests ────────────────────────────

#[test]
fn test_retract_basic() {
    let kb = new_kb();
    let id = assert_id(&kb, make_assertion("alis", "gerku"), "la alis gerku");
    assert!(query(&kb, make_query("alis", "gerku")));
    kb.retract_fact_inner(id).unwrap();
    assert!(!query(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_retract_preserves_other_facts() {
    let kb = new_kb();
    let id1 = assert_id(&kb, make_assertion("alis", "gerku"), "");
    let _id2 = assert_id(&kb, make_assertion("bob", "mlatu"), "");
    kb.retract_fact_inner(id1).unwrap();
    assert!(!query(&kb, make_query("alis", "gerku")));
    assert!(query(&kb, make_query("bob", "mlatu")));
}

#[test]
fn test_retract_derived_facts_gone() {
    let kb = new_kb();
    let base_id = assert_id(&kb, make_assertion("alis", "gerku"), "");
    let _rule_id = assert_id(&kb, make_universal("gerku", "danlu"), "");
    // "alis danlu" should be derivable via the rule
    assert!(query(&kb, make_query("alis", "danlu")));
    kb.retract_fact_inner(base_id).unwrap();
    // After retracting the base fact, "alis danlu" should no longer hold
    assert!(!query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_retract_rule_preserves_base_facts() {
    let kb = new_kb();
    let _base_id = assert_id(&kb, make_assertion("alis", "gerku"), "");
    let rule_id = assert_id(&kb, make_universal("gerku", "danlu"), "");
    assert!(query(&kb, make_query("alis", "danlu")));
    kb.retract_fact_inner(rule_id).unwrap();
    // Base fact preserved
    assert!(query(&kb, make_query("alis", "gerku")));
    // Derived fact gone (rule retracted)
    assert!(!query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_retract_and_reassert_new_id() {
    let kb = new_kb();
    let id1 = assert_id(&kb, make_assertion("alis", "gerku"), "");
    kb.retract_fact_inner(id1).unwrap();
    let id2 = assert_id(&kb, make_assertion("alis", "gerku"), "");
    assert!(id2 > id1);
    assert!(query(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_retract_nonexistent_errors() {
    let kb = new_kb();
    assert!(kb.retract_fact_inner(999).is_err());
}

#[test]
fn test_retract_idempotent() {
    let kb = new_kb();
    let id = assert_id(&kb, make_assertion("alis", "gerku"), "");
    kb.retract_fact_inner(id).unwrap();
    kb.retract_fact_inner(id).unwrap(); // second retract is no-op
    assert!(!query(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_retract_duplicate_ground_fact_keeps_live_copy() {
    // Two records assert the SAME ground fact. Retracting one must NOT remove
    // the fact from the store while the other record is still live (the
    // HashSet store has no multiplicity — incremental retraction must consult
    // the surviving registry records).
    let kb = new_kb();
    let id1 = assert_id(&kb, make_assertion("alis", "gerku"), "copy 1");
    let id2 = assert_id(&kb, make_assertion("alis", "gerku"), "copy 2");
    kb.retract_fact_inner(id1).unwrap();
    assert!(
        query(&kb, make_query("alis", "gerku")),
        "fact must survive while record #{id2} still asserts it"
    );
    // Retracting the second (last) record removes the fact for real.
    kb.retract_fact_inner(id2).unwrap();
    assert!(!query(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_retract_multi_root_removes_all_roots() {
    // A single record whose buffer has TWO roots: assertion processes both, so
    // retraction must remove both (it used to process only roots.first()).
    let mut nodes = Vec::new();
    let r1 = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let r2 = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("bob".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let kb = new_kb();
    let id = assert_id(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![r1, r2],
        },
        "two roots",
    );
    assert!(query(&kb, make_query("alis", "gerku")));
    assert!(query(&kb, make_query("bob", "mlatu")));
    kb.retract_fact_inner(id).unwrap();
    assert!(
        !query(&kb, make_query("alis", "gerku")),
        "first root's fact must be retracted"
    );
    assert!(
        !query(&kb, make_query("bob", "mlatu")),
        "second root's fact must be retracted too (not just roots.first())"
    );
}

// ─── Negative-Fact Storage / Contradiction Detection Tests ───────

/// Build a negated ground assertion: Not(Pred(predicate, [Const(entity), Zoe])).
fn make_negated_assertion(entity: &str, predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let inner = pred(
        &mut nodes,
        predicate,
        vec![
            LogicalTerm::Constant(entity.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = not(&mut nodes, inner);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Build the event-decomposed form smuni emits for "<entity> cu <pred>":
/// ∃e. ((pred(e) ∧ pred_x1(e, entity)) ∧ pred_x2(e, zo'e)), optionally negated
/// (the negation wraps the OUTSIDE of the existential, as the pipeline emits).
fn make_event_decomposed(entity: &str, predicate: &str, negated: bool) -> LogicBuffer {
    let mut nodes = Vec::new();
    let ev = || LogicalTerm::Variable("_ev0".to_string());
    let type_pred = pred(&mut nodes, predicate, vec![ev()]);
    let x1 = pred(
        &mut nodes,
        &format!("{predicate}_x1"),
        vec![ev(), LogicalTerm::Constant(entity.to_string())],
    );
    let x2 = pred(
        &mut nodes,
        &format!("{predicate}_x2"),
        vec![ev(), LogicalTerm::Unspecified],
    );
    let a1 = and(&mut nodes, type_pred, x1);
    let a2 = and(&mut nodes, a1, x2);
    let ex = exists(&mut nodes, "_ev0", a2);
    let root = if negated { not(&mut nodes, ex) } else { ex };
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_negated_ground_fact_contradicts_contrary_positive() {
    // Assert ¬gerku(alis), then gerku(alis): both must be accepted (a negative
    // premise stays assertable), and check_contradictions must flag the pair.
    let kb = new_kb();
    assert_id(&kb, make_negated_assertion("alis", "gerku"), "na gerku");
    assert_id(&kb, make_assertion("alis", "gerku"), "gerku");
    let violations = kb.check_contradictions();
    assert!(
        violations
            .iter()
            .any(|v| v.contains("Negation contradiction")),
        "contrary positive after an asserted negation must be flagged: {violations:?}"
    );
}

#[test]
fn test_negated_ground_fact_alone_is_not_a_contradiction() {
    // A bare negative premise (no contrary positive) must not be flagged, and
    // NAF query semantics are unchanged: the positive is simply not derivable.
    let kb = new_kb();
    assert_id(&kb, make_negated_assertion("alis", "gerku"), "na gerku");
    assert!(!query(&kb, make_query("alis", "gerku")));
    assert!(
        kb.check_contradictions().is_empty(),
        "a lone negative fact is not a contradiction"
    );
}

#[test]
fn test_negated_event_decomposed_fact_contradicts_contrary_positive() {
    // The pipeline shape (probe-verified): `la .adam. na gerku` compiles to
    // ¬∃e.(gerku(e) ∧ gerku_x1(e, adam) ∧ gerku_x2(e, zo'e)), and the later
    // contrary positive gets a DIFFERENT fresh event Skolem. The negative
    // templates generalize the event argument, so the contradiction must still
    // be detected across the Skolem mismatch.
    let kb = new_kb();
    assert_id(
        &kb,
        make_event_decomposed("adam", "gerku", true),
        "na gerku",
    );
    assert_id(&kb, make_event_decomposed("adam", "gerku", false), "gerku");
    let violations = kb.check_contradictions();
    assert!(
        violations
            .iter()
            .any(|v| v.contains("Negation contradiction")),
        "event-decomposed contrary positive must be flagged: {violations:?}"
    );
}

#[test]
fn test_negated_event_decomposed_fact_ignores_other_entities() {
    // ¬gerku(adam) + gerku(bob) is NOT a contradiction: the whole negative
    // template group must unify under ONE event binding, so an unrelated
    // entity's dog-event cannot trigger a false positive.
    let kb = new_kb();
    assert_id(
        &kb,
        make_event_decomposed("adam", "gerku", true),
        "na gerku",
    );
    assert_id(
        &kb,
        make_event_decomposed("bob", "gerku", false),
        "bob gerku",
    );
    assert!(
        kb.check_contradictions().is_empty(),
        "a different entity's positive must not contradict adam's negation"
    );
}

#[test]
fn test_negated_fact_retraction_clears_contradiction() {
    // Retracting the negative record must clear the contradiction (the
    // negation-bearing buffer takes the rebuild path, which repopulates the
    // negative registry from the surviving records).
    let kb = new_kb();
    let neg_id = assert_id(&kb, make_negated_assertion("alis", "gerku"), "na gerku");
    assert_id(&kb, make_assertion("alis", "gerku"), "gerku");
    assert!(!kb.check_contradictions().is_empty());
    kb.retract_fact_inner(neg_id).unwrap();
    assert!(
        kb.check_contradictions().is_empty(),
        "retracting the negation must clear the contradiction"
    );
    // The positive fact must survive the rebuild.
    assert!(query(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_list_facts_empty() {
    let kb = new_kb();
    let facts = kb.list_facts_inner().unwrap();
    assert!(facts.is_empty());
}

#[test]
fn test_list_facts_after_assert() {
    let kb = new_kb();
    assert_id(&kb, make_assertion("alis", "gerku"), "la alis gerku");
    let facts = kb.list_facts_inner().unwrap();
    assert_eq!(facts.len(), 1);
    assert_eq!(facts[0].label, "la alis gerku");
    assert_eq!(facts[0].root_count, 1);
}

#[test]
fn test_list_facts_excludes_retracted() {
    let kb = new_kb();
    let id = assert_id(&kb, make_assertion("alis", "gerku"), "");
    assert_id(&kb, make_assertion("bob", "mlatu"), "bob mlatu");
    kb.retract_fact_inner(id).unwrap();
    let facts = kb.list_facts_inner().unwrap();
    assert_eq!(facts.len(), 1);
    assert_eq!(facts[0].id, 1); // bob's fact
    assert_eq!(facts[0].label, "bob mlatu");
}

#[test]
fn test_reset_clears_registry() {
    let kb = new_kb();
    assert_id(&kb, make_assertion("alis", "gerku"), "");
    kb.inner.borrow_mut().reset();
    let facts = kb.list_facts_inner().unwrap();
    assert!(facts.is_empty());
    assert!(!query(&kb, make_query("alis", "gerku")));
}

// ─── C5: Description term opacity tests ──────────────────────

/// Helper: make an assertion with a Description term in x1.
fn make_desc_assertion(desc_name: &str, predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        predicate,
        vec![
            LogicalTerm::Description(desc_name.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Helper: make a query with a Description term in x1.
fn make_desc_query(desc_name: &str, predicate: &str) -> LogicBuffer {
    make_desc_assertion(desc_name, predicate)
}

#[test]
fn test_desc_gets_indomain() {
    // Assert a fact with Description term → Desc should be in InDomain
    let kb = new_kb();
    assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
    let inner = kb.inner.borrow();
    assert!(
        inner.known_descriptions.contains("gerku"),
        "expected 'gerku' in known_descriptions"
    );
}

#[test]
fn test_desc_conjunction_introduction() {
    // Two facts about same Desc term → conjunction should be derivable
    let kb = new_kb();
    assert_buf(&kb, make_desc_assertion("gerku", "danlu"));
    assert_buf(&kb, make_desc_assertion("gerku", "sutra"));

    // Query And(danlu(Desc "gerku"), sutra(Desc "gerku"))
    let mut nodes = Vec::new();
    let p1 = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Description("gerku".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let p2 = pred(
        &mut nodes,
        "sutra",
        vec![
            LogicalTerm::Description("gerku".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = and(&mut nodes, p1, p2);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes,
                roots: vec![root]
            }
        ),
        "conjunction of two Desc-term facts should hold via conjunction introduction"
    );
}

#[test]
fn test_desc_does_not_trigger_rule_without_restrictor() {
    // Assert sutra(Desc "gerku") (but NOT gerku(Desc "gerku"))
    // Assert rule: ro lo gerku cu danlu (∀x. gerku(x) → danlu(x))
    // Query danlu(Desc "gerku") → should FAIL (the restrictor isn't satisfied)
    let kb = new_kb();
    assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert!(
        !query(&kb, make_desc_query("gerku", "danlu")),
        "universal rule should NOT fire without restrictor being satisfied for Desc term"
    );
}

#[test]
fn test_desc_triggers_rule_when_restrictor_satisfied() {
    // Assert gerku(Desc "gerku") AND sutra(Desc "gerku")
    // Assert rule: ro lo gerku cu danlu
    // Query danlu(Desc "gerku") → should SUCCEED
    let kb = new_kb();
    assert_buf(&kb, make_desc_assertion("gerku", "gerku"));
    assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert!(
        query(&kb, make_desc_query("gerku", "danlu")),
        "universal rule should fire when restrictor IS satisfied for Desc term"
    );
}

#[test]
fn test_desc_exists_witness() {
    // Assert sutra(Desc "gerku") → ∃x. sutra(x) should find Desc "gerku" as witness
    let kb = new_kb();
    assert_buf(&kb, make_desc_assertion("gerku", "sutra"));

    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "sutra",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes,
                roots: vec![root]
            }
        ),
        "existential query should find Desc term as witness"
    );
}

#[test]
fn test_backward_chain_derives_facts() {
    // Assert a fact and a rule, then verify backward-chaining derives conclusions
    let kb = new_kb();
    // Assert: gerku(alis)
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // Assert: ∀x. ¬gerku(x) ∨ danlu(x) (i.e., gerku → danlu)
    assert_buf(&kb, make_universal("gerku", "danlu"));

    // Query: danlu(alis) — should be derived via backward-chaining
    assert!(
        query(&kb, make_query("alis", "danlu")),
        "backward-chaining should derive danlu(alis) from gerku(alis) and universal rule"
    );
}

// ─── Event-decomposed universal rule tests ──────────────────────

/// Build an event-decomposed ground assertion:
///   Exists(_ev0, And(P(_ev0), P_x1(_ev0, entity)))
fn make_event_assertion(entity: &str, predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let p_type = pred(
        &mut nodes,
        predicate,
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let p_role = pred(
        &mut nodes,
        &format!("{}_x1", predicate),
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Constant(entity.to_string()),
        ],
    );
    let p_and = and(&mut nodes, p_type, p_role);
    let root = exists(&mut nodes, "_ev0", p_and);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Build an event-decomposed universal rule:
///   ForAll(_v0, Or(
///     Not(Exists(_ev0, And(P(_ev0), P_x1(_ev0, _v0)))),
///     Exists(_ev1, And(Q(_ev1), Q_x1(_ev1, _v0)))
///   ))
fn make_event_universal(restrictor: &str, consequent: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    // Condition: Exists(_ev0, And(P(_ev0), P_x1(_ev0, _v0)))
    let p_type = pred(
        &mut nodes,
        restrictor,
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let p_role = pred(
        &mut nodes,
        &format!("{}_x1", restrictor),
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Variable("_v0".to_string()),
        ],
    );
    let p_and = and(&mut nodes, p_type, p_role);
    let p_exists = exists(&mut nodes, "_ev0", p_and);

    // Consequent: Exists(_ev1, And(Q(_ev1), Q_x1(_ev1, _v0)))
    let q_type = pred(
        &mut nodes,
        consequent,
        vec![LogicalTerm::Variable("_ev1".to_string())],
    );
    let q_role = pred(
        &mut nodes,
        &format!("{}_x1", consequent),
        vec![
            LogicalTerm::Variable("_ev1".to_string()),
            LogicalTerm::Variable("_v0".to_string()),
        ],
    );
    let q_and = and(&mut nodes, q_type, q_role);
    let q_exists = exists(&mut nodes, "_ev1", q_and);

    // Implication: Or(Not(p_exists), q_exists)
    let neg = not(&mut nodes, p_exists);
    let disj = or(&mut nodes, neg, q_exists);
    let root = forall(&mut nodes, "_v0", disj);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Build an event-decomposed existential query (same structure as assertion).
fn make_event_query(entity: &str, predicate: &str) -> LogicBuffer {
    make_event_assertion(entity, predicate)
}

#[test]
fn test_event_decomposed_rule_fires() {
    let kb = new_kb();
    assert_buf(&kb, make_event_assertion("alis", "gerku"));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert!(
        query(&kb, make_event_query("alis", "danlu")),
        "event-decomposed rule should derive danlu(alis) from gerku(alis)"
    );
}

/// Build `Exists(ev, And(P(ev), P_x1(ev, entity)))` for a GROUND entity constant.
fn event_operand(nodes: &mut Vec<LogicNode>, ev: &str, predicate: &str, entity: &str) -> u32 {
    let p_type = pred(
        nodes,
        predicate,
        vec![LogicalTerm::Variable(ev.to_string())],
    );
    let p_role = pred(
        nodes,
        &format!("{}_x1", predicate),
        vec![
            LogicalTerm::Variable(ev.to_string()),
            LogicalTerm::Constant(entity.to_string()),
        ],
    );
    let p_and = and(nodes, p_type, p_role);
    exists(nodes, ev, p_and)
}

/// Ground event-decomposed material conditional: Or(Not(A), B), operands over a constant.
fn make_event_material_conditional(
    entity: &str,
    antecedent: &str,
    consequent: &str,
) -> LogicBuffer {
    let mut nodes = Vec::new();
    let a = event_operand(&mut nodes, "_ev0", antecedent, entity);
    let b = event_operand(&mut nodes, "_ev1", consequent, entity);
    let neg_a = not(&mut nodes, a);
    let root = or(&mut nodes, neg_a, b);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Ground event-decomposed biconditional: And(Or(Not(A),B), Or(Not(B),A)).
fn make_event_biconditional(entity: &str, a: &str, b: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let a1 = event_operand(&mut nodes, "_ev0", a, entity);
    let b1 = event_operand(&mut nodes, "_ev1", b, entity);
    let neg_a1 = not(&mut nodes, a1);
    let impl1 = or(&mut nodes, neg_a1, b1);
    let b2 = event_operand(&mut nodes, "_ev2", b, entity);
    let a2 = event_operand(&mut nodes, "_ev3", a, entity);
    let neg_b2 = not(&mut nodes, b2);
    let impl2 = or(&mut nodes, neg_b2, a2);
    let root = and(&mut nodes, impl1, impl2);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_event_decomposed_ground_material_conditional() {
    // Or(Not(∃e. gerku(e) ∧ gerku_x1(e, adam)), ∃e2. danlu(e2) ∧ danlu_x1(e2, adam))
    // + gerku(adam) ⇒ danlu(adam) (modus ponens over event-decomposed operands).
    let kb = new_kb();
    assert_buf(
        &kb,
        make_event_material_conditional("adam", "gerku", "danlu"),
    );
    assert_buf(&kb, make_event_assertion("adam", "gerku"));
    assert!(
        query(&kb, make_event_query("adam", "danlu")),
        "ground material conditional should derive danlu(adam) from gerku(adam)"
    );
}

#[test]
fn test_event_decomposed_ground_material_conditional_no_antecedent() {
    // Negative control: without the antecedent fact the conclusion is not derivable.
    let kb = new_kb();
    assert_buf(
        &kb,
        make_event_material_conditional("adam", "gerku", "danlu"),
    );
    assert!(
        !query(&kb, make_event_query("adam", "danlu")),
        "danlu(adam) must NOT hold without gerku(adam)"
    );
}

#[test]
fn test_event_decomposed_ground_biconditional_both_directions() {
    // A ↔ B reasons both ways over event-decomposed operands (no CycleCut).
    let kb = new_kb();
    assert_buf(&kb, make_event_biconditional("adam", "gerku", "danlu"));
    assert_buf(&kb, make_event_assertion("adam", "gerku"));
    assert!(
        query(&kb, make_event_query("adam", "danlu")),
        "biconditional: danlu(adam) should derive from gerku(adam) (forward)"
    );

    let kb2 = new_kb();
    assert_buf(&kb2, make_event_biconditional("adam", "gerku", "danlu"));
    assert_buf(&kb2, make_event_assertion("adam", "danlu"));
    assert!(
        query(&kb2, make_event_query("adam", "gerku")),
        "biconditional: gerku(adam) should derive from danlu(adam) (reverse)"
    );
}

#[test]
fn test_event_decomposed_rule_selective() {
    let kb = new_kb();
    assert_buf(&kb, make_event_assertion("alis", "gerku"));
    assert_buf(&kb, make_event_assertion("bob", "mlatu"));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert!(
        query(&kb, make_event_query("alis", "danlu")),
        "danlu(alis) should hold (alis is a gerku)"
    );
    assert!(
        !query(&kb, make_event_query("bob", "danlu")),
        "danlu(bob) should NOT hold (bob is a mlatu, not gerku)"
    );
}

#[test]
fn test_event_decomposed_entity_after_rule() {
    let kb = new_kb();
    // Add rule first, then fact — should still fire after saturation
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert_buf(&kb, make_event_assertion("alis", "gerku"));
    assert!(
        query(&kb, make_event_query("alis", "danlu")),
        "rule should fire even when added before fact"
    );
}

#[test]
fn test_event_decomposed_temporal_rule() {
    let kb = new_kb();
    // Assert: Past(Exists(_ev0, And(gerku(_ev0), gerku_x1(_ev0, alis))))
    let mut a_nodes = Vec::new();
    let p_type = pred(
        &mut a_nodes,
        "gerku",
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let p_role = pred(
        &mut a_nodes,
        "gerku_x1",
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Constant("alis".to_string()),
        ],
    );
    let p_and = and(&mut a_nodes, p_type, p_role);
    let p_exists = exists(&mut a_nodes, "_ev0", p_and);
    let a_root = past(&mut a_nodes, p_exists);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![a_root],
        },
    );

    // Add timeless rule: ro lo gerku ku danlu (event-decomposed)
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    // Query: Past(Exists(_ev0, And(danlu(_ev0), danlu_x1(_ev0, alis))))
    let mut q_nodes = Vec::new();
    let q_type = pred(
        &mut q_nodes,
        "danlu",
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let q_role = pred(
        &mut q_nodes,
        "danlu_x1",
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Constant("alis".to_string()),
        ],
    );
    let q_and = and(&mut q_nodes, q_type, q_role);
    let q_exists = exists(&mut q_nodes, "_ev0", q_and);
    let q_root = past(&mut q_nodes, q_exists);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes: q_nodes,
                roots: vec![q_root],
            }
        ),
        "temporal lifting should derive Past(danlu(alis)) from Past(gerku(alis)) and timeless rule"
    );
}

#[test]
fn test_event_decomposed_multi_hop() {
    let kb = new_kb();
    assert_buf(&kb, make_event_assertion("alis", "gerku"));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "xanlu"));
    assert!(
        query(&kb, make_event_query("alis", "xanlu")),
        "multi-hop: gerku→danlu→xanlu should derive xanlu(alis)"
    );
}

#[test]
fn test_event_decomposed_proof_trace() {
    let kb = new_kb();
    assert_buf(&kb, make_event_assertion("alis", "gerku"));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    // Query with proof trace
    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_event_query("alis", "danlu"))
        .unwrap();
    assert!(
        holds.is_true(),
        "entailment should hold for derived event-decomposed fact"
    );

    // Check that the proof trace contains a Derived step
    let has_derived = trace
        .steps
        .iter()
        .any(|step| matches!(&step.rule, ProofRule::Derived(_)));
    assert!(
        has_derived,
        "proof trace should contain at least one Derived step for rule-derived fact"
    );
}

#[test]
fn test_event_decomposed_xorlo() {
    let kb = new_kb();
    // Only add the rule (no ground facts) — xorlo presupposition should
    // create Skolem constants that make the restrictor domain non-empty
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    // The xorlo presupposition should have created event + entity Skolems
    // such that gerku(sk_ev) and gerku_x1(sk_ev, sk_entity) hold.
    // Query: exists something that is a gerku (via xorlo presupposition)
    let mut q_nodes = Vec::new();
    let q_type = pred(
        &mut q_nodes,
        "gerku",
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let q_role = pred(
        &mut q_nodes,
        "gerku_x1",
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Variable("_v0".to_string()),
        ],
    );
    let q_and = and(&mut q_nodes, q_type, q_role);
    let q_ev = exists(&mut q_nodes, "_ev0", q_and);
    let q_root = exists(&mut q_nodes, "_v0", q_ev);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes: q_nodes,
                roots: vec![q_root],
            }
        ),
        "xorlo presupposition should make ∃x.∃e. gerku(e)∧gerku_x1(e,x) hold"
    );
}

// ─── Zoo Ontology integration tests (REPL demo scenarios) ───────

/// Build a temporal event-decomposed assertion:
///   Tense(Exists(_ev0, And(P(_ev0), P_x1(_ev0, entity))))
/// where tense_fn wraps the inner Exists with Past/Present/Future.
fn make_temporal_event_assertion(
    entity: &str,
    predicate: &str,
    tense_fn: fn(&mut Vec<LogicNode>, u32) -> u32,
) -> LogicBuffer {
    let mut nodes = Vec::new();
    let p_type = pred(
        &mut nodes,
        predicate,
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let p_role = pred(
        &mut nodes,
        &format!("{}_x1", predicate),
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Constant(entity.to_string()),
        ],
    );
    let p_and = and(&mut nodes, p_type, p_role);
    let p_exists = exists(&mut nodes, "_ev0", p_and);
    let root = tense_fn(&mut nodes, p_exists);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Build a temporal event-decomposed query (same structure as temporal assertion).
fn make_temporal_event_query(
    entity: &str,
    predicate: &str,
    tense_fn: fn(&mut Vec<LogicNode>, u32) -> u32,
) -> LogicBuffer {
    make_temporal_event_assertion(entity, predicate, tense_fn)
}

#[test]
fn test_zoo_multi_hop_temporal_past() {
    // REPL: pu la .alis. gerku → ro lo gerku cu danlu → ro lo danlu cu jmive
    // Query: ?! pu la .alis. jmive → TRUE
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "jmive"));
    assert!(
        query(&kb, make_temporal_event_query("alis", "jmive", past)),
        "multi-hop temporal: Past(gerku→danlu→jmive) should derive Past(jmive(alis))"
    );
}

#[test]
fn test_zoo_multi_hop_temporal_present() {
    // REPL: ca la .bob. mlatu → ro lo mlatu cu danlu → ro lo danlu cu jmive
    // Query: ?! ca la .bob. jmive → TRUE
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
    assert_buf(&kb, make_event_universal("mlatu", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "jmive"));
    assert!(
        query(&kb, make_temporal_event_query("bob", "jmive", present)),
        "multi-hop temporal: Present(mlatu→danlu→jmive) should derive Present(jmive(bob))"
    );
}

#[test]
fn test_zoo_tense_discrimination() {
    // Assert Past(gerku(alis)), derive Past(jmive(alis))
    // Query Present(jmive(alis)) → FALSE (strict tense discrimination)
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "jmive"));

    // Past query should succeed
    assert!(
        query(&kb, make_temporal_event_query("alis", "jmive", past)),
        "Past(jmive(alis)) should hold"
    );
    // Present query should FAIL — alice was a dog in the past, not present
    assert!(
        !query(&kb, make_temporal_event_query("alis", "jmive", present)),
        "Present(jmive(alis)) should NOT hold — wrong tense"
    );
}

#[test]
fn test_zoo_mixed_tenses() {
    // REPL demo: two entities with different tenses
    // pu la .alis. gerku + ca la .bob. mlatu + rules
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
    assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert_buf(&kb, make_event_universal("mlatu", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "jmive"));

    // Each entity derivable only in its own tense
    assert!(query(&kb, make_temporal_event_query("alis", "jmive", past)));
    assert!(query(
        &kb,
        make_temporal_event_query("bob", "jmive", present)
    ));
    // Cross-tense queries fail
    assert!(!query(
        &kb,
        make_temporal_event_query("alis", "jmive", present)
    ));
    assert!(!query(&kb, make_temporal_event_query("bob", "jmive", past)));
}

#[test]
fn test_zoo_witness_extraction_event_decomposed() {
    // REPL: ?? ma danlu — find witnesses after event-decomposed derivation
    let kb = new_kb();
    assert_buf(&kb, make_event_assertion("alis", "gerku"));
    assert_buf(&kb, make_event_assertion("bob", "gerku"));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    // Query: ∃_v0. ∃_ev0. danlu(_ev0) ∧ danlu_x1(_ev0, _v0)
    let mut q_nodes = Vec::new();
    let q_type = pred(
        &mut q_nodes,
        "danlu",
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let q_role = pred(
        &mut q_nodes,
        "danlu_x1",
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Variable("_v0".to_string()),
        ],
    );
    let q_and = and(&mut q_nodes, q_type, q_role);
    let q_ev = exists(&mut q_nodes, "_ev0", q_and);
    let q_root = exists(&mut q_nodes, "_v0", q_ev);
    let results = query_find(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root],
        },
    );

    // Should find witnesses for both alis and bob
    assert!(
        !results.is_empty(),
        "should find witnesses for danlu after event-decomposed derivation"
    );
    // Extract entity bindings (filter to _v0 which is the entity variable)
    let entity_witnesses: Vec<String> = results
        .iter()
        .filter_map(|bindings| {
            bindings.iter().find_map(|b| {
                if b.variable == "_v0" {
                    match &b.term {
                        LogicalTerm::Constant(c) => Some(c.clone()),
                        _ => None,
                    }
                } else {
                    None
                }
            })
        })
        .collect();
    assert!(
        entity_witnesses.contains(&"alis".to_string()),
        "alis should be a witness for danlu"
    );
    assert!(
        entity_witnesses.contains(&"bob".to_string()),
        "bob should be a witness for danlu"
    );
}

#[test]
fn test_zoo_retraction_with_event_decomposition() {
    // REPL demo: retract alice's fact, bob should survive
    let kb = new_kb();
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert_buf(&kb, make_event_universal("mlatu", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "jmive"));

    let alis_id = kb
        .assert_fact_inner(
            make_temporal_event_assertion("alis", "gerku", past),
            "pu la .alis. gerku".into(),
        )
        .unwrap();
    let _bob_id = kb
        .assert_fact_inner(
            make_temporal_event_assertion("bob", "mlatu", present),
            "ca la .bob. mlatu".into(),
        )
        .unwrap();

    // Both should hold before retraction
    assert!(query(&kb, make_temporal_event_query("alis", "jmive", past)));
    assert!(query(
        &kb,
        make_temporal_event_query("bob", "jmive", present)
    ));

    // Retract alice's assertion
    kb.retract_fact_inner(alis_id).unwrap();

    // Alice's derivation should be gone
    assert!(
        !query(&kb, make_temporal_event_query("alis", "jmive", past)),
        "after retracting alis's gerku fact, Past(jmive(alis)) should be FALSE"
    );
    // Bob's derivation should still hold
    assert!(
        query(&kb, make_temporal_event_query("bob", "jmive", present)),
        "bob's Present(jmive(bob)) should still hold after retracting alis"
    );
}

#[test]
fn test_zoo_proof_trace_multi_hop_temporal() {
    // REPL: ?! pu la .alis. jmive — proof trace for multi-hop temporal derivation
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "jmive"));

    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_temporal_event_query("alis", "jmive", past))
        .unwrap();
    assert!(
        holds.is_true(),
        "Past(jmive(alis)) should hold with proof trace"
    );

    // Proof should contain Derived steps (from rule application)
    let derived_count = trace
        .steps
        .iter()
        .filter(|step| matches!(&step.rule, ProofRule::Derived(_)))
        .count();
    assert!(
        derived_count >= 2,
        "multi-hop derivation should have at least 2 Derived steps (gerku→danlu, danlu→jmive), got {}",
        derived_count
    );

    // Proof should contain a ModalPassthrough for past tense
    let has_modal = trace
        .steps
        .iter()
        .any(|step| matches!(&step.rule, ProofRule::ModalPassthrough(t) if t == "past"));
    assert!(
        has_modal,
        "proof trace should contain a ModalPassthrough(past) step"
    );
}

#[test]
fn backchain_temporal_trace_label_present() {
    // A tensed goal proved via a bare (timeless) rule + temporal lifting must
    // carry the tense in its Derived step's LABEL (the `[past]` suffix emitted by
    // the merged core's temporal phase via `emit_derived`). This is distinct from
    // the ModalPassthrough(past) wrapper step and pins that the merge kept the
    // tense-label keying when folding the traced temporal block into the core.
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_temporal_event_query("alis", "danlu", past))
        .unwrap();
    assert!(holds.is_true(), "Past(danlu(alis)) should hold");

    let has_tensed_derived = trace.steps.iter().any(
        |step| matches!(&step.rule, ProofRule::Derived((label, _)) if label.contains("[past]")),
    );
    assert!(
        has_tensed_derived,
        "temporal-lifted derivation should carry a `[past]` tag in a Derived label; rules seen: {:?}",
        trace
            .steps
            .iter()
            .filter_map(|s| match &s.rule {
                ProofRule::Derived((l, _)) => Some(l.clone()),
                _ => None,
            })
            .collect::<Vec<_>>()
    );
}

// ---- Proof trace memoization tests ----

#[test]
fn test_proof_memo_deduplication() {
    // Multi-hop event-decomposed trace should use ProofRef for repeated sub-proofs.
    // Without memoization: mlatu base facts appear 12× in a 2-hop 3-role chain.
    // With memoization: repeated facts get ProofRef nodes instead.
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
    assert_buf(&kb, make_event_universal("mlatu", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "jmive"));

    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_temporal_event_query("bob", "jmive", present))
        .unwrap();
    assert!(holds.is_true(), "Present(jmive(bob)) should hold");

    // Count ProofRef steps — should be present due to repeated condition proofs
    let proof_ref_count = trace
        .steps
        .iter()
        .filter(|step| matches!(&step.rule, ProofRule::ProofRef(_)))
        .count();
    assert!(
        proof_ref_count > 0,
        "2-hop event-decomposed trace should have ProofRef nodes for deduplicated sub-proofs, got {}",
        proof_ref_count
    );

    // With memoization, condition proofs that repeat across different
    // conclusion derivations get ProofRef instead of full re-expansion.
    // The ExistsNode witness search also generates overhead (failed candidates),
    // but the key improvement is visible in the successful derivation path.
    assert!(
        proof_ref_count >= 3,
        "2-hop event trace should have at least 3 ProofRef nodes (deduplicated conditions), got {}",
        proof_ref_count
    );
}

#[test]
fn proof_ref_children_are_holds_true() {
    // Stage 2d invariant: every ProofRef leaf resolves to a holds:true step, because
    // only holds:true derivations (Asserted / Derived / EqualitySubstitution) are
    // memoized — the depth-relative PredicateNotFound no longer is, so a stale
    // not-found can never be reached via a ProofRef. Exercised across several
    // memo-bearing trace shapes. (A direct RED reproduction of the cross-recursion-
    // depth poisoning is unconstructible in the same way the 2a/2b divergence tests
    // were — the verdict cache + horizon short-circuit collapse the scenario — so
    // this asserts the resulting PROPERTY rather than the elusive walk order.)

    // (a) Multi-hop event chain — heavy ProofRef dedup of repeated role conditions.
    {
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
        assert_buf(&kb, make_event_universal("mlatu", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "jmive"));
        let (_holds, trace) = kb
            .query_entailment_with_proof_inner(make_temporal_event_query("bob", "jmive", present))
            .unwrap();
        assert_proof_refs_resolve_to_holds_true(&trace);
    }
    // (b) du-equivalence — exercises the EqualitySubstitution memo path.
    {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("adam", "gerku"));
        assert_buf(&kb, make_du("adam", "betty"));
        let (_holds, trace) = kb
            .query_entailment_with_proof_inner(make_query("betty", "gerku"))
            .unwrap();
        assert_proof_refs_resolve_to_holds_true(&trace);
    }
    // (c) Flat universal-rule syllogism.
    {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_assertion("alis", "gerku"));
        let (_holds, trace) = kb
            .query_entailment_with_proof_inner(make_query("alis", "danlu"))
            .unwrap();
        assert_proof_refs_resolve_to_holds_true(&trace);
    }
}

#[test]
fn proof_trace_byte_deterministic_3x() {
    // The proof trace must be byte-reproducible run-to-run (no HashSet-order leakage
    // into the recorded structure). Build a memo-heavy 2-hop event chain in three
    // fresh KB instances and assert the serialized trace is identical each time.
    let render = || {
        let kb = new_kb();
        assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
        assert_buf(&kb, make_event_universal("mlatu", "danlu"));
        assert_buf(&kb, make_event_universal("danlu", "jmive"));
        let (_holds, trace) = kb
            .query_entailment_with_proof_inner(make_temporal_event_query("bob", "jmive", present))
            .unwrap();
        format!("{trace:?}")
    };
    let a = render();
    let b = render();
    let c = render();
    assert_eq!(a, b, "proof trace not deterministic (run 1 vs run 2)");
    assert_eq!(b, c, "proof trace not deterministic (run 2 vs run 3)");
}

#[test]
fn proof_trace_equals_pinned_resolving_depth() {
    // The iterative-deepening proof query returns the trace built at the RESOLVING
    // depth (the shallowest non-ResourceExceeded(Depth) depth). This locks that
    // invariant: the deepening loop's trace == a single proof build pinned at the
    // resolving depth — the property the build-once-at-resolving-depth optimization
    // relies on. A 2-hop chain (proof at depth >1) exercises it: querying the
    // shallow depths hits the depth horizon (RE) before the chain resolves.

    // (A) Build the trace ONCE, pinned at the resolving depth. The resolving depth
    //     is found with the cheap UNTRACED walk on a freshly-cleared per-KB cache
    //     (clear it so a prior query's cached True can't make a shallow probe
    //     spuriously resolve).
    let kb_pin = new_kb();
    assert_buf(&kb_pin, make_assertion("alis", "gerku"));
    assert_buf(&kb_pin, make_universal("gerku", "danlu"));
    assert_buf(&kb_pin, make_universal("danlu", "xanlu"));
    let configured_max = {
        let inner = kb_pin.inner.borrow();
        clear_and_enable_pred_cache(&inner);
        inner.max_chain_depth
    };
    let mut resolving_depth = configured_max;
    for depth_limit in 1..=configured_max {
        kb_pin.inner.borrow_mut().max_chain_depth = depth_limit;
        let r = kb_pin
            .run_entailment_check(&make_query("alis", "xanlu"))
            .unwrap();
        if !matches!(r, QueryResult::ResourceExceeded(ResourceKind::Depth)) {
            resolving_depth = depth_limit;
            break;
        }
    }
    kb_pin.inner.borrow_mut().max_chain_depth = resolving_depth;
    let (r_pin, t_pin) = kb_pin
        .run_entailment_check_with_proof(&make_query("alis", "xanlu"))
        .unwrap();
    kb_pin.inner.borrow_mut().max_chain_depth = configured_max;

    // (B) The full iterative-deepening proof query (clears the cache at its start).
    let kb_loop = new_kb();
    assert_buf(&kb_loop, make_assertion("alis", "gerku"));
    assert_buf(&kb_loop, make_universal("gerku", "danlu"));
    assert_buf(&kb_loop, make_universal("danlu", "xanlu"));
    let (r_loop, t_loop) = kb_loop
        .query_entailment_with_proof_inner(make_query("alis", "xanlu"))
        .unwrap();

    assert!(
        r_loop.is_true(),
        "xanlu(alis) should hold via the 2-hop chain"
    );
    assert!(
        resolving_depth > 1,
        "expected a multi-hop proof (resolving depth >1), got {resolving_depth}"
    );
    assert_eq!(
        r_loop, r_pin,
        "verdict mismatch: deepening loop vs pinned at resolving depth"
    );
    assert_eq!(
        format!("{t_loop:?}"),
        format!("{t_pin:?}"),
        "trace mismatch: deepening loop vs single build at resolving depth {resolving_depth}"
    );
}

#[test]
fn test_proof_memo_correctness() {
    // Memoized trace still reports the correct result and contains proper Derived + Asserted steps.
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_temporal_event_query("alis", "danlu", past))
        .unwrap();
    assert!(holds.is_true(), "Past(danlu(alis)) should hold");

    // Should still have Derived steps from the rule application
    let derived_count = trace
        .steps
        .iter()
        .filter(|step| matches!(&step.rule, ProofRule::Derived(_)))
        .count();
    assert!(
        derived_count >= 1,
        "should have at least 1 Derived step from gerku→danlu rule, got {}",
        derived_count
    );

    // First occurrence of base facts should be Asserted or PredicateCheck (not ProofRef)
    let has_asserted_or_check = trace.steps.iter().any(|step| {
        matches!(&step.rule, ProofRule::Asserted(_))
            || matches!(&step.rule, ProofRule::PredicateCheck(_))
    });
    assert!(
        has_asserted_or_check,
        "first occurrence of base facts should be Asserted or PredicateCheck, not ProofRef"
    );
}

#[test]
fn test_proof_memo_single_hop_no_unnecessary_refs() {
    // Single-hop with one entity: each condition is unique,
    // so no ProofRef should be needed.
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("alis", "gerku", past));
    assert_buf(&kb, make_event_universal("gerku", "danlu"));

    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_temporal_event_query("alis", "danlu", past))
        .unwrap();
    assert!(holds.is_true(), "Past(danlu(alis)) should hold");

    // In a single-hop scenario, conditions are gerku(e), gerku_x1(e, alis), gerku_x2(e, zo'e)
    // These are all unique facts, so no ProofRef should be needed for condition proofs.
    // ProofRef may still appear if the same fact is checked multiple times through
    // different paths, but the count should be very low.
    let proof_ref_count = trace
        .steps
        .iter()
        .filter(|step| matches!(&step.rule, ProofRule::ProofRef(_)))
        .count();
    // Allow a small number — the point is it's not the cubic blowup
    assert!(
        proof_ref_count <= 3,
        "single-hop trace should have very few ProofRef nodes (unique conditions), got {}",
        proof_ref_count
    );
}

// ─── Book example regression test (event Skolem InDomain blowup) ────

/// Build a 2-argument event-decomposed assertion:
///   ∃ev0. P(ev0) ∧ P_x1(ev0, entity1) ∧ P_x2(ev0, entity2)
/// This models sentences like "lo prenu cu ponse lo datni" where both
/// the subject and object are concrete entities.
fn make_event_assertion_2arg(entity1: &str, entity2: &str, predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let p_type = pred(
        &mut nodes,
        predicate,
        vec![LogicalTerm::Variable("_ev0".to_string())],
    );
    let p_role1 = pred(
        &mut nodes,
        &format!("{}_x1", predicate),
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Constant(entity1.to_string()),
        ],
    );
    let p_role2 = pred(
        &mut nodes,
        &format!("{}_x2", predicate),
        vec![
            LogicalTerm::Variable("_ev0".to_string()),
            LogicalTerm::Constant(entity2.to_string()),
        ],
    );
    let a1 = and(&mut nodes, p_type, p_role1);
    let a2 = and(&mut nodes, a1, p_role2);
    let root = exists(&mut nodes, "_ev0", a2);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_book_example_no_oom() {
    // Regression test for the book example that was crashing with OOM:
    //   .i lo prenu cu ponse lo datni
    //   .i ro lo prenu poi ponse lo datni cu bilga lo nu curmi
    //   ?! lo prenu cu bilga lo nu curmi
    //
    // The crash was caused by event Skolem constants being registered in
    // `known_entities`, causing O(N²) blowup in guarded
    // conjunction introduction. With 2-arg predicates and universal rules,
    // each event constant linked ~6 predicates → C(6,2)=15 conjunctions
    // → commutativity doubled them → exponential growth.
    //
    // This test models the scenario with multiple entities and predicates
    // to verify no memory explosion occurs.
    let kb = new_kb();

    // Assert: "A person possesses data"
    // ∃ev0. ponse(ev0) ∧ ponse_x1(ev0, prenu_sk) ∧ ponse_x2(ev0, datni_sk)
    assert_buf(
        &kb,
        make_event_assertion_2arg("prenu_sk", "datni_sk", "ponse"),
    );

    // Also assert the gadri decompositions (what `lo prenu` and `lo datni` produce):
    // ∃ev1. prenu(ev1) ∧ prenu_x1(ev1, prenu_sk)
    assert_buf(&kb, make_event_assertion("prenu_sk", "prenu"));
    // ∃ev2. datni(ev2) ∧ datni_x1(ev2, datni_sk)
    assert_buf(&kb, make_event_assertion("datni_sk", "datni"));

    // Assert universal rule: "Every person who possesses data is obligated"
    // This is simplified as: ∀x. prenu(x) → bilga(x)
    assert_buf(&kb, make_event_universal("prenu", "bilga"));

    // Add another universal rule to increase backward-chaining depth
    assert_buf(&kb, make_event_universal("bilga", "zukte"));

    // Query: "A person is obligated" — should hold via prenu→bilga derivation
    assert!(
        query(&kb, make_event_assertion("prenu_sk", "bilga")),
        "prenu_sk should be derived as bilga via universal rule"
    );

    // Query with proof trace — this is what was crashing before the fix
    let (holds, _trace) = kb
        .query_entailment_with_proof_inner(make_event_assertion("prenu_sk", "bilga"))
        .unwrap();
    assert!(
        holds.is_true(),
        "proof-traced query should hold for bilga(prenu_sk)"
    );

    // Multi-hop: prenu→bilga→zukte
    assert!(
        query(&kb, make_event_assertion("prenu_sk", "zukte")),
        "multi-hop prenu→bilga→zukte should derive zukte(prenu_sk)"
    );

    // Proof trace for multi-hop should complete without OOM
    let (holds2, _trace2) = kb
        .query_entailment_with_proof_inner(make_event_assertion("prenu_sk", "zukte"))
        .unwrap();
    assert!(
        holds2.is_true(),
        "proof-traced multi-hop should hold for zukte(prenu_sk)"
    );
}

// ─── And flattening regression test ────

#[test]
fn test_and_flattening_prevents_rewrite_explosion() {
    // Regression test: a deeply nested And tree with 7 leaves (matching the
    // real Neo-Davidsonian decomposition of ".i lo prenu cu ponse lo datni")
    // previously caused combinatorial explosion. After flattening, each leaf
    // is asserted individually, so the fact count should be bounded.
    let kb = new_kb();

    // Build: ∃ev. P1(ev) ∧ P2(ev,a) ∧ P3(ev,b) ∧ P4(a) ∧ P5(b) ∧ P6(a) ∧ P7(b)
    // This simulates a 2-arg predicate with xorlo restrictors.
    let mut nodes = Vec::new();
    let p1 = pred(
        &mut nodes,
        "ponse",
        vec![LogicalTerm::Variable("_ev0".into())],
    );
    let p2 = pred(
        &mut nodes,
        "ponse_x1",
        vec![
            LogicalTerm::Variable("_ev0".into()),
            LogicalTerm::Variable("_v0".into()),
        ],
    );
    let p3 = pred(
        &mut nodes,
        "ponse_x2",
        vec![
            LogicalTerm::Variable("_ev0".into()),
            LogicalTerm::Variable("_v1".into()),
        ],
    );
    let p4 = pred(
        &mut nodes,
        "prenu",
        vec![LogicalTerm::Variable("_v0".into())],
    );
    let p5 = pred(
        &mut nodes,
        "datni",
        vec![LogicalTerm::Variable("_v1".into())],
    );
    let p6 = pred(
        &mut nodes,
        "prenu_x1",
        vec![
            LogicalTerm::Variable("_ev1".into()),
            LogicalTerm::Variable("_v0".into()),
        ],
    );
    let p7 = pred(
        &mut nodes,
        "datni_x1",
        vec![
            LogicalTerm::Variable("_ev2".into()),
            LogicalTerm::Variable("_v1".into()),
        ],
    );

    // Build deeply nested And tree (7 leaves, 6 And nodes)
    let a1 = and(&mut nodes, p1, p2);
    let a2 = and(&mut nodes, a1, p3);
    let a3 = and(&mut nodes, a2, p4);
    let a4 = and(&mut nodes, a3, p5);
    let a5 = and(&mut nodes, a4, p6);
    let a6 = and(&mut nodes, a5, p7);

    // Wrap in existentials (these will be Skolemized)
    let e0 = exists(&mut nodes, "_ev0", a6);
    let e1 = exists(&mut nodes, "_ev1", e0);
    let e2 = exists(&mut nodes, "_ev2", e1);
    let e3 = exists(&mut nodes, "_v0", e2);
    let root = exists(&mut nodes, "_v1", e3);

    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };

    assert_buf(&kb, buf);

    // Verify the fact count is bounded — each leaf gets a single entry
    // in the fact store (no combinatorial And explosion).
    let inner = kb.inner.borrow();
    let fact_count = inner.fact_store.len();
    eprintln!("[Test] fact_store count: {}", fact_count);
    assert!(
        fact_count < 100,
        "Asserted facts should be < 100 after flattening, got {}",
        fact_count
    );
}

// ─── Compute error propagation tests ─────────────────────────

#[test]
fn test_compute_backend_error_surfaces() {
    // ComputeNode for unknown predicate without registered backend
    // should return false (no backend = cannot prove), not panic.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let root = compute(
        &mut nodes,
        "tenfa", // not a built-in arithmetic predicate
        vec![
            LogicalTerm::Number(8.0),
            LogicalTerm::Number(2.0),
            LogicalTerm::Number(3.0),
        ],
    );
    // Without a registered backend, this falls back to KB lookup (fails)
    // and then dispatch_to_backend returns Err. The error should propagate
    // as false (not provable), not crash.
    assert!(!query(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    ));
}

// ─── ProofRef memo back-reference validation ─────────────────

#[test]
fn test_proof_ref_carries_cached_index() {
    // Verify that ProofRef steps carry the original step index in children.
    let kb = new_kb();
    assert_buf(&kb, make_temporal_event_assertion("bob", "mlatu", present));
    assert_buf(&kb, make_event_universal("mlatu", "danlu"));
    assert_buf(&kb, make_event_universal("danlu", "jmive"));

    let (holds, trace) = kb
        .query_entailment_with_proof_inner(make_temporal_event_query("bob", "jmive", present))
        .unwrap();
    assert!(holds.is_true());

    // Every ProofRef step should have exactly one child pointing to the
    // original step, and its holds value should match the referenced step.
    for step in &trace.steps {
        if let ProofRule::ProofRef(_) = &step.rule {
            assert_eq!(
                step.children.len(),
                1,
                "ProofRef should have exactly 1 child (back-reference)"
            );
            let referenced_idx = step.children[0] as usize;
            assert!(
                referenced_idx < trace.steps.len(),
                "ProofRef back-reference {} out of bounds ({})",
                referenced_idx,
                trace.steps.len()
            );
            assert_eq!(
                step.holds, trace.steps[referenced_idx].holds,
                "ProofRef.holds should match the referenced step's holds"
            );
        }
    }
}

// ─── unify_facts edge case tests ─────────────────────────────

#[test]
fn test_unify_pattern_var_rebinding_consistent() {
    use super::kb::*;
    // Pattern variable bound to "alis" in first arg must match "alis" in second.
    let template = StoredFact::Bare(GroundFact::new(
        "friends",
        vec![
            GroundTerm::PatternVar("x".into()),
            GroundTerm::PatternVar("x".into()),
        ],
    ));
    let concrete = StoredFact::Bare(GroundFact::new(
        "friends",
        vec![
            GroundTerm::Constant("alis".into()),
            GroundTerm::Constant("alis".into()),
        ],
    ));
    let result = unify_facts(&template, &concrete);
    assert!(result.is_some(), "same-value rebinding should succeed");
    assert_eq!(
        result.unwrap().get("x"),
        Some(&GroundTerm::Constant("alis".into()))
    );
}

#[test]
fn test_unify_pattern_var_rebinding_conflict() {
    use super::kb::*;
    // Pattern variable "x" bound to "alis" then "bob" should fail.
    let template = StoredFact::Bare(GroundFact::new(
        "friends",
        vec![
            GroundTerm::PatternVar("x".into()),
            GroundTerm::PatternVar("x".into()),
        ],
    ));
    let concrete = StoredFact::Bare(GroundFact::new(
        "friends",
        vec![
            GroundTerm::Constant("alis".into()),
            GroundTerm::Constant("bob".into()),
        ],
    ));
    assert!(
        unify_facts(&template, &concrete).is_none(),
        "conflicting rebinding should fail"
    );
}

#[test]
fn test_unify_skolem_fn_nested() {
    use super::kb::*;
    // SkolemFn("sk_0", PatternVar("x")) against SkolemFn("sk_0", Constant("alis"))
    let template = StoredFact::Bare(GroundFact::new(
        "rel",
        vec![GroundTerm::SkolemFn(
            "sk_0".into(),
            Box::new(GroundTerm::PatternVar("x".into())),
        )],
    ));
    let concrete = StoredFact::Bare(GroundFact::new(
        "rel",
        vec![GroundTerm::SkolemFn(
            "sk_0".into(),
            Box::new(GroundTerm::Constant("alis".into())),
        )],
    ));
    let result = unify_facts(&template, &concrete);
    assert!(
        result.is_some(),
        "SkolemFn nested unification should succeed"
    );
    assert_eq!(
        result.unwrap().get("x"),
        Some(&GroundTerm::Constant("alis".into()))
    );
}

#[test]
fn test_unify_dep_pair() {
    use super::kb::*;
    // DepPair(PatternVar("x"), PatternVar("y")) against DepPair(Const("a"), Const("b"))
    let template = StoredFact::Bare(GroundFact::new(
        "rel",
        vec![GroundTerm::DepPair(
            Box::new(GroundTerm::PatternVar("x".into())),
            Box::new(GroundTerm::PatternVar("y".into())),
        )],
    ));
    let concrete = StoredFact::Bare(GroundFact::new(
        "rel",
        vec![GroundTerm::DepPair(
            Box::new(GroundTerm::Constant("a".into())),
            Box::new(GroundTerm::Constant("b".into())),
        )],
    ));
    let result = unify_facts(&template, &concrete);
    assert!(result.is_some(), "DepPair unification should succeed");
    let bindings = result.unwrap();
    assert_eq!(bindings.get("x"), Some(&GroundTerm::Constant("a".into())));
    assert_eq!(bindings.get("y"), Some(&GroundTerm::Constant("b".into())));
}

#[test]
fn test_unify_skolem_fn_name_mismatch() {
    use super::kb::*;
    // SkolemFn("sk_0", ...) vs SkolemFn("sk_1", ...) should fail
    let template = StoredFact::Bare(GroundFact::new(
        "rel",
        vec![GroundTerm::SkolemFn(
            "sk_0".into(),
            Box::new(GroundTerm::Constant("a".into())),
        )],
    ));
    let concrete = StoredFact::Bare(GroundFact::new(
        "rel",
        vec![GroundTerm::SkolemFn(
            "sk_1".into(),
            Box::new(GroundTerm::Constant("a".into())),
        )],
    ));
    assert!(
        unify_facts(&template, &concrete).is_none(),
        "SkolemFn name mismatch should fail"
    );
}

// ═══════════════════════════════════════════════════════════════════
// STRATIFICATION TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_safe_stratified_negation() {
    // ∀x. gerku(x) → danlu(x) — positive dependency, no negative cycle.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_safe_positive_recursion() {
    // P→Q, Q→R — positive chain. No negative edges.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(query(&kb, make_query("alis", "jmive")));
}

#[test]
fn test_ground_material_conditional_no_false_positive() {
    // ganai gerku gi danlu — ground material conditional.
    // Or(Not(gerku(alis)), danlu(alis)) → positive dependency gerku→danlu.
    // Stratification check should NOT reject this — it's a positive dependency.
    let kb = new_kb();
    let buf = LogicBuffer {
        nodes: vec![
            LogicNode::Predicate(("gerku".into(), vec![LogicalTerm::Constant("alis".into())])),
            LogicNode::NotNode(0),
            LogicNode::Predicate(("danlu".into(), vec![LogicalTerm::Constant("alis".into())])),
            LogicNode::OrNode((1, 2)),
        ],
        roots: vec![3],
    };
    // Should not error — the Not in Or(Not(P), Q) encodes implication, not body-negation.
    assert!(
        kb.assert_fact_inner(buf, "ganai gerku gi danlu".into())
            .is_ok(),
        "ground material conditional should not trigger stratification error"
    );
}

#[test]
fn test_retraction_rebuilds_dep_graph() {
    let kb = new_kb();
    let id1 = assert_id(&kb, make_universal("gerku", "danlu"), "rule1");
    let _id2 = assert_id(&kb, make_universal("mlatu", "danlu"), "rule2");

    // Both rules registered — dep graph should have edges for both.
    {
        let inner = kb.inner.borrow();
        assert!(inner.pred_dep_graph.contains_key("danlu"));
    }

    // Retract rule1 — dep graph should rebuild with only rule2's edges.
    kb.retract_fact_inner(id1).unwrap();

    {
        let inner = kb.inner.borrow();
        // danlu should still be in graph (from rule2: mlatu → danlu).
        if let Some(edges) = inner.pred_dep_graph.get("danlu") {
            // Only mlatu should remain as a dependency, not gerku.
            let has_gerku = edges.iter().any(|(dep, _)| dep == "gerku");
            assert!(
                !has_gerku,
                "gerku edge should be gone after retracting rule1"
            );
            let has_mlatu = edges.iter().any(|(dep, _)| dep == "mlatu");
            assert!(has_mlatu, "mlatu edge should remain from rule2");
        }
    }
}

/// Build a ground material conditional for stratification tests:
/// `concl <- cond`  (positive edge concl->cond) as Or(Not(cond), concl), or
/// `concl <- ¬cond` (negative/NAF edge)         as Or(Not(Not(cond)), concl).
/// The inner Not is the NAF body-negation that `build_rule_template_fact_with_negation`
/// marks negated; the outer Not is the implication arm `decompose_implication` consumes.
fn make_material_cond(concl: &str, cond: &str, neg: bool) -> LogicBuffer {
    let mut nodes = Vec::new();
    let cond_pred = pred(&mut nodes, cond, vec![LogicalTerm::Constant("x".into())]);
    let not_cond = not(&mut nodes, cond_pred);
    let antecedent = if neg {
        not(&mut nodes, not_cond)
    } else {
        not_cond
    };
    let concl_pred = pred(&mut nodes, concl, vec![LogicalTerm::Constant("x".into())]);
    let root = or(&mut nodes, antecedent, concl_pred);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

const STRAT_PERMS: [[usize; 3]; 6] = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
];

#[test]
fn test_neg_cycle_rejected_all_orderings() {
    // {a <- ¬b; b <- ¬c; c <- b}: the SCC {b,c} contains the negative edge
    // b->¬c; a->¬b feeds IN but a is OUTSIDE the SCC (the position-blindness
    // trap). Pre-fix the verdict flips with the DFS root order (a fresh KB per
    // iteration reseeds the dep-graph HashMap, ~1/3 wrongly accept); post-fix
    // every ordering/seed rejects deterministically.
    let rules: [(&str, &str, bool); 3] = [
        ("a", "b", true),  // a <- ¬b
        ("b", "c", true),  // b <- ¬c
        ("c", "b", false), // c <- b
    ];
    for perm in STRAT_PERMS {
        for _ in 0..20 {
            let kb = new_kb();
            let mut any_err = false;
            for &i in &perm {
                let (concl, cond, neg) = rules[i];
                if kb
                    .assert_fact_inner(make_material_cond(concl, cond, neg), String::new())
                    .is_err()
                {
                    any_err = true;
                }
            }
            assert!(
                any_err,
                "unstratifiable negative cycle must be rejected (insertion order {perm:?})"
            );
        }
    }
}

#[test]
fn test_positive_cycle_accepted_all_orderings() {
    // {a <- b; b <- c; c <- a}: an all-positive cycle (no negative edge in the
    // SCC) is stratifiable and must ALWAYS be accepted — guards the SCC fix
    // against over-rejecting positive recursion routed through a cycle.
    let rules: [(&str, &str, bool); 3] = [("a", "b", false), ("b", "c", false), ("c", "a", false)];
    for perm in STRAT_PERMS {
        for _ in 0..20 {
            let kb = new_kb();
            for &i in &perm {
                let (concl, cond, neg) = rules[i];
                assert!(
                    kb.assert_fact_inner(make_material_cond(concl, cond, neg), String::new())
                        .is_ok(),
                    "all-positive cycle must be accepted (insertion order {perm:?})"
                );
            }
        }
    }
}

#[test]
fn test_neg_self_loop_rejected() {
    // a <- ¬a : a size-1 SCC with a negative self-edge — a degenerate negative
    // cycle that must be rejected (no `len() > 1` gate may skip it).
    let kb = new_kb();
    assert!(
        kb.assert_fact_inner(make_material_cond("a", "a", true), String::new())
            .is_err(),
        "negative self-loop a<-¬a must be rejected"
    );
}

#[test]
fn test_compute_sccs_partition() {
    // a <-> b (2-cycle), b -> c (tail; c is an edge target but NOT a graph key),
    // and an isolated key d. The partition must be {a,b}, {c}, {d} regardless of
    // HashMap order — pins the Tarjan port + the edge-target-as-node inclusion.
    let mut graph: std::collections::HashMap<String, Vec<(String, bool)>> =
        std::collections::HashMap::new();
    graph.insert("a".into(), vec![("b".into(), false)]);
    graph.insert("b".into(), vec![("a".into(), false), ("c".into(), false)]);
    graph.insert("d".into(), vec![]);
    let sccs = compute_sccs(&graph);
    let scc_of = |name: &str| -> Vec<String> {
        let mut s = sccs
            .iter()
            .find(|s| s.iter().any(|n| n.as_str() == name))
            .unwrap_or_else(|| panic!("no SCC contains {name}"))
            .clone();
        s.sort();
        s
    };
    assert_eq!(scc_of("a"), vec!["a".to_string(), "b".to_string()]);
    assert_eq!(scc_of("c"), vec!["c".to_string()]);
    assert_eq!(scc_of("d"), vec!["d".to_string()]);
}

// ═══════════════════════════════════════════════════════════════════
// EQUALITY / du TESTS
// ═══════════════════════════════════════════════════════════════════

/// Helper: build du(a, b) assertion.
fn make_du(a: &str, b: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "du",
        vec![
            LogicalTerm::Constant(a.to_string()),
            LogicalTerm::Constant(b.to_string()),
        ],
    );
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Helper: build du query.
fn make_du_query(a: &str, b: &str) -> LogicBuffer {
    make_du(a, b)
}

/// Helper: build a 2-arg assertion P(a, b).
fn make_assertion_2(entity1: &str, entity2: &str, predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        predicate,
        vec![
            LogicalTerm::Constant(entity1.to_string()),
            LogicalTerm::Constant(entity2.to_string()),
        ],
    );
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_du_basic_substitution() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_du("alis", "bob"));
    assert!(
        query(&kb, make_query("bob", "gerku")),
        "gerku(bob) should hold via du(alis, bob) + gerku(alis)"
    );
}

#[test]
fn test_du_symmetry() {
    let kb = new_kb();
    assert_buf(&kb, make_du("alis", "bob"));
    assert!(
        query(&kb, make_du_query("bob", "alis")),
        "du(bob, alis) should hold via symmetry"
    );
}

#[test]
fn test_du_transitivity() {
    let kb = new_kb();
    assert_buf(&kb, make_du("alis", "bob"));
    assert_buf(&kb, make_du("bob", "carol"));
    assert!(
        query(&kb, make_du_query("alis", "carol")),
        "du(alis, carol) should hold via transitivity"
    );
}

#[test]
fn test_du_reflexivity() {
    let kb = new_kb();
    // du(alis, alis) should hold without any assertion.
    assert!(
        query(&kb, make_du_query("alis", "alis")),
        "du(alis, alis) should hold via reflexivity"
    );
}

#[test]
fn test_du_with_backward_chain() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_du("alis", "bob"));
    assert!(
        query(&kb, make_query("bob", "danlu")),
        "danlu(bob) should hold via gerku→danlu + gerku(alis) + du(alis, bob)"
    );
}

#[test]
fn test_du_multiarg() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion_2("alis", "bob", "prami"));
    assert_buf(&kb, make_du("bob", "carol"));
    assert!(
        query(&kb, make_assertion_2("alis", "carol", "prami")),
        "prami(alis, carol) should hold via du(bob, carol) + prami(alis, bob)"
    );
}

#[test]
fn test_du_retraction_rebuild() {
    let kb = new_kb();
    let du_id = assert_id(&kb, make_du("alis", "bob"), "du");
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(
        query(&kb, make_query("bob", "gerku")),
        "should hold before retraction"
    );

    kb.retract_fact_inner(du_id).unwrap();
    assert!(
        !query(&kb, make_query("bob", "gerku")),
        "gerku(bob) should be FALSE after retracting du(alis, bob)"
    );
}

#[test]
fn test_du_no_tensed() {
    // Past(du(alis, bob)) should NOT activate equivalence.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let du_node = pred(
        &mut nodes,
        "du",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Constant("bob".to_string()),
        ],
    );
    let past = {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::PastNode(du_node));
        id
    };
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![past],
        },
    );
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(
        !query(&kb, make_query("bob", "gerku")),
        "gerku(bob) should be FALSE — tensed du does not activate equivalence"
    );
}

/// Helper: build a flat negated du assertion/query: Not(du(a, b)).
fn make_negated_du(a: &str, b: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let inner = pred(
        &mut nodes,
        "du",
        vec![
            LogicalTerm::Constant(a.to_string()),
            LogicalTerm::Constant(b.to_string()),
        ],
    );
    let root = not(&mut nodes, inner);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_na_du_transitive_contradiction() {
    // du(alis,bob) ∧ du(bob,carol) makes alis ≡ carol via the union-find even
    // though du(alis,carol) was never stored; asserting `na du(alis, carol)`
    // must be flagged. RED before the union-find-aware section: section 4 only
    // checks store membership, and du(alis,carol) is not in the store.
    let kb = new_kb();
    assert_buf(&kb, make_du("alis", "bob"));
    assert_buf(&kb, make_du("bob", "carol"));
    assert_id(&kb, make_negated_du("alis", "carol"), "na du");
    let violations = kb.check_contradictions();
    assert!(
        violations
            .iter()
            .any(|v| v.contains("Inequality contradiction")),
        "transitive equality must contradict the asserted inequality: {violations:?}"
    );
}

#[test]
fn test_na_du_unrelated_no_contradiction() {
    // du(alis,bob) but carol is unrelated: `na du(alis, carol)` is consistent.
    let kb = new_kb();
    assert_buf(&kb, make_du("alis", "bob"));
    assert_id(&kb, make_negated_du("alis", "carol"), "na du");
    assert!(
        kb.check_contradictions().is_empty(),
        "an inequality between non-equivalent terms is not a contradiction"
    );
}

#[test]
fn test_na_du_inequality_query() {
    // Inequality querying via NAF over the union-find: na du holds when the two
    // terms are not equivalent, and fails when they are.
    let kb = new_kb();
    assert_buf(&kb, make_du("alis", "bob"));
    assert!(
        query(&kb, make_negated_du("alis", "carol")),
        "na du(alis, carol) should hold — they are not equivalent"
    );
    assert!(
        !query(&kb, make_negated_du("alis", "bob")),
        "na du(alis, bob) should fail — they ARE equivalent"
    );
}

// ═══════════════════════════════════════════════════════════════════
// PREDICATE SIGNATURE VALIDATION TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_predicate_valid_arity_consistent() {
    // Two assertions of the same predicate with the same arity — no warning.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    let inner = kb.inner.borrow();
    let sig = inner.predicate_registry.get("gerku").unwrap();
    assert_eq!(sig.arity, 2, "gerku should be registered with arity 2");
}

#[test]
fn test_predicate_arity_mismatch_detected() {
    // Assert gerku(alis, zo'e) (arity 2), then gerku(bob) (arity 1).
    // The registry should have arity 2 from the first assertion.
    // The second assertion warns but still inserts (permissive mode).
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku")); // arity 2
    // Now assert gerku with arity 1 (single arg).
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Constant("bob".to_string())],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    // Both facts should be in the store (permissive mode).
    let inner = kb.inner.borrow();
    assert!(
        inner.fact_store.len() >= 2,
        "both facts should be stored despite arity mismatch"
    );
    let sig = inner.predicate_registry.get("gerku").unwrap();
    assert_eq!(sig.arity, 2, "registry keeps the first-seen arity");
}

#[test]
fn test_predicate_unknown_registered_as_inferred() {
    // Assert a predicate not in the dictionary.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "xyzzy",
        vec![LogicalTerm::Constant("alis".to_string())],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    let inner = kb.inner.borrow();
    let sig = inner.predicate_registry.get("xyzzy").unwrap();
    assert_eq!(sig.arity, 1);
    assert!(matches!(sig.source, SignatureSource::Inferred));
}

#[test]
fn test_predicate_dictionary_source() {
    // Assert a known gismu — should be registered with Dictionary source.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let inner = kb.inner.borrow();
    let sig = inner.predicate_registry.get("gerku").unwrap();
    assert!(matches!(sig.source, SignatureSource::Dictionary));
}

#[test]
fn test_predicate_registry_cleared_on_reset() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    {
        let inner = kb.inner.borrow();
        assert!(!inner.predicate_registry.is_empty());
    }
    kb.reset().unwrap();
    {
        let inner = kb.inner.borrow();
        assert!(
            inner.predicate_registry.is_empty(),
            "registry should be empty after reset"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════
// INTEGRITY CONSTRAINT TESTS
// ═══════════════════════════════════════════════════════════════════

/// Helper: build a ground StoredFact for constraint registration.
fn constraint_fact(rel: &str, entity: &str) -> StoredFact {
    StoredFact::Bare(GroundFact::new(
        rel,
        vec![
            GroundTerm::Constant(entity.to_string()),
            GroundTerm::Unspecified,
        ],
    ))
}

#[test]
fn test_constraint_no_violation() {
    let kb = new_kb();
    // deny gerku(adam) ∧ mlatu(adam)
    kb.register_constraint(
        "no-gerku-and-mlatu".into(),
        vec![
            constraint_fact("gerku", "adam"),
            constraint_fact("mlatu", "adam"),
        ],
    );
    // Assert only gerku(adam) — no violation.
    assert_buf(&kb, make_assertion("adam", "gerku"));
    // Should still be queryable.
    assert!(query(&kb, make_query("adam", "gerku")));
}

#[test]
fn test_constraint_violation_detected() {
    let kb = new_kb();
    // deny gerku(adam) ∧ mlatu(adam)
    kb.register_constraint(
        "no-gerku-and-mlatu".into(),
        vec![
            constraint_fact("gerku", "adam"),
            constraint_fact("mlatu", "adam"),
        ],
    );
    // Assert both — violation warning printed (permissive mode).
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert_buf(&kb, make_assertion("adam", "mlatu"));
    // Both facts are still in the store (permissive mode).
    assert!(query(&kb, make_query("adam", "gerku")));
    assert!(query(&kb, make_query("adam", "mlatu")));
}

#[test]
fn test_constraint_different_entities_no_violation() {
    let kb = new_kb();
    // deny gerku(adam) ∧ mlatu(adam) — specific to adam.
    kb.register_constraint(
        "no-gerku-and-mlatu-adam".into(),
        vec![
            constraint_fact("gerku", "adam"),
            constraint_fact("mlatu", "adam"),
        ],
    );
    // Assert gerku(adam) and mlatu(bob) — no violation (different entities).
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert_buf(&kb, make_assertion("bob", "mlatu"));
    // No violation — the constraint is about adam specifically.
}

#[test]
fn test_constraint_survives_reset() {
    let kb = new_kb();
    kb.register_constraint(
        "test-constraint".into(),
        vec![constraint_fact("gerku", "adam")],
    );
    {
        let inner = kb.inner.borrow();
        assert_eq!(inner.integrity_constraints.len(), 1);
    }
    // Constraints survive reset (they're structural declarations).
    kb.reset().unwrap();
    {
        let inner = kb.inner.borrow();
        assert_eq!(
            inner.integrity_constraints.len(),
            1,
            "constraints should survive reset"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════
// NAF DEPENDENCY TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_naf_dependency_detected() {
    // Query ¬P where P is not asserted → NAF flips False to True.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku")); // Need at least one entity in domain.
    let mut nodes = Vec::new();
    let p = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let not_p = {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::NotNode(p));
        id
    };
    let buf = LogicBuffer {
        nodes,
        roots: vec![not_p],
    };
    let (result, trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    assert!(result.is_true(), "¬mlatu(alis) should hold via NAF");
    assert!(
        trace.has_naf_dependency(),
        "proof trace should flag NAF dependency"
    );
}

#[test]
fn test_no_naf_for_positive_fact() {
    // Query a directly asserted fact — no NAF involved.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let (result, trace) = kb
        .query_entailment_with_proof_inner(make_query("alis", "gerku"))
        .unwrap();
    assert!(result.is_true());
    assert!(
        !trace.has_naf_dependency(),
        "direct fact should not be NAF-dependent"
    );
}

#[test]
fn test_naf_false_when_inner_proved() {
    // Query ¬P where P IS asserted → negation holds=false (not NAF).
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let mut nodes = Vec::new();
    let p = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let not_p = {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::NotNode(p));
        id
    };
    let buf = LogicBuffer {
        nodes,
        roots: vec![not_p],
    };
    let (result, trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    assert!(result.is_false(), "¬gerku(alis) should be false");
    assert!(
        !trace.has_naf_dependency(),
        "failed negation (inner proved) is not NAF"
    );
}

// ═══════════════════════════════════════════════════════════════════
// FAILURE TRACE TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_failure_trace_predicate_not_found() {
    // Query a predicate that was never asserted and no rules derive it.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku")); // Need domain member.
    let (result, trace) = kb
        .query_entailment_with_proof_inner(make_query("alis", "mlatu"))
        .unwrap();
    assert!(result.is_false());
    // The trace should contain a PredicateNotFound step.
    let has_not_found = trace
        .steps
        .iter()
        .any(|s| matches!(s.rule, ProofRule::PredicateNotFound(_)));
    assert!(
        has_not_found,
        "failure trace should contain PredicateNotFound for mlatu(alis)"
    );
}

#[test]
fn test_failure_trace_rule_attempt_failed() {
    // Assert rule gerku→danlu, query danlu(alis) where gerku(alis) is NOT asserted.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "mlatu")); // alis exists but not as gerku.
    let (result, trace) = kb
        .query_entailment_with_proof_inner(make_query("alis", "danlu"))
        .unwrap();
    assert!(result.is_false());
    // The trace should contain a RuleAttemptFailed showing the gerku condition failed.
    let has_rule_failed = trace
        .steps
        .iter()
        .any(|s| matches!(s.rule, ProofRule::RuleAttemptFailed(_)));
    assert!(
        has_rule_failed,
        "failure trace should show the gerku→danlu rule was tried and gerku condition failed"
    );
}

#[test]
fn test_failure_trace_conjunction_partial() {
    // Query P∧Q where P holds but Q doesn't.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let mut nodes = Vec::new();
    let p = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let q = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let conj = and(&mut nodes, p, q);
    let buf = LogicBuffer {
        nodes,
        roots: vec![conj],
    };
    let (result, trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    assert!(
        result.is_false(),
        "gerku(alis) ∧ mlatu(alis) should be false"
    );
    // The trace should show gerku succeeded but mlatu failed.
    let has_not_found = trace
        .steps
        .iter()
        .any(|s| matches!(s.rule, ProofRule::PredicateNotFound(_)));
    assert!(
        has_not_found,
        "conjunction failure should show mlatu not found"
    );
}

// ═══════════════════════════════════════════════════════════════════
// HYPOTHETICAL / COUNTERFACTUAL REASONING TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_hypothetical_doesnt_persist() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // In hypothetical: assume mlatu(alis), verify it holds.
    let result = kb
        .with_assumptions(&[make_assertion("alis", "mlatu")], |hyp| {
            query(hyp, make_query("alis", "mlatu"))
        })
        .unwrap();
    assert!(result, "mlatu(alis) should hold inside hypothetical");

    // Back in real KB: mlatu(alis) should NOT hold.
    assert!(
        !query(&kb, make_query("alis", "mlatu")),
        "mlatu(alis) should NOT persist after hypothetical"
    );
    // Original fact should still hold.
    assert!(query(&kb, make_query("alis", "gerku")));
}

#[test]
fn test_hypothetical_query_conjunction() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // In hypothetical: assume mlatu(alis), query gerku(alis) ∧ mlatu(alis).
    let result = kb
        .with_assumptions(&[make_assertion("alis", "mlatu")], |hyp| {
            // Build conjunction query.
            let mut nodes = Vec::new();
            let p = pred(
                &mut nodes,
                "gerku",
                vec![
                    LogicalTerm::Constant("alis".to_string()),
                    LogicalTerm::Unspecified,
                ],
            );
            let q = pred(
                &mut nodes,
                "mlatu",
                vec![
                    LogicalTerm::Constant("alis".to_string()),
                    LogicalTerm::Unspecified,
                ],
            );
            let conj = and(&mut nodes, p, q);
            let buf = LogicBuffer {
                nodes,
                roots: vec![conj],
            };
            query(hyp, buf)
        })
        .unwrap();
    assert!(result, "gerku ∧ mlatu should hold inside hypothetical");
}

#[test]
fn test_hypothetical_with_rule() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));

    // In hypothetical: assume gerku(alis), query danlu(alis) via backward chaining.
    let result = kb
        .with_assumptions(&[make_assertion("alis", "gerku")], |hyp| {
            query(hyp, make_query("alis", "danlu"))
        })
        .unwrap();
    assert!(
        result,
        "danlu(alis) should hold via gerku→danlu + assumed gerku(alis)"
    );

    // Back in real KB: danlu(alis) should NOT hold (no gerku(alis) asserted).
    assert!(
        !query(&kb, make_query("alis", "danlu")),
        "danlu(alis) should NOT persist after hypothetical"
    );
}

// ══════════════════════════════════════════════���════════════════════
// AGGREGATION TESTS
// ═════════���════════════════════════════���════════════════════════════

/// Helper: build ∃x. P(x, zo'e) — existential find query (unbound x).
fn make_find_query(predicate: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        predicate,
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_count_witnesses_zero() {
    let kb = new_kb();
    let count = kb.count_witnesses(make_find_query("gerku")).unwrap();
    assert_eq!(count, 0, "no gerku asserted → 0 witnesses");
}

#[test]
fn test_count_witnesses_multiple() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    assert_buf(&kb, make_assertion("carol", "gerku"));
    let count = kb.count_witnesses(make_find_query("gerku")).unwrap();
    assert!(count >= 3, "at least 3 gerku witnesses, got {}", count);
}

#[test]
fn test_aggregate_sum() {
    // Assert numeric facts: tenfa(2, zo'e), tenfa(3, zo'e), tenfa(5, zo'e)
    // Sum over x in ∃x. tenfa(x, zo'e) → 2+3+5 = 10
    let kb = new_kb();
    for val in [2.0, 3.0, 5.0] {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "tenfa",
            vec![LogicalTerm::Number(val), LogicalTerm::Unspecified],
        );
        assert_buf(
            &kb,
            LogicBuffer {
                nodes,
                roots: vec![root],
            },
        );
    }
    // Build ∃x. tenfa(x, zo'e)
    let mut nodes = Vec::new();
    let body = pred(
        &mut nodes,
        "tenfa",
        vec![
            LogicalTerm::Variable("x".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = exists(&mut nodes, "x", body);
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };
    use nibli_types::logic::AggregateOp;
    let sum = kb.aggregate(buf, "x", AggregateOp::Sum).unwrap();
    assert_eq!(sum, Some(10.0), "sum of 2+3+5 should be 10");
}

#[test]
fn test_count_with_backward_chain() {
    // Rule: gerku → danlu. Assert gerku for 2 entities.
    // Count ∃x. danlu(x) should find at least 2 (+ xorlo Skolems).
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    let count = kb.count_witnesses(make_find_query("danlu")).unwrap();
    assert!(
        count >= 2,
        "at least 2 danlu witnesses via backward chain, got {}",
        count
    );
}

// ═══════════════════════════════════════════════════════════════════
// ITERATIVE DEEPENING TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_iterative_deepening_finds_shallow() {
    // Chain: gerku→danlu→jmive (depth 2). Should find proof.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(
        query(&kb, make_query("alis", "jmive")),
        "jmive(alis) should hold via 2-step chain"
    );
}

#[test]
fn test_iterative_deepening_returns_false_not_exceeded() {
    // Query something genuinely underivable → should be False, not ResourceExceeded.
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let result = query_result(&kb, make_query("alis", "mlatu"));
    assert!(
        result.is_false(),
        "underivable predicate should return False, got {:?}",
        result
    );
}

#[test]
fn test_iterative_deepening_exceeds_max() {
    // Set max_chain_depth=2, chain of depth 3 → ResourceExceeded.
    let kb = new_kb();
    kb.inner.borrow_mut().max_chain_depth = 2;
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    assert_buf(&kb, make_universal("jmive", "xanlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let result = query_result(&kb, make_query("alis", "xanlu"));
    assert!(
        matches!(result, QueryResult::ResourceExceeded(ResourceKind::Depth)),
        "depth-3 chain with max_chain_depth=2 should exceed, got {:?}",
        result
    );
}

// ═══════════════════════════════════════════════════════════════════
// ARGUMENT-POSITION INDEX TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_arg_index_populated() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("bob", "gerku"));
    let inner = kb.inner.borrow();
    // Index should have entries for (gerku, 0) and (gerku, 1).
    let key0 = ("gerku".to_string(), 0usize);
    assert!(
        inner.arg_position_index.contains_key(&key0),
        "index should have (gerku, 0)"
    );
    let values_at_0 = &inner.arg_position_index[&key0];
    // Position 0 should have entries for "alis" and "bob".
    assert!(
        values_at_0.contains_key(&GroundTerm::Constant("alis".to_string())),
        "index should map alis at position 0"
    );
    assert!(
        values_at_0.contains_key(&GroundTerm::Constant("bob".to_string())),
        "index should map bob at position 0"
    );
}

#[test]
fn arg_index_dedups_reingested_fact() {
    // Re-ingesting an Eq-identical ground fact (e.g. compute auto-assert firing
    // on every query) must NOT append a duplicate to the arg_position_index leaf.
    // Duplicates would grow the index unboundedly AND inflate
    // bind_join_vars_from_index's `matching.len() == 1` uniqueness check,
    // suppressing a valid join binding. The store (a HashSet) already dedups; the
    // index now stays consistent with it. RED pre-fix (leaf len would be 2).
    let kb = new_kb();
    assert_buf(&kb, make_assertion("rex", "gerku"));
    assert_buf(&kb, make_assertion("rex", "gerku")); // identical fact, re-ingested
    let inner = kb.inner.borrow();
    let leaf = &inner.arg_position_index[&("gerku".to_string(), 0)]
        [&GroundTerm::Constant("rex".to_string())];
    assert_eq!(
        leaf.len(),
        1,
        "re-ingesting an identical fact must not duplicate its arg-index entry"
    );
}

#[test]
fn test_arg_index_cleared_on_reset() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    {
        let inner = kb.inner.borrow();
        assert!(!inner.arg_position_index.is_empty());
    }
    kb.reset().unwrap();
    {
        let inner = kb.inner.borrow();
        assert!(
            inner.arg_position_index.is_empty(),
            "arg index should be empty after reset"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════
// INCREMENTAL TRUTH MAINTENANCE TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_incremental_retract_fact() {
    let kb = new_kb();
    let id1 = assert_id(&kb, make_assertion("alis", "gerku"), "alis gerku");
    let _id2 = assert_id(&kb, make_assertion("bob", "gerku"), "bob gerku");
    let _id3 = assert_id(&kb, make_assertion("carol", "mlatu"), "carol mlatu");

    assert!(query(&kb, make_query("alis", "gerku")));
    assert!(query(&kb, make_query("bob", "gerku")));
    assert!(query(&kb, make_query("carol", "mlatu")));

    // Retract alis's fact.
    kb.retract_fact_inner(id1).unwrap();

    assert!(
        !query(&kb, make_query("alis", "gerku")),
        "alis gerku should be gone after retraction"
    );
    assert!(
        query(&kb, make_query("bob", "gerku")),
        "bob gerku should survive"
    );
    assert!(
        query(&kb, make_query("carol", "mlatu")),
        "carol mlatu should survive"
    );
}

#[test]
fn test_incremental_retract_rule() {
    let kb = new_kb();
    let rule_id = assert_id(&kb, make_universal("gerku", "danlu"), "rule");
    assert_buf(&kb, make_assertion("alis", "gerku"));

    assert!(
        query(&kb, make_query("alis", "danlu")),
        "danlu(alis) should hold via rule"
    );

    // Retract the rule.
    kb.retract_fact_inner(rule_id).unwrap();

    assert!(
        !query(&kb, make_query("alis", "danlu")),
        "danlu(alis) should be gone after retracting the rule"
    );
    assert!(
        query(&kb, make_query("alis", "gerku")),
        "base fact gerku(alis) should survive"
    );
}

#[test]
fn test_incremental_retract_du() {
    let kb = new_kb();
    let du_id = assert_id(&kb, make_du("alis", "bob"), "du");
    assert_buf(&kb, make_assertion("alis", "gerku"));

    assert!(
        query(&kb, make_query("bob", "gerku")),
        "gerku(bob) should hold via du(alis, bob)"
    );

    // Retract the du fact.
    kb.retract_fact_inner(du_id).unwrap();

    assert!(
        !query(&kb, make_query("bob", "gerku")),
        "gerku(bob) should be gone after retracting du"
    );
    assert!(
        query(&kb, make_query("alis", "gerku")),
        "gerku(alis) should survive"
    );
}

// ═══════════════════════════════════════════════════════════════════
// CONTRADICTIONS SCAN TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_contradictions_none() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    let violations = kb.check_contradictions();
    assert!(violations.is_empty(), "no contradictions expected");
}

#[test]
fn test_contradictions_integrity_violation() {
    let kb = new_kb();
    kb.register_constraint(
        "no-gerku-and-mlatu".into(),
        vec![
            constraint_fact("gerku", "adam"),
            constraint_fact("mlatu", "adam"),
        ],
    );
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert_buf(&kb, make_assertion("adam", "mlatu"));
    let violations = kb.check_contradictions();
    assert!(!violations.is_empty(), "should detect integrity violation");
    assert!(
        violations[0].contains("Integrity violation"),
        "violation message should mention integrity: {}",
        violations[0]
    );
}

#[test]
fn test_contradictions_arity_inconsistency() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku")); // arity 2
    // Assert gerku with arity 1 (single arg).
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "gerku",
        vec![LogicalTerm::Constant("bob".to_string())],
    );
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    let violations = kb.check_contradictions();
    assert!(
        violations.iter().any(|v| v.contains("Arity inconsistency")),
        "should detect arity mismatch: {:?}",
        violations
    );
}

// ═══════════════════════════════════════════════════════════════════
// SELECTIVE FORWARD CHAINING TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_forward_chain_basic() {
    // Rule: gerku→danlu (forward). Assert gerku(alis) → danlu(alis) auto-derived.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    kb.set_rule_forward("danlu", true);
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // danlu(alis) should be directly in the fact store (forward-derived),
    // not just backward-chainable.
    let inner = kb.inner.borrow();
    let danlu_facts = inner.fact_store.lookup_predicate("danlu");
    assert!(
        danlu_facts.is_some() && !danlu_facts.unwrap().is_empty(),
        "danlu(alis) should be forward-derived into the fact store"
    );
}

#[test]
fn test_forward_chain_no_flag() {
    // Same rule without forward flag → danlu(alis) NOT in fact store.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    // Do NOT call set_rule_forward.
    assert_buf(&kb, make_assertion("alis", "gerku"));

    let inner = kb.inner.borrow();
    let danlu_facts = inner.fact_store.lookup_predicate("danlu");
    // danlu should not be forward-derived (only available via backward chain).
    let has_danlu_alis = danlu_facts
        .map(|set| {
            set.iter().any(|f| {
                f.inner().relation == "danlu"
                    && f.inner().args.first() == Some(&GroundTerm::Constant("alis".to_string()))
            })
        })
        .unwrap_or(false);
    assert!(
        !has_danlu_alis,
        "danlu(alis) should NOT be forward-derived without forward flag"
    );
}

#[test]
fn test_forward_chain_transitive() {
    // Chain: gerku→danlu (forward), danlu→jmive (forward).
    // Assert gerku(alis) → danlu(alis) auto-derived → jmive(alis) auto-derived.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    kb.set_rule_forward("danlu", true);
    kb.set_rule_forward("jmive", true);
    assert_buf(&kb, make_assertion("alis", "gerku"));

    let inner = kb.inner.borrow();
    let jmive_facts = inner.fact_store.lookup_predicate("jmive");
    assert!(
        jmive_facts.is_some() && !jmive_facts.unwrap().is_empty(),
        "jmive(alis) should be transitively forward-derived"
    );
}

#[test]
fn test_forward_chain_skipped_during_rebuild() {
    // Forward chain should not fire during retraction rebuild.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    kb.set_rule_forward("danlu", true);
    let id = assert_id(&kb, make_assertion("alis", "gerku"), "gerku");

    // danlu(alis) should be forward-derived.
    assert!(query(&kb, make_query("alis", "danlu")));

    // Retract gerku(alis) — triggers rebuild. Forward chains should not re-fire.
    kb.retract_fact_inner(id).unwrap();

    // After retraction, danlu(alis) should NOT hold.
    assert!(
        !query(&kb, make_query("alis", "danlu")),
        "danlu(alis) should be gone after retracting gerku(alis)"
    );
}

// ═══════════════════════════════════════════════════════════════════
// TABLING / PERSISTENT MEMOIZATION TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_tabling_cache_survives_queries() {
    // Query P(a) twice — second should use cached result (same answer).
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));

    // First query — populates cache.
    assert!(query(&kb, make_query("alis", "danlu")));
    // Second query — uses cache (same result).
    assert!(query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_tabling_invalidated_on_assert() {
    // Query P(a) → False, assert P(a), query again → True.
    let kb = new_kb();
    assert!(!query(&kb, make_query("alis", "gerku")));
    // Cache now has gerku(alis) → False.
    assert_buf(&kb, make_assertion("alis", "gerku"));
    // After assertion, cache should be invalidated.
    assert!(
        query(&kb, make_query("alis", "gerku")),
        "gerku(alis) should be True after assertion (cache invalidated)"
    );
}

#[test]
fn test_tabling_invalidated_on_retract() {
    // Assert P(a), query → True, retract, query → False.
    let kb = new_kb();
    let id = assert_id(&kb, make_assertion("alis", "gerku"), "gerku");
    assert!(query(&kb, make_query("alis", "gerku")));
    // Cache now has gerku(alis) → True.
    kb.retract_fact_inner(id).unwrap();
    // After retraction, cache should be invalidated.
    assert!(
        !query(&kb, make_query("alis", "gerku")),
        "gerku(alis) should be False after retraction (cache invalidated)"
    );
}

// ═══════════════════════════════════════════════════════════════════
// DEFEASIBLE / PRIORITIZED RULES TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_priority_higher_rule_wins() {
    // Two rules for danlu: gerku→danlu (priority 0) and mlatu→danlu (priority 10).
    // Assert both gerku(alis) and mlatu(alis). Both rules match.
    // The higher-priority rule (mlatu→danlu) should be tried first.
    // Since both succeed, the result is the same — but we verify the mechanism works.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("mlatu", "danlu"));
    kb.set_rule_priority("danlu", 10); // Both danlu rules get priority 10.
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_assertion("alis", "mlatu"));
    assert!(query(&kb, make_query("alis", "danlu")));
}

#[test]
fn test_priority_default_zero() {
    // Rules without explicit priority should default to 0.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    let inner = kb.inner.borrow();
    if let Some(rules) = inner.universal_rules.get("danlu") {
        for rule in rules {
            assert_eq!(rule.priority, 0, "default priority should be 0");
        }
    }
}

#[test]
fn test_priority_set_and_query() {
    // Set priority for a specific predicate's rules.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    kb.set_rule_priority("danlu", 5);
    let inner = kb.inner.borrow();
    if let Some(rules) = inner.universal_rules.get("danlu") {
        for rule in rules {
            assert_eq!(rule.priority, 5, "priority should be 5 after set");
        }
    }
}

#[test]
fn matching_rules_bucket_stays_descending_after_late_registration() {
    // INVARIANT: universal_rules buckets are kept sorted by descending priority
    // at mutation time, so the backward-chain read path (matching_rules_typed)
    // can borrow a pre-sorted slice without cloning or re-sorting. A
    // low-priority rule registered AFTER a high-priority rule for the same
    // conclusion must land AFTER it. (The suite-wide debug_assert in
    // matching_rules_typed is the broader net; this pins one explicit case.)
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    kb.set_rule_priority("danlu", 10); // the gerku→danlu rule now has priority 10
    assert_buf(&kb, make_universal("mlatu", "danlu")); // new rule, default priority 0
    let inner = kb.inner.borrow();
    let bucket = inner
        .universal_rules
        .get("danlu")
        .expect("danlu bucket exists");
    assert_eq!(
        bucket.len(),
        2,
        "both rules concluding danlu are in the bucket"
    );
    assert!(
        bucket.is_sorted_by_key(|r| std::cmp::Reverse(r.priority)),
        "bucket must stay descending-sorted: {:?}",
        bucket.iter().map(|r| r.priority).collect::<Vec<_>>()
    );
    assert_eq!(bucket[0].priority, 10, "high-priority rule comes first");
    assert_eq!(bucket[1].priority, 0, "late low-priority rule comes last");
}

// ═══════════════════════════════════════════════════════════════════
// SORTED LOGIC / TYPE HIERARCHY TESTS
// ═══════════════════════════════════════════════════════════════════

#[test]
fn test_sort_valid_entity() {
    // person ⊂ animal, adam: person, gerku expects (animal, _).
    // adam is compatible with animal via subsort → no warning.
    let kb = new_kb();
    kb.declare_subsort("person", "animal");
    kb.declare_entity_sort("adam", "person");
    kb.set_predicate_sorts("gerku", vec!["animal".into(), String::new()]);
    assert_buf(&kb, make_assertion("adam", "gerku"));
    // Should succeed without sort warning (person ⊂ animal).
    assert!(query(&kb, make_query("adam", "gerku")));
}

#[test]
fn test_sort_invalid_entity() {
    // adam: number_sort, gerku expects (animal, _).
    // number_sort is NOT a subsort of animal → sort warning printed.
    let kb = new_kb();
    kb.declare_entity_sort("adam", "number_sort");
    kb.set_predicate_sorts("gerku", vec!["animal".into(), String::new()]);
    // This should print a sort warning but still insert (permissive mode).
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert!(query(&kb, make_query("adam", "gerku")));
}

#[test]
fn test_sort_hierarchy_transitive() {
    // person ⊂ animal ⊂ entity.
    // adam: person. Predicate expects entity.
    // person is transitively compatible with entity.
    let kb = new_kb();
    kb.declare_subsort("person", "animal");
    kb.declare_subsort("animal", "entity");
    kb.declare_entity_sort("adam", "person");
    kb.set_predicate_sorts("gerku", vec!["entity".into(), String::new()]);
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert!(query(&kb, make_query("adam", "gerku")));
}

#[test]
fn test_sort_unset_no_check() {
    // No sorts declared → no checking (fully backward compatible).
    let kb = new_kb();
    assert_buf(&kb, make_assertion("adam", "gerku"));
    assert!(query(&kb, make_query("adam", "gerku")));
    // No sort warning — sorts not declared.
}

/// Cross-depth tabling: a 3-step transitive chain must resolve True across
/// iterative-deepening passes. Passes 1 and 2 return ResourceExceeded(Depth);
/// because the cache write is gated to definitive (True/False) results only,
/// those Depth verdicts are never cached, so pass 3 re-derives the chain and
/// returns True. Before the gating fix, persisting a stale Depth across passes
/// would poison pass 3 and the query would wrongly return ResourceExceeded.
#[test]
fn test_tabling_cross_depth_persistence() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    assert_buf(&kb, make_universal("jmive", "xanlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(
        query(&kb, make_query("alis", "xanlu")),
        "xanlu(alis) should hold via a 3-step chain across depth iterations"
    );
    // A fresh query (entry clear) must remain True.
    assert!(
        query(&kb, make_query("alis", "xanlu")),
        "re-query of xanlu(alis) should remain True"
    );
}

/// A cycle-cut must not poison a sibling goal within a single query. Proving the
/// left conjunct a(alis) first explores the cyclic rule `f→a → a→f → a` (a on the
/// visited stack) which yields Unknown(CycleCut) for f(alis); a is then proved via
/// seed→a. The right conjunct f(alis) must NOT read a cached CycleCut — it is
/// derivable via a→f. The cyclic rule f→a is registered before the resolver seed→a
/// so the cyclic branch is tried first. Before the gating fix the cached CycleCut
/// poisoned the second conjunct and And(a, f) came back not-True.
#[test]
fn test_cycle_cut_does_not_poison_sibling_conjunct() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "seed"));
    assert_buf(&kb, make_universal("f", "a")); // cyclic rule registered FIRST
    assert_buf(&kb, make_universal("a", "f"));
    assert_buf(&kb, make_universal("seed", "a")); // resolver registered AFTER

    let mut nodes = Vec::new();
    let left = pred(
        &mut nodes,
        "a",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let right = pred(
        &mut nodes,
        "f",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = and(&mut nodes, left, right);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes,
                roots: vec![root],
            }
        ),
        "And(a(alis), f(alis)) should hold; sibling f must not read a poisoned CycleCut"
    );
}

/// A fact true only via a du-equivalent, RULE-DERIVED variant must get an honest
/// EqualitySubstitution proof step — not a holds:true "unknown" leaf with no
/// derivation. The ground material conditional `seed(adam) -> danlu(adam)` has a
/// GROUND conclusion, so `danlu(betty)` does not unify with it and routes through the
/// du-equivalence fallback that the traced path previously lacked.
#[test]
fn test_proof_trace_du_substitution_rule_derived() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("adam", "seed"));

    // Ground material conditional: Or(Not(seed(adam)), danlu(adam)) — a ground
    // conclusion danlu(adam), auto-registered as a zero-variable rule.
    let mut nodes = Vec::new();
    let seed_adam = pred(
        &mut nodes,
        "seed",
        vec![
            LogicalTerm::Constant("adam".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let danlu_adam = pred(
        &mut nodes,
        "danlu",
        vec![
            LogicalTerm::Constant("adam".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_seed = not(&mut nodes, seed_adam);
    let cond = or(&mut nodes, neg_seed, danlu_adam);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![cond],
        },
    );
    assert_buf(&kb, make_du("adam", "betty"));

    // Sanity: danlu(betty) holds (untraced) via the du-equivalence fallback over the
    // rule-derived danlu(adam).
    assert!(
        query(&kb, make_query("betty", "danlu")),
        "danlu(betty) should hold via rule-derived danlu(adam) + adam du betty"
    );

    let (result, trace) = query_with_proof(&kb, make_query("betty", "danlu"));
    assert!(result, "traced verdict for danlu(betty) should be True");
    assert!(
        trace
            .steps
            .iter()
            .any(|s| matches!(s.rule, ProofRule::EqualitySubstitution(_)) && s.holds),
        "trace should contain a holds:true EqualitySubstitution step"
    );
    assert!(
        !trace.steps.iter().any(|s| {
            matches!(&s.rule, ProofRule::PredicateCheck((src, _)) if src == "unknown") && s.holds
        }),
        "trace must not contain a holds:true PredicateCheck(\"unknown\", ...) leaf"
    );
    assert!(
        trace.steps[trace.root as usize].holds,
        "root step holds must match the True verdict"
    );
}

// ═══════════════════════════════════════════════════════════════════
// DETERMINISM PINS (todo.md: witness/proof output ordering was
// HashSet-derived and varied with the process hasher seed)
// ═══════════════════════════════════════════════════════════════════

#[test]
fn find_witness_ordering_is_deterministic_across_kb_instances() {
    // Same facts, two DIFFERENT assertion orders, two fresh KB instances
    // (each std HashSet gets its own RandomState even in-process). The FULL
    // ordered binding list must be identical: query_find_inner sorts binding
    // sets canonically at its return boundary, so the order is hasher-seed
    // independent by construction. NOTE: an in-process pin is weaker than a
    // two-process check (which exercises different global seeds); the sort
    // makes order seed-independent by construction, and the gasnu script-mode
    // byte-identity check covers the two-process case empirically.
    let names = ["zeta", "alis", "mike", "bob", "carol", "dave", "erin"];
    let kb1 = new_kb();
    for n in names {
        assert_buf(&kb1, make_assertion(n, "gerku"));
    }
    let kb2 = new_kb();
    for n in names.iter().rev() {
        assert_buf(&kb2, make_assertion(n, "gerku"));
    }

    let r1a = query_find(&kb1, make_find_query("gerku"));
    let r1b = query_find(&kb1, make_find_query("gerku"));
    let r2 = query_find(&kb2, make_find_query("gerku"));

    assert_eq!(r1a.len(), names.len(), "one binding set per asserted gerku");
    assert_eq!(r1a, r1b, "same KB, repeated query: order must be stable");
    assert_eq!(
        r1a, r2,
        "different assertion order: canonical witness order must agree"
    );
}

#[test]
fn domain_member_cache_order_is_deterministic() {
    // Domain-iteration-order probe: the typed domain member cache must be
    // sorted regardless of HashSet insertion order. This cache drives ForAll
    // member iteration and the ForallVerified entity order in proof output.
    let names = ["zeta", "alis", "mike", "bob"];
    let kb1 = new_kb();
    for n in names {
        assert_buf(&kb1, make_assertion(n, "gerku"));
    }
    let kb2 = new_kb();
    for n in names.iter().rev() {
        assert_buf(&kb2, make_assertion(n, "gerku"));
    }

    let m1: Vec<GroundTerm> = {
        let mut inner = kb1.inner.borrow_mut();
        inner.ensure_domain_members_cached();
        inner.all_typed_domain_members().to_vec()
    };
    let m2: Vec<GroundTerm> = {
        let mut inner = kb2.inner.borrow_mut();
        inner.ensure_domain_members_cached();
        inner.all_typed_domain_members().to_vec()
    };
    assert_eq!(
        m1, m2,
        "domain member order must be insertion/hasher independent"
    );
    let mut sorted = m1.clone();
    sorted.sort();
    assert_eq!(m1, sorted, "domain member cache must be sorted");
}
