use super::*;
use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm, ProofRule, ProofTrace};

// ─────────────────────────────────────────────────────────────────────────────
// FLAT vs SURFACE TEST SHAPES — read before adding a reasoning test.
//
// The `make_*` helpers below hand-build FLAT `LogicBuffer`s (a bare `gerku(adam)`), which is
// NOT the shape the shipped pipeline produces: nibli-semantics event-decomposes to
// `∃ev. gerku(ev) ∧ gerku_x1(ev, adam) ∧ …` (`nibli_semantics::event_decompose`) and
// `transform_compute_nodes` turns compute predicates into `ComputeNode`s. A flat and a surface
// buffer give the SAME verdict for shape-INDEPENDENT behaviors (plain lookup, modus ponens,
// chains, NAF, `du`) — pinned test-by-behavior in `mod flat_vs_surface` below — but can DIVERGE
// on shape-DEPENDENT behaviors: the `cwa_false` / `naf_dependent` proof flags, the
// `ComputeCheck(numeric)` step, and witness/Skolem dependency.
//
// Rules for adding a test:
//   * Verdict / rule-firing behavior → the flat `make_*` helpers are fine.
//   * Anything that inspects proof-trace shape or the numeric/compute path → build the buffer
//     the real way with `compile_surface("<lojban>")`, or use the `make_decomposed_*` helpers,
//     or write a `nibli-engine` integration test. NEVER assert `cwa_false` / `ComputeCheck` /
//     witness shape on a bare flat buffer — that tests a shape the engine never builds.
//   * `make_numeric_query` / `make_compute_query` build the flat numeric shape ON PURPOSE — they
//     exercise nibli-reason's flat detection arm (a real production path); the surface shape is covered
//     by `make_decomposed_*` and `compile_surface`. `du` stays flat by design (union-find).
// See CLAUDE.md "Test discipline".
// ─────────────────────────────────────────────────────────────────────────────

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

/// Like `query`, but asserts the DEFINITIVE FALSE verdict — distinct from Unknown
/// / ResourceExceeded. Use for negatives that must be derivably FALSE: a bare
/// `query_false(...)` also passes for Unknown/ResourceExceeded, blunting the
/// safety-critical False-vs-Unknown boundary this engine is built to keep.
fn query_false(kb: &KnowledgeBase, buf: LogicBuffer) -> bool {
    kb.query_entailment_inner(buf).unwrap().is_false()
}

fn query_result(kb: &KnowledgeBase, buf: LogicBuffer) -> QueryResult {
    kb.query_entailment_inner(buf).unwrap()
}

/// Compile KR text to a `LogicBuffer` the SHIPPED way — the exact chain
/// `nibli-engine` runs: `nibli_kr::parse_checked` → `nibli_semantics::compile_from_ast`
/// → `transform_compute_nodes`. Unlike the flat `make_*` helpers, this event-decomposes
/// (`∃ev. rel(ev) ∧ rel_x1(ev, arg) ∧ …`) and converts compute predicates to `ComputeNode`,
/// so a test built on it cannot diverge from the real pipeline. Use it for anything whose
/// behavior depends on IR shape (compute/numeric, `cwa_false`, witness/Skolem). Vocabulary
/// must resolve in the in-tree fallback dictionary (CI has no data file).
fn compile_surface(text: &str) -> LogicBuffer {
    let ast = nibli_kr::parse_checked(text).unwrap_or_else(|e| panic!("parse '{text}': {e}"));
    let mut buf =
        nibli_semantics::compile_from_ast(ast).unwrap_or_else(|e| panic!("compile '{text}': {e}"));
    transform_compute_nodes(&mut buf, &default_compute_predicates());
    buf
}

#[test]
fn compile_surface_smoke() {
    // A ground fact + query through the real front-end must reason correctly, and produce
    // the event-decomposed shape (a `dog_x1` role predicate, not a bare `dog`).
    let kb = new_kb();
    assert_buf(&kb, compile_surface("dog(Adam)."));
    assert!(query(&kb, compile_surface("dog(Adam).")));
    assert!(query_false(&kb, compile_surface("cat(Adam).")));
    let buf = compile_surface("dog(Adam).");
    assert!(
        buf.nodes.iter().any(|n| matches!(n,
            LogicNode::Predicate((rel, _)) if rel == "dog_x1")),
        "surface compile must event-decompose (expected a dog_x1 role predicate): {buf:?}"
    );
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

/// `∀x. (pos(x) ∧ ¬neg(x)) → consequent(x)` — a rule with a negation-as-failure
/// condition. Compiles to a `UniversalRuleRecord` with a non-empty
/// `negated_condition_indices`.
fn make_universal_naf(pos: &str, neg: &str, consequent: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let p = pred(
        &mut nodes,
        pos,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let n = pred(
        &mut nodes,
        neg,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let not_n = not(&mut nodes, n);
    let ante = and(&mut nodes, p, not_n);
    let body = pred(
        &mut nodes,
        consequent,
        vec![
            LogicalTerm::Variable("_v0".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let not_ante = not(&mut nodes, ante);
    let disj = or(&mut nodes, not_ante, body);
    let root = forall(&mut nodes, "_v0", disj);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
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
    assert!(query_false(&kb, make_query("bob", "danlu")));
}

// ─── Topical submodules (split 2026-07-18; each carries its section-local
//     `make_*` helpers — the broadly-shared harness above is reachable via
//     `use super::*;`) ─────────────────────────────────────────────────────

mod assertions;
mod compute_ingest;
mod conditionals_deontic;
mod descriptions_events;
mod disjunctive;
mod existential;
mod find_aggregates;
mod memo_regressions;
mod numeric_compute;
mod provenance;
mod retraction_negation;
mod rules_edges;
mod skolem;
mod strict;
mod tense;
mod traces;
mod unify_equality;
mod witnesses;
mod zoo;

/// Metamorphic differential guard: the flat `make_*` helpers must agree with the SHIPPED
/// pipeline (`compile_surface`) on every reasoning behavior class. A flat unit test builds a
/// hand-rolled `LogicBuffer`; if its shape ever diverges from nibli-semantics's event-decomposed output
/// in an OBSERVABLE way (verdict, or the `cwa_false`/`naf_dependent` trace flags), a test here
/// fails — so the unit layer cannot silently "lie" about a behavior the real engine gets right.
/// Corpus vocabulary is restricted to the in-tree fallback dictionary so this runs in CI (no
/// data file). See the module-level note above `make_assertion` and CLAUDE.md "Test discipline".
mod flat_vs_surface;

// ─── Cross-section helpers hoisted at the 2026-07-18 split (used by
//     more than one topical submodule) ─────────────────────────────

/// Stage 2d invariant: the proof memo only caches `holds:true` derivations (the
/// depth-relative `PredicateNotFound` is no longer memoized), so EVERY `ProofRef`
/// leaf must resolve to a `holds:true` step. A `ProofRef` pointing at a `holds:false`
/// step is the cross-recursion-depth not-found poisoning this stage removed.
fn assert_proof_refs_resolve_to_holds_true(trace: &ProofTrace) {
    for (i, step) in trace.steps.iter().enumerate() {
        if matches!(step.rule, ProofRule::ProofRef { .. }) {
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

/// Helper: build du(a, b) assertion.
fn make_equals(a: &str, b: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        "equals",
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

fn count(nodes: &mut Vec<LogicNode>, var: &str, cnt: u32, body: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::CountNode((var.to_string(), cnt, body)));
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

fn make_numeric_query(relation: &str, a: f64, b: f64) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = make_numeric_pred(&mut nodes, relation, a, b);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Helper: build a ComputeNode with the given relation and args.
fn compute(nodes: &mut Vec<LogicNode>, rel: &str, args: Vec<LogicalTerm>) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::ComputeNode((rel.to_string(), args)));
    id
}

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

/// Build an event-decomposed existential query (same structure as assertion).
fn make_event_query(entity: &str, predicate: &str) -> LogicBuffer {
    make_event_assertion(entity, predicate)
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

/// Build the rule ∀x. (gerku(x) ∧ ¬mlatu(x)) → danlu(x)
/// encoded as ∀x. ¬(gerku(x) ∧ ¬mlatu(x)) ∨ danlu(x).
fn make_negated_antecedent_rule() -> LogicBuffer {
    let mut nodes = Vec::new();
    let dog = pred(
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
    let antecedent = and(&mut nodes, dog, neg_mlatu);
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

/// Helper: build an ObligatoryNode wrapping the given node.
fn obligatory(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::ObligatoryNode(inner));
    id
}

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

fn query_with_proof(kb: &KnowledgeBase, buf: LogicBuffer) -> (bool, ProofTrace) {
    let (result, trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    (result.is_true(), trace)
}

fn query_find(kb: &KnowledgeBase, buf: LogicBuffer) -> Vec<Vec<WitnessBinding>> {
    kb.query_find_inner(buf).unwrap()
}

/// Build a comparison predicate: Pred(rel, [Num(a), Num(b), Zoe, ...])
fn make_numeric_pred(nodes: &mut Vec<LogicNode>, relation: &str, a: f64, b: f64) -> u32 {
    let mut args = vec![
        LogicalTerm::Number(a),
        LogicalTerm::Number(b),
        LogicalTerm::Unspecified,
    ];
    // zmadu and mleca have arity 4; dunli has arity 3
    if relation == "greater" || relation == "less" {
        args.push(LogicalTerm::Unspecified);
    }
    pred(nodes, relation, args)
}
