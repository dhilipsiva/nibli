//! Known-failure backlog — raw-FOL (nibli-reason public contract) defects from the
//! 2026-06-10 deep code-review panel (see `todo.md` → "Deep code-review panel
//! findings" and `code-review-panel-2026-06-10.json`).
//!
//! These bugs are NOT reachable through surface Lojban today — they are guarded
//! by incidental, unenforced invariants of the nibli-semantics→nibli-reason pipeline (e.g. every
//! nibli-semantics-compiled conclusion atom carries a rule-unique SkolemFn base name, so
//! two surface rules never unify against the same conclusion). They ARE reachable
//! through nibli-reason's documented public FOL interface (`KnowledgeBase::assert_fact` /
//! `query_entailment` over a hand-built `LogicBuffer`), exactly as nibli-reason's own
//! inline tests build rules and facts — and as any embedder feeding plain FOL
//! would hit them. So they live in this nibli-reason-level integration file rather than
//! the engine-level `known_failures.rs`.
//!
//! Each test encodes the DESIRED (post-fix) behaviour, so it FAILS today (the bug
//! reproduces) and PASSES once the corresponding `todo.md` item is fixed. Every
//! test is `#[ignore]`d so the normal suite stays green.
//!
//! Run the backlog (expect failures — that's the point):
//!   cargo test -p nibli-reason --test known_failures_fol -- --ignored --test-threads=1

use nibli_reason::KnowledgeBase;
use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

// ─── Tiny raw-FOL builders (mirroring nibli-reason/src/tests.rs helpers) ───────────

/// Single-arg ground fact `P(a)`.
fn fact(predicate: &str, entity: &str) -> LogicBuffer {
    LogicBuffer {
        nodes: vec![LogicNode::Predicate((
            predicate.to_string(),
            vec![LogicalTerm::Constant(entity.to_string())],
        ))],
        roots: vec![0],
    }
}

/// Single-variable material-conditional rule `∀x. P(x) → Q(x)`, i.e.
/// `ForAll(x, Or(Not(P(x)), Q(x)))` — the shape nibli-reason registers as a
/// backward-chaining rule (one antecedent predicate, one conclusion predicate).
fn rule(antecedent: &str, consequent: &str) -> LogicBuffer {
    let var = LogicalTerm::Variable("_x".to_string());
    let mut nodes = vec![
        LogicNode::Predicate((antecedent.to_string(), vec![var.clone()])), // 0
        LogicNode::Predicate((consequent.to_string(), vec![var])),         // 1
        LogicNode::NotNode(0),                                             // 2
        LogicNode::OrNode((2, 1)),                                         // 3
        LogicNode::ForAllNode(("_x".to_string(), 3)),                      // 4
    ];
    let _ = &mut nodes;
    LogicBuffer {
        nodes,
        roots: vec![4],
    }
}

/// Single-arg query `P(a)`.
fn query(predicate: &str, entity: &str) -> LogicBuffer {
    fact(predicate, entity)
}

// ─── best_result wipe in backward chaining (todo.md: HIGH) ──────────────────
// `best_result = rule_pending.and_then(|r| prefer_non_definitive(best_result, r))`
// (reasoning.rs:791/823/937/968): when a *later* unifying rule for the same
// conclusion fails definitively (rule_pending == None), the `and_then` discards
// the *earlier* rule's pending ResourceExceeded(Depth). The predicate then
// resolves to a definitive False, which is cached cross-depth and halts iterative
// deepening before the genuine proof depth is reached — so an entailed query
// returns a wrong definitive False (and `¬ppp` returns a wrong True under NAF).
//
// Reachability note: surface Lojban cannot trigger this today only because every
// nibli-semantics-compiled conclusion atom carries a rule-unique SkolemFn base name, so two
// rules never unify against the same conclusion. Raw FOL (this file) has no such
// guard: here two rules both conclude `ppp(_x)`.

/// Control: a single deep chain (no competing rule). The 5-hop chain
/// `aaa → bbb → ccc → ddd → eee → qqq` then `qqq → ppp` must resolve to True
/// under iterative deepening (default max_chain_depth = 10). This pins that the
/// chain itself is provable, so the failure in the bug test below is attributable
/// to the competing rule, not to depth.
#[test]
fn best_result_control_deep_chain_alone_is_true() {
    let kb = KnowledgeBase::new();
    kb.assert_fact(fact("aaa", "alis"), "aaa(alis)".into())
        .unwrap();
    kb.assert_fact(rule("aaa", "bbb"), "aaa→bbb".into())
        .unwrap();
    kb.assert_fact(rule("bbb", "ccc"), "bbb→ccc".into())
        .unwrap();
    kb.assert_fact(rule("ccc", "ddd"), "ccc→ddd".into())
        .unwrap();
    kb.assert_fact(rule("ddd", "eee"), "ddd→eee".into())
        .unwrap();
    kb.assert_fact(rule("eee", "qqq"), "eee→qqq".into())
        .unwrap();
    kb.assert_fact(rule("qqq", "ppp"), "qqq→ppp".into())
        .unwrap();

    let r = kb.query_entailment(query("ppp", "alis")).unwrap();
    assert!(
        r.is_true(),
        "control: the deep chain alone must entail ppp(alis), got {r:?}"
    );
}

/// Bug: add a SECOND rule `ttt → ppp` whose antecedent `ttt(alis)` is never
/// derivable. That rule fails definitively; if it is consulted AFTER the deep
/// `qqq → ppp` rule has returned a pending ResourceExceeded(Depth) at a shallow
/// deepening pass, the `and_then` wipes the pending → definitive False is cached
/// cross-depth → deepening halts early → entailed `ppp(alis)` returns wrong False.
#[test]
fn best_result_wipe_entailed_query_must_be_true() {
    let kb = KnowledgeBase::new();
    kb.assert_fact(fact("aaa", "alis"), "aaa(alis)".into())
        .unwrap();
    kb.assert_fact(rule("aaa", "bbb"), "aaa→bbb".into())
        .unwrap();
    kb.assert_fact(rule("bbb", "ccc"), "bbb→ccc".into())
        .unwrap();
    kb.assert_fact(rule("ccc", "ddd"), "ccc→ddd".into())
        .unwrap();
    kb.assert_fact(rule("ddd", "eee"), "ddd→eee".into())
        .unwrap();
    kb.assert_fact(rule("eee", "qqq"), "eee→qqq".into())
        .unwrap();
    // Two rules concluding ppp; the deep one is registered first, the
    // definitively-failing one (no `ttt` fact anywhere) second.
    kb.assert_fact(rule("qqq", "ppp"), "qqq→ppp".into())
        .unwrap();
    kb.assert_fact(rule("ttt", "ppp"), "ttt→ppp".into())
        .unwrap();

    let r = kb.query_entailment(query("ppp", "alis")).unwrap();
    assert!(
        r.is_true(),
        "ppp(alis) is entailed via the deep qqq chain, but the competing ttt→ppp \
         rule wiped the pending Depth result → wrong verdict: {r:?}"
    );
}

/// Companion: under negation-as-failure the wrong False above flips to a wrong
/// True for `¬ppp(alis)`. The DESIRED behaviour is that ¬ppp does NOT hold,
/// because ppp is entailed.
#[test]
fn best_result_wipe_negation_must_not_be_true() {
    let kb = KnowledgeBase::new();
    kb.assert_fact(fact("aaa", "alis"), "aaa(alis)".into())
        .unwrap();
    kb.assert_fact(rule("aaa", "bbb"), "aaa→bbb".into())
        .unwrap();
    kb.assert_fact(rule("bbb", "ccc"), "bbb→ccc".into())
        .unwrap();
    kb.assert_fact(rule("ccc", "ddd"), "ccc→ddd".into())
        .unwrap();
    kb.assert_fact(rule("ddd", "eee"), "ddd→eee".into())
        .unwrap();
    kb.assert_fact(rule("eee", "qqq"), "eee→qqq".into())
        .unwrap();
    kb.assert_fact(rule("qqq", "ppp"), "qqq→ppp".into())
        .unwrap();
    kb.assert_fact(rule("ttt", "ppp"), "ttt→ppp".into())
        .unwrap();

    // ¬ppp(alis): Not(Predicate ppp(alis)).
    let neg = LogicBuffer {
        nodes: vec![
            LogicNode::Predicate((
                "ppp".to_string(),
                vec![LogicalTerm::Constant("alis".to_string())],
            )),
            LogicNode::NotNode(0),
        ],
        roots: vec![1],
    };
    let r = kb.query_entailment(neg).unwrap();
    assert!(
        !r.is_true(),
        "ppp(alis) is entailed, so ¬ppp(alis) must NOT hold; the best_result wipe \
         flipped it to a wrong True: {r:?}"
    );
}
