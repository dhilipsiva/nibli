use super::*;

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

/// Conformance bridge to `proofs/Unify.lean` (`unify_sound`): over hand-crafted + random
/// (template, ground-concrete) pairs, a successful `unify_facts` must satisfy the proven
/// soundness property — `substitute_fact(template, σ) == concrete` — plus determinism and
/// minimal bindings (every bound variable occurs in the template). Corpus, not exhaustive
/// (terms are unbounded), matching the SCC/stratification bridges.
#[test]
fn unify_conformance() {
    use super::kb::*;
    use std::collections::{BTreeSet, HashMap};

    // Deterministic LCG (same constants as `nibli-verify::generator` / `pseudo_random_graph`).
    struct Lcg(u64);
    impl Lcg {
        fn new(seed: u64) -> Self {
            Lcg(seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407))
        }
        fn below(&mut self, n: u64) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (self.0 >> 33) % n
        }
    }

    const CONSTS: &[&str] = &["adam", "bel", "kim"];
    const PVARS: &[&str] = &["x", "y", "z"];

    fn gen_leaf(rng: &mut Lcg, allow_pvar: bool) -> GroundTerm {
        let n = if allow_pvar { 5 } else { 4 };
        match rng.below(n) {
            0 => GroundTerm::Constant(CONSTS[rng.below(CONSTS.len() as u64) as usize].into()),
            1 => GroundTerm::Number(rng.below(5)),
            2 => GroundTerm::Description(format!("d{}", rng.below(3))),
            3 => GroundTerm::Unspecified,
            _ => GroundTerm::PatternVar(PVARS[rng.below(PVARS.len() as u64) as usize].into()),
        }
    }

    // A random term; `allow_pvar` distinguishes a template (with pattern vars) from a ground term.
    fn gen_term(rng: &mut Lcg, depth: u32, allow_pvar: bool) -> GroundTerm {
        if depth == 0 || rng.below(2) == 0 {
            gen_leaf(rng, allow_pvar)
        } else if rng.below(2) == 0 {
            GroundTerm::SkolemFn(
                format!("sk{}", rng.below(2)),
                Box::new(gen_term(rng, depth - 1, allow_pvar)),
            )
        } else {
            GroundTerm::DepPair(
                Box::new(gen_term(rng, depth - 1, allow_pvar)),
                Box::new(gen_term(rng, depth - 1, allow_pvar)),
            )
        }
    }

    fn pvars_of(t: &GroundTerm, out: &mut BTreeSet<String>) {
        match t {
            GroundTerm::PatternVar(n) => {
                out.insert(n.clone());
            }
            GroundTerm::SkolemFn(_, d) => pvars_of(d, out),
            GroundTerm::DepPair(a, b) => {
                pvars_of(a, out);
                pvars_of(b, out);
            }
            _ => {}
        }
    }

    // Consistently instantiate a template's pattern vars from `theta`, yielding a ground term.
    fn instantiate(t: &GroundTerm, theta: &HashMap<String, GroundTerm>) -> GroundTerm {
        match t {
            GroundTerm::PatternVar(n) => theta.get(n).cloned().unwrap_or(GroundTerm::Unspecified),
            GroundTerm::SkolemFn(nm, d) => {
                GroundTerm::SkolemFn(nm.clone(), Box::new(instantiate(d, theta)))
            }
            GroundTerm::DepPair(a, b) => GroundTerm::DepPair(
                Box::new(instantiate(a, theta)),
                Box::new(instantiate(b, theta)),
            ),
            other => other.clone(),
        }
    }

    let mut guaranteed = 0usize;
    let mut independent_matched = 0usize;
    for seed in 0u64..500 {
        let mut rng = Lcg::new(seed);
        let n_args = 1 + rng.below(3) as usize; // 1..=3 args
        let t_args: Vec<GroundTerm> = (0..n_args).map(|_| gen_term(&mut rng, 3, true)).collect();
        let template = StoredFact::Bare(GroundFact::new("rel", t_args.clone()));

        // Build a guaranteed-matching ground instance: each pattern var → a fresh ground term.
        let mut pv = BTreeSet::new();
        for a in &t_args {
            pvars_of(a, &mut pv);
        }
        let mut theta: HashMap<String, GroundTerm> = HashMap::new();
        for name in &pv {
            theta.insert(name.clone(), gen_term(&mut rng, 2, false));
        }
        let c_args: Vec<GroundTerm> = t_args.iter().map(|a| instantiate(a, &theta)).collect();
        let concrete = StoredFact::Bare(GroundFact::new("rel", c_args));

        // (1) SOUNDNESS on the guaranteed match (this is `unify_sound`).
        let sigma = unify_facts(&template, &concrete).unwrap_or_else(|| {
            panic!(
                "seed {seed}: an instance of the template must unify: {template:?} vs {concrete:?}"
            )
        });
        assert_eq!(
            substitute_fact(&template, &sigma),
            concrete,
            "seed {seed}: SOUNDNESS FAILED — substitute_fact(template, σ) != concrete"
        );
        guaranteed += 1;

        // (2) DETERMINISM.
        assert_eq!(
            unify_facts(&template, &concrete),
            Some(sigma.clone()),
            "seed {seed}: unify_facts not deterministic"
        );

        // (3) MINIMAL BINDINGS: every bound key is a pattern var of the template.
        for key in sigma.keys() {
            assert!(
                pv.contains(key),
                "seed {seed}: unify bound an extraneous variable '{key}' absent from the template"
            );
        }

        // (4) Independent random ground concrete: if it unifies, soundness must still hold.
        let c2: Vec<GroundTerm> = (0..n_args).map(|_| gen_term(&mut rng, 3, false)).collect();
        let concrete2 = StoredFact::Bare(GroundFact::new("rel", c2));
        if let Some(sigma3) = unify_facts(&template, &concrete2) {
            assert_eq!(
                substitute_fact(&template, &sigma3),
                concrete2,
                "seed {seed}: SOUNDNESS FAILED on an independent random concrete"
            );
            independent_matched += 1;
        }
    }
    assert_eq!(
        guaranteed, 500,
        "the guaranteed-match arm must run on every seed"
    );
    assert!(
        independent_matched > 0,
        "no independent random pair ever unified — the breadth arm is vacuous"
    );
}

/// Negative control for `proofs/Unify.lean`'s `NoVar c` PRECONDITION: the proof
/// speaks only about GROUND concretes; this pins the engine-side envelope.
/// (a) A pattern var in a STRUCTURAL position of the concrete is rejected — a
/// template constant or ground skolem dependency never matches it. (b) A
/// concrete pattern var meets only a template pattern var, where unification
/// binds var→var — OUTSIDE the proven envelope, but the proven equation
/// `substitute_fact(template, σ) == concrete` still holds there. (c) The
/// envelope itself is guaranteed for every STORED concrete by the
/// assert-boundary groundness mechanism
/// (`non_ground_fact_is_dropped_at_the_assert_boundary`).
#[test]
fn unify_non_ground_concrete_envelope() {
    use super::kb::*;

    let concrete_pv = StoredFact::Bare(GroundFact::new(
        "rel",
        vec![GroundTerm::PatternVar("x".to_string())],
    ));

    // (a) Structural positions REJECT a non-ground concrete.
    let template_const = StoredFact::Bare(GroundFact::new(
        "rel",
        vec![GroundTerm::Constant("adam".to_string())],
    ));
    assert!(
        unify_facts(&template_const, &concrete_pv).is_none(),
        "a concrete pattern var never structurally matches a template constant"
    );

    let template_sk = StoredFact::Bare(GroundFact::new(
        "rel",
        vec![GroundTerm::SkolemFn(
            "sk_1".to_string(),
            Box::new(GroundTerm::Constant("adam".to_string())),
        )],
    ));
    let concrete_sk_pv = StoredFact::Bare(GroundFact::new(
        "rel",
        vec![GroundTerm::SkolemFn(
            "sk_1".to_string(),
            Box::new(GroundTerm::PatternVar("x".to_string())),
        )],
    ));
    assert!(
        unify_facts(&template_sk, &concrete_sk_pv).is_none(),
        "a nested concrete pattern var never matches a ground skolem dependency"
    );

    // (b) A template pattern var DOES bind a concrete pattern var — outside the
    // NoVar envelope, but the unify_sound equation still holds.
    let template_pv = StoredFact::Bare(GroundFact::new(
        "rel",
        vec![GroundTerm::PatternVar("t".to_string())],
    ));
    let sigma = unify_facts(&template_pv, &concrete_pv)
        .expect("a template pattern var binds any concrete term, ground or not");
    assert_eq!(
        substitute_fact(&template_pv, &sigma),
        concrete_pv,
        "substitute_fact(template, σ) == concrete holds even outside the NoVar envelope"
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
        kb.assert_fact_inner(buf, "dog() -> animal().".into())
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
            let has_dog = edges.iter().any(|(dep, _)| dep == "gerku");
            assert!(!has_dog, "gerku edge should be gone after retracting rule1");
            let has_mlatu = edges.iter().any(|(dep, _)| dep == "mlatu");
            assert!(has_mlatu, "mlatu edge should remain from rule2");
        }
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

/// Helper: build du query.
fn make_equals_query(a: &str, b: &str) -> LogicBuffer {
    make_equals(a, b)
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
fn test_equals_basic_substitution() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_equals("alis", "bob"));
    assert!(
        query(&kb, make_query("bob", "gerku")),
        "gerku(bob) should hold via du(alis, bob) + gerku(alis)"
    );
}

#[test]
fn test_equals_symmetry() {
    let kb = new_kb();
    assert_buf(&kb, make_equals("alis", "bob"));
    assert!(
        query(&kb, make_equals_query("bob", "alis")),
        "du(bob, alis) should hold via symmetry"
    );
}

#[test]
fn test_equals_transitivity() {
    let kb = new_kb();
    assert_buf(&kb, make_equals("alis", "bob"));
    assert_buf(&kb, make_equals("bob", "carol"));
    assert!(
        query(&kb, make_equals_query("alis", "carol")),
        "du(alis, carol) should hold via transitivity"
    );
}

#[test]
fn test_equals_reflexivity() {
    let kb = new_kb();
    // du(alis, alis) should hold without any assertion.
    assert!(
        query(&kb, make_equals_query("alis", "alis")),
        "du(alis, alis) should hold via reflexivity"
    );
}

#[test]
fn test_equals_with_backward_chain() {
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_equals("alis", "bob"));
    assert!(
        query(&kb, make_query("bob", "danlu")),
        "danlu(bob) should hold via gerku→danlu + gerku(alis) + du(alis, bob)"
    );
}

#[test]
fn test_equals_multiarg() {
    let kb = new_kb();
    assert_buf(&kb, make_assertion_2("alis", "bob", "prami"));
    assert_buf(&kb, make_equals("bob", "carol"));
    assert!(
        query(&kb, make_assertion_2("alis", "carol", "prami")),
        "prami(alis, carol) should hold via du(bob, carol) + prami(alis, bob)"
    );
}

#[test]
fn test_equals_retraction_rebuild() {
    let kb = new_kb();
    let equals_id = assert_id(&kb, make_equals("alis", "bob"), "equals");
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert!(
        query(&kb, make_query("bob", "gerku")),
        "should hold before retraction"
    );

    kb.retract_fact_inner(equals_id).unwrap();
    assert!(
        query_false(&kb, make_query("bob", "gerku")),
        "gerku(bob) should be FALSE after retracting du(alis, bob)"
    );
}

#[test]
fn test_equals_no_tensed() {
    // Past(du(alis, bob)) should NOT activate equivalence.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let equals_node = pred(
        &mut nodes,
        "equals",
        vec![
            LogicalTerm::Constant("alis".to_string()),
            LogicalTerm::Constant("bob".to_string()),
        ],
    );
    let past = {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::PastNode(equals_node));
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
        query_false(&kb, make_query("bob", "gerku")),
        "gerku(bob) should be FALSE — tensed du does not activate equivalence"
    );
}

/// Helper: build a flat negated du assertion/query: Not(du(a, b)).
fn make_negated_equals(a: &str, b: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let inner = pred(
        &mut nodes,
        "equals",
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
fn test_not_equals_transitive_contradiction() {
    // du(alis,bob) ∧ du(bob,carol) makes alis ≡ carol via the union-find even
    // though du(alis,carol) was never stored; asserting `na du(alis, carol)`
    // must be flagged. RED before the union-find-aware section: section 4 only
    // checks store membership, and du(alis,carol) is not in the store.
    let kb = new_kb();
    assert_buf(&kb, make_equals("alis", "bob"));
    assert_buf(&kb, make_equals("bob", "carol"));
    assert_id(&kb, make_negated_equals("alis", "carol"), "na du");
    let violations = kb.check_contradictions();
    assert!(
        violations
            .iter()
            .any(|v| v.contains("Inequality contradiction")),
        "transitive equality must contradict the asserted inequality: {violations:?}"
    );
}

#[test]
fn test_not_equals_unrelated_no_contradiction() {
    // du(alis,bob) but carol is unrelated: `na du(alis, carol)` is consistent.
    let kb = new_kb();
    assert_buf(&kb, make_equals("alis", "bob"));
    assert_id(&kb, make_negated_equals("alis", "carol"), "na du");
    assert!(
        kb.check_contradictions().is_empty(),
        "an inequality between non-equivalent terms is not a contradiction"
    );
}

#[test]
fn test_not_equals_inequality_query() {
    // Inequality querying via NAF over the union-find: na du holds when the two
    // terms are not equivalent, and fails when they are.
    let kb = new_kb();
    assert_buf(&kb, make_equals("alis", "bob"));
    assert!(
        query(&kb, make_negated_equals("alis", "carol")),
        "na du(alis, carol) should hold — they are not equivalent"
    );
    assert!(
        query_false(&kb, make_negated_equals("alis", "bob")),
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
    // Assert a known ENGLISH corpus relation — registered with Dictionary
    // source (gismu spellings stopped resolving at the committed-corpus
    // milestone; a raw gismu now registers as Inferred like any unknown word).
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "dog"));
    let inner = kb.inner.borrow();
    let sig = inner.predicate_registry.get("dog").unwrap();
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
        .any(|s| matches!(s.rule, ProofRule::PredicateNotFound { .. }));
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
    assert_buf(&kb, make_assertion("alis", "mlatu")); // alis exists but not as dog.
    let (result, trace) = kb
        .query_entailment_with_proof_inner(make_query("alis", "danlu"))
        .unwrap();
    assert!(result.is_false());
    // The trace should contain a RuleAttemptFailed showing the gerku condition failed.
    let has_rule_failed = trace
        .steps
        .iter()
        .any(|s| matches!(s.rule, ProofRule::RuleAttemptFailed { .. }));
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
        .any(|s| matches!(s.rule, ProofRule::PredicateNotFound { .. }));
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
        query_false(&kb, make_query("alis", "mlatu")),
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
        query_false(&kb, make_query("alis", "danlu")),
        "danlu(alis) should NOT persist after hypothetical"
    );
}
