use super::*;

// ─── Witness extraction tests ────────────────────────────────

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
            ProofRule::ExistsWitness {
                term: LogicalTerm::Constant(c),
                ..
            } => Some(c.clone()),
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
