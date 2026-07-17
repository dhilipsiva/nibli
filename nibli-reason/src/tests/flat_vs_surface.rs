use super::*;

/// True if two verdicts agree on the TRUE / FALSE / indeterminate classification.
fn same_verdict(a: &QueryResult, b: &QueryResult) -> bool {
    a.is_true() == b.is_true() && a.is_false() == b.is_false()
}

/// Assert a flat KB+query agrees with the surface (real-pipeline) KB+query, and matches the
/// expected verdict. Returns the SURFACE proof trace for flag assertions.
fn check(
    name: &str,
    surface_kb: &[&str],
    surface_query: &str,
    flat_kb: Vec<LogicBuffer>,
    flat_query: LogicBuffer,
    expect_true: bool,
) -> ProofTrace {
    let sk = new_kb();
    for line in surface_kb {
        assert_buf(&sk, compile_surface(line));
    }
    let (surf_res, surf_trace) = sk
        .query_entailment_with_proof_inner(compile_surface(surface_query))
        .unwrap();

    let fk = new_kb();
    for buf in flat_kb {
        assert_buf(&fk, buf);
    }
    let flat_res = query_result(&fk, flat_query);

    assert!(
        same_verdict(&surf_res, &flat_res),
        "{name}: flat vs surface DISAGREE — surface={surf_res:?} flat={flat_res:?}"
    );
    assert_eq!(
        surf_res.is_true(),
        expect_true,
        "{name}: surface verdict {surf_res:?} != expected TRUE={expect_true}"
    );
    surf_trace
}

#[test]
fn ground_predicate_true() {
    check(
        "ground_true",
        &["dog(Adam)."],
        "dog(Adam).",
        vec![make_assertion("adam", "gerku")],
        make_query("adam", "gerku"),
        true,
    );
}

#[test]
fn absence_false_is_closed_world() {
    // A missing fact is FALSE, and the SURFACE trace flags it as a closed-world (cwa) FALSE.
    let trace = check(
        "absence_false",
        &["dog(Adam)."],
        "cat(Adam).",
        vec![make_assertion("adam", "gerku")],
        make_query("adam", "mlatu"),
        false,
    );
    assert!(
        trace.cwa_false,
        "an absence-driven FALSE must set cwa_false on the surface trace"
    );
}

#[test]
fn universal_modus_ponens_true() {
    check(
        "modus_ponens",
        &["animal(every dog).", "dog(Adam)."],
        "animal(Adam).",
        vec![
            make_universal("gerku", "danlu"),
            make_assertion("adam", "gerku"),
        ],
        make_query("adam", "danlu"),
        true,
    );
}

#[test]
fn transitive_chain_true() {
    check(
        "transitive_chain",
        &["animal(every dog).", "alive(every animal).", "dog(Adam)."],
        "alive(Adam).",
        vec![
            make_universal("gerku", "danlu"),
            make_universal("danlu", "jmive"),
            make_assertion("adam", "gerku"),
        ],
        make_query("adam", "jmive"),
        true,
    );
}

#[test]
fn naf_rule_true_and_flagged() {
    // "every person who is not a dog is an animal"; adam is a person, not a dog -> animal,
    // via negation-as-failure. The surface trace must mark it naf_dependent.
    let trace = check(
        "naf_rule",
        &["animal(every person where ~dog).", "person(Adam)."],
        "animal(Adam).",
        vec![
            make_universal_naf("prenu", "gerku", "danlu"),
            make_assertion("adam", "prenu"),
        ],
        make_query("adam", "danlu"),
        true,
    );
    assert!(
        trace.naf_dependent,
        "a NAF-derived TRUE must set naf_dependent on the surface trace"
    );
}

#[test]
fn equals_substitution_true() {
    // adam = bob, bob is a dog -> adam is a dog (substitutivity). `du` stays flat by design.
    let mut du_nodes = Vec::new();
    let equals_root = pred(
        &mut du_nodes,
        "equals",
        vec![
            LogicalTerm::Constant("adam".into()),
            LogicalTerm::Constant("bob".into()),
        ],
    );
    let equals_buf = LogicBuffer {
        nodes: du_nodes,
        roots: vec![equals_root],
    };
    check(
        "du_equality",
        &["Adam = Bob.", "dog(Bob)."],
        "dog(Adam).",
        vec![equals_buf, make_assertion("bob", "gerku")],
        make_query("adam", "gerku"),
        true,
    );
}

#[test]
fn numeric_arithmetic_true() {
    // 6 is the product of 2 and 3.
    check(
        "numeric_pilji_true",
        &[],
        "product(6, 2, 3).",
        vec![],
        make_compute_query("product", 6.0, 2.0, 3.0),
        true,
    );
}

#[test]
fn numeric_comparison_decided_true() {
    check(
        "numeric_dunli_true",
        &[],
        "num_equal(5, 5).",
        vec![],
        make_numeric_query("num_equal", 5.0, 5.0),
        true,
    );
}

#[test]
fn numeric_comparison_decided_false_is_not_closed_world() {
    // 5 = 3 is a DECIDED false, not a closed-world absence: the surface trace must NOT set
    // cwa_false (the exact flat-vs-surface divergence this whole item closes).
    let trace = check(
        "numeric_dunli_false",
        &[],
        "num_equal(5, 3).",
        vec![],
        make_numeric_query("num_equal", 5.0, 3.0),
        false,
    );
    assert!(
        !trace.cwa_false,
        "a numeric-decided FALSE must NOT set cwa_false on the surface trace"
    );
}
