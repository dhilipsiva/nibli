use super::*;

fn holds(kb: &KnowledgeBase, text: &str) -> QueryResult {
    kb.query_entailment(compile_surface(text)).unwrap()
}

#[test]
fn zero_dependency_consequent_witness_waits_for_its_guard_and_retraction() {
    let kb = new_kb();
    kb.set_materialization(false);
    assert_buf(&kb, compile_surface("dog(Adam) -> likes(Adam, some cat)."));
    assert_eq!(holds(&kb, "all $x: $x = Adam."), QueryResult::True);
    assert_eq!(holds(&kb, "cat(some cat)."), QueryResult::False);

    let id = assert_id(&kb, compile_surface("dog(Adam)."), "guard");
    assert_eq!(holds(&kb, "all $x: $x = Adam."), QueryResult::False);
    assert_eq!(holds(&kb, "likes(Adam, exactly 1 cat)."), QueryResult::True);
    assert_eq!(kb.query_find(compile_surface("cat($x).")).unwrap().len(), 1);
    kb.retract_fact(id).unwrap();
    assert_eq!(holds(&kb, "all $x: $x = Adam."), QueryResult::True);
    assert!(
        kb.query_find(compile_surface("cat($x)."))
            .unwrap()
            .is_empty()
    );
}

#[test]
fn conditional_antecedent_existentials_are_patterns_not_domain_seeds() {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("dog(some cat) -> bird(Adam)."));
    assert_eq!(holds(&kb, "all $x: $x = Adam."), QueryResult::True);
    assert_eq!(holds(&kb, "bird(Adam)."), QueryResult::False);
}

#[test]
fn explicit_ground_and_leading_existentials_remain_unconditional() {
    let ground = new_kb();
    assert_buf(&ground, compile_surface("cat(some cat)."));
    assert_eq!(holds(&ground, "cat(some cat)."), QueryResult::True);

    let leading = new_kb();
    assert_buf(&leading, compile_surface("likes($y, every dog)."));
    assert_eq!(holds(&leading, "$x = $x."), QueryResult::True);
    assert_eq!(holds(&leading, "dog(some dog)."), QueryResult::False);
}

#[test]
fn activated_witness_trace_preserves_the_original_noncyclic_guard_support() {
    let kb = new_kb();
    kb.set_materialization(false);
    for text in [
        "dog(Adam).",
        "likes(Adam, some mouse) -> cat(Adam).",
        "dog(Adam) -> cat(Adam).",
        "cat(Adam) -> likes(Adam, some mouse).",
    ] {
        assert_buf(&kb, compile_surface(text));
    }
    let query = "likes(Adam, some mouse).";
    let (result, trace) = kb
        .query_entailment_with_proof(compile_surface(query))
        .unwrap();
    assert_eq!(result, QueryResult::True);
    let envelope = nibli_types::logic::ProofEnvelope::bind(
        query,
        result,
        trace,
        nibli_types::logic::EngineProfile {
            strict: false,
            existential_import: false,
            materialization: false,
            max_chain_depth: kb.max_chain_depth(),
        },
    );
    nibli_types::logic::validate_envelope(&envelope)
        .expect("the activation has a finite dog-supported proof");
}

#[test]
fn implicit_domain_negative_cycle_cannot_certify_an_event_as_an_individual() {
    for materialization in [false, true] {
        let kb = new_kb();
        kb.set_materialization(materialization);
        for text in ["all $x: $x = $x -> cat($x).", "~cat() -> dog(some dog)."] {
            assert_buf(&kb, compile_surface(text));
        }
        assert!(kb.inner.borrow().known_entities.is_empty());
        for query in [
            "cat(some cat).",
            "dog(some dog).",
            "~cat(some cat).",
            "all $x: cat($x).",
        ] {
            let result = holds(&kb, query);
            assert!(
                !result.is_definitive(),
                "materialization={materialization}, {query}: {result:?}"
            );
        }
        assert!(kb.query_find(compile_surface("cat($x).")).is_err());
    }
}

fn valid_proof_result(kb: &KnowledgeBase, query: &str, materialization: bool) -> QueryResult {
    let (result, trace) = kb
        .query_entailment_with_proof(compile_surface(query))
        .unwrap();
    let envelope = nibli_types::logic::ProofEnvelope::bind(
        query,
        result.clone(),
        trace,
        nibli_types::logic::EngineProfile {
            strict: false,
            existential_import: false,
            materialization,
            max_chain_depth: kb.max_chain_depth(),
        },
    );
    nibli_types::logic::validate_envelope(&envelope).expect("opacity proof must validate");
    result
}

#[test]
fn activated_entitlement_does_not_assert_its_quoted_event() {
    for materialization in [false, true] {
        let kb = new_kb();
        kb.set_materialization(materialization);
        for text in ["person(Adam).", "entitled(every person, event { eats() })."] {
            assert_buf(&kb, compile_surface(text));
        }
        assert_eq!(
            valid_proof_result(&kb, "entitled(Adam, event { eats() }).", materialization),
            QueryResult::True
        );
        assert_eq!(
            valid_proof_result(&kb, "eats().", materialization),
            QueryResult::False
        );
        assert!(
            kb.query_find(compile_surface("eats($x)."))
                .unwrap()
                .is_empty()
        );
    }
}

#[test]
fn activated_entitlement_does_not_generate_quoted_individuals() {
    for materialization in [false, true] {
        let kb = new_kb();
        kb.set_materialization(materialization);
        for text in [
            "person(Adam).",
            "entitled(every person, event { eats(some cat) }).",
        ] {
            assert_buf(&kb, compile_surface(text));
        }
        assert_eq!(
            valid_proof_result(
                &kb,
                "entitled(Adam, event { eats(some cat) }).",
                materialization
            ),
            QueryResult::True
        );
        for query in ["cat(some cat).", "eats(some cat).", "eats()."] {
            assert_eq!(holds(&kb, query), QueryResult::False, "{query}");
        }
        assert_eq!(holds(&kb, "cat(exactly 0 cat)."), QueryResult::True);
        assert!(
            kb.query_find(compile_surface("cat($x)."))
                .unwrap()
                .is_empty()
        );
    }
}

#[test]
fn activated_real_witness_does_not_publish_a_sibling_quoted_body() {
    for materialization in [false, true] {
        let kb = new_kb();
        kb.set_materialization(materialization);
        for text in [
            "person(Adam).",
            "all $x: person($x) -> likes($x, some cat) & entitled($x, event { eats(some dog) }).",
        ] {
            assert_buf(&kb, compile_surface(text));
        }
        for query in [
            "likes(Adam, some cat).",
            "entitled(Adam, event { eats(some dog) }).",
        ] {
            assert_eq!(
                valid_proof_result(&kb, query, materialization),
                QueryResult::True
            );
        }
        assert_eq!(holds(&kb, "likes(Adam, exactly 1 cat)."), QueryResult::True);
        assert_eq!(kb.query_find(compile_surface("cat($x).")).unwrap().len(), 1);
        for query in ["dog(some dog).", "eats(some dog).", "eats()."] {
            assert_eq!(holds(&kb, query), QueryResult::False, "{query}");
        }
        assert_eq!(holds(&kb, "dog(exactly 0 dog)."), QueryResult::True);
        assert!(
            kb.query_find(compile_surface("dog($x)."))
                .unwrap()
                .is_empty()
        );
    }
}

#[test]
fn quoted_individuals_preserve_the_outer_domain_for_ground_and_conditional_assertions() {
    for materialization in [false, true] {
        for subject in ["Adam", "every person"] {
            for body in ["eats()", "eats(some cat)"] {
                let kb = new_kb();
                kb.set_materialization(materialization);
                assert_buf(&kb, compile_surface("person(Adam)."));
                assert_buf(
                    &kb,
                    compile_surface(&format!("entitled({subject}, event {{ {body} }}).")),
                );
                assert_eq!(
                    holds(&kb, "all $x: person($x) | entitled(Adam, $x)."),
                    QueryResult::True,
                    "subject={subject}, body={body}, materialization={materialization}"
                );
                assert_eq!(
                    kb.query_find(compile_surface("entitled(Adam, $x)."))
                        .unwrap()
                        .len(),
                    1
                );
            }
        }
    }
}
