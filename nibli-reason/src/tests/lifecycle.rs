use super::*;
use nibli_types::logic::AssertionStatus;

#[test]
fn rejected_transaction_preserves_registry_allocator_policy_and_answers() {
    let kb = new_kb();
    let before = kb.next_fact_id().unwrap();
    let error = kb
        .transaction(|candidate| {
            candidate.assert_fact(
                compile_surface("derived_only(\"cat\")."),
                "declaration".into(),
            )?;
            candidate.assert_fact(compile_surface("dog(Alis)."), "temporary".into())?;
            candidate.assert_fact(compile_surface("cat(Bob)."), "refused".into())
        })
        .unwrap_err();
    assert!(error.to_string().contains("derived"));
    assert_eq!(kb.next_fact_id().unwrap(), before);
    assert!(kb.list_assertion_records().unwrap().is_empty());
    assert!(!kb.is_derived_only("cat"));
    assert_eq!(
        kb.query_entailment(compile_surface("dog(Alis).")).unwrap(),
        QueryResult::False
    );
    kb.assert_fact(compile_surface("cat(Bob)."), "allowed".into())
        .unwrap();
}

#[test]
fn withdrawn_metadata_reserves_identity_and_never_becomes_a_premise() {
    let kb = new_kb();
    kb.restore_withdrawn_assertion(41, "obsolete syntax need not compile".into())
        .unwrap();
    assert!(
        kb.restore_withdrawn_assertion(41, "collision".into())
            .is_err()
    );
    assert_eq!(kb.next_fact_id().unwrap(), 42);
    assert!(kb.list_facts().unwrap().is_empty());
    let id = kb
        .assert_fact(compile_surface("dog(Alis)."), "dog(Alis).".into())
        .unwrap();
    assert_eq!(id, 42);
    kb.retract_fact(id).unwrap();
    kb.retract_fact(id).unwrap();
    let records = kb.list_assertion_records().unwrap();
    assert_eq!(
        records.iter().map(|record| record.id).collect::<Vec<_>>(),
        vec![41, 42]
    );
    assert!(
        records
            .iter()
            .all(|record| record.status == AssertionStatus::Withdrawn)
    );
    assert_eq!(
        kb.query_entailment(compile_surface("dog(Alis).")).unwrap(),
        QueryResult::False
    );
    kb.reset().unwrap();
    assert!(kb.list_assertion_records().unwrap().is_empty());
    assert_eq!(kb.next_fact_id().unwrap(), 0);
}

#[test]
fn recovery_guard_covers_exposed_kb_queries_mutations_and_history() {
    let kb = new_kb();
    kb.assert_fact(compile_surface("dog(Alis)."), "dog".into())
        .unwrap();
    kb.require_recovery("commit outcome is uncertain".into());
    assert!(kb.query_entailment(compile_surface("dog(Alis).")).is_err());
    assert!(kb.query_find(compile_surface("dog($x).")).is_err());
    assert!(
        kb.query_entailment_with_proof(compile_surface("dog(Alis)."))
            .is_err()
    );
    assert!(
        kb.assert_fact(compile_surface("cat(Bob)."), "cat".into())
            .is_err()
    );
    assert!(kb.retract_fact(0).is_err());
    assert!(
        kb.restore_withdrawn_assertion(4, "metadata".into())
            .is_err()
    );
    assert!(kb.reset().is_err());
    assert!(kb.list_facts().is_err());
    assert!(kb.list_assertion_records().is_err());
    assert!(kb.active_typed_facts().is_err());
    assert!(!kb.check_contradictions_report().is_clean());
    assert!(kb.set_max_chain_depth(2).is_err());
}

#[test]
fn depth_and_private_assumptions_survive_lifecycle_without_registry_leaks() {
    let kb = new_kb();
    kb.set_max_chain_depth(17).unwrap();
    let id = kb
        .assert_fact(compile_surface("dog(Alis)."), "dog".into())
        .unwrap();
    kb.with_assumptions(&[compile_surface("cat(Bob).")], |temporary| {
        assert_eq!(temporary.max_chain_depth(), 17);
        assert_eq!(temporary.list_assertion_records().unwrap().len(), 2);
    })
    .unwrap();
    assert_eq!(kb.list_assertion_records().unwrap().len(), 1);
    kb.retract_fact(id).unwrap();
    kb.set_existential_import(true).unwrap();
    kb.reset().unwrap();
    assert_eq!(kb.max_chain_depth(), 17);
    assert!(kb.set_max_chain_depth(0).is_err());
    assert_eq!(kb.max_chain_depth(), 17);
}

#[test]
fn transaction_reentrant_use_returns_error_without_panicking() {
    let kb = new_kb();
    kb.transaction(|candidate| {
        assert!(kb.query_entailment(compile_surface("dog(Alis).")).is_err());
        candidate.assert_fact(compile_surface("dog(Alis)."), "dog".into())
    })
    .unwrap();
    assert_eq!(
        kb.query_entailment(compile_surface("dog(Alis).")).unwrap(),
        QueryResult::True
    );
}
