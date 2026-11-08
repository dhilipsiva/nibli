use super::*;

// This is the unchanged 315-byte corpus seed from the hosted fuzz_query OOM.
// The fuzzer asserted and queried two concatenated copies (SHA-1 of 630 bytes:
// 29f35755c7242959b4140fbc5351e7fc52376cdd). Eight universal binders over seven
// constants previously grew a multi-million-step certificate beyond 2 GiB.
const HOSTED_SEED: &str = "all $a, $ep, $pair, $s, $i, $e, $ir, $sr: record($a, $ep, $pair, AssessmentRegister) & record($pair, $s, $i, InteractionPairs) & record($ir, $i, $e, MechanismRegister) & member($ir, InhibitionEdges) & record($sr, $s, $e, MechanismRegister) & member($sr, SubstrateEdges) -> fit($a, SharedMechanism, ScreeningPolicy).";

struct BudgetGuard;
impl BudgetGuard {
    fn formula(limit: usize) -> Self {
        crate::compute::TEST_MAX_FORMULA_EVALUATIONS.with(|c| c.set(Some(limit)));
        Self
    }
    fn proof(limit: usize) -> Self {
        crate::reasoning::TEST_MAX_PROOF_STEPS.with(|c| c.set(Some(limit)));
        Self
    }
}
impl Drop for BudgetGuard {
    fn drop(&mut self) {
        crate::compute::TEST_MAX_FORMULA_EVALUATIONS.with(|c| c.set(None));
        crate::reasoning::TEST_MAX_PROOF_STEPS.with(|c| c.set(None));
    }
}

#[test]
fn hosted_quantified_fuzz_seed_stops_at_real_formula_budget() {
    let kb = new_kb();
    let logic = compile_surface(HOSTED_SEED);
    assert_buf(&kb, logic.clone());
    let (result, trace) = kb.query_entailment_with_proof_inner(logic).unwrap();
    assert_eq!(result, QueryResult::ResourceExceeded(ResourceKind::Fuel));
    assert_eq!(trace.steps.len(), 1, "no partial certificate escapes");
    assert!(!trace.steps[trace.root as usize].holds);
    assert!(!trace.naf_dependent);
    assert!(!trace.cwa_false);
    assert!(
        matches!(trace.steps[0].rule, ProofRule::PredicateCheck { ref method, .. } if method == "indeterminate")
    );
    // The exhausted query must not retain its budget, partial depth, or lookup
    // setting in the reusable KB.
    assert_buf(&kb, compile_surface("dog(Adam)."));
    let (result, trace) = kb
        .query_entailment_with_proof_inner(compile_surface("dog(Adam)."))
        .unwrap();
    assert_eq!(result, QueryResult::True);
    assert!(trace.steps[trace.root as usize].holds);
}

#[test]
fn formula_budget_is_non_false_and_shared_by_plain_and_proof_search() {
    let kb = new_kb();
    let logic = compile_surface(HOSTED_SEED);
    assert_buf(&kb, logic.clone());
    let configured_depth = kb.inner.borrow().max_chain_depth;
    {
        let _budget = BudgetGuard::formula(40);
        assert_eq!(
            kb.query_entailment_inner(logic.clone()).unwrap(),
            QueryResult::ResourceExceeded(ResourceKind::Fuel)
        );
        let (result, trace) = kb.query_entailment_with_proof_inner(logic).unwrap();
        assert_eq!(result, QueryResult::ResourceExceeded(ResourceKind::Fuel));
        assert!(!trace.steps[trace.root as usize].holds);
        assert_eq!(kb.inner.borrow().max_chain_depth, configured_depth);
        assert!(kb.inner.borrow().positive_lookup.get());
    }
    assert_buf(&kb, compile_surface("dog(Adam)."));
    let query = compile_surface("dog(Adam).");
    let plain = kb.query_entailment_inner(query.clone()).unwrap();
    let (traced, trace) = kb.query_entailment_with_proof_inner(query).unwrap();
    assert_eq!(plain, QueryResult::True);
    assert_eq!(plain, traced);
    assert!(trace.steps[trace.root as usize].holds);
}

#[test]
fn proof_cap_aborts_quantified_rewalk_without_publishing_partial_certificate() {
    let kb = new_kb();
    let text = "all $a, $b, $c: record($a, $b, $c, Registry) -> fit($a, Policy, Screen).";
    let logic = compile_surface(text);
    assert_buf(&kb, logic.clone());
    let plain = kb.query_entailment_inner(logic.clone()).unwrap();
    assert_eq!(plain, QueryResult::True);
    {
        let _budget = BudgetGuard::proof(8);
        let error = kb
            .query_entailment_with_proof_inner(logic.clone())
            .unwrap_err();
        assert!(error.contains("step/indexable size limit"), "{error}");
    }
    let (result, trace) = kb.query_entailment_with_proof_inner(logic).unwrap();
    assert_eq!(result, plain);
    assert!(trace.steps.len() > 8);
    for step in &trace.steps {
        assert!(
            step.children
                .iter()
                .all(|child| (*child as usize) < trace.steps.len())
        );
    }
}
