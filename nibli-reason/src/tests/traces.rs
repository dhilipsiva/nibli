use super::*;

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
                    ProofRule::ForallCounterexample { .. }
                        | ProofRule::ExistsFailed
                        | ProofRule::PredicateNotFound { .. }
                ),
                "non-definitive verdict {result:?} but root asserts a decided failure: {:?}",
                root.rule
            );
        }
    }
    assert_proof_refs_resolve_to_holds_true(trace);
}

/// Conformance bridge to `proofs/Trace.lean` (`cert_sound` / `qproof_sound`): every recorded proof
/// trace, read as a proof CERTIFICATE, must be a valid certificate — each step's `holds` is justified
/// locally by its rule + children (the `Pos`/`Neg`/`QProof`/`QRefute` constructors), AND the trace's
/// leaves/steps are tied to the real engine, bridging the `PerfectModel` axioms: `factAx` (an
/// Asserted leaf is a KB fact), `candOk`/`ruleClosed` (a Derived step maps to a registered rule), and
/// `supported` (a closed-world FALSE atom is genuinely not a fact and records only real blocked
/// rules — the `notFound` certificate the engine emits). Composed with the Lean theorem "a valid
/// certificate ⇒ the conclusion holds in the perfect model," this makes the capstone load-bearing,
/// not proof-conditional. (`ruleClosed`'s firing step is separately proved + bridged by
/// `rule_firing_conformance`. Corpus-tested, not exhaustive; the `supported` completeness direction —
/// no fireable rule silently skipped — rests on the engine's emission invariant, itself cross-checked
/// by the `nibli-verify` differential gates' verdict-vs-independent-model comparison.)
///
/// The depth-boundary contract, pinned exactly (the audit's one unresolved probe leg):
/// with `max_chain_depth = D`, a chain whose shallowest proof needs ≤ D rule steps is
/// TRUE, a chain needing D+1 steps is `ResourceExceeded(Depth)` — NEVER FALSE — and a
/// goal with no rule path at all is FALSE (search exhausted below the bound) — never
/// RESOURCE_EXCEEDED. Pinned at a REDUCED depth via the public `set_max_chain_depth`
/// knob: the default depth-10 boundary is computationally unreachable in any build
/// profile (iterative-deepening cost grows ~15×+ per chain level — measured 0.8 s at
/// chain 3, 21.5 s at chain 4 in a debug build), and the contract is depth-uniform,
/// so the small-depth pin is the same guarantee.
#[test]
fn depth_boundary_contract() {
    let kb = new_kb();
    kb.set_max_chain_depth(3);

    // Chain: gerku(alis) --∀--> danlu --∀--> jmive --∀--> xanlu --∀--> melbi
    // (shallowest proofs: danlu=1 step, jmive=2, xanlu=3, melbi=4).
    assert_buf(&kb, make_assertion("alis", "gerku"));
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "jmive"));
    assert_buf(&kb, make_universal("jmive", "xanlu"));
    assert_buf(&kb, make_universal("xanlu", "melbi"));

    let verdict = |p: &str| {
        kb.query_entailment_inner(make_query("alis", p))
            .unwrap_or_else(|e| panic!("query {p}: {e}"))
    };

    // Within the bound: TRUE at every chain length up to D.
    for p in ["gerku", "danlu", "jmive", "xanlu"] {
        assert_eq!(
            verdict(p),
            QueryResult::True,
            "chain to {p} is within depth 3"
        );
    }
    // One past the bound: RESOURCE_EXCEEDED(Depth) — the proof exists deeper, and the
    // engine must say "could not determine within bounds", never a confident FALSE.
    assert_eq!(
        verdict("melbi"),
        QueryResult::ResourceExceeded(ResourceKind::Depth),
        "chain needing depth 4 under a depth-3 bound is RESOURCE_EXCEEDED(Depth)"
    );
    // No rule path at all: the search exhausts BELOW the bound — closed-world FALSE,
    // never a resource verdict (the discrimination GUARANTEES §Completeness draws).
    assert_eq!(
        verdict("cipni"),
        QueryResult::False,
        "an unreachable goal is FALSE, not RESOURCE_EXCEEDED"
    );

    // Restoring the bound makes the deeper chain provable — the RE verdict above was
    // the bound speaking, not the KB.
    kb.set_max_chain_depth(4);
    assert_eq!(verdict("melbi"), QueryResult::True, "depth 4 reaches melbi");
}

/// Exact-count bound logic with a NON-DEFINITIVE member (mutation-baseline kill,
/// 2026-07 sweep): `check_formula_holds_core`'s CountNode fallback decides
/// `satisfying > count || satisfying + unresolved < count → FALSE`, else returns
/// the best non-definitive sub-result. No prior test enumerated a count body over
/// a member whose sub-check is unresolved. Built on `compile_surface` (CountNode
/// is IR-shape-dependent); the unresolved member comes from a 2-rule chain under
/// a depth-1 bound (RESOURCE_EXCEEDED(Depth) — never a silent True/False).
#[test]
fn exact_count_with_unresolved_member_bounds() {
    // KB 1: kim is a ground gerku; danlu(kim) needs cipni→jmive→danlu (2 rule
    // steps) — unreachable under depth 1, so that member is unresolved.
    // satisfying=0, unresolved=1.
    let kb = new_kb();
    for s in [
        "dog(Kim).",
        "bird(Kim).",
        "all $da: bird($da) -> alive($da).",
        "all $da: alive($da) -> animal($da).",
    ] {
        assert_buf(&kb, compile_surface(s));
    }
    kb.set_max_chain_depth(1);

    // count=1: neither bound is decisive (0 > 1 is false; 0+1 < 1 is false) —
    // the verdict is the member's own non-definitive result, NEVER a guess.
    assert_eq!(
        kb.query_entailment_inner(compile_surface("animal(exactly 1 dog)."))
            .unwrap(),
        QueryResult::ResourceExceeded(ResourceKind::Depth),
        "0 satisfying + 1 unresolved vs count 1: non-definitive, not FALSE"
    );
    // count=2: the sum bound IS decisive (0+1 < 2) — a confident FALSE even
    // with the unresolved member (it cannot reach the count either way).
    assert_eq!(
        kb.query_entailment_inner(compile_surface("animal(exactly 2 dog)."))
            .unwrap(),
        QueryResult::False,
        "0 satisfying + 1 unresolved vs count 2: sum bound gives FALSE"
    );

    // KB 2: two ground satisfiers + the unresolved member: the over-count bound
    // is decisive (2 > 1) — FALSE regardless of the unresolved member.
    let kb2 = new_kb();
    for s in [
        "dog(Adam).",
        "dog(Bel).",
        "dog(Kim).",
        "animal(Adam).",
        "animal(Bel).",
        "bird(Kim).",
        "all $da: bird($da) -> alive($da).",
        "all $da: alive($da) -> animal($da).",
    ] {
        assert_buf(&kb2, compile_surface(s));
    }
    kb2.set_max_chain_depth(1);
    assert_eq!(
        kb2.query_entailment_inner(compile_surface("animal(exactly 1 dog)."))
            .unwrap(),
        QueryResult::False,
        "2 satisfying vs count 1: over-count bound gives FALSE"
    );
    // count == satisfying with an unresolved member: NEITHER bound is decisive
    // (2 > 2 is false — strictly-greater, not >=; 2+1 < 2 is false) — the
    // unresolved member could push the tally past the exact count, so the
    // verdict must stay non-definitive, never a confident FALSE.
    assert_eq!(
        kb2.query_entailment_inner(compile_surface("animal(exactly 2 dog)."))
            .unwrap(),
        QueryResult::ResourceExceeded(ResourceKind::Depth),
        "satisfying == count with an unresolved member: non-definitive, not FALSE"
    );
}

/// The ForAll/Count-over-ComputeNode BATCH fast path
/// (`batch_evaluate_compute_for_members`) — raw-FOL-only (the surface pipeline
/// never leaves a bare ComputeNode body). Its decisive per-member branches need
/// NUMERIC members, and numbers never enter the quantifier domain (asserting
/// `namcu(4.0)`/`namcu(5.0)` below adds NO member — pinned at the engine level
/// too, `numeric_terms_are_not_universal_domain_members`). With real (constant)
/// members the arithmetic is non-evaluable and no backend is configured, so the
/// batch must stay NON-DEFINITIVE — never a fabricated True/False — except where
/// the count sum-bound is decisive regardless of the unresolved member.
#[test]
fn flat_forall_and_count_over_compute_batch_stays_non_definitive() {
    let kb = new_kb();
    for n in [4.0, 5.0] {
        let mut nodes = Vec::new();
        let root = pred(&mut nodes, "namcu", vec![LogicalTerm::Number(n)]);
        assert_buf(
            &kb,
            LogicBuffer {
                nodes,
                roots: vec![root],
            },
        );
    }
    assert_buf(&kb, make_assertion("alis", "prenu"));

    let compute_body = |nodes: &mut Vec<LogicNode>| {
        compute(
            nodes,
            "sum",
            vec![
                LogicalTerm::Variable("_v0".to_string()),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        )
    };

    let mut nodes = Vec::new();
    let body = compute_body(&mut nodes);
    let root = forall(&mut nodes, "_v0", body);
    assert_eq!(
        query_result(
            &kb,
            LogicBuffer {
                nodes,
                roots: vec![root],
            }
        ),
        QueryResult::Unknown(UnknownReason::BackendUnavailable),
        "forall over an un-evaluable compute member is non-definitive"
    );

    for (cnt, expected) in [
        (
            1u32,
            QueryResult::Unknown(UnknownReason::BackendUnavailable),
        ),
        // 0 satisfying + 1 unresolved < 2: the sum bound is decisive.
        (2u32, QueryResult::False),
    ] {
        let mut nodes = Vec::new();
        let body = compute_body(&mut nodes);
        let root = count(&mut nodes, "_v0", cnt, body);
        assert_eq!(
            query_result(
                &kb,
                LogicBuffer {
                    nodes,
                    roots: vec![root],
                }
            ),
            expected,
            "count {cnt} over an un-evaluable compute member"
        );
    }
}

/// A universal over a COMPUTE body takes the batch fast path
/// (`batch_evaluate_compute_for_members`): the first FAILING member is the
/// counterexample. Pin both verdict directions so the fail-detection polarity
/// cannot silently flip (an all-false body must be FALSE, never a vacuous TRUE).
#[test]
fn forall_over_compute_body_batch_path() {
    let kb = new_kb();
    // Populate the domain with two entities.
    assert_buf(&kb, compile_surface("dog(Adam)."));
    assert_buf(&kb, compile_surface("dog(Bel)."));

    // No entity equals 2 + 3: the universal is FALSE with a counterexample.
    assert_eq!(
        kb.query_entailment_inner(compile_surface("all $da: sum($da, 2, 3)."))
            .unwrap(),
        QueryResult::False,
        "a compute body false for every member makes the universal FALSE"
    );
}

/// The groundness invariant is a MECHANISM at the store boundary, not call-site
/// discipline: `assert_typed_fact` drops (fail-closed, with a warning) any fact whose
/// args contain a pattern variable — including one nested inside a `SkolemFn`
/// dependency or `DepPair` component, which a flat top-level scan would miss. This is
/// the engine-side enforcement of `proofs/Unify.lean`'s `NoVar c` hypothesis (the
/// concrete side of unification is always ground).
#[test]
fn non_ground_fact_is_dropped_at_the_assert_boundary() {
    let kb = new_kb();
    let mut inner = kb.inner.borrow_mut();

    // Top-level PatternVar.
    crate::rules::assert_typed_fact(
        StoredFact::Bare(GroundFact {
            relation: "gerku".into(),
            args: vec![GroundTerm::PatternVar("x__v0".into())],
        }),
        &mut inner,
    );
    // PatternVar hiding inside a SkolemFn dependency.
    crate::rules::assert_typed_fact(
        StoredFact::Bare(GroundFact {
            relation: "mlatu".into(),
            args: vec![GroundTerm::SkolemFn(
                "sk_9".into(),
                Box::new(GroundTerm::PatternVar("y__v1".into())),
            )],
        }),
        &mut inner,
    );
    // PatternVar hiding inside a DepPair component.
    crate::rules::assert_typed_fact(
        StoredFact::Bare(GroundFact {
            relation: "cipni".into(),
            args: vec![GroundTerm::SkolemFn(
                "sk_10".into(),
                Box::new(GroundTerm::DepPair(
                    Box::new(GroundTerm::Constant("adam".into())),
                    Box::new(GroundTerm::PatternVar("z__v2".into())),
                )),
            )],
        }),
        &mut inner,
    );
    assert!(
        inner.fact_store.is_empty(),
        "non-ground facts must be dropped at the boundary, store has: {:?}",
        inner.fact_store.all_facts().collect::<Vec<_>>()
    );

    // A genuinely ground fact (skolem dependency and all) still inserts.
    crate::rules::assert_typed_fact(
        StoredFact::Bare(GroundFact {
            relation: "gerku".into(),
            args: vec![GroundTerm::SkolemFn(
                "sk_0".into(),
                Box::new(GroundTerm::Constant("adam".into())),
            )],
        }),
        &mut inner,
    );
    assert_eq!(
        inner.fact_store.len(),
        1,
        "a ground fact must still insert normally"
    );
}

/// `validate_cert` walks every step; `trace_soundness_conformance` runs it over a curated corpus, and
/// `Exercised` counters assert each KB-tied bridge fired (never vacuous).
#[test]
fn trace_soundness_conformance() {
    /// How many times each KB-tied bridge check actually fired — so a future corpus change can't
    /// make a bridge silently vacuous.
    #[derive(Default)]
    struct Exercised {
        factax: usize,      // Asserted leaf checked against the fact store
        derived: usize,     // Derived step checked against a registered rule
        notfound: usize,    // PredicateNotFound checked to be a genuine non-fact
        ruleblocked: usize, // RuleAttemptFailed child checked to name a registered rule
        // The strengthened `supported`/Neg bridge (Trace.lean:91):
        cand_complete: usize, // candidate rule verified to appear among the blocked children
        blocker_definitive: usize, // candidate verified blocked by a DEFINITIVE premise
    }

    /// Parse a BARE `rel(arg1, arg2)` fact display back into a `StoredFact` — the shape a
    /// closed-world FALSE goal takes in this corpus. Tense-wrapped, skolem-argument, or
    /// otherwise exotic displays return `None` (those steps keep the unstrengthened checks).
    fn parse_bare_fact_display(s: &str) -> Option<StoredFact> {
        let (rel, rest) = s.split_once('(')?;
        let inner = rest.strip_suffix(')')?;
        if rel.is_empty() || rel.contains(' ') || inner.contains('(') || inner.contains('?') {
            return None;
        }
        let args: Vec<GroundTerm> = if inner.is_empty() {
            Vec::new()
        } else {
            inner
                .split(", ")
                .map(|a| {
                    if a == "_" {
                        GroundTerm::Unspecified
                    } else if let Ok(v) = a.parse::<f64>() {
                        GroundTerm::from_f64(v)
                    } else {
                        GroundTerm::Constant(a.to_string())
                    }
                })
                .collect()
        };
        Some(StoredFact::Bare(GroundFact {
            relation: rel.to_string(),
            args,
        }))
    }

    /// Assert each step's `holds` is locally justified by its rule + children (the `Trace.lean`
    /// certificate constructors) AND — the axiom bridges — that the trace's leaves/steps are tied to
    /// the real KB + rule registry: `factAx` (an Asserted leaf is a KB fact), `candOk`/`ruleClosed`
    /// (a Derived step maps to a registered rule), and `supported` (a closed-world FALSE atom is
    /// genuinely not a fact, and each blocked candidate it records is a real rule — the `notFound`
    /// certificate the engine emits at `reasoning.rs:1086`).
    fn validate_cert(
        kb: &KnowledgeBase,
        trace: &ProofTrace,
        ex: &mut Exercised,
    ) -> Result<(), String> {
        let inner = kb.inner.borrow();
        // The store's fact display strings + the registered rules' base labels — the engine-side
        // ground truth the trace's leaves must be tied to.
        let fact_displays: std::collections::HashSet<String> = inner
            .fact_store
            .all_facts()
            .map(|f| f.to_display_string())
            .collect();
        let rule_labels: std::collections::HashSet<&str> = inner
            .universal_rules
            .values()
            .flatten()
            .map(|r| r.label.as_str())
            .collect();
        // A `Derived`/`RuleAttemptFailed` label may carry a `" [past]"`/`" [present]"` tense suffix.
        fn base_label(l: &str) -> &str {
            l.split(" [").next().unwrap_or(l)
        }

        let holds = |c: u32| trace.steps[c as usize].holds;
        for (i, step) in trace.steps.iter().enumerate() {
            let all_hold = step.children.iter().all(|&c| holds(c));
            let any_hold = step.children.iter().any(|&c| holds(c));
            match &step.rule {
                // Pos.fact — a positive leaf certificate is a true leaf AND (factAx) a genuine KB fact.
                ProofRule::Asserted { fact } => {
                    if !step.holds {
                        return Err(format!("step #{i} Asserted but holds=false"));
                    }
                    if !fact_displays.contains(fact) {
                        return Err(format!(
                            "step #{i} Asserted '{fact}' is not in the fact store (factAx bridge)"
                        ));
                    }
                    ex.factax += 1;
                }
                // Pos.fire — holds ⟹ condition children present + all hold; AND (candOk/ruleClosed)
                // the fired rule is registered.
                ProofRule::Derived { label, .. } => {
                    if step.holds && (step.children.is_empty() || !all_hold) {
                        return Err(format!(
                            "step #{i} Derived holds=true but a condition child is missing or does not hold"
                        ));
                    }
                    if !rule_labels.contains(base_label(label)) {
                        return Err(format!(
                            "step #{i} Derived label '{}' is not a registered rule (candOk/ruleClosed bridge)",
                            base_label(label)
                        ));
                    }
                    ex.derived += 1;
                }
                // Neg / closed-world FALSE — (supported) the atom is genuinely not a fact, every
                // recorded blocked candidate is a real rule, and — the strengthened bridge,
                // matching `Trace.lean:91`'s `Neg` constructor exactly — EVERY candidate rule
                // whose conclusion unifies with the goal is recorded as blocked
                // (candidate-completeness), each by a premise the engine refutes/certifies
                // DEFINITIVELY at the authoritative depth (blocker-definitiveness:
                // `∃ p ∈ f.pos, Neg p  ∨  ∃ n ∈ f.neg, Pos n` — never an Unknown standing in
                // for a refutation).
                ProofRule::PredicateNotFound { predicate } => {
                    if step.holds {
                        return Err(format!("step #{i} PredicateNotFound but holds=true"));
                    }
                    if fact_displays.contains(predicate) {
                        return Err(format!(
                            "step #{i} PredicateNotFound '{predicate}' is actually a stored fact (supported bridge)"
                        ));
                    }
                    let mut blocked_labels: Vec<&str> = Vec::new();
                    for &c in &step.children {
                        match &trace.steps[c as usize].rule {
                            ProofRule::RuleAttemptFailed { rule_label, .. } => {
                                if !rule_labels.contains(base_label(rule_label)) {
                                    return Err(format!(
                                        "step #{i} PredicateNotFound records blocked rule '{}' that is not registered (supported bridge)",
                                        base_label(rule_label)
                                    ));
                                }
                                blocked_labels.push(base_label(rule_label));
                                ex.ruleblocked += 1;
                            }
                            other => {
                                return Err(format!(
                                    "step #{i} PredicateNotFound child is not RuleAttemptFailed: {other:?}"
                                ));
                            }
                        }
                    }
                    if let Some(goal) = parse_bare_fact_display(predicate) {
                        let candidates =
                            crate::reasoning::matching_rules_typed(&goal, &inner.universal_rules);
                        for rule in candidates {
                            let unifying: Vec<_> = rule
                                .typed_conclusions
                                .iter()
                                .filter_map(|c| unify_facts(c, &goal))
                                .collect();
                            if unifying.is_empty() {
                                continue; // not a candidate for this goal (no conclusion unifies)
                            }
                            // (a) Candidate-completeness: the Lean Neg constructor quantifies
                            // over ALL candidates — an unrecorded one is an incomplete cert.
                            if !blocked_labels.contains(&base_label(&rule.label)) {
                                return Err(format!(
                                    "step #{i} PredicateNotFound '{predicate}': candidate rule '{}' \
                                     unifies with the goal but is not recorded as blocked \
                                     (Neg candidate-completeness)",
                                    rule.label
                                ));
                            }
                            ex.cand_complete += 1;
                            // (b) Blocker-definitiveness: re-derive the block AUTHORITATIVELY
                            // (depth 0, the verdict's own regime): some positive premise must be
                            // definitively False, or some negated premise definitively True.
                            // Rules carrying negated-exists groups (`poi na <predicate>`) block
                            // through the group check instead — out of this re-derivation's
                            // scope; their completeness is still enforced above.
                            if rule.negated_exists_groups.is_empty() {
                                let mut definitive = false;
                                for bindings in &unifying {
                                    for (ci, ct) in rule.typed_conditions.iter().enumerate() {
                                        let cond_fact = substitute_fact(ct, bindings);
                                        let r = crate::reasoning::check_predicate_in_kb_typed(
                                            &cond_fact,
                                            &inner,
                                            0,
                                            &mut std::collections::HashSet::new(),
                                        );
                                        let negated = rule.negated_condition_indices.contains(&ci);
                                        if (!negated && matches!(r, QueryResult::False))
                                            || (negated && r.is_true())
                                        {
                                            definitive = true;
                                        }
                                    }
                                }
                                if !definitive {
                                    return Err(format!(
                                        "step #{i} PredicateNotFound '{predicate}': blocked \
                                         candidate '{}' has no definitively-refuted positive \
                                         premise and no definitively-holding negated premise \
                                         (Neg blocker-definitiveness)",
                                        rule.label
                                    ));
                                }
                                ex.blocker_definitive += 1;
                            }
                        }
                    }
                    ex.notfound += 1;
                }
                // Combiner conjunction law: holds ⟺ all children hold.
                ProofRule::Conjunction => {
                    if step.holds != all_hold {
                        return Err(format!(
                            "step #{i} Conjunction holds={} but all-children-hold={all_hold}",
                            step.holds
                        ));
                    }
                }
                // Disjunction: a holding disjunction has a holding child (intro records the true side).
                ProofRule::DisjunctionIntro { .. } | ProofRule::DisjunctionCheck { .. } => {
                    if step.holds && !step.children.is_empty() && !any_hold {
                        return Err(format!(
                            "step #{i} Disjunction holds=true but no child holds"
                        ));
                    }
                }
                // NAF / combiner negation: an empty-child Negation is a NAF-success leaf (holds=true);
                // otherwise holds ⟺ the inner child does NOT hold.
                ProofRule::Negation => {
                    if step.children.is_empty() {
                        if !step.holds {
                            return Err(format!("step #{i} Negation leaf but holds=false"));
                        }
                    } else if step.holds == holds(step.children[0]) {
                        return Err(format!(
                            "step #{i} Negation holds={} but its child holds={}",
                            step.holds,
                            holds(step.children[0])
                        ));
                    }
                }
                // Memo dedup: the referent's verdict must match.
                ProofRule::ProofRef { .. } => {
                    if step.children.is_empty() || step.holds != holds(step.children[0]) {
                        return Err(format!(
                            "step #{i} ProofRef holds mismatch with its referent"
                        ));
                    }
                }
                // Other false leaves & failures: must not hold.
                ProofRule::RuleAttemptFailed { .. }
                | ProofRule::ExistsFailed
                | ProofRule::ForallCounterexample { .. } => {
                    if step.holds {
                        return Err(format!("step #{i} {:?} but holds=true", step.rule));
                    }
                }
                // Other variants carry no core logical structure the certificate models — checked
                // only for verdict/root consistency by `assert_trace_consistent`.
                _ => {}
            }
        }
        Ok(())
    }

    let ex = std::cell::RefCell::new(Exercised::default());
    let run_case = |name: &str, kb: &KnowledgeBase, query: LogicBuffer| {
        let (result, trace) = kb.query_entailment_with_proof_inner(query).unwrap();
        validate_cert(kb, &trace, &mut ex.borrow_mut())
            .unwrap_or_else(|e| panic!("invalid certificate on '{name}': {e}\n{trace:?}"));
        assert_trace_consistent(&result, &trace);
    };

    // Build a conjunction / negation query buffer from two/one predicate leaves.
    fn conj_query(e: &str, p1: &str, p2: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let a = pred(
            &mut nodes,
            p1,
            vec![LogicalTerm::Constant(e.into()), LogicalTerm::Unspecified],
        );
        let b = pred(
            &mut nodes,
            p2,
            vec![LogicalTerm::Constant(e.into()), LogicalTerm::Unspecified],
        );
        let root = and(&mut nodes, a, b);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    }
    fn neg_query(e: &str, p: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let inner = pred(
            &mut nodes,
            p,
            vec![LogicalTerm::Constant(e.into()), LogicalTerm::Unspecified],
        );
        let root = not(&mut nodes, inner);
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    }

    let mut checked = 0usize;

    // 1. Asserted leaf (Pos.fact).
    {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        run_case("asserted", &kb, make_query("alis", "gerku"));
        checked += 1;
    }
    // 2. Single-hop derived (Pos.fire).
    {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        run_case("derived_single", &kb, make_query("alis", "danlu"));
        checked += 1;
    }
    // 3. Multi-hop derived (nested Pos.fire).
    {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("danlu", "xanlu"));
        run_case("derived_multi", &kb, make_query("alis", "xanlu"));
        checked += 1;
    }
    // 4. NAF firing (Pos.fire with a NAF-discharge Negation child).
    {
        let kb = new_kb();
        assert_buf(&kb, make_negated_antecedent_rule());
        assert_buf(&kb, make_assertion("alis", "gerku"));
        run_case("naf_firing", &kb, make_query("alis", "danlu"));
        checked += 1;
    }
    // 5. NAF blocked → closed-world FALSE (Neg / notFound path).
    {
        let kb = new_kb();
        assert_buf(&kb, make_negated_antecedent_rule());
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("alis", "mlatu"));
        run_case("naf_blocked_false", &kb, make_query("alis", "danlu"));
        checked += 1;
    }
    // 6. Plain closed-world FALSE (PredicateNotFound).
    {
        let kb = new_kb();
        run_case("predicate_not_found", &kb, make_query("mi", "klama"));
        checked += 1;
    }
    // 7. Conjunction query (QProof.and → two Pos.fact children).
    {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));
        assert_buf(&kb, make_assertion("mi", "prami"));
        run_case("conjunction", &kb, conj_query("mi", "klama", "prami"));
        checked += 1;
    }
    // 8. Negation of a missing atom (QRefute.atom → Negation over a false inner).
    {
        let kb = new_kb();
        run_case("negation_missing", &kb, neg_query("mi", "klama"));
        checked += 1;
    }
    // 9. Per-entity instantiation: derived holds for the matched entity only.
    {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("bel", "mlatu"));
        run_case("two_entities_true", &kb, make_query("alis", "danlu"));
        run_case("two_entities_false", &kb, make_query("bel", "danlu"));
        checked += 2;
    }
    // 10. Horn rule tried but blocked → closed-world FALSE whose PredicateNotFound records a
    //     RuleAttemptFailed child (the missing `gerku` condition) — exercises the `supported` bridge.
    {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu")); // rule present, but no dog(adam)
        run_case("horn_blocked_false", &kb, make_query("adam", "danlu"));
        checked += 1;
    }
    // 11. TWO candidate rules for the same goal, both blocked → the Neg certificate must
    //     record BOTH as RuleAttemptFailed children (candidate-completeness bites with a
    //     multi-candidate goal, not just the single-rule shape of case 10).
    {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("mlatu", "danlu"));
        run_case(
            "two_candidates_both_blocked",
            &kb,
            make_query("adam", "danlu"),
        );
        checked += 1;
    }
    // 12. Candidate blocked by a premise that is itself closed-world FALSE only through a
    //     further rule attempt (danlu(adam) has its own blocked candidate) — the
    //     blocker-definitiveness re-derivation must recurse through the rule search, not
    //     just the fact store.
    {
        let kb = new_kb();
        assert_buf(&kb, make_universal("danlu", "xanlu"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        run_case("chain_blocked_false", &kb, make_query("adam", "xanlu"));
        checked += 1;
    }

    assert!(
        checked >= 12,
        "trace-soundness corpus too small ({checked}); gate near-vacuous"
    );
    // The axiom bridges must not be vacuous: each KB-tied check fired at least once across the corpus.
    let ex = ex.borrow();
    assert!(
        ex.factax > 0,
        "factAx bridge never exercised (no Asserted leaf checked vs the store)"
    );
    assert!(
        ex.derived > 0,
        "candOk/ruleClosed bridge never exercised (no Derived step checked vs a rule)"
    );
    assert!(
        ex.notfound > 0,
        "supported bridge never exercised (no PredicateNotFound checked)"
    );
    assert!(
        ex.cand_complete >= 2,
        "Neg candidate-completeness never exercised on a multi-candidate goal \
         (need at least the two-candidate case)"
    );
    assert!(
        ex.blocker_definitive > 0,
        "Neg blocker-definitiveness never exercised (no blocked candidate re-derived \
         to a definitive premise)"
    );
    assert!(
        ex.ruleblocked > 0,
        "supported bridge's blocked-rule check never exercised (no RuleAttemptFailed child validated)"
    );
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
    assert_buf(&kb, make_universal("danlu", "gerku")); // dog ⟸ danlu ⟸ dog cycle
    assert_buf(&kb, make_assertion("rex", "mlatu")); // a definitively-True conjunct

    let mut nodes = Vec::new();
    let dog_rex = pred(
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
    let root = and(&mut nodes, dog_rex, mlatu_rex);
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
fn true_and_unknown_right_is_unknown() {
    // Regression for the four-valued combiner bug: `True ∧ Unknown` must be Unknown,
    // never a fabricated definitive FALSE. The sibling test above
    // (`unknown_left_and_evaluates_right_conjunct`) pins the LEFT-unknown order, which
    // always folded correctly; this pins the RIGHT-unknown order, which
    // `combine_conjunction` previously collapsed to FALSE via `.unwrap_or(False)`.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "gerku")); // dog ⟸ danlu ⟸ dog cycle
    assert_buf(&kb, make_assertion("rex", "mlatu")); // definitively-True conjunct

    let mut nodes = Vec::new();
    let mlatu_rex = pred(
        &mut nodes,
        "mlatu",
        vec![
            LogicalTerm::Constant("rex".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let dog_rex = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("rex".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = and(&mut nodes, mlatu_rex, dog_rex); // True (left) ∧ Unknown (right)
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };

    let (result, _trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    assert!(
        matches!(result, QueryResult::Unknown(UnknownReason::CycleCut)),
        "True ∧ Unknown(CycleCut) should be Unknown(CycleCut), got {result:?}"
    );
}

#[test]
fn false_or_unknown_right_is_unknown() {
    // Regression: `False ∨ Unknown` must be Unknown, never a fabricated FALSE — the
    // disjunction side of the same combiner bug.
    let kb = new_kb();
    assert_buf(&kb, make_universal("gerku", "danlu"));
    assert_buf(&kb, make_universal("danlu", "gerku")); // cycle → Unknown(CycleCut)

    let mut nodes = Vec::new();
    let absent = pred(
        &mut nodes,
        "blanu",
        vec![
            LogicalTerm::Constant("rex".into()),
            LogicalTerm::Unspecified,
        ],
    ); // no facts/rules for blanu → definitively False (CWA)
    let dog_rex = pred(
        &mut nodes,
        "gerku",
        vec![
            LogicalTerm::Constant("rex".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = or(&mut nodes, absent, dog_rex); // False (left) ∨ Unknown (right)
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };

    let (result, _trace) = kb.query_entailment_with_proof_inner(buf).unwrap();
    assert!(
        matches!(result, QueryResult::Unknown(UnknownReason::CycleCut)),
        "False ∨ Unknown(CycleCut) should be Unknown(CycleCut), got {result:?}"
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
            .any(|s| matches!(s.rule, ProofRule::ForallCounterexample { .. })),
        "depth-exceeded ForAll must not display a decided counterexample"
    );
}

#[test]
fn trace_naf_flag_false_when_inner_is_unknown() {
    // ¬gerku(alis) where gerku(alis) is Unknown(CycleCut), NOT definitively False.
    // The verdict is Unknown (negate_result yields Unknown(NafDependent) for an
    // undetermined inner — see negate_unknown_inner_yields_naf_dependent), and the
    // trace must NOT claim a NAF dependency: that PROOF flag marks a SUCCESSFUL NAF
    // (a Negation step that holds), which an Unknown inner is not (a boolean !false
    // would wrongly set it).
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
fn negate_unknown_inner_yields_naf_dependent() {
    // ¬gerku(alis) where gerku(alis) is Unknown(CycleCut) (gerku ⟸ danlu ⟸ gerku).
    // Negating an UNDETERMINED sub-goal depends on a NAF check that is itself
    // undetermined → the verdict reason is Unknown(NafDependent), the four-valued
    // contract's promised reason (previously never constructed — negate_result
    // forwarded the inner CycleCut). RED pre-fix.
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
    assert!(
        matches!(result, QueryResult::Unknown(UnknownReason::NafDependent)),
        "negating an Unknown sub-goal must yield Unknown(NafDependent), got {result:?}"
    );
    // Distinct from the PROOF flag: this is an UNDETERMINED NAF (no Negation step
    // holds:true), so has_naf_dependency stays false and the trace stays consistent.
    assert!(!trace.has_naf_dependency());
    assert_trace_consistent(&result, &trace);
}

#[test]
fn trace_exists_failed_only_when_all_definitively_false() {
    // Ground material conditionals gerku(x)⟸danlu(x) and danlu(x)⟸gerku(x) form a
    // positive cycle WITHOUT existential-import witnesses (unlike `ro lo` universals), so
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
            .any(|s| matches!(s.rule, ProofRule::ForallCounterexample { .. })),
        "a genuine False member must still be shown as a counterexample"
    );
}
