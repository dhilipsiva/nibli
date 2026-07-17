use super::*;

// ─── Disjunctive + deontic rule antecedents ─────────────────────────────────

#[test]
fn test_dnf_condition_clauses_splits_or_and_distributes_and() {
    // Or(P, Q) → two single-leaf clauses.
    let mut nodes = Vec::new();
    let p = pred(&mut nodes, "p", vec![]);
    let q = pred(&mut nodes, "q", vec![]);
    let o = or(&mut nodes, p, q);
    let buf = LogicBuffer {
        nodes,
        roots: vec![],
    };
    assert_eq!(
        dnf_condition_clauses(&buf, &[o], MAX_DNF_CLAUSES).unwrap(),
        vec![vec![p], vec![q]]
    );

    // Pure And → a single clause with both leaves.
    let mut nodes = Vec::new();
    let p = pred(&mut nodes, "p", vec![]);
    let q = pred(&mut nodes, "q", vec![]);
    let a = and(&mut nodes, p, q);
    let buf = LogicBuffer {
        nodes,
        roots: vec![],
    };
    assert_eq!(
        dnf_condition_clauses(&buf, &[a], MAX_DNF_CLAUSES).unwrap(),
        vec![vec![p, q]]
    );

    // And(Or(P,Q), R) → distributes to [P,R], [Q,R].
    let mut nodes = Vec::new();
    let p = pred(&mut nodes, "p", vec![]);
    let q = pred(&mut nodes, "q", vec![]);
    let r = pred(&mut nodes, "r", vec![]);
    let o = or(&mut nodes, p, q);
    let a = and(&mut nodes, o, r);
    let buf = LogicBuffer {
        nodes,
        roots: vec![],
    };
    assert_eq!(
        dnf_condition_clauses(&buf, &[a], MAX_DNF_CLAUSES).unwrap(),
        vec![vec![p, r], vec![q, r]]
    );

    // Nested Or(Or(P,Q),R) → three clauses.
    let mut nodes = Vec::new();
    let p = pred(&mut nodes, "p", vec![]);
    let q = pred(&mut nodes, "q", vec![]);
    let r = pred(&mut nodes, "r", vec![]);
    let o1 = or(&mut nodes, p, q);
    let o2 = or(&mut nodes, o1, r);
    let buf = LogicBuffer {
        nodes,
        roots: vec![],
    };
    assert_eq!(
        dnf_condition_clauses(&buf, &[o2], MAX_DNF_CLAUSES).unwrap(),
        vec![vec![p], vec![q], vec![r]]
    );
}

#[test]
fn test_dnf_condition_clauses_cap_rejects_blowup() {
    // (a∨b)∧(c∨d) expands to 4 clauses.
    let mut nodes = Vec::new();
    let a = pred(&mut nodes, "a", vec![]);
    let b = pred(&mut nodes, "b", vec![]);
    let c = pred(&mut nodes, "c", vec![]);
    let d = pred(&mut nodes, "d", vec![]);
    let o1 = or(&mut nodes, a, b);
    let o2 = or(&mut nodes, c, d);
    let conj = and(&mut nodes, o1, o2);
    let buf = LogicBuffer {
        nodes,
        roots: vec![],
    };
    assert!(
        dnf_condition_clauses(&buf, &[conj], 2).is_err(),
        "4 clauses must exceed a cap of 2 (fail closed)"
    );
    assert!(
        dnf_condition_clauses(&buf, &[conj], 4).is_ok(),
        "4 clauses fit a cap of 4"
    );
}

/// Build a DISJUNCTIVE event-decomposed universal rule (`ro lo X poi P ja Q cu R`):
///   ForAll(_v0, Or(
///     Not(Or(Exists(_ev0, P-event), Exists(_ev1, Q-event))),  // poi P ja Q restrictor
///     Exists(_ev2, R-event)                                    // consequent
///   ))
/// If `conjunctive`, the restrictor is `And` instead of `Or` (the `je` control).
fn make_branched_event_universal(
    r1: &str,
    r2: &str,
    consequent: &str,
    conjunctive: bool,
) -> LogicBuffer {
    let mut nodes = Vec::new();
    let event_pred = |nodes: &mut Vec<LogicNode>, rel: &str, ev: &str| -> u32 {
        let t = pred(nodes, rel, vec![LogicalTerm::Variable(ev.to_string())]);
        let role = pred(
            nodes,
            &format!("{}_x1", rel),
            vec![
                LogicalTerm::Variable(ev.to_string()),
                LogicalTerm::Variable("_v0".to_string()),
            ],
        );
        let a = and(nodes, t, role);
        exists(nodes, ev, a)
    };
    let p1 = event_pred(&mut nodes, r1, "_ev0");
    let p2 = event_pred(&mut nodes, r2, "_ev1");
    let restrictor = if conjunctive {
        and(&mut nodes, p1, p2)
    } else {
        or(&mut nodes, p1, p2)
    };
    let q = event_pred(&mut nodes, consequent, "_ev2");
    let neg = not(&mut nodes, restrictor);
    let disj = or(&mut nodes, neg, q);
    let root = forall(&mut nodes, "_v0", disj);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_disjunctive_antecedent_fires_either_branch() {
    // `ro lo X poi prami ja pendo cu danlu` — fires if X loves OR befriends.
    let kb = new_kb();
    assert_buf(
        &kb,
        make_branched_event_universal("prami", "pendo", "danlu", false),
    );
    assert_buf(&kb, make_event_assertion("alis", "prami")); // left disjunct
    assert!(
        query(&kb, make_event_query("alis", "danlu")),
        "left disjunct (prami) satisfied → disjunctive rule fires"
    );

    let kb2 = new_kb();
    assert_buf(
        &kb2,
        make_branched_event_universal("prami", "pendo", "danlu", false),
    );
    assert_buf(&kb2, make_event_assertion("bemo", "pendo")); // right disjunct
    assert!(
        query(&kb2, make_event_query("bemo", "danlu")),
        "right disjunct (pendo) satisfied → disjunctive rule fires"
    );
}

#[test]
fn test_disjunctive_antecedent_neither_false() {
    let kb = new_kb();
    assert_buf(
        &kb,
        make_branched_event_universal("prami", "pendo", "danlu", false),
    );
    assert_buf(&kb, make_event_assertion("alis", "prenu")); // neither prami nor pendo
    assert!(
        matches!(
            query_result(&kb, make_event_query("alis", "danlu")),
            QueryResult::False
        ),
        "neither disjunct satisfied → disjunctive rule does not fire"
    );
}

#[test]
fn test_disjunctive_registers_one_rule_per_branch() {
    let kb = new_kb();
    assert_buf(
        &kb,
        make_branched_event_universal("prami", "pendo", "danlu", false),
    );
    let inner = kb.inner.borrow();
    let danlu_rules = inner
        .universal_rules
        .get("danlu")
        .map(|v| v.len())
        .unwrap_or(0);
    assert_eq!(
        danlu_rules, 2,
        "a 2-way disjunctive antecedent registers one rule per disjunct"
    );
}

#[test]
fn test_conjunctive_je_still_requires_both() {
    // `poi prami je pendo` must require BOTH (the conjunctive control).
    let kb = new_kb();
    assert_buf(
        &kb,
        make_branched_event_universal("prami", "pendo", "danlu", true),
    );
    assert_buf(&kb, make_event_assertion("alis", "prami")); // only one
    assert!(
        matches!(
            query_result(&kb, make_event_query("alis", "danlu")),
            QueryResult::False
        ),
        "conjunctive restrictor requires both — one is not enough"
    );

    let kb2 = new_kb();
    assert_buf(
        &kb2,
        make_branched_event_universal("prami", "pendo", "danlu", true),
    );
    assert_buf(&kb2, make_event_assertion("bemo", "prami"));
    assert_buf(&kb2, make_event_assertion("bemo", "pendo")); // both
    assert!(
        query(&kb2, make_event_query("bemo", "danlu")),
        "conjunctive restrictor with both satisfied fires"
    );
}

/// Build a DEONTIC event-decomposed universal rule (raw-FOL only — surface
/// unreachable): `ForAll(_v0, Or(Not(<deontic>(Exists(_ev0, P-event))), R-event))`.
/// The deontic wrapper is transparent, so this compiles as `P(x) → R(x)`.
fn make_deontic_event_universal(
    restrictor: &str,
    consequent: &str,
    permitted: bool,
) -> LogicBuffer {
    let mut nodes = Vec::new();
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
    let deontic = {
        let id = nodes.len() as u32;
        nodes.push(if permitted {
            LogicNode::PermittedNode(p_exists)
        } else {
            LogicNode::ObligatoryNode(p_exists)
        });
        id
    };
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
    let neg = not(&mut nodes, deontic);
    let disj = or(&mut nodes, neg, q_exists);
    let root = forall(&mut nodes, "_v0", disj);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// `make_event_assertion` wrapped in a deontic node — asserts a FLAVORED event
/// fact (stored as `StoredFact::Obligatory`/`Permitted`).
fn make_deontic_event_assertion(entity: &str, predicate: &str, permitted: bool) -> LogicBuffer {
    let mut buf = make_event_assertion(entity, predicate);
    let inner_root = buf.roots[0];
    let id = buf.nodes.len() as u32;
    buf.nodes.push(if permitted {
        LogicNode::PermittedNode(inner_root)
    } else {
        LogicNode::ObligatoryNode(inner_root)
    });
    buf.roots = vec![id];
    buf
}

#[test]
fn test_deontic_obligatory_antecedent_is_flavor_exact() {
    // `Obligatory(P(x)) → R(x)` fires only on a stored Obligatory(P) fact — a
    // BARE P must not satisfy the deontic condition. (2026-07 fix: this test
    // used to pin the opposite "transparent" reading, chosen when the shape was
    // believed surface-unreachable; `ganai ei A gi B` reaches it from the
    // surface, so the transparent strip let a deontic condition fire on a bare
    // fact. Flavor-exact everywhere now, matching the fact-storage model.)
    let kb = new_kb();
    assert_buf(&kb, make_deontic_event_universal("bilga", "kajde", false));
    assert_buf(&kb, make_event_assertion("alis", "bilga"));
    assert!(
        matches!(
            query_result(&kb, make_event_query("alis", "kajde")),
            QueryResult::False
        ),
        "a bare inner fact must NOT fire a deontic antecedent"
    );

    // The Obligatory-flavored fact DOES fire it.
    let kb2 = new_kb();
    assert_buf(&kb2, make_deontic_event_universal("bilga", "kajde", false));
    assert_buf(&kb2, make_deontic_event_assertion("alis", "bilga", false));
    assert!(
        query(&kb2, make_event_query("alis", "kajde")),
        "the Obligatory-flavored fact fires the deontic antecedent"
    );

    // Negative control: inner condition absent entirely → no fire.
    let kb3 = new_kb();
    assert_buf(&kb3, make_deontic_event_universal("bilga", "kajde", false));
    assert_buf(&kb3, make_event_assertion("alis", "prenu"));
    assert!(
        matches!(
            query_result(&kb3, make_event_query("alis", "kajde")),
            QueryResult::False
        ),
        "deontic antecedent does not fire without the inner condition"
    );
}

#[test]
fn test_deontic_permitted_antecedent_is_flavor_exact() {
    let kb = new_kb();
    assert_buf(&kb, make_deontic_event_universal("curmi", "kajde", true));
    assert_buf(&kb, make_event_assertion("alis", "curmi"));
    assert!(
        matches!(
            query_result(&kb, make_event_query("alis", "kajde")),
            QueryResult::False
        ),
        "a bare inner fact must NOT fire a Permitted antecedent"
    );

    let kb2 = new_kb();
    assert_buf(&kb2, make_deontic_event_universal("curmi", "kajde", true));
    assert_buf(&kb2, make_deontic_event_assertion("alis", "curmi", true));
    assert!(
        query(&kb2, make_event_query("alis", "kajde")),
        "the Permitted-flavored fact fires the Permitted antecedent"
    );
}

// ─── Disjunctive rule CONCLUSIONS as integrity constraints ──────────────────

/// Build `ro lo R cu D1 ja D2` → ForAll(_v0, Or(Not(R(_v0)), Or(D1(_v0), D2(_v0)))).
/// A disjunctive HEAD — not a Horn clause; compiled to a `DisjunctiveConstraint`.
fn make_disjunctive_conclusion(restrictor: &str, d1: &str, d2: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let restrict = pred(
        &mut nodes,
        restrictor,
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg = not(&mut nodes, restrict);
    let q = pred(
        &mut nodes,
        d1,
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let r = pred(
        &mut nodes,
        d2,
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let disj = or(&mut nodes, q, r);
    let body = or(&mut nodes, neg, disj);
    let forall = {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::ForAllNode(("_v0".into(), body)));
        id
    };
    LogicBuffer {
        nodes,
        roots: vec![forall],
    }
}

#[test]
fn test_disjunctive_conclusion_registers_constraint() {
    let kb = new_kb();
    assert_buf(&kb, make_disjunctive_conclusion("gerku", "danlu", "xanlu"));
    let inner = kb.inner.borrow();
    assert_eq!(
        inner.disjunctive_constraints.len(),
        1,
        "a disjunctive conclusion registers one integrity constraint"
    );
    assert!(
        inner.universal_rules.get("danlu").is_none()
            && inner.universal_rules.get("xanlu").is_none(),
        "no Horn rule is registered for a disjunctive head (deriving a disjunct is unsound)"
    );
}

#[test]
fn test_disjunctive_conclusion_flags_when_all_disjuncts_denied() {
    let kb = new_kb();
    assert_buf(&kb, make_disjunctive_conclusion("gerku", "danlu", "xanlu"));
    assert_buf(&kb, make_assertion("rex", "gerku")); // P(rex) holds
    assert_buf(&kb, make_negated_assertion("rex", "danlu")); // na danlu(rex)
    assert_buf(&kb, make_negated_assertion("rex", "xanlu")); // na xanlu(rex)
    let v = kb.check_contradictions();
    assert!(
        v.iter()
            .any(|m| m.contains("Disjunctive constraint violated")),
        "P holds and both disjuncts explicitly denied → contradiction: {v:?}"
    );
}

#[test]
fn test_disjunctive_conclusion_one_disjunct_denied_no_violation() {
    let kb = new_kb();
    assert_buf(&kb, make_disjunctive_conclusion("gerku", "danlu", "xanlu"));
    assert_buf(&kb, make_assertion("rex", "gerku"));
    assert_buf(&kb, make_negated_assertion("rex", "danlu")); // only one denied
    assert!(
        kb.check_contradictions().is_empty(),
        "only one disjunct denied → the other could hold → no contradiction"
    );
}

#[test]
fn test_disjunctive_conclusion_antecedent_absent_no_violation() {
    let kb = new_kb();
    assert_buf(&kb, make_disjunctive_conclusion("gerku", "danlu", "xanlu"));
    // P (gerku) NOT asserted, though both disjuncts denied.
    assert_buf(&kb, make_negated_assertion("rex", "danlu"));
    assert_buf(&kb, make_negated_assertion("rex", "xanlu"));
    assert!(
        kb.check_contradictions().is_empty(),
        "antecedent does not hold → no contradiction"
    );
}

#[test]
fn test_disjunctive_conclusion_retraction_clears_constraint() {
    let kb = new_kb();
    let rule_id = assert_id(
        &kb,
        make_disjunctive_conclusion("gerku", "danlu", "xanlu"),
        "disjunctive rule",
    );
    assert_buf(&kb, make_assertion("rex", "gerku"));
    assert_buf(&kb, make_negated_assertion("rex", "danlu"));
    assert_buf(&kb, make_negated_assertion("rex", "xanlu"));
    assert!(
        !kb.check_contradictions().is_empty(),
        "precondition: the constraint is violated before retraction"
    );
    // Retracting the rule (skolem-free) must trigger a rebuild that drops the constraint.
    kb.retract_fact_inner(rule_id).unwrap();
    assert!(
        kb.inner.borrow().disjunctive_constraints.is_empty(),
        "retracting the disjunctive rule clears the constraint registry"
    );
    assert!(
        kb.check_contradictions().is_empty(),
        "no constraint → no contradiction after retraction"
    );
}

/// Build a MIXED conclusion head `∀x. R(x) → (P(x) ∧ (Q(x) ∨ S(x)))`:
///   ForAll(_v0, Or(Not(R(_v0)), And(P(_v0), Or(Q(_v0), S(_v0)))))
/// Soundly splits into a Horn rule (R → P) + a `DisjunctiveConstraint` (R → Q ∨ S).
/// Not surface-reachable — `gi'e` desugars at the SENTENCE level (head repeated,
/// so `ro lo … gi'e …` is a conjunction of two universals, never one rule with a
/// compound conclusion). A raw-FOL / forward-compat shape.
fn make_mixed_conclusion(restrictor: &str, p: &str, q: &str, s: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let v = || {
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ]
    };
    let restrict = pred(&mut nodes, restrictor, v());
    let neg = not(&mut nodes, restrict);
    let p_atom = pred(&mut nodes, p, v());
    let q_atom = pred(&mut nodes, q, v());
    let s_atom = pred(&mut nodes, s, v());
    let disj = or(&mut nodes, q_atom, s_atom);
    let conj = and(&mut nodes, p_atom, disj);
    let body = or(&mut nodes, neg, conj);
    let root = forall(&mut nodes, "_v0", body);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_mixed_conclusion_registers_horn_and_constraint() {
    // ∀x. gerku(x) → (broda(x) ∧ (danlu(x) ∨ xanlu(x))) splits into a Horn rule
    // (gerku → broda) + one DisjunctiveConstraint (gerku → danlu ∨ xanlu).
    let kb = new_kb();
    assert_buf(
        &kb,
        make_mixed_conclusion("gerku", "broda", "danlu", "xanlu"),
    );
    let inner = kb.inner.borrow();
    assert!(
        inner.universal_rules.get("broda").is_some(),
        "the non-Or conjunct compiles to a Horn rule"
    );
    assert_eq!(
        inner.disjunctive_constraints.len(),
        1,
        "the Or conjunct compiles to one integrity constraint"
    );
    assert!(
        inner.universal_rules.get("danlu").is_none()
            && inner.universal_rules.get("xanlu").is_none(),
        "no Horn rule is registered for a disjunct (deriving one is unsound)"
    );
}

#[test]
fn test_mixed_conclusion_derives_horn_and_fires_constraint() {
    let kb = new_kb();
    let rule_id = assert_id(
        &kb,
        make_mixed_conclusion("gerku", "broda", "danlu", "xanlu"),
        "mixed",
    );
    assert_buf(&kb, make_assertion("rex", "gerku"));
    // The Horn conjunct derives broda(rex).
    assert!(
        query(&kb, make_query("rex", "broda")),
        "the Horn conjunct derives broda(rex)"
    );
    // The constraint fires when both disjuncts are explicitly denied.
    assert_buf(&kb, make_negated_assertion("rex", "danlu"));
    assert_buf(&kb, make_negated_assertion("rex", "xanlu"));
    assert!(
        kb.check_contradictions()
            .iter()
            .any(|m| m.contains("Disjunctive constraint violated")),
        "gerku(rex) holds + both disjuncts denied → contradiction"
    );
    // Retracting the mixed-head assertion drops BOTH the constraint and the Horn rule.
    kb.retract_fact_inner(rule_id).unwrap();
    let inner = kb.inner.borrow();
    assert!(
        inner.disjunctive_constraints.is_empty(),
        "retraction clears the constraint"
    );
    assert!(
        inner.universal_rules.get("broda").is_none(),
        "retraction clears the Horn rule"
    );
}

#[test]
fn test_mixed_conclusion_conservative_p_check_misses_derived_antecedent() {
    // (sub-part a) `check_contradictions` §6 binds the antecedent P by STORE MEMBERSHIP
    // only. A rule-DERIVED gerku(rex) does NOT trigger the constraint — sound +
    // conservative (it can only MISS a contradiction, never falsely flag one).
    let kb = new_kb();
    assert_buf(&kb, make_universal("mlatu", "gerku")); // mlatu → dog (DERIVES P)
    assert_buf(
        &kb,
        make_mixed_conclusion("gerku", "broda", "danlu", "xanlu"),
    );
    assert_buf(&kb, make_assertion("rex", "mlatu")); // derives dog(rex); NOT stored as dog
    assert_buf(&kb, make_negated_assertion("rex", "danlu"));
    assert_buf(&kb, make_negated_assertion("rex", "xanlu"));
    assert!(
        kb.check_contradictions().is_empty(),
        "a DERIVED antecedent does not trigger the disjunctive constraint (store-membership only)"
    );
}

#[test]
fn test_mixed_conclusion_dirty_horn_atom_rejected() {
    // A Not-bearing retained (Horn) atom — the shape `jo`/`ju` predicate-connective
    // expansions produce — is not a flat predicate, so the mixed head stays
    // fail-closed (its remainder is not a Horn clause).
    let kb = new_kb();
    let mut nodes = Vec::new();
    let v = || {
        vec![
            LogicalTerm::Variable("_v0".into()),
            LogicalTerm::Unspecified,
        ]
    };
    let restrict = pred(&mut nodes, "gerku", v());
    let neg_r = not(&mut nodes, restrict);
    let broda = pred(&mut nodes, "broda", v());
    let not_broda = not(&mut nodes, broda); // dirty: Not-bearing Horn atom
    let danlu = pred(&mut nodes, "danlu", v());
    let xanlu = pred(&mut nodes, "xanlu", v());
    let disj = or(&mut nodes, danlu, xanlu);
    let conj = and(&mut nodes, not_broda, disj);
    let body = or(&mut nodes, neg_r, conj);
    let root = forall(&mut nodes, "_v0", body);
    let buf = LogicBuffer {
        nodes,
        roots: vec![root],
    };
    assert!(
        kb.assert_fact_inner(buf, String::new()).is_err(),
        "a Not-bearing Horn atom must fail closed"
    );
    assert!(
        kb.inner.borrow().disjunctive_constraints.is_empty(),
        "the failed assertion leaves no constraint (rollback)"
    );
}

/// Build an event-decomposed group `∃ev. name(ev) ∧ name_x1(ev, _v0)`.
fn event_group(nodes: &mut Vec<LogicNode>, name: &str, ev: &str) -> u32 {
    let t = pred(nodes, name, vec![LogicalTerm::Variable(ev.into())]);
    let role = pred(
        nodes,
        &format!("{name}_x1"),
        vec![
            LogicalTerm::Variable(ev.into()),
            LogicalTerm::Variable("_v0".into()),
        ],
    );
    let conj = and(nodes, t, role);
    exists(nodes, ev, conj)
}

#[test]
fn test_mixed_conclusion_event_decomposed_no_registry_pollution() {
    // The realistic (event-decomposed) mixed head — what a rule-conclusion-level GIhA
    // would lower to (the shipped `gi'e` desugars at sentence level instead):
    // ∀x. gerku(x) → (broda(x) ∧ (danlu(x) ∨ xanlu(x))), every predicate a Neo-Davidsonian
    // group with a DISTINCT event var. Verifies the Horn part compiles AND the Or-part's
    // conclusion event existentials are filtered out of the GLOBAL skolem_fn_registry.
    let kb = new_kb();
    let mut nodes = Vec::new();
    let r_grp = event_group(&mut nodes, "gerku", "_ev0"); // restrictor (condition)
    let neg = not(&mut nodes, r_grp);
    let p_grp = event_group(&mut nodes, "broda", "_ev1"); // Horn conclusion
    let q_grp = event_group(&mut nodes, "danlu", "_ev2"); // disjunct
    let s_grp = event_group(&mut nodes, "xanlu", "_ev3"); // disjunct
    let disj = or(&mut nodes, q_grp, s_grp);
    let conj = and(&mut nodes, p_grp, disj);
    let body = or(&mut nodes, neg, conj);
    let root = forall(&mut nodes, "_v0", body);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes,
            roots: vec![root],
        },
    );
    let inner = kb.inner.borrow();
    assert!(
        inner.universal_rules.get("broda").is_some(),
        "the Horn conjunct (broda) compiles"
    );
    assert_eq!(
        inner.disjunctive_constraints.len(),
        1,
        "one constraint for the Or part"
    );
    // Only the Horn conjunct's event skolem registers; the Or-part's danlu/xanlu event
    // existentials are filtered out (without the filter this would be 3).
    assert_eq!(
        inner.skolem_fn_registry.len(),
        1,
        "Or-part event existentials must not pollute skolem_fn_registry (got {})",
        inner.skolem_fn_registry.len()
    );
}

#[test]
fn verbose_flag_defaults_off_and_survives_reset_and_clone() {
    // The diagnostic-verbosity flag gates the informational stdout prints
    // (`[Rule]`/`[Skolem]`/`[Constraint] Registered`). It is CONFIGURATION, not
    // derived state: a silent default, flipped by nibli-pipeline (nibli-host) + the native
    // REPL, and it must survive `reset()` (so a UI-style reset-and-reassert cycle
    // does not silently re-enable diagnostics) and a clone (hypothetical queries).
    let kb = KnowledgeBase::new();
    assert!(
        !kb.is_verbose(),
        "verbose must default OFF (silent library)"
    );

    kb.set_verbose(true);
    assert!(kb.is_verbose(), "set_verbose(true) must enable diagnostics");

    kb.reset().expect("reset");
    assert!(
        kb.is_verbose(),
        "reset() must PRESERVE verbose — it is configuration, not derived state"
    );

    // The Clone (used by hypothetical-query snapshots) must carry verbose through.
    let cloned = kb.inner.borrow().clone();
    assert!(cloned.verbose, "Clone must preserve verbose");

    kb.set_verbose(false);
    assert!(
        !kb.is_verbose(),
        "set_verbose(false) must disable diagnostics"
    );
}
