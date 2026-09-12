//! Stratum-ordered materialisation ([`crate::materialize`]).
//!
//! These are SURFACE tests (`compile_surface`), not flat ones, and that is not a style
//! choice: materialisation is defined on the event-decomposed shape — it projects
//! `∃ev. rel(ev) ∧ rel_x1(ev,a) ∧ …` back to `rel(a, …)` — so a hand-built flat buffer
//! exercises none of it. See the FLAT vs SURFACE note at the top of `tests.rs`.
//!
//! The load-bearing property is the FIRST test: materialisation must never change a
//! verdict, only how fast one is reached. Everything else here pins a way that could
//! stop being true.

use super::*;

#[test]
fn warming_rule_plan_performs_no_query_and_shares_only_immutable_planning() {
    let run = |warm: bool| {
        let kb = new_kb();
        assert_buf(&kb, compile_surface("person(Ara)."));
        assert_buf(
            &kb,
            compile_surface("all $x: person($x) & ~rotten($x) -> fit($x)."),
        );
        let before = {
            let inner = kb.inner.borrow();
            (
                inner.fact_counter,
                inner.fact_registry.len(),
                inner
                    .fact_store
                    .all_facts()
                    .cloned()
                    .collect::<HashSet<_>>(),
            )
        };
        if warm {
            kb.prepare_materialization_plan().unwrap();
            let plan = kb
                .inner
                .borrow()
                .materialization_plan
                .borrow()
                .clone()
                .unwrap();
            kb.prepare_materialization_plan().unwrap();
            let inner = kb.inner.borrow();
            assert!(Arc::ptr_eq(
                &plan,
                inner.materialization_plan.borrow().as_ref().unwrap()
            ));
            assert!(inner.materialized.borrow().is_none());
            assert!(inner.pred_cache.borrow().is_empty());
            assert_eq!(
                before,
                (
                    inner.fact_counter,
                    inner.fact_registry.len(),
                    inner
                        .fact_store
                        .all_facts()
                        .cloned()
                        .collect::<HashSet<_>>()
                )
            );
        }
        let mut results = Vec::new();
        kb.with_assumptions(&[], |snapshot| {
            if warm {
                assert!(Arc::ptr_eq(
                    kb.inner
                        .borrow()
                        .materialization_plan
                        .borrow()
                        .as_ref()
                        .unwrap(),
                    snapshot
                        .inner
                        .borrow()
                        .materialization_plan
                        .borrow()
                        .as_ref()
                        .unwrap()
                ));
                assert!(snapshot.inner.borrow().materialized.borrow().is_none());
            }
            results.push(query_result(snapshot, compile_surface("fit(Ara).")));
            assert_buf(snapshot, compile_surface("rotten(Ara)."));
            results.push(query_result(snapshot, compile_surface("fit(Ara).")));
        })
        .unwrap();
        results.push(query_result(&kb, compile_surface("fit(Ara).")));
        results
    };
    let cold = run(false);
    assert_eq!(
        cold,
        vec![QueryResult::True, QueryResult::False, QueryResult::True]
    );
    assert_eq!(run(true), cold);
}

#[test]
fn shared_join_indexes_do_not_confuse_full_delta_or_later_rounds() {
    let kb = new_kb();
    for line in [
        "parent(Ara, Bel).",
        "parent(Bel, Cyd).",
        "parent(Cyd, Dana).",
        "all $x: all $y: parent($x, $y) -> earlier($x, $y).",
        "all $x: all $y: all $z: earlier($x, $y) & earlier($y, $z) -> earlier($x, $z).",
    ] {
        assert_buf(&kb, compile_surface(line));
    }
    let names = ["Ara", "Bel", "Cyd", "Dana", "Eve"];
    for length in [4, 5] {
        if length == 5 {
            assert_buf(&kb, compile_surface("parent(Dana, Eve)."));
        }
        // Force complete materialization instead of exercising the independent
        // positive-query/backward-chaining selection policy.
        assert_eq!(
            query_result(&kb, compile_surface("~earlier(Eve, Ara).")),
            QueryResult::True
        );
        for (from, from_name) in names.iter().enumerate() {
            for (to, to_name) in names.iter().enumerate() {
                let query = format!("earlier({from_name}, {to_name}).");
                let expected = if from < to && to < length {
                    QueryResult::True
                } else {
                    QueryResult::False
                };
                assert_eq!(
                    query_result(&kb, compile_surface(&query)),
                    expected,
                    "{query}, chain length {length}"
                );
            }
        }
    }
}

#[test]
fn reusable_rule_plan_tracks_mutations_and_keeps_snapshot_isolation() {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("person(Ara)."));
    assert_buf(
        &kb,
        compile_surface("all $x: person($x) & ~rotten($x) -> fit($x)."),
    );
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::True
    );
    let plan = kb
        .inner
        .borrow()
        .materialization_plan
        .borrow()
        .clone()
        .unwrap();
    assert_buf(&kb, compile_surface("person(Bel)."));
    assert_eq!(
        query_result(&kb, compile_surface("fit(Bel).")),
        QueryResult::True
    );
    assert!(Arc::ptr_eq(
        &plan,
        kb.inner
            .borrow()
            .materialization_plan
            .borrow()
            .as_ref()
            .unwrap()
    ));
    kb.with_assumptions(&[compile_surface("rotten(Ara).")], |snapshot| {
        assert_eq!(
            query_result(snapshot, compile_surface("fit(Ara).")),
            QueryResult::False
        );
        assert!(Arc::ptr_eq(
            &plan,
            snapshot
                .inner
                .borrow()
                .materialization_plan
                .borrow()
                .as_ref()
                .unwrap()
        ));
    })
    .unwrap();
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::True
    );
    let rule = assert_id(
        &kb,
        compile_surface("all $x: person($x) -> rotten($x)."),
        "new rule",
    );
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::False
    );
    assert!(!Arc::ptr_eq(
        &plan,
        kb.inner
            .borrow()
            .materialization_plan
            .borrow()
            .as_ref()
            .unwrap()
    ));
    kb.retract_fact(rule).unwrap();
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::True
    );
    assert_buf(&kb, compile_surface("rotten(Bel)."));
    assert_buf(&kb, compile_surface("Ara = Bel."));
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::False
    );
    kb.reset().unwrap();
    assert_buf(&kb, compile_surface("person(Ara)."));
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::False
    );
}

/// Both engines, same KB, same queries. Returns `(with_materialisation, without)`.
fn both_ways(kb_lines: &[&str], queries: &[&str]) -> (Vec<QueryResult>, Vec<QueryResult>) {
    let run = |on: bool| -> Vec<QueryResult> {
        let kb = new_kb();
        kb.set_materialization(on);
        for l in kb_lines {
            assert_buf(&kb, compile_surface(l));
        }
        queries
            .iter()
            .map(|q| query_result(&kb, compile_surface(q)))
            .collect()
    };
    (run(true), run(false))
}

/// A stratified-NAF KB shaped like utopia's Article 3/4 pair: a wide multi-variable
/// rule concludes `false`, and a merit rule reads it under `~`.
const AUDIT_KB: &[&str] = &[
    "person(Ara).",
    "person(Bel).",
    "person(Cyd).",
    "teaches(Ara, Cyd).",
    "teaches(Bel, Cyd).",
    "judge(Ara, Bel).",
    "capture(Ara, Bel).",
    "all $a: all $x: judge($a, $x) & capture($a, $x) & ~deceive($a, $x) -> false($x).",
    "all $t: all $s: teaches($t, $s) & ~false($t) -> reward($t).",
];

/// THE property. Materialisation is an optimisation: it may make a previously
/// non-definitive verdict definitive (that is the completeness gain), but it must never
/// turn one definitive verdict into a different one.
#[test]
fn naf_verdicts_are_unchanged_by_materialization() {
    let queries = [
        "reward(Ara).", // Ara is not voided → merit rule fires
        "reward(Bel).", // Bel IS voided by Ara's audit → blocked
        "false(Bel).",  // the voided party
        "false(Ara).",  // nobody audited Ara
        "reward(Cyd).", // teaches nobody
    ];
    let (on, off) = both_ways(AUDIT_KB, &queries);
    for ((q, a), b) in queries.iter().zip(&on).zip(&off) {
        if a == b {
            continue;
        }
        assert!(
            !b.is_definitive(),
            "materialisation changed a DEFINITIVE verdict for {q}: {b:?} → {a:?}"
        );
        assert!(
            a.is_definitive(),
            "materialisation made {q} LESS definitive: {b:?} → {a:?}"
        );
    }
    // And the verdicts are the ones the KB actually entails.
    assert_eq!(on[0], QueryResult::True, "Ara is unvoided and teaches");
    assert_eq!(on[1], QueryResult::False, "Bel is voided, so no reward");
    assert_eq!(on[2], QueryResult::True, "Bel was audited");
    assert_eq!(on[3], QueryResult::False, "Ara was not audited");
}

/// THE deliberate behaviour change (GUARANTEES §Completeness).
///
/// A saturated extension is complete regardless of `max_chain_depth`, so a NAF whose
/// positive would need a chain past the bound now answers definitively where it used to
/// return `ResourceExceeded(Depth)`. That is a completeness GAIN — non-definitive
/// becoming definitive — never a flip between two definitive verdicts, which is what
/// the first test in this file pins.
///
/// Its positive twin is `positive_goal_past_the_depth_bound_becomes_definitive`. Since
/// both halves are shortcut, `depth_boundary_contract` (tests/traces.rs) now runs with
/// materialisation OFF — it pins the SEARCH contract, and a complete extension is exactly
/// what removes the search.
#[test]
fn naf_over_a_chain_past_the_depth_bound_becomes_definitive() {
    let kb_lines = [
        "dog(Rex).",
        "all $x: dog($x) -> animal($x).",
        "all $x: animal($x) -> alive($x).",
        "all $x: alive($x) -> beautiful($x).",
        // `beautiful` is 3 rule hops from the `dog` fact; read it under `~`.
        "all $x: person($x) & ~beautiful($x) -> rotten($x).",
        "person(Rex).",
    ];
    let verdict = |on: bool| {
        let kb = new_kb();
        kb.set_materialization(on);
        // A bound too small for the 3-hop chain the NAF has to refute.
        kb.set_max_chain_depth(1).unwrap();
        for l in kb_lines {
            assert_buf(&kb, compile_surface(l));
        }
        query_result(&kb, compile_surface("rotten(Rex)."))
    };
    let off = verdict(false);
    assert!(
        !off.is_definitive(),
        "without materialisation a NAF past the depth bound must be non-definitive, got {off:?}"
    );
    let on = verdict(true);
    assert!(
        on.is_definitive(),
        "with materialisation the saturated extension decides it regardless of the bound, got {on:?}"
    );
    // Rex IS beautiful (via the chain), so `~beautiful(Rex)` fails and `rotten` does not hold.
    assert_eq!(on, QueryResult::False);
}

/// A saturation is a claim about the KB's CONTENT, so a later assertion must drop it.
/// Getting this wrong is not a stale-cache annoyance: the NAF would keep answering TRUE
/// for a positive the new fact just made derivable.
#[test]
fn a_later_assertion_invalidates_the_saturation() {
    let kb = new_kb();
    for l in [
        "person(Ara).",
        "all $x: person($x) & ~rotten($x) -> fit($x).",
    ] {
        assert_buf(&kb, compile_surface(l));
    }
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::True,
        "nothing makes Ara rotten yet"
    );
    // This is the fact the stale extension would not know about.
    assert_buf(&kb, compile_surface("rotten(Ara)."));
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::False,
        "the new `rotten` fact must block the NAF — a stale saturation would still say TRUE"
    );
}

/// The retraction twin. `rebuild_inner` clears the saturation directly rather than
/// relying on its callers pairing with `invalidate_pred_cache`, because
/// `KnowledgeBase::rebuild` does not.
#[test]
fn retraction_invalidates_the_saturation() {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("person(Ara)."));
    assert_buf(
        &kb,
        compile_surface("all $x: person($x) & ~rotten($x) -> fit($x)."),
    );
    let rotten = assert_id(&kb, compile_surface("rotten(Ara)."), "rotten");
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::False
    );
    kb.retract_fact_inner(rotten).unwrap();
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::True,
        "retracting the blocker must re-open the NAF — a saturation surviving the rebuild would not"
    );
}

/// `KnowledgeBase::rebuild` is the one rebuild entry point that does NOT invalidate the
/// predicate cache, so the saturation must be dropped inside `rebuild_inner` itself.
/// Without that, this query answers from a knowledge base that no longer exists.
#[test]
fn a_bare_rebuild_drops_the_saturation() {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("person(Ara)."));
    assert_buf(
        &kb,
        compile_surface("all $x: person($x) & ~rotten($x) -> fit($x)."),
    );
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::True
    );
    assert!(
        kb.inner.borrow().materialized.borrow().is_some(),
        "the query should have built a saturation"
    );
    kb.rebuild().unwrap();
    assert!(
        kb.inner.borrow().materialized.borrow().is_none(),
        "rebuild must drop the saturation itself, not rely on caller discipline"
    );
}

/// The projection does not model tense, so a flavoured relation must be REFUSED
/// rather than saturated with the flavour
/// silently dropped (which would merge `past P(x)` and `P(x)` into one tuple).
#[test]
fn a_flavoured_relation_is_refused_and_still_answers_correctly() {
    let kb_lines = [
        "person(Ara).",
        "past rotten(Ara).",
        "all $x: person($x) & ~rotten($x) -> fit($x).",
    ];
    let (on, off) = both_ways(&kb_lines, &["fit(Ara)."]);
    assert_eq!(
        on, off,
        "a flavoured KB must fall back, giving byte-identical verdicts"
    );
    let kb = new_kb();
    for l in kb_lines {
        assert_buf(&kb, compile_surface(l));
    }
    let _ = query_result(&kb, compile_surface("fit(Ara)."));
    let (complete, _) = kb.materialization_report().unwrap();
    assert!(
        !complete.iter().any(|r| r == "rotten"),
        "a relation with a Past fact must not be reported complete: {complete:?}"
    );
}

#[test]
fn bare_temporal_non_lifting_is_identical_with_materialization_on_or_off() {
    let kb_lines = ["all $x: dog($x) -> animal($x).", "past dog(Ara)."];
    let (on, off) = both_ways(&kb_lines, &["past animal(Ara)."][..]);
    assert_eq!(on, vec![QueryResult::False]);
    assert_eq!(on, off, "materialization must not invent temporal lifting");
}

#[test]
fn explicit_temporal_rule_falls_back_without_changing_the_verdict() {
    let kb_lines = ["all $x: past dog($x) -> past animal($x).", "past dog(Ara)."];
    let (on, off) = both_ways(&kb_lines, &["past animal(Ara)."][..]);
    assert_eq!(on, vec![QueryResult::True]);
    assert_eq!(on, off, "the exact backward-chain fallback must agree");

    let kb = new_kb();
    for line in kb_lines {
        assert_buf(&kb, compile_surface(line));
    }
    let _ = query_result(&kb, compile_surface("past animal(Ara)."));
    // A successful exact entailment proof stays lazy. Find requires a complete positive
    // extension, so it asks the materializer to inspect the relation and records why the
    // flavored rule cannot be saturated.
    let _ = kb
        .query_find_inner(compile_surface("past animal(Ara)."))
        .unwrap();
    let (complete, refused) = kb.materialization_report().unwrap();
    assert!(
        !complete.iter().any(|relation| relation == "animal"),
        "a flavored rule head must not be reported complete: {complete:?}"
    );
    assert!(
        refused.iter().any(|(relation, why)| {
            relation == "animal" && why.contains("tense/deontic flavour")
        }),
        "the report must disclose the flavored-rule refusal: {refused:?}"
    );
}

#[test]
fn explicit_temporal_naf_never_uses_the_bare_materialized_extension() {
    let kb_lines = [
        "fit(every person where past ~rotten(it)).",
        "person(Ara).",
        "rotten(Ara).",
    ];
    let (on, off) = both_ways(&kb_lines, &["fit(Ara)."][..]);
    assert_eq!(
        off,
        vec![QueryResult::True],
        "a bare rotten witness must not block `past ~rotten`"
    );
    assert_eq!(
        on, off,
        "materialization must refuse the flavored NAF group and fall back"
    );
}

/// `du` makes fact lookup modulo union-find, so a plain set-membership test on a
/// projected tuple could miss an equivalent variant and report "no witness" wrongly.
/// The whole KB is refused when any equivalence class exists.
#[test]
fn equality_classes_refuse_the_whole_kb() {
    let kb_lines = [
        "person(Ara).",
        "rotten(Bel).",
        "Ara = Bel.",
        "all $x: person($x) & ~rotten($x) -> fit($x).",
    ];
    let (on, off) = both_ways(&kb_lines, &["fit(Ara)."]);
    assert_eq!(
        on, off,
        "with `du` present the engine must fall back, not answer from a projection"
    );
    let kb = new_kb();
    for l in kb_lines {
        assert_buf(&kb, compile_surface(l));
    }
    let _ = query_result(&kb, compile_surface("fit(Ara)."));
    let (complete, _) = kb.materialization_report().unwrap();
    assert!(
        complete.is_empty(),
        "no relation may be saturated while equivalence classes exist: {complete:?}"
    );
}

/// The report is the only way a knowledge base can tell whether its slow `~p(x)`
/// actually got the lookup, so it must name what was saturated.
#[test]
fn the_report_names_what_was_saturated() {
    let kb = new_kb();
    for l in AUDIT_KB {
        assert_buf(&kb, compile_surface(l));
    }
    let _ = query_result(&kb, compile_surface("reward(Ara)."));
    let (complete, refused) = kb.materialization_report().unwrap();
    assert!(
        complete.iter().any(|r| r == "false"),
        "`false` is read under `~` and is projectable — expected it saturated: \
         complete={complete:?} refused={refused:?}"
    );
    // Every refusal carries a human-readable reason, never an empty string.
    assert!(refused.iter().all(|(_, why)| !why.is_empty()));
}

/// A shallow, negation-free positive query should take its indexed backward proof without
/// first constructing the whole relation extension. Positive materialisation remains the
/// fallback past the depth horizon (pinned by the next test).
#[test]
fn a_shallow_positive_proof_stays_unsaturated() {
    let kb = new_kb();
    for l in ["dog(Rex).", "all $x: dog($x) -> animal($x)."] {
        assert_buf(&kb, compile_surface(l));
    }
    assert!(query(&kb, compile_surface("animal(Rex).")));
    let (complete, refused) = kb.materialization_report().unwrap();
    assert!(
        !complete.iter().any(|r| r == "animal"),
        "a definitive shallow proof must not eagerly saturate `animal`: \
         complete={complete:?} refused={refused:?}"
    );
}

/// The positive twin of `naf_over_a_chain_past_the_depth_bound_becomes_definitive`, and
/// the reason `depth_boundary_contract` had to be scoped: a completed extension decides
/// regardless of `max_chain_depth`, so a positive goal past the bound now answers instead
/// of returning `ResourceExceeded(Depth)`. Non-definitive → definitive, the sound
/// direction; the differential gate is what forbids the other one.
#[test]
fn positive_goal_past_the_depth_bound_becomes_definitive() {
    let kb_lines = [
        "dog(Rex).",
        "all $x: dog($x) -> animal($x).",
        "all $x: animal($x) -> alive($x).",
        "all $x: alive($x) -> beautiful($x).",
    ];
    let verdict = |on: bool| {
        let kb = new_kb();
        kb.set_materialization(on);
        kb.set_max_chain_depth(1).unwrap();
        for l in kb_lines {
            assert_buf(&kb, compile_surface(l));
        }
        query_result(&kb, compile_surface("beautiful(Rex)."))
    };
    let off = verdict(false);
    assert!(
        !off.is_definitive(),
        "a 3-hop chain under a depth-1 bound must be non-definitive without \
         materialisation, got {off:?}"
    );
    assert_eq!(
        verdict(true),
        QueryResult::True,
        "the saturated extension decides it regardless of the bound"
    );
}

/// A proof-traced query keeps the BACKWARD-CHAINING path: a lookup has no derivation, and
/// the trace contract assumes one. Gating that per-sink rather than per-query is what
/// broke `flat_vs_surface::transitive_chain_true` in development — phase 1 resolved at
/// depth 1 by lookup, then phase 2 rebuilt the trace by chaining at that same depth and
/// could not reach it, turning a TRUE into `ResourceExceeded(Depth)`.
#[test]
fn a_traced_query_agrees_with_its_untraced_twin() {
    let kb = new_kb();
    for l in [
        "dog(Rex).",
        "all $x: dog($x) -> animal($x).",
        "all $x: animal($x) -> alive($x).",
    ] {
        assert_buf(&kb, compile_surface(l));
    }
    let untraced = query_result(&kb, compile_surface("alive(Rex)."));
    let (traced, trace) = kb
        .query_entailment_with_proof_inner(compile_surface("alive(Rex)."))
        .unwrap();
    assert_eq!(untraced, QueryResult::True);
    assert_eq!(
        traced, untraced,
        "traced and untraced verdicts must not diverge"
    );
    assert!(
        trace
            .steps
            .get(trace.root as usize)
            .is_some_and(|s| s.holds),
        "a TRUE verdict must carry a holding root step, not a not-found leaf"
    );
}

/// Recursion through a positive cycle is one stratum, evaluated to a fixpoint — the
/// case a non-recursive "evaluate each rule once" saturation would silently truncate,
/// under-deriving the extension and turning a NAF FALSE into a wrong TRUE.
#[test]
fn a_recursive_positive_relation_saturates_to_its_fixpoint() {
    let kb_lines = [
        "person(Ara).",
        "parent(Ara, Bel).",
        "parent(Bel, Cyd).",
        "parent(Cyd, Dee).",
        // Transitive closure: `judge` is recursive through itself (a POSITIVE cycle,
        // which stratification accepts and which must be run to a fixpoint).
        "all $x: all $y: parent($x, $y) -> judge($x, $y).",
        "all $x: all $y: all $z: judge($x, $y) & parent($y, $z) -> judge($x, $z).",
        // Read the closure under `~`.
        "all $x: person($x) & ~judge($x, Dee) -> rotten($x).",
    ];
    let (on, off) = both_ways(&kb_lines, &["rotten(Ara).", "judge(Ara, Dee)."]);
    assert_eq!(on, off, "recursion must not change under materialisation");
    assert_eq!(
        on[1],
        QueryResult::True,
        "Ara reaches Dee in three hops of the transitive closure"
    );
    assert_eq!(
        on[0],
        QueryResult::False,
        "so `~judge(Ara, Dee)` fails — a truncated fixpoint would wrongly say TRUE"
    );
}

/// A purely positive cycle with no seed is non-definitive under cycle-cut backward
/// search, but its least fixpoint is the complete empty extension. Lazy positive
/// materialisation must therefore retry every non-definitive result, not only a depth
/// exhaustion; it must never retry (and potentially replace) a definitive FALSE.
#[test]
fn an_empty_positive_cycle_becomes_definitive_after_lazy_fallback() {
    let kb_lines = [
        "all $x: cat($x) -> animal($x).",
        "all $x: animal($x) -> cat($x).",
        "person(Ara).",
    ];
    let (on, off) = both_ways(&kb_lines, &["cat(Ara)."][..]);
    assert!(
        !off[0].is_definitive(),
        "cycle-cut search without materialisation must remain non-definitive: {off:?}"
    );
    assert_eq!(
        on,
        vec![QueryResult::False],
        "the saturated least fixpoint is complete and empty"
    );
}

/// The kill switch is what makes the ON/OFF differential expressible, and it must take
/// effect immediately rather than at the next mutation.
#[test]
fn toggling_materialization_off_drops_the_saturation() {
    let kb = new_kb();
    for l in AUDIT_KB {
        assert_buf(&kb, compile_surface(l));
    }
    let _ = query_result(&kb, compile_surface("reward(Ara)."));
    assert!(kb.inner.borrow().materialized.borrow().is_some());
    kb.set_materialization(false);
    assert!(
        kb.inner.borrow().materialized.borrow().is_none(),
        "turning the switch off must drop the extension now, not later"
    );
    assert!(!kb.is_materialization());
    // And the verdict is unchanged.
    assert_eq!(
        query_result(&kb, compile_surface("reward(Ara).")),
        QueryResult::True
    );
}

/// Configuration, not derived state — `reset()` wipes the KB but keeps the mode, exactly
/// like `strict` and `existential_import`.
#[test]
fn the_materialization_mode_survives_reset() {
    let kb = new_kb();
    kb.set_materialization(false);
    kb.reset().unwrap();
    assert!(
        !kb.is_materialization(),
        "the mode is session configuration, not KB content"
    );
}

/// THE BUG THE DIFFERENTIAL CAUGHT (`mat_seed4` / `mat_seed35`, 2026-07-31).
///
/// `eligible_relations` closes downward over relations it cannot PROJECT. But a relation
/// can also become unusable later, when `seed_edb` refuses its STORED FACTS — a `past`
/// fact, a role gap, an arity clash. Those refusals are invisible to the eligibility
/// analysis, so a rule reading `~rotten` was still saturated while `rotten`'s extension
/// was ABSENT. An absent extension reads as "nothing derived", so the negated condition
/// passed and the head was derived for everyone: a definitive WRONG TRUE, the exact
/// failure this module exists to prevent.
///
/// Here `rotten` carries a Past fact, so it cannot be projected; `fit` reads it under `~`
/// and must therefore be refused too, not silently completed over a hole.
#[test]
fn a_relation_whose_negated_dependency_is_unseedable_is_refused_not_completed() {
    let kb_lines = [
        "person(Ara).",
        "rotten(Ara).",
        // Makes `rotten` unprojectable: the projection detects the flavor and
        // refuses the relation wholesale rather than dropping it.
        "past rotten(Ara).",
        "all $x: person($x) & ~rotten($x) -> fit($x).",
    ];
    let (on, off) = both_ways(&kb_lines, &["fit(Ara)."]);
    assert_eq!(
        on[0],
        QueryResult::False,
        "Ara IS rotten, so `~rotten(Ara)` fails and `fit` must not hold"
    );
    assert_eq!(on, off, "materialisation must not change this verdict");

    let kb = new_kb();
    for l in kb_lines {
        assert_buf(&kb, compile_surface(l));
    }
    let _ = query_result(&kb, compile_surface("fit(Ara)."));
    let (complete, refused) = kb.materialization_report().unwrap();
    assert!(
        !complete.iter().any(|r| r == "fit"),
        "`fit` reads an unseedable relation under `~` — it must NOT be complete: \
         complete={complete:?}"
    );
    assert!(
        refused
            .iter()
            .any(|(rel, why)| rel == "fit" && why.contains("rotten")),
        "the refusal must NAME the dependency that caused it: refused={refused:?}"
    );
    // And the reason for `rotten` itself must point at the DATA, not at a rule — the two
    // are different repairs.
    assert!(
        refused
            .iter()
            .any(|(rel, why)| rel == "rotten" && why.contains("stored fact")),
        "refused={refused:?}"
    );
}

/// THE ABSTRACTION PROJECTION, and the firewall it must not break.
///
/// `entitled(every person, event { P() }).` compiles to a head carrying an abstraction
/// referent — `event(sk_1(x))` and `__abs_<id>(sk_1(x))`, two arity-1 atoms on ONE event
/// term, plus `entitled_x2(sk_3(x), sk_1(x))`, the referent in a role VALUE. Untreated
/// that is `AmbiguousAnchor` + `SkolemInValue`, and EVERY abstraction-bearing rule sits
/// outside the saturation.
///
/// The projection maps the referent to its marker relation name as an opaque constant —
/// the identity that crosses compiles is that NAME, not any term. What makes this safe to
/// materialise is a property of the compiled form, not of the refusal: the abstraction
/// body's event term is `sk_2(Unspecified)`, INDEPENDENT of the universal, so its role
/// values are `Unspecified` and the body projects to a tuple about nobody. An entitlement
/// therefore cannot fabricate the actuality it guarantees.
#[test]
fn an_entitlement_is_materialised_without_fabricating_the_actuality() {
    let kb_lines = ["entitled(every person, event { eats() }).", "person(Adam)."];
    let (on, off) = both_ways(
        &kb_lines,
        &[
            "entitled(Adam, event { eats() }).",
            "eats(Adam).",
            "eats(some person).",
            "entitled(Adam, event { choose() }).",
            "entitled(Adam, fact { eats() }).",
        ],
    );
    assert_eq!(on, off, "the projection must not change any verdict");
    assert_eq!(on[0], QueryResult::True, "the entitlement must still MATCH");
    assert_eq!(
        on[1],
        QueryResult::False,
        "the actuality must still MISS — an entitlement does not feed anyone"
    );
    assert_eq!(on[2], QueryResult::False, "nor for anyone else");
    assert_eq!(
        on[3],
        QueryResult::False,
        "a different body is a different lossless identity"
    );
    assert_eq!(
        on[4],
        QueryResult::False,
        "abstraction kind survives projection into the marker identity"
    );

    // And it is genuinely materialised, not passing by falling back to the chainer.
    let kb = new_kb();
    for l in kb_lines {
        assert_buf(&kb, compile_surface(l));
    }
    let _ = kb.query_find_inner(compile_surface("eats(Adam).")).unwrap();
    let (complete, refused) = kb.materialization_report().unwrap();
    assert!(
        complete.iter().any(|r| r == "eats"),
        "`eats` should be saturable now: complete={complete:?} refused={refused:?}"
    );
    // The typing markers must be REFUSED, never merely omitted: `is_edb` is
    // "no rule and not refused", and an omitted marker would be marked complete over an
    // empty seed, so `~event(x)` would answer TRUE where the chainer answers FALSE.
    assert!(
        refused.iter().any(|(r, _)| r == "event"),
        "the `event` typing anchor must be refused, not left to look like EDB: \
         refused={refused:?}"
    );
    assert!(
        refused.iter().any(|(r, _)| r.starts_with("__abs_")),
        "the abstraction marker must be refused too: refused={refused:?}"
    );
}

const OPAQUE_QUERY_WITH_UNRELATED_PATH_KB: &[&str] = &[
    "derived_only(\"entitled\").",
    "entitled(every person, event { eats() }).",
    "person(Adam).",
    "earlier(NodeA, NodeB).",
    "earlier(NodeB, NodeC).",
    "earlier(NodeC, NodeD).",
    "earlier(NodeD, NodeE).",
    "earlier(NodeE, NodeF).",
    "earlier(NodeF, NodeG).",
    "earlier(NodeG, NodeH).",
    "earlier(NodeH, NodeI).",
    "all $first: all $middle: all $last: earlier($first, $middle) & earlier($middle, $last) & ~($first = $last) -> earlier($first, $last).",
    "later(MomentA, MomentB).",
    "later(MomentB, MomentC).",
    "later(MomentC, MomentD).",
    "all $first: all $middle: all $last: later($first, $middle) & later($middle, $last) & ~($first = $last) -> later($first, $last).",
];

/// A query must pay only for its own materialisation cone. The binary path relation is
/// deliberately unrelated to the opaque entitlement: globally saturating it turns a
/// constant-time exact match into a transitive-closure workload before reasoning even
/// reaches the query.
///
/// The stable performance threshold is structural, not a wall clock: an unrelated
/// relation gets exactly ZERO tuple-unification attempts. Eight seed edges make the
/// control non-trivial (the full closure has 36 tuples, 28 of them derived), while the
/// follow-up query proves that lazy targeting does not disable transitive semantics.
#[test]
fn an_opaque_query_does_no_work_for_an_unrelated_binary_transitive_relation() {
    let kb = new_kb();
    for line in OPAQUE_QUERY_WITH_UNRELATED_PATH_KB {
        assert_buf(&kb, compile_surface(line));
    }

    // The target collector itself must honor abstraction opacity. The exact query can
    // resolve before materialization runs, so checking only the later report would be a
    // hollow test of this boundary.
    let opaque_query = compile_surface("entitled(Adam, event { eats() }).");
    let mut positive_roots = HashSet::new();
    crate::materialize::collect_query_relations(&opaque_query, &mut positive_roots);
    assert!(positive_roots.contains("entitled"));
    assert!(
        !positive_roots.contains("eats"),
        "quoted content is opaque identity, not a positive actuality root: {positive_roots:?}"
    );
    let mut negative_roots = HashSet::new();
    crate::materialize::collect_negated_relations(
        &compile_surface("~entitled(Adam, event { eats() })."),
        &mut negative_roots,
    );
    assert!(negative_roots.contains("entitled"));
    assert!(
        !negative_roots.contains("eats"),
        "quoted content stays opaque under NAF too: {negative_roots:?}"
    );

    assert_eq!(query_result(&kb, opaque_query), QueryResult::True);
    let (complete, refused) = kb.materialization_report().unwrap();
    let unrelated_attempts = kb.materialization_tuple_bind_attempts("earlier");
    assert!(
        !complete.iter().any(|r| r == "entitled"),
        "an exact backward proof must not eagerly saturate even its positive root: \
         complete={complete:?} refused={refused:?}"
    );
    assert!(
        !complete.iter().any(|r| r == "earlier"),
        "an unrelated path closure must stay lazy: complete={complete:?}, \
         earlier tuple-unification attempts={unrelated_attempts}"
    );
    assert!(
        !complete.iter().any(|r| r == "eats"),
        "quoted abstraction content is identity, not an actuality target: complete={complete:?}"
    );
    assert_eq!(
        unrelated_attempts, 0,
        "the exact regression threshold is zero unrelated tuple-unification attempts"
    );
    assert_eq!(
        kb.materialization_tuple_bind_attempts("later"),
        0,
        "a second unrelated closure must also perform exactly zero work"
    );
    assert_eq!(
        kb.materialization_tuple_bind_attempts("entitled"),
        0,
        "a definitive indexed proof must perform no positive saturation work"
    );

    // A later query on the SAME unchanged KB must expand the cached target set rather
    // than treating the first query's empty saturation as globally complete. Force the
    // ordinary proof past its one-level horizon so this also exercises lazy positive
    // materialisation rather than merely backward-chaining the short fixture.
    kb.set_max_chain_depth(1).unwrap();
    assert_eq!(
        query_result(&kb, compile_surface("earlier(NodeA, NodeI).")),
        QueryResult::True
    );
    let (complete, refused) = kb.materialization_report().unwrap();
    assert!(
        complete.iter().any(|r| r == "earlier"),
        "the newly requested path relation must now be complete: complete={complete:?} refused={refused:?}"
    );
    assert!(
        kb.materialization_tuple_bind_attempts("earlier") > 0,
        "the follow-up path query must exercise the transitive materialiser"
    );
    let closure_size = {
        let inner = kb.inner.borrow();
        let materialized = inner.materialized.borrow();
        materialized
            .as_ref()
            .and_then(|m| m.ext.get("earlier"))
            .map(HashSet::len)
            .unwrap_or_default()
    };
    assert_eq!(
        closure_size, 36,
        "eight ordered edges must retain their exact 8 + 28 tuple transitive closure"
    );

    // A second non-empty target proves the cache is a union, not merely a replacement.
    assert_eq!(
        query_result(&kb, compile_surface("later(MomentA, MomentD).")),
        QueryResult::True
    );
    let (complete, _) = kb.materialization_report().unwrap();
    assert!(complete.iter().any(|r| r == "earlier"));
    assert!(complete.iter().any(|r| r == "later"));
    {
        let inner = kb.inner.borrow();
        let materialized = inner.materialized.borrow();
        let requested = &materialized.as_ref().unwrap().requested;
        assert!(requested.contains("earlier"));
        assert!(requested.contains("later"));
    }

    // Mutation invalidates the union. Re-requesting only the first root must not expose
    // the stale second closure as complete.
    assert_buf(&kb, compile_surface("later(MomentD, MomentE)."));
    assert_eq!(
        query_result(&kb, compile_surface("earlier(NodeA, NodeI).")),
        QueryResult::True
    );
    let (complete, _) = kb.materialization_report().unwrap();
    assert!(complete.iter().any(|r| r == "earlier"));
    // `later` may now STAY complete across the mutation — an in-cone insert is
    // folded in incrementally (`resume_with_delta`) instead of dropping the
    // cache. What must never happen is a STALE extension being served, so the
    // requirement is pinned on the verdict: the newly asserted tuple has to be
    // visible through the materialised `later` extension.
    assert_eq!(
        query_result(&kb, compile_surface("~later(MomentD, MomentE).")),
        QueryResult::False,
        "the delta must be folded in; a stale `later` extension would answer TRUE"
    );
}

/// The backward-chaining twin of the materialisation regression. With saturation off,
/// the opaque marker is a mandatory relation-scoped anchor; candidate collection must
/// use it to bound the generic `event` anchor before walking every dependent-Skolem
/// family contributed by unrelated rules.
#[test]
fn an_opaque_query_bounds_generic_event_candidate_generation() {
    let kb = new_kb();
    kb.set_materialization(false);
    for line in OPAQUE_QUERY_WITH_UNRELATED_PATH_KB {
        assert_buf(&kb, compile_surface(line));
    }

    crate::kb::reset_entailment_candidate_cartesian_steps();
    crate::reasoning::reset_global_candidate_cartesian_steps();
    assert_eq!(
        query_result(&kb, compile_surface("entitled(Adam, event { eats() }).")),
        QueryResult::True
    );
    let global_steps = crate::reasoning::global_candidate_cartesian_steps();
    assert_eq!(
        global_steps, 0,
        "the exact catastrophic-work threshold is zero full-registry Cartesian visits, \
         got {global_steps}"
    );
    let unrelated_skolem_steps = crate::kb::entailment_candidate_cartesian_steps("person_x1");
    assert_eq!(
        unrelated_skolem_steps, 0,
        "bound role arguments must specialize dependent Skolems before Cartesian \
         expansion; exact threshold is zero, got {unrelated_skolem_steps}"
    );
}

/// Fixture-bound regression for the composed path: the queried opaque projection is
/// available only after proving its subject through a high-arity event-decomposed rule.
/// Shared role variables must constrain each next event before the rule search reaches a
/// complete assignment. At release commit 5cec800 this exact fixture evaluated 61,098
/// complete assignments; the repaired search evaluates 94, below the checked ceiling.
#[test]
fn an_opaque_projection_joins_a_derived_subject_chain_before_cartesian_expansion() {
    let kb = new_kb();
    kb.set_materialization(false);
    for line in [
        "derived_only(\"fit\").",
        "derived_only(\"believe\").",
        "earlier(NoiseA, NoiseB).",
        "earlier(NoiseC, NoiseD).",
        "earlier(NoiseE, NoiseF).",
        "earlier(NoiseG, NoiseH).",
        "earlier(NoiseI, NoiseJ).",
        "earlier(NoiseK, NoiseL).",
        "earlier(NoiseM, NoiseN).",
        "earlier(NoiseO, NoiseP).",
        "owns(Goal, LiveA).",
        "earlier(LiveA, LiveB).",
        "earlier(LiveB, LiveC).",
        "earlier(LiveC, LiveD).",
        "earlier(LiveD, LiveE).",
        "dog(LiveE).",
        "all $subject: all $a: all $b: all $c: all $d: all $e: owns($subject, $a) & earlier($a, $b) & earlier($b, $c) & earlier($c, $d) & earlier($d, $e) & dog($e) -> fit($subject).",
        "all $subject: fit($subject) -> believe($subject, event { eats() }).",
    ] {
        assert_buf(&kb, compile_surface(line));
    }

    crate::kb::reset_entailment_candidate_cartesian_steps();
    crate::reasoning::reset_global_candidate_cartesian_steps();
    crate::reasoning::reset_rule_event_search_leaf_attempts();
    assert_eq!(
        query_result(
            &kb,
            compile_surface("believe(Goal, event { eats() }) & fit(Goal).")
        ),
        QueryResult::True,
        "one query process must prove both derived standing and its opaque projection"
    );
    let leaf_attempts = crate::reasoning::rule_event_search_leaf_attempts();
    assert!(
        leaf_attempts <= 128,
        "fixture-bound threshold is at most 128 complete rule-event assignments, got {leaf_attempts}"
    );
    let anchor_cartesian_steps = crate::kb::entailment_candidate_cartesian_total_steps();
    assert!(
        anchor_cartesian_steps <= 1_024,
        "fixture-bound ceiling is 1,024 relation-scoped anchor Cartesian visits, got {anchor_cartesian_steps}"
    );
    assert_eq!(
        crate::reasoning::global_candidate_cartesian_steps(),
        0,
        "the composed path must not fall back to the global candidate registry"
    );
    assert_eq!(
        kb.materialization_tuple_bind_attempts("earlier"),
        0,
        "the composed positive path must remain backward-chained, not globally materialized"
    );
}

/// The composed projection must not exhaust every possible subject witness before the
/// ordinary depth-bounded chainer can report that its one positive antecedent needs a
/// complete extension. The fallback requests exactly that antecedent's relation cone;
/// the opaque conclusion, its quoted body, and unrelated path relations stay lazy.
#[test]
fn an_opaque_projection_materializes_only_its_depth_bound_subject_cone() {
    let kb = new_kb();
    kb.set_max_chain_depth(1).unwrap();
    for line in [
        "derived_only(\"fit\").",
        "derived_only(\"believe\").",
        "dog(Goal).",
        "all $subject: dog($subject) -> animal($subject).",
        "all $subject: animal($subject) -> fit($subject).",
        "all $subject: fit($subject) -> believe($subject, event { eats() }).",
        "earlier(NodeA, NodeB).",
        "earlier(NodeB, NodeC).",
        "all $first: all $middle: all $last: earlier($first, $middle) & earlier($middle, $last) -> earlier($first, $last).",
    ] {
        assert_buf(&kb, compile_surface(line));
    }

    assert_eq!(
        query_result(
            &kb,
            compile_surface("believe(Goal, event { eats() }) & fit(Goal).")
        ),
        QueryResult::True,
        "one process must complete the depth-bound standing proof and use it in the opaque projection"
    );
    let (complete, refused) = kb.materialization_report().unwrap();
    assert!(
        complete.iter().any(|relation| relation == "fit"),
        "the exact positive antecedent must be completed: complete={complete:?} refused={refused:?}"
    );
    for unrelated in ["believe", "earlier", "eats"] {
        assert!(
            !complete.iter().any(|relation| relation == unrelated),
            "the fallback must remain relation-scoped; unexpectedly completed {unrelated}: {complete:?}"
        );
    }
    assert_eq!(
        kb.materialization_tuple_bind_attempts("earlier"),
        0,
        "the exact unrelated-work threshold is zero path tuple-unification attempts"
    );
}

fn force_abstraction_digest(buffer: &mut LogicBuffer, digest: &str) {
    assert_eq!(digest.len(), 16);
    let digest = u64::from_str_radix(digest, 16).unwrap();
    let mut rewritten = 0;
    for node in &mut buffer.nodes {
        if let LogicNode::Predicate((relation, _)) = node
            && relation.starts_with("__abs_v1_")
        {
            let (_, key_hex) = relation
                .strip_prefix("__abs_v1_")
                .unwrap()
                .split_once('_')
                .unwrap();
            let key: Vec<u8> = key_hex
                .as_bytes()
                .chunks_exact(2)
                .map(|pair| {
                    let pair = std::str::from_utf8(pair).unwrap();
                    u8::from_str_radix(pair, 16).unwrap()
                })
                .collect();
            *relation = nibli_types::abstraction::encode_v1_with_digest(&key, digest);
            rewritten += 1;
        }
    }
    assert_eq!(
        rewritten, 1,
        "collision seam must rewrite exactly one abstraction marker"
    );
}

fn abstraction_marker_relation(buffer: &LogicBuffer) -> String {
    let markers: Vec<String> = buffer
        .nodes
        .iter()
        .filter_map(|node| match node {
            LogicNode::Predicate((relation, _)) if relation.starts_with("__abs_v1_") => {
                Some(relation.clone())
            }
            _ => None,
        })
        .collect();
    assert_eq!(markers.len(), 1);
    markers.into_iter().next().unwrap()
}

#[test]
fn abstraction_digest_prefix_is_canonicalized_from_the_full_key() {
    let mut asserted = compile_surface("believe(me, fact { goes(Adam) }).");
    let mut same_query = compile_surface("believe(me, fact { goes(Adam) }).");
    let mut different_query = compile_surface("believe(me, fact { goes(Bel) }).");
    force_abstraction_digest(&mut asserted, "0000000000000000");
    force_abstraction_digest(&mut same_query, "ffffffffffffffff");
    force_abstraction_digest(&mut different_query, "0000000000000000");

    let kb = new_kb();
    assert_buf(&kb, asserted);
    assert!(
        query(&kb, same_query),
        "the same full key must match even when supplied digest prefixes differ"
    );
    assert!(
        query_false(&kb, different_query),
        "equal digest prefixes must not conflate different proposition bodies"
    );
}

#[test]
fn equal_abstraction_digest_prefixes_do_not_match_distinct_full_keys() {
    let mut first = compile_surface("believe(me, fact { goes(Adam) }).");
    let mut second = compile_surface("believe(me, fact { goes(Bel) }).");
    force_abstraction_digest(&mut first, "0000000000000000");
    force_abstraction_digest(&mut second, "0000000000000000");
    let first_relation = abstraction_marker_relation(&first);
    let second_relation = abstraction_marker_relation(&second);
    assert_ne!(first_relation, second_relation);
    assert_eq!(
        &first_relation[.."__abs_v1_".len() + 16],
        &second_relation[.."__abs_v1_".len() + 16],
        "the seam must create a real digest-prefix collision"
    );

    let referent = GroundTerm::Constant("opaque".to_string());
    let stored = StoredFact::Bare(GroundFact::new(first_relation, vec![referent.clone()]));
    let colliding_query = StoredFact::Bare(GroundFact::new(second_relation, vec![referent]));
    let kb = new_kb();
    let mut inner = kb.inner.borrow_mut();
    assert_typed_fact(stored.clone(), &mut inner);
    assert!(typed_fact_is_stored(&stored, &inner));
    assert!(
        !typed_fact_is_stored(&colliding_query, &inner),
        "the core matcher must compare the complete key, not the equal digest prefix"
    );
}

#[test]
fn legacy_hash_only_abstraction_markers_fail_closed_on_every_buffer_path() {
    let mut legacy = compile_surface("believe(me, fact { goes(Adam) }).");
    for node in &mut legacy.nodes {
        if let LogicNode::Predicate((relation, _)) = node
            && relation.starts_with("__abs_v1_")
        {
            *relation = "__abs_0123456789abcdef".to_string();
        }
    }

    let kb = new_kb();
    let assertion_error = kb
        .assert_fact_inner(legacy.clone(), "legacy persisted buffer".to_string())
        .expect_err("hash-only assertion replay must be rejected");
    assert!(assertion_error.contains("recompile/re-import"));
    let query_error = kb
        .query_entailment_inner(legacy.clone())
        .expect_err("hash-only entailment queries must be rejected");
    assert!(query_error.contains("legacy hash-only"));
    let proof_error = kb
        .query_entailment_with_proof_inner(legacy.clone())
        .expect_err("hash-only proof queries must be rejected");
    assert!(proof_error.contains("legacy hash-only"));
    let find_error = kb
        .query_find_inner(legacy)
        .expect_err("hash-only find/count/aggregate queries must be rejected");
    assert!(find_error.contains("legacy hash-only"));
}

#[test]
fn malformed_and_unknown_abstraction_markers_fail_closed() {
    for malformed_relation in [
        "__abs_v2_0123456789abcdef_00",
        "__abs_v1_short_00",
        "__abs_v1_0123456789abcdef_0",
        "__abs_v1_0123456789abcdef_FF",
    ] {
        let mut malformed = compile_surface("believe(me, fact { goes(Adam) }).");
        for node in &mut malformed.nodes {
            if let LogicNode::Predicate((relation, _)) = node
                && relation.starts_with("__abs_v1_")
            {
                *relation = malformed_relation.to_string();
            }
        }
        let error = new_kb()
            .assert_fact_inner(malformed, "malformed marker".to_string())
            .expect_err("unknown/malformed markers must never enter the fact store");
        assert!(
            error.contains("unsupported or malformed opaque-abstraction marker"),
            "unexpected error for {malformed_relation}: {error}"
        );
    }

    let mut wrong_arity = compile_surface("believe(me, fact { goes(Adam) }).");
    for node in &mut wrong_arity.nodes {
        if let LogicNode::Predicate((relation, args)) = node
            && relation.starts_with("__abs_v1_")
        {
            args.push(LogicalTerm::Unspecified);
        }
    }
    let arity_error = new_kb()
        .assert_fact_inner(wrong_arity, "non-unary marker".to_string())
        .expect_err("an internal marker must remain unary");
    assert!(arity_error.contains("unary Predicate") && arity_error.contains("arity 2"));

    let mut compute_marker = compile_surface("believe(me, fact { goes(Adam) }).");
    let marker_index = compute_marker
        .nodes
        .iter()
        .position(|node| {
            matches!(node, LogicNode::Predicate((relation, _)) if relation.starts_with("__abs_v1_"))
        })
        .expect("fixture must contain a marker");
    let (relation, args) = match compute_marker.nodes[marker_index].clone() {
        LogicNode::Predicate(pair) => pair,
        _ => unreachable!("selected a Predicate marker"),
    };
    compute_marker.nodes[marker_index] = LogicNode::ComputeNode((relation, args));
    let kb = new_kb();
    let assertion_error = kb
        .assert_fact_inner(compute_marker.clone(), "compute marker".to_string())
        .expect_err("an internal marker must never be asserted as a ComputeNode");
    assert!(
        assertion_error.contains("never ComputeNode"),
        "marker validation must run before treating anything as opaque: {assertion_error}"
    );
    assert_eq!(
        kb.next_fact_id().unwrap(),
        0,
        "malformed marker rejection must precede id allocation"
    );
    let query_error = kb
        .query_entailment_inner(compute_marker)
        .expect_err("an internal marker must never be queried as a ComputeNode");
    assert!(query_error.contains("never ComputeNode"));
}

#[test]
fn nested_abstraction_identity_keeps_the_complete_inner_proposition() {
    let asserted = "believe(me, fact { believe(Bel, fact { goes(Adam) }) }).";
    let same = asserted;
    let different_body = "believe(me, fact { believe(Bel, fact { goes(Gia) }) }).";
    let different_kind = "believe(me, fact { believe(Bel, event { goes(Adam) }) }).";

    let kb = new_kb();
    assert_buf(&kb, compile_surface(asserted));
    assert!(query(&kb, compile_surface(same)));
    assert!(query_false(&kb, compile_surface(different_body)));
    assert!(query_false(&kb, compile_surface(different_kind)));
    assert!(
        query_false(&kb, compile_surface("believe(Bel, fact { goes(Adam) }).")),
        "the nested abstraction body must remain opaque"
    );
}

/// A MATERIALISED relation must flip when an assertion changes what it derives.
///
/// This is the engine-side twin of the consuming project's release sequence
/// (`13-the-one-thing-taken.pins.nibli`: `dwell(Hano)` TRUE at :46, `free(Hano).` at :72,
/// `dwell(Hano)` FALSE at :101). Before the abstraction projection those relations were
/// REFUSED, so they were backward-chained and invalidation was irrelevant to them; now
/// they are saturated and the flip is a live test that the extension is dropped.
///
/// Distinct from `a_later_assertion_invalidates_the_saturation` in asserting that the
/// relation really was COMPLETE on both sides — otherwise a silent fallback would make
/// this pass while pinning nothing.
#[test]
fn a_materialised_relation_flips_across_an_assertion() {
    let kb = new_kb();
    for l in [
        "person(Ara).",
        "all $x: person($x) & ~rotten($x) -> fit($x).",
    ] {
        assert_buf(&kb, compile_surface(l));
    }
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::True
    );
    let (before, _) = kb.materialization_report().unwrap();
    assert!(
        before.iter().any(|r| r == "fit"),
        "`fit` must be materialised for this to test anything: {before:?}"
    );

    assert_buf(&kb, compile_surface("rotten(Ara)."));
    assert_eq!(
        query_result(&kb, compile_surface("fit(Ara).")),
        QueryResult::False,
        "the new fact must block the NAF — a surviving extension would still say TRUE"
    );
    let (after, _) = kb.materialization_report().unwrap();
    assert!(
        after.iter().any(|r| r == "fit"),
        "and it must be re-saturated, not silently demoted to fallback: {after:?}"
    );
}

// ─── Stratification report (the machine-readable dump) ───────────────────────

/// Load a shipped corpus into a fresh KB, skipping lines that are not plain KB text.
fn kb_from_corpus(src: &str) -> KnowledgeBase {
    let kb = new_kb();
    for raw in src.lines() {
        let line = raw.trim();
        if line.is_empty()
            || line.starts_with('#')
            || line.starts_with(':')
            || line.starts_with('?')
        {
            continue;
        }
        if let Ok(ast) = nibli_kr::parse_checked(line)
            && let Ok(mut buf) = nibli_semantics::compile_from_ast(ast)
        {
            transform_compute_nodes(&mut buf, &default_compute_predicates());
            let _ = kb.assert_fact(buf, line.to_string());
        }
    }
    kb
}

#[test]
fn strata_surface_projection_is_lossless() {
    // `stratification_report` collapses event-decomposed role predicates (`p_x1`) onto
    // their anchor (`p`). That is only honest if every member of a decomposed atom lands
    // in the SAME stratum — which it must, since the roles and the anchor are conditions
    // and conclusions of exactly the same rules and therefore carry identical dependency
    // sets. This pins it on the shipped corpora rather than trusting the argument: if it
    // ever fails, the report is silently picking a stratum and the collapse must go.
    for (name, src) in [
        ("utopia", include_str!("../../../utopia.nibli")),
        ("gdpr", include_str!("../../../gdpr.nibli")),
        (
            "drug-interactions",
            include_str!("../../../drug-interactions.nibli"),
        ),
        (
            "determinism",
            include_str!("../../../determinism-corpus.nibli"),
        ),
    ] {
        let kb = kb_from_corpus(src);
        let inner = kb.inner.borrow();
        let strata = crate::materialize::compute_strata(&inner.pred_dep_graph);
        let mut by_surface: std::collections::BTreeMap<&str, std::collections::BTreeSet<usize>> =
            std::collections::BTreeMap::new();
        for (raw, lvl) in &strata {
            by_surface
                .entry(crate::materialize::surface_relation(raw))
                .or_default()
                .insert(*lvl);
        }
        for (surface, levels) in &by_surface {
            assert_eq!(
                levels.len(),
                1,
                "{name}: `{surface}` spans strata {levels:?} — the anchor and its role \
                 predicates disagree, so collapsing them loses information"
            );
        }
    }
}

#[test]
fn stratification_report_is_stable_and_well_formed() {
    let kb = kb_from_corpus(include_str!("../../../utopia.nibli"));
    let rows = kb.stratification_report().unwrap();
    assert!(!rows.is_empty(), "utopia must produce a non-empty report");

    // Deterministic: same KB, same bytes. `pred_dep_graph` is a HashMap, so this is the
    // property a consumer diffing across runs actually depends on.
    let again = kb.stratification_report().unwrap();
    assert_eq!(rows, again, "two reports off one KB must be identical");

    // Sorted by predicate, edges sorted and deduplicated.
    let names: Vec<&str> = rows.iter().map(|r| r.predicate.as_str()).collect();
    let mut sorted = names.clone();
    sorted.sort_unstable();
    assert_eq!(names, sorted, "rows must be sorted by predicate");
    for r in &rows {
        let mut e = r.edges.clone();
        e.sort();
        e.dedup();
        assert_eq!(
            e, r.edges,
            "{}: edges must be sorted and deduplicated",
            r.predicate
        );
        // No role predicate survives the surface projection.
        assert_eq!(
            crate::materialize::surface_relation(&r.predicate),
            r.predicate,
            "a role predicate leaked into the report"
        );
    }

    // base/derived agrees with "a rule concludes it", the definition the dump documents.
    let inner = kb.inner.borrow();
    let derived: std::collections::BTreeSet<&str> = inner
        .universal_rules
        .keys()
        .map(|k| crate::materialize::surface_relation(k))
        .collect();
    for r in &rows {
        assert_eq!(
            r.base,
            !derived.contains(r.predicate.as_str()),
            "{}: base/derived disagrees with the rule-head set",
            r.predicate
        );
    }

    // utopia reads `false` under negation, so a negative edge must be present somewhere —
    // otherwise the polarity column is uniformly `+` and pins nothing.
    assert!(
        rows.iter().any(|r| r.edges.iter().any(|e| e.negative)),
        "utopia has NAF rules; the report must mark at least one negative edge"
    );
}

#[test]
fn a_negative_edge_raises_the_stratum_it_reads_from() {
    // The property the whole dump exists to communicate: a predicate read under `~` must
    // sit STRICTLY below the predicate reading it, and a positive edge must not raise it.
    let kb = new_kb();
    for line in [
        "person(Adam).",
        "all $x: person($x) & ~home($x) -> prisoner($x).",
        "all $x: prisoner($x) -> reward($x).",
    ] {
        assert_buf(&kb, compile_surface(line));
    }
    let rows = kb.stratification_report().unwrap();
    let get = |p: &str| {
        rows.iter()
            .find(|r| r.predicate == p)
            .unwrap_or_else(|| panic!("{p}"))
    };

    let home = get("home");
    let prisoner = get("prisoner");
    let watched = get("reward");
    assert!(
        prisoner.stratum > home.stratum,
        "a NAF read must raise the reader's stratum: prisoner={} home={}",
        prisoner.stratum,
        home.stratum
    );
    assert_eq!(
        watched.stratum, prisoner.stratum,
        "a POSITIVE edge must not raise the stratum"
    );
    assert!(home.base, "`home` is concluded by no rule");
    assert!(!prisoner.base, "`prisoner` is concluded by a rule");
    assert!(
        prisoner.edges.iter().any(|e| e.to == "home" && e.negative),
        "the prisoner -> home edge must be marked negative: {:?}",
        prisoner.edges
    );
    assert!(
        watched
            .edges
            .iter()
            .any(|e| e.to == "prisoner" && !e.negative),
        "the watched -> prisoner edge must be marked positive: {:?}",
        watched.edges
    );
}

// ─── The join loop's binding paths ───────────────────────────────────────────
//
// `eval_rule`'s inner `walk` extends a binding environment once per candidate
// tuple per join level. Everything below pins what happens when a candidate is
// REJECTED PART-WAY THROUGH — after it has already bound something.
//
// These exist because an audit of every positive body template in the shipped
// corpora, `pins/`, this file, and `materialize_diff`'s generator found that
// path had NO coverage at all: nothing anywhere rejects on a literal constant
// after an insert, no atom anywhere repeats a variable, and nothing materialises
// a relation wider than arity 2. The real KBs this engine is used on are made of
// exactly those shapes.
//
// ORDER SENSITIVITY, stated once. Extension tuples live in a `HashSet` whose
// iteration order is seeded per process, so a stranded binding only changes the
// result when the poisoned tuple happens to be visited before the good one.
// Every test below is therefore over-provisioned with decoys, and the honest
// backstop is running them in many processes (see the plan's determinism loop),
// not a single green run.

/// Canonical rendering of the saturated extension: relations sorted, tuples
/// sorted by their `Debug` form, one `relation :: tuple` per line.
///
/// A STRING rather than a hash, on purpose — a golden test whose failure is an
/// opaque digest mismatch tells a reader nothing about what moved.
///
/// `Debug` rather than a friendly display, also on purpose: it keeps
/// `Constant("x")` and `Description("x")` distinct and shows `Number` by its
/// stored bit pattern, so `0.0` and `-0.0` cannot silently merge into one tuple.
fn extension_digest(kb: &KnowledgeBase) -> String {
    let inner = kb.inner.borrow();
    let materialized = inner.materialized.borrow();
    let Some(m) = materialized.as_ref() else {
        return "(no saturation)".to_string();
    };
    let mut relations: Vec<&String> = m.ext.keys().collect();
    relations.sort();
    let mut out = String::new();
    for rel in relations {
        let mut tuples: Vec<String> = m.ext[rel].iter().map(|t| format!("{t:?}")).collect();
        tuples.sort();
        for t in tuples {
            out.push_str(rel);
            out.push_str(" :: ");
            out.push_str(&t);
            out.push('\n');
        }
    }
    out
}

/// Load a KB and force its NAF cone to saturate, returning the engine.
fn saturated_kb(kb_lines: &[&str], forcing_query: &str) -> KnowledgeBase {
    let kb = new_kb();
    for l in kb_lines {
        assert_buf(&kb, compile_surface(l));
    }
    // The verdict is irrelevant here; the point is that a NAF-bearing cone was
    // requested, which is what makes the saturator run.
    let _ = query_result(&kb, compile_surface(forcing_query));
    kb
}

/// `observe/4` — two variable positions followed by two literal constants. This is
/// the shape a real constitution is built from, and the one `bind_tuple`'s
/// constant-mismatch arm exists for.
///
/// Each `OtherScope` row binds `$o` at position 2 and only then fails at position
/// 4, so this exercises the arm BOTH ways and the cast is built to detect both:
///
/// * Ara and Bel each own one matching row among rejecting decoys. A binding
///   STRANDED by a rejection makes that matching row fail an equality check it
///   should pass, the derivation is lost, and they wrongly become rotten. That is
///   an under-derived extension — how this optimisation turns a
///   negation-as-failure FALSE into a definitive wrong TRUE.
/// * Cyd owns NO matching row, so Cyd must stay rotten. An arm that stops
///   discriminating (the mutation `other if true`) accepts an `OtherScope` row and
///   Cyd wrongly stops being rotten — over-derivation, the other direction.
///
/// Cyd is not decoration: with an all-matching cast this test passes under that
/// mutation, and only the extension digest catches it. Verified by applying it.
#[test]
fn a_constant_rejection_after_a_binding_does_not_strand_it() {
    let kb_lines = [
        "person(Ara).",
        "person(Bel).",
        "person(Cyd).",
        // Ara and Bel: one matching row each, buried among decoys that reject at
        // the LAST position — after `$o` has bound.
        "observe(Ara, Alpha, Sight, CaseScope).",
        "observe(Ara, Beta, Sight, OtherScope).",
        "observe(Ara, Gamma, Sight, OtherScope).",
        "observe(Ara, Delta, Sight, OtherScope).",
        "observe(Bel, Epsilon, Sight, CaseScope).",
        "observe(Bel, Zeta, Sight, OtherScope).",
        "observe(Bel, Eta, Sight, OtherScope).",
        "observe(Bel, Theta, Sight, OtherScope).",
        // Cyd: rejecting rows ONLY — the over-derivation control.
        "observe(Cyd, Iota, Sight, OtherScope).",
        "observe(Cyd, Kappa, Sight, OtherScope).",
        "observe(Cyd, Lambda, Sight, OtherScope).",
        "observe(Cyd, Mu, Sight, OtherScope).",
        "all $p: all $o: person($p) & observe($p, $o, Sight, CaseScope) -> reward($p).",
        "all $q: person($q) & ~reward($q) -> rotten($q).",
    ];
    let queries = ["rotten(Ara).", "rotten(Bel).", "rotten(Cyd)."];
    let (on, off) = both_ways(&kb_lines, &queries);
    assert_eq!(on, off, "materialisation must not change these verdicts");
    assert_eq!(
        on[0],
        QueryResult::False,
        "Ara has a CaseScope row, so `reward(Ara)` derives. A stranded `$o` binding \
         loses it behind the decoys and flips this to TRUE."
    );
    assert_eq!(
        on[1],
        QueryResult::False,
        "Bel has a CaseScope row, so `reward(Bel)` derives. Same failure mode as Ara."
    );
    assert_eq!(
        on[2],
        QueryResult::True,
        "Cyd has ONLY OtherScope rows, so `reward(Cyd)` must not derive. An arm that \
         stops discriminating on the trailing literal accepts one and flips this."
    );
}

/// An atom that repeats a variable — `loves($x, $x)` — with `$x` FRESH at the
/// atom, so position 1 inserts it and position 2 must read it back.
///
/// This is the property that rules out the whole "test the tuple against the
/// entry bindings, then build the extension" family of optimisations: resolving
/// both positions against a SNAPSHOT sees `$x` unbound twice and accepts
/// `loves(Ara, Bel)`, over-deriving. Nothing else in the suite has ever put a
/// repeated variable in an atom.
#[test]
fn a_repeated_variable_in_one_atom_matches_only_equal_pairs() {
    let kb_lines = [
        "person(Ara).",
        "person(Bel).",
        "person(Cyd).",
        "loves(Ara, Ara).",
        "loves(Ara, Bel).",
        "loves(Bel, Ara).",
        "loves(Bel, Cyd).",
        "loves(Cyd, Bel).",
        "all $x: loves($x, $x) -> fit($x).",
        "all $q: person($q) & ~fit($q) -> rotten($q).",
    ];
    let queries = ["rotten(Ara).", "rotten(Bel).", "rotten(Cyd)."];
    let (on, off) = both_ways(&kb_lines, &queries);
    assert_eq!(on, off, "materialisation must not change these verdicts");
    assert_eq!(
        on[0],
        QueryResult::False,
        "Ara loves Ara, so `fit(Ara)` derives and Ara is not rotten"
    );
    assert_eq!(
        on[1],
        QueryResult::True,
        "Bel loves Ara and Cyd but not Bel — over-deriving `fit(Bel)` flips this"
    );
    assert_eq!(
        on[2],
        QueryResult::True,
        "Cyd loves only Bel — over-deriving `fit(Cyd)` flips this"
    );
}

/// The saturated extension itself, byte for byte, over the two fixtures above.
///
/// The verdict tests can only see a change that reaches a query. This one sees
/// every derived tuple, so a join that starts deriving one tuple too many or too
/// few fails here even when no queried verdict moves.
#[test]
fn the_saturated_extension_is_byte_identical() {
    let kb = saturated_kb(
        &[
            "person(Ara).",
            "person(Bel).",
            "loves(Ara, Ara).",
            "loves(Ara, Bel).",
            "loves(Bel, Ara).",
            "observe(Ara, Alpha, Sight, CaseScope).",
            "observe(Ara, Beta, Sight, OtherScope).",
            "observe(Bel, Gamma, Sight, OtherScope).",
            "all $x: loves($x, $x) -> fit($x).",
            "all $p: all $o: person($p) & observe($p, $o, Sight, CaseScope) -> reward($p).",
            "all $q: person($q) & ~fit($q) & ~reward($q) -> rotten($q).",
        ],
        "rotten(Bel).",
    );
    let digest = extension_digest(&kb);
    assert_eq!(
        digest, EXPECTED_EXTENSION,
        "the saturated extension moved:\n{digest}"
    );
}

/// Pinned by [`the_saturated_extension_is_byte_identical`]. Regenerate ONLY when
/// a deliberate semantic change explains every added and removed line.
///
/// Reading it: `fit` holds Ara alone (Ara is the only self-lover), `reward` holds
/// Ara alone (every other `observe` row is `OtherScope` and rejects at its last
/// position), and `rotten` therefore holds Bel alone. The trailing `Unspecified`
/// slots are the unfilled places of the wider corpus relations, carried through
/// the event projection.
const EXPECTED_EXTENSION: &str = r#"fit :: [Constant("ara"), Unspecified, Unspecified]
loves :: [Constant("ara"), Constant("ara")]
loves :: [Constant("ara"), Constant("bel")]
loves :: [Constant("bel"), Constant("ara")]
observe :: [Constant("ara"), Constant("alpha"), Constant("sight"), Constant("casescope")]
observe :: [Constant("ara"), Constant("beta"), Constant("sight"), Constant("otherscope")]
observe :: [Constant("bel"), Constant("gamma"), Constant("sight"), Constant("otherscope")]
person :: [Constant("ara")]
person :: [Constant("bel")]
reward :: [Constant("ara"), Unspecified, Unspecified, Unspecified]
rotten :: [Constant("bel"), Unspecified]
"#;

/// A `<->` compiles to (¬a ∨ b) ∧ (¬b ∨ a) over a SHARED node arena, so each
/// predicate is reachable both positively and under a negation. The negated-
/// target collector must visit a shared subtree once PER POLARITY — a memo
/// keyed on node id alone skips the second-polarity visit and silently drops
/// a relation from the NAF target set, making its own "deliberately
/// over-approximating" doc comment false.
#[test]
fn negated_relations_cover_both_polarities_of_a_shared_subtree() {
    let mut out = std::collections::HashSet::new();
    crate::materialize::collect_negated_relations(
        &compile_surface("goes(me) <-> loves(you)."),
        &mut out,
    );
    for rel in ["goes", "loves"] {
        assert!(
            out.contains(rel),
            "`{rel}` occurs under a Not in the biconditional expansion and \
             must be collected regardless of which polarity the walk reaches \
             first: {out:?}"
        );
    }
}

/// The join index bounds the WORK, not just the verdict: a transitive-closure
/// saturation must enumerate O(|R| * fanout) candidates per round, not
/// O(|R|^2). Kills the performance-shape mutants a verdict test cannot see
/// (an emptied/degraded bound-position analysis or a bypassed index all fall
/// back to the SOUND full scan — same verdicts, quadratic enumeration).
#[test]
fn join_index_bounds_transitive_closure_bind_attempts() {
    let kb = new_kb();
    for i in 0..12 {
        assert_buf(
            &kb,
            compile_surface(&format!("earlier(E{}, E{}).", i, i + 1)),
        );
    }
    assert_buf(
        &kb,
        compile_surface(
            "all $a: all $b: all $c: earlier($a, $b) & earlier($b, $c) -> earlier($a, $c).",
        ),
    );
    assert_eq!(
        query_result(&kb, compile_surface("~earlier(E12, E0).")),
        QueryResult::True,
        "the NAF query must force the earlier cone's saturation"
    );
    let attempts = kb.materialization_tuple_bind_attempts("earlier");
    assert!(attempts > 0, "the closure must do real join work");
    // Measured at pinning time: 618 indexed vs 7631 with the index disabled —
    // the 2,000 threshold sits well clear of both.
    assert!(
        attempts <= 2_000,
        "transitive closure over a 12-link chain must stay indexed \
         (O(|R| * fanout) per round); {attempts} attempts means the level-1 \
         join degraded to a full scan"
    );
}

/// The bound-position ANALYSIS must be real, not coincidental: this rule's
/// second atom joins on POSITION 1 (`earlier($c, $b)` — `$b` is the variable
/// level 0 bound), so an analysis hardwired to position 0 keys the index on
/// the unbound `$c`, falls open to the full scan, and blows the work bound.
/// (The transitive-closure pin above cannot see that mutant — its join
/// position happens to BE 0.)
#[test]
fn join_index_analysis_handles_non_leading_bound_positions() {
    let kb = new_kb();
    for i in 0..12 {
        assert_buf(
            &kb,
            compile_surface(&format!("earlier(E{}, E{}).", i, i + 1)),
        );
    }
    assert_buf(
        &kb,
        compile_surface(
            "all $a: all $b: all $c: earlier($a, $b) & earlier($c, $b) -> concurrent($a, $c).",
        ),
    );
    assert_eq!(
        query_result(&kb, compile_surface("~concurrent(E0, E0).")),
        QueryResult::False,
        "E0 converges with itself on E1, so the NAF query is FALSE"
    );
    let attempts = kb.materialization_tuple_bind_attempts("concurrent");
    assert!(attempts > 0, "the converging join must do real work");
    // Measured at pinning time: 24 indexed; a position-0-hardwired analysis
    // full-scans at ~144.
    assert!(
        attempts <= 60,
        "the position-1 join must stay indexed; {attempts} attempts means the \
         analysis mis-keyed and degraded to a full scan"
    );
}

// ─── Rollback preserves the saturation (C3's strictly-sound subset) ──────

/// Build a KB whose `animal` cone is saturated by a NAF query, and return it
/// with the saturation live.
fn kb_with_live_saturation() -> KnowledgeBase {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("derived_only(\"fit\")."));
    assert_buf(&kb, compile_surface("dog(Rex)."));
    assert_buf(&kb, compile_surface("all $x: dog($x) -> animal($x)."));
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Bel).")),
        QueryResult::True
    );
    assert!(
        kb.materialization_report()
            .unwrap()
            .0
            .iter()
            .any(|r| r == "animal"),
        "fixture must leave a live saturation of the animal cone"
    );
    kb
}

/// A REFUSED assertion that mutated nothing must not throw the saturation
/// away: its rollback replay reproduces the very state the extensions were
/// computed from. The control — a SUCCESSFUL assertion — must still drop it.
#[test]
fn a_refused_assertion_preserves_the_saturation() {
    let kb = kb_with_live_saturation();

    // `fit` is closed to direct assertion, so this is refused at ingress,
    // before any store or rule mutation.
    kb.assert_fact_inner(compile_surface("fit(Rex)."), String::new())
        .expect_err("a derived_only relation must refuse direct assertion");
    assert!(
        kb.materialization_report()
            .unwrap()
            .0
            .iter()
            .any(|r| r == "animal"),
        "a non-mutating rollback must leave the saturation intact"
    );

    // Control: a real IN-CONE mutation is not ignored. It no longer drops the
    // cache (it is folded in at the next query), so the requirement is pinned
    // where it belongs — on the verdict.
    assert_buf(&kb, compile_surface("dog(Bel)."));
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Bel).")),
        QueryResult::False,
        "a successful in-cone assertion must be visible at the next query"
    );
}

/// The preserved saturation must not strand a stale extension: verdicts after
/// a refused assertion match a KB that never saw it, and the NEXT real
/// assertion is visible immediately.
#[test]
fn preserved_saturation_answers_exactly_as_a_rebuilt_one() {
    let kb = kb_with_live_saturation();
    kb.assert_fact_inner(compile_surface("fit(Rex)."), String::new())
        .expect_err("refused");

    // Answers from the preserved extensions.
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Bel).")),
        QueryResult::True,
        "Bel is still not derivable"
    );
    assert_eq!(
        query_result(&kb, compile_surface("animal(Rex).")),
        QueryResult::True,
        "Rex is still derivable"
    );

    // …and a genuine mutation is seen at once (no stale hold-over).
    assert_buf(&kb, compile_surface("dog(Bel)."));
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Bel).")),
        QueryResult::False,
        "the new dog must make Bel an animal — a preserved saturation must \
         never survive a real mutation"
    );

    // Byte-for-byte agreement with a KB that never saw the refused statement.
    let fresh = kb_with_live_saturation();
    assert_buf(&fresh, compile_surface("dog(Bel)."));
    assert_eq!(
        query_result(&fresh, compile_surface("~animal(Bel).")),
        query_result(&kb, compile_surface("~animal(Bel).")),
    );
}

/// The rollback's cache hygiene is NOT relaxed along with the saturation: the
/// derived predicate cache and its depth-cut table are still cleared and the
/// cache still disabled, so nothing the failed attempt derived can outlive it.
/// (Pins `invalidate_pred_cache_keeping_saturation` doing its two jobs — a
/// gutted version leaves the saturation intact and is otherwise invisible.)
#[test]
fn a_refused_assertion_still_clears_and_disables_the_predicate_cache() {
    let kb = kb_with_live_saturation();
    {
        // Warm the cache the way a query does, so the clear has something to do.
        let inner = kb.inner.borrow();
        clear_and_enable_pred_cache(&inner);
    }
    assert!(query(&kb, compile_surface("animal(Rex).")));

    kb.assert_fact_inner(compile_surface("fit(Rex)."), String::new())
        .expect_err("refused");

    let inner = kb.inner.borrow();
    assert!(
        !inner.pred_cache_enabled.get(),
        "the rollback must leave the predicate cache DISABLED"
    );
    assert!(
        inner.pred_cache.borrow().is_empty(),
        "the rollback must leave the predicate cache EMPTY"
    );
    assert!(
        inner.depth_cut_table.borrow().is_empty(),
        "the depth-cut table shares the cache lifecycle and must be cleared too"
    );
    drop(inner);
    assert!(
        kb.materialization_report()
            .unwrap()
            .0
            .iter()
            .any(|r| r == "animal"),
        "…while the saturation still survives"
    );
}

/// A rollback whose EARLIER root already mutated the store must still answer as
/// if nothing happened. The insert marked the saturation grown rather than
/// dropping it, and the replay then removed the tuple again — so the pending
/// delta must resolve to nothing at the next query, not to a phantom fact.
#[test]
fn a_mutating_rollback_leaves_no_phantom_in_the_saturation() {
    let kb = kb_with_live_saturation();
    let multi = compile_surface("dog(Bel). fit(Bel).");
    assert!(
        multi.roots.len() > 1,
        "fixture must be a multi-root buffer to mutate before failing"
    );
    kb.assert_fact_inner(multi, String::new())
        .expect_err("the derived_only root must refuse the whole assertion");

    // The rolled-back `dog(Bel)` must NOT have reached the extensions.
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Bel).")),
        QueryResult::True,
        "the refused assertion's earlier root must leave no phantom derivation"
    );
    // And a KB that never saw it agrees.
    let fresh = kb_with_live_saturation();
    assert_eq!(
        query_result(&fresh, compile_surface("~animal(Bel).")),
        query_result(&kb, compile_surface("~animal(Bel).")),
    );
}

// ─── Insert invalidation is CONE-RELEVANCE filtered ──────────────────────

/// An insert about a relation the saturation's cone does not contain cannot
/// change any extension in it, so the saturation stands. The control — an
/// insert INSIDE the cone — still drops it.
#[test]
fn an_out_of_cone_insert_preserves_the_saturation() {
    let kb = kb_with_live_saturation(); // cone = {animal, dog}

    assert_buf(&kb, compile_surface("cat(Bel)."));
    assert!(
        kb.materialization_report()
            .unwrap()
            .0
            .iter()
            .any(|r| r == "animal"),
        "an insert about an unrelated relation must leave the saturation standing"
    );

    // An insert INSIDE the cone is folded in rather than dropped — pinned on the
    // verdict, which is what "not ignored" actually means.
    assert_buf(&kb, compile_surface("dog(Bel)."));
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Bel).")),
        QueryResult::False,
        "an in-cone insert must reach the extensions at the next query"
    );
}

/// THE non-monotone case. A relation read under NEGATION is in the cone, so
/// inserting into it invalidates — growth through a negated condition REMOVES
/// derived tuples, and a preserved extension would answer with a tuple the new
/// fact just blocked. Pinned on the VERDICT, not merely the report.
#[test]
fn an_insert_under_a_negation_invalidates_and_the_verdict_follows() {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("dog(Rex)."));
    assert_buf(&kb, compile_surface("fit(every dog where ~cat)."));

    assert_eq!(
        query_result(&kb, compile_surface("fit(Rex).")),
        QueryResult::True,
        "Rex is a dog and no cat blocks it"
    );
    assert_eq!(
        query_result(&kb, compile_surface("~fit(Bel).")),
        QueryResult::True,
        "the NAF query saturates the fit cone"
    );
    assert!(
        !kb.materialization_report().unwrap().0.is_empty(),
        "fixture must leave a live saturation"
    );

    // `cat` is read under `~`, so it is IN the cone: this must invalidate.
    assert_buf(&kb, compile_surface("cat(Rex)."));
    assert!(
        kb.materialization_report().unwrap().0.is_empty(),
        "a fact read under negation must invalidate — its growth SHRINKS the model"
    );
    assert_eq!(
        query_result(&kb, compile_surface("fit(Rex).")),
        QueryResult::False,
        "the new cat must block the derivation; a stale extension would still say TRUE"
    );
}

/// A relation outside the cone carries no completeness claim, so a later query
/// ABOUT it recomputes rather than reading the preserved extensions.
#[test]
fn a_query_about_an_out_of_cone_relation_recomputes() {
    let kb = kb_with_live_saturation();
    assert_buf(&kb, compile_surface("cat(Bel).")); // preserved, out of cone

    assert_eq!(
        query_result(&kb, compile_surface("~cat(Rex).")),
        QueryResult::True,
        "Rex is not a cat"
    );
    assert_eq!(
        query_result(&kb, compile_surface("~cat(Bel).")),
        QueryResult::False,
        "Bel IS a cat — the preserved saturation must not hide the new fact"
    );
}

/// A `du` link is a GLOBAL guard, not a tuple in some cone: a saturation built
/// before the merge must die even though `equals` is nowhere near the query's
/// dependency closure. Pinned on the VERDICT — a seed carries no equivalence
/// expansion, so a preserved extension would answer `~rotten(Ara)` TRUE where
/// backward chaining correctly says FALSE.
#[test]
fn an_equality_merge_invalidates_even_though_it_is_out_of_cone() {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("dog(Rex)."));
    assert_buf(&kb, compile_surface("animal(every dog)."));
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Bel).")),
        QueryResult::True
    );
    assert!(
        !kb.materialization_report().unwrap().0.is_empty(),
        "fixture must leave a live saturation"
    );

    assert_buf(&kb, compile_surface("Bel = Rex."));
    assert!(
        kb.materialization_report().unwrap().0.is_empty(),
        "an equality merge must invalidate: the equality guard runs at BUILD time, \
         so a saturation built before it would never see the class"
    );
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Bel).")),
        QueryResult::False,
        "Bel is now Rex, hence an animal; a stale extension would still say TRUE"
    );
}

// ─── The IN-CONE delta resume ────────────────────────────────────────────

/// A delta must PROPAGATE up every stratum above it, not merely land in its own
/// relation. Four-level chain, saturated by a NAF query, then one new base fact:
/// the top of the chain must follow. (In debug builds `resume_with_delta` also
/// verifies itself against a full recompute, so this additionally exercises that
/// equality on a multi-stratum program.)
#[test]
fn a_delta_propagates_up_every_stratum() {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("dog(Rex)."));
    assert_buf(&kb, compile_surface("animal(every dog)."));
    assert_buf(&kb, compile_surface("alive(every animal)."));
    assert_buf(&kb, compile_surface("beautiful(every alive)."));

    assert_eq!(
        query_result(&kb, compile_surface("~beautiful(Bel).")),
        QueryResult::True,
        "Bel is nothing yet; this saturates the whole chain"
    );
    assert!(
        kb.materialization_report()
            .unwrap()
            .0
            .iter()
            .any(|r| r == "beautiful"),
        "fixture must complete the top of the chain"
    );

    // One new BASE fact, three strata below the top.
    assert_buf(&kb, compile_surface("dog(Bel)."));
    for (q, expected) in [
        ("animal(Bel).", QueryResult::True),
        ("alive(Bel).", QueryResult::True),
        ("beautiful(Bel).", QueryResult::True),
        ("~beautiful(Bel).", QueryResult::False),
    ] {
        assert_eq!(
            query_result(&kb, compile_surface(q)),
            expected,
            "{q} must follow from the folded delta"
        );
    }
}

/// A delta landing in the MIDDLE of a chain propagates upward from there, and
/// leaves the strata below it alone.
#[test]
fn a_mid_chain_delta_propagates_upward_only() {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("dog(Rex)."));
    assert_buf(&kb, compile_surface("animal(every dog)."));
    assert_buf(&kb, compile_surface("alive(every animal)."));
    assert_eq!(
        query_result(&kb, compile_surface("~alive(Cyan).")),
        QueryResult::True
    );

    assert_buf(&kb, compile_surface("animal(Cyan)."));
    assert_eq!(
        query_result(&kb, compile_surface("alive(Cyan).")),
        QueryResult::True,
        "the mid-chain delta must reach the stratum above it"
    );
    assert_eq!(
        query_result(&kb, compile_surface("dog(Cyan).")),
        QueryResult::False,
        "…and must not manufacture anything BELOW it"
    );
}

/// Repeated deltas accumulate correctly: several asserts between queries, and a
/// duplicate assert (which adds no tuple) must leave the extensions right.
#[test]
fn repeated_and_duplicate_deltas_accumulate_correctly() {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("dog(Rex)."));
    assert_buf(&kb, compile_surface("animal(every dog)."));
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Bel).")),
        QueryResult::True
    );

    assert_buf(&kb, compile_surface("dog(Bel)."));
    assert_buf(&kb, compile_surface("dog(Cyan)."));
    assert_buf(&kb, compile_surface("dog(Bel).")); // duplicate — no new tuple
    for who in ["Rex", "Bel", "Cyan"] {
        assert_eq!(
            query_result(&kb, compile_surface(&format!("animal({who})."))),
            QueryResult::True,
            "{who} must be an animal after the accumulated deltas"
        );
    }
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Dana).")),
        QueryResult::True,
        "and nobody else may be invented"
    );
}

/// The incremental path must actually RUN. Refusing to resume is always
/// correct — it falls back to a full recompute — so no verdict test can tell
/// the two apart; this pins the mechanism itself. An in-cone insert must be
/// FOLDED (a resume), and an out-of-cone one must not even attempt it.
#[test]
fn an_in_cone_insert_is_folded_and_an_out_of_cone_one_is_not() {
    let kb = kb_with_live_saturation(); // cone = {animal, dog}
    assert_eq!(
        kb.materialization_resumes(),
        0,
        "a fresh saturation has folded nothing yet"
    );

    // OUT of cone: no growth is recorded, so the next query folds nothing.
    assert_buf(&kb, compile_surface("cat(Bel)."));
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Bel).")),
        QueryResult::True
    );
    assert_eq!(
        kb.materialization_resumes(),
        0,
        "an out-of-cone insert must not even attempt a fold"
    );

    // IN cone: the next query must fold the delta in, NOT recompute (a
    // recompute would install a fresh cache whose counter reads zero).
    assert_buf(&kb, compile_surface("dog(Bel)."));
    assert_eq!(
        query_result(&kb, compile_surface("~animal(Bel).")),
        QueryResult::False
    );
    assert_eq!(
        kb.materialization_resumes(),
        1,
        "an in-cone insert must be folded into the existing saturation"
    );

    // And folds accumulate rather than resetting.
    assert_buf(&kb, compile_surface("dog(Cyan)."));
    assert_eq!(
        query_result(&kb, compile_surface("animal(Cyan).")),
        QueryResult::True
    );
    assert_eq!(kb.materialization_resumes(), 2, "folds must accumulate");
}

/// A relation read under NEGATION must never be folded: it invalidates, so the
/// next query REBUILDS (fold count back to zero on the fresh cache).
#[test]
fn a_negated_relation_insert_is_never_folded() {
    let kb = new_kb();
    assert_buf(&kb, compile_surface("dog(Rex)."));
    assert_buf(&kb, compile_surface("fit(every dog where ~cat)."));
    assert_eq!(
        query_result(&kb, compile_surface("~fit(Bel).")),
        QueryResult::True
    );

    assert_buf(&kb, compile_surface("cat(Rex)."));
    assert_eq!(
        query_result(&kb, compile_surface("fit(Rex).")),
        QueryResult::False,
        "the new cat blocks the derivation"
    );
    assert_eq!(
        kb.materialization_resumes(),
        0,
        "a negatively-read relation must force a rebuild, never a fold"
    );
}

/// A fold must do DELTA work, not re-derive the stratum. Several mutations of
/// `semi_naive_stratum` (mis-detecting the resume, or never advancing the round
/// counter) leave every answer correct while quietly reverting to a full
/// evaluation per round — invisible to verdicts, so the work is pinned instead.
#[test]
fn a_fold_costs_delta_work_not_a_full_re_evaluation() {
    let kb = new_kb();
    for i in 0..12 {
        assert_buf(
            &kb,
            compile_surface(&format!("earlier(E{}, E{}).", i, i + 1)),
        );
    }
    assert_buf(
        &kb,
        compile_surface(
            "all $a: all $b: all $c: earlier($a, $b) & earlier($b, $c) -> earlier($a, $c).",
        ),
    );
    assert_eq!(
        query_result(&kb, compile_surface("~earlier(E12, E0).")),
        QueryResult::True
    );
    let after_build = kb.materialization_tuple_bind_attempts("earlier");
    assert!(after_build > 0, "the fixture must saturate a real closure");

    // One new edge, then a query: the fold must join it against the closure,
    // not rebuild the closure.
    assert_buf(&kb, compile_surface("earlier(E12, E13)."));
    assert_eq!(
        query_result(&kb, compile_surface("earlier(E0, E13).")),
        QueryResult::True,
        "the new edge must extend the closure"
    );
    assert_eq!(kb.materialization_resumes(), 1, "it must be a fold");
    let fold_cost = kb.materialization_tuple_bind_attempts("earlier") - after_build;
    // Measured at pinning time: build 618, fold 261. A fold that reverted to
    // full round-0 evaluations (a mis-detected resume, or a round counter that
    // never advances) re-derives the closure instead of joining against it.
    assert!(
        fold_cost < 400,
        "a fold must cost DELTA work, not a re-evaluation: fold={fold_cost} \
         (build was {after_build}; measured fold at pinning time was 261)"
    );
}

/// A CONSTANT in a rule body must keep filtering the join.
///
/// `bind_tuple` matches a template term against a tuple value: a `PatternVar` binds,
/// anything else must be EQUAL. Drop that equality and a literal in a body atom stops
/// selecting — `teaches($x, Cyd)` matches every `teaches` tuple — so the rule fires for
/// subjects it does not cover. That is over-derivation, and it is definitive in both
/// directions: the head reads TRUE for the wrong subject, and anything reading the head
/// under `~` reads FALSE for them. Nothing else in this file puts a constant in a body
/// atom, which is why the equality guard was unpinned.
#[test]
fn a_constant_in_a_rule_body_still_filters_the_join() {
    let kb_lines = [
        "person(Ara).",
        "person(Bel).",
        "teaches(Ara, Cyd).",
        "teaches(Bel, Dee).",
        "all $x: teaches($x, Cyd) -> reward($x).",
        "all $y: person($y) & ~reward($y) -> fit($y).",
    ];
    let (on, off) = both_ways(
        &kb_lines,
        &["reward(Ara).", "reward(Bel).", "fit(Bel).", "fit(Ara)."],
    );
    assert_eq!(on[0], QueryResult::True, "Ara teaches Cyd");
    assert_eq!(
        on[1],
        QueryResult::False,
        "Bel teaches Dee, not Cyd — the constant must still select"
    );
    assert_eq!(on[2], QueryResult::True, "so Bel is not a reward-holder");
    assert_eq!(on[3], QueryResult::False);
    assert_eq!(on, off, "materialisation must not change any of these");
}

/// An identity restrictor must keep cutting the diagonal.
///
/// `~($a = $b)` is decided by `builtin_holds` and applied by the `holds != negated`
/// guard in the join walk. Either half failing admits the self-pair: `judge(Ara, Ara)`
/// would satisfy a rule that explicitly excludes it. This shape is real — `utopia.nibli`
/// carries exactly it — and it is doubly exposed, since an over-derived head flips every
/// `~head` reader to a definitive wrong FALSE.
#[test]
fn an_identity_restrictor_still_cuts_the_diagonal() {
    let kb_lines = [
        "person(Ara).",
        "person(Bel).",
        "judge(Ara, Ara).",
        "judge(Bel, Cyd).",
        "all $a: all $b: judge($a, $b) & ~($a = $b) -> reward($a).",
        "all $y: person($y) & ~reward($y) -> fit($y).",
    ];
    let (on, off) = both_ways(
        &kb_lines,
        &["reward(Ara).", "reward(Bel).", "fit(Ara).", "fit(Bel)."],
    );
    assert_eq!(
        on[0],
        QueryResult::False,
        "Ara only judges herself, which `~($a = $b)` excludes"
    );
    assert_eq!(on[1], QueryResult::True, "Bel judges someone else");
    assert_eq!(on[2], QueryResult::True);
    assert_eq!(on[3], QueryResult::False);
    assert_eq!(on, off, "materialisation must not change any of these");
}

/// Four stratified-NAF levels, end to end. The strata tests above pin
/// `compute_strata` on hand-built graphs; this pins that a real KB whose negation
/// chain is four deep still agrees with backward chaining at every level.
#[test]
fn a_four_stratum_negative_chain_agrees_with_backward_chaining() {
    let kb_lines = [
        "person(Ara).",
        "person(Bel).",
        "judge(Ara, Bel).",
        "capture(Ara, Bel).",
        "all $a: all $x: judge($a, $x) & capture($a, $x) & ~deceive($a, $x) -> false($x).",
        "all $t: person($t) & ~false($t) -> reward($t).",
        "all $u: person($u) & ~reward($u) -> fit($u).",
        "all $v: person($v) & ~fit($v) -> awake($v).",
    ];
    let queries = [
        "false(Bel).",
        "reward(Bel).",
        "fit(Bel).",
        "awake(Bel).",
        "false(Ara).",
        "reward(Ara).",
        "fit(Ara).",
        "awake(Ara).",
    ];
    let (on, off) = both_ways(&kb_lines, &queries);
    assert_eq!(on, off, "materialisation must not change any verdict here");
    // Bel is voided; Ara is not. The verdicts alternate up the chain.
    let expected = [
        QueryResult::True,
        QueryResult::False,
        QueryResult::True,
        QueryResult::False,
        QueryResult::False,
        QueryResult::True,
        QueryResult::False,
        QueryResult::True,
    ];
    for ((q, got), want) in queries.iter().zip(&on).zip(&expected) {
        assert_eq!(got, want, "{q}");
    }
}

/// AN INSERT TWO HOPS BELOW A NEGATED GUARD MUST NOT BE FOLDED IN.
///
/// Reported from a downstream `nibli-pin` suite, 2026-08-17, against the in-cone
/// delta resume. `judge` is inserted after `free` has already been answered;
/// `judge` is not itself read under `~`, so the old refusal (which looked only at
/// the DELTA's own relations) let the fold proceed. One derivation step later
/// `clean` grows, and `free` — which reads `~clean` — must LOSE the tuple it was
/// given at the first query. A monotone fold can only add, so the stale `free`
/// tuple survived and the second query answered TRUE where the stratified model
/// says FALSE.
///
/// The refusal now closes FORWARD over the rules from the delta, so anything the
/// delta can reach that is negatively read forces a full recompute. The `travel`
/// leg is the same defect in its most visible form: with `free -> travel`, a
/// stale `free` and a correctly-recomputed `travel` are mutually inconsistent
/// inside one process, which no monotone-assert reading can explain away.
#[test]
fn an_insert_two_hops_below_a_negated_guard_is_not_folded_in() {
    let run = |on: bool| -> Vec<QueryResult> {
        let kb = new_kb();
        kb.set_materialization(on);
        for line in [
            "all $x: judge(Court, $x) -> clean($x).",
            "all $x: person($x) & ~clean($x) -> free($x).",
            "all $x: free($x) -> travel($x).",
            "person(Ada).",
        ] {
            assert_buf(&kb, compile_surface(line));
        }
        // Answer the guarded atom BEFORE the insert — this is what puts it in the
        // saturation and makes the stale answer reachable.
        let mut out = vec![
            query_result(&kb, compile_surface("free(Ada).")),
            query_result(&kb, compile_surface("travel(Ada).")),
        ];
        assert_buf(&kb, compile_surface("judge(Court, Ada)."));
        out.push(query_result(&kb, compile_surface("clean(Ada).")));
        out.push(query_result(&kb, compile_surface("free(Ada).")));
        out.push(query_result(&kb, compile_surface("travel(Ada).")));
        out
    };
    let (on, off) = (run(true), run(false));
    assert_eq!(
        on, off,
        "materialisation must not change any of these verdicts"
    );
    assert_eq!(on[0], QueryResult::True, "nothing derives clean(Ada) yet");
    assert_eq!(on[1], QueryResult::True, "so travel follows from free");
    assert_eq!(on[2], QueryResult::True, "the insert derives clean(Ada)");
    assert_eq!(
        on[3],
        QueryResult::False,
        "clean(Ada) now holds, so `~clean` blocks free — the stale tuple must go"
    );
    assert_eq!(
        on[4],
        QueryResult::False,
        "and travel must agree with free in the same process"
    );
}
