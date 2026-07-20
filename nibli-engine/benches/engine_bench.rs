//! Criterion benchmarks for the Nibli reasoning engine.
//!
//! Run: `cargo bench -p nibli-engine --bench engine_bench`
//! Results stored in `target/criterion/`.

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use nibli_engine::{EngineLogicalTerm, EngineQueryResult, NibliEngine};

/// A fresh KR-mode engine (benched text ported to KR at THE DROP — timing
/// comparisons against pre-drop figures cross the front-end change).
fn fresh_engine() -> NibliEngine {
    NibliEngine::new()
}

/// Assert N ground facts via direct assertion (bypasses parser). The relation
/// name must be the ENGLISH corpus spelling: surface queries (`dog(Adam).`,
/// `dog(?).`) compile to English relations since the committed-corpus flip, so
/// a gismu-injected fact is unreachable from query text (the silent-miss class
/// the hit guards below exist to catch — the old `gerku` injection broke the
/// query-latency and witness groups exactly that way).
fn populate_kb(engine: &NibliEngine, n: usize) {
    for i in 0..n {
        engine
            .assert_fact_direct(
                "dog".to_string(),
                vec![
                    EngineLogicalTerm::Constant(format!("ent{}", i)),
                    EngineLogicalTerm::Unspecified,
                ],
            )
            .unwrap();
    }
}

// ─── Benchmark: Assertion throughput vs KB size ──────────────────

fn bench_assertion_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("assertion_throughput");
    for &n in &[100, 500, 1000] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_with_setup(NibliEngine::new, |engine| {
                populate_kb(&engine, n);
            });
        });
    }
    group.finish();
}

// ─── Benchmark: Query latency vs KB size ─────────────────────────

fn bench_query_latency(c: &mut Criterion) {
    let mut group = c.benchmark_group("query_latency_vs_kb_size");
    for &n in &[10, 100, 1000] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            let engine = fresh_engine();
            populate_kb(&engine, n);
            // Assert one target fact for a nameable constant so the query RESOLVES
            // (a hit) instead of scanning all N facts to fail. `adam` is nameable
            // from surface query text; the `entN` fillers are direct-injected
            // constants the surface cannot name, so a query against them was a
            // guaranteed miss (it timed the failure path, not query resolution).
            engine
                .assert_fact_direct(
                    "dog".to_string(),
                    vec![
                        EngineLogicalTerm::Constant("adam".to_string()),
                        EngineLogicalTerm::Unspecified,
                    ],
                )
                .unwrap();
            // Guard so the bench can never silently regress to a miss: the query
            // must resolve TRUE against the KB, else we are timing the failure path.
            assert!(
                matches!(
                    engine.query_holds("dog(Adam).").unwrap(),
                    EngineQueryResult::True
                ),
                "query_latency bench must measure a hit, not a miss"
            );
            b.iter(|| {
                engine.query_holds("dog(Adam).").unwrap();
            });
        });
    }
    group.finish();
}

// ─── Benchmark: Recursive rule chains ────────────────────────────
//
// Depth set re-extended to [2, 4, 6, 8, 10] at the 2026-07-18 sound-tabling
// landing (the budget-keyed depth-cut table in nibli-reason): the deep-chain
// cliff — ~30×/hop since the 90b3f59 predicate-cache soundness fix, measured
// 2026-07-03 as 163 µs @ 2 / 41 ms @ 4 / 1.5 s @ 5 / 47 s @ 6, with depth 10
// no longer completing — is RECOVERED. Measured 2026-07-18 (release):
// depth 2 = 173 µs, 4 = 4.2 ms, 6 = 24 ms (was 47 s), 8 = 93 ms, 10 = 241 ms
// — the formerly-exponential curve is polynomial, and depth 10 beats even the
// pre-90b3f59 UNSOUND cache (~1.3 s) ~5×. (The book's fact-store chapter
// reconciled its Table to post-tabling figures on 2026-07-19.)
// Vocabulary went English at the committed-corpus milestone (gismu spellings
// no longer resolve — the old gerku→danlu chain had silently broken this
// bench, and the gerku-injected populate_kb broke the query-latency and
// witness groups the same way until 2026-07-19).

fn bench_rule_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("rule_chain_depth");
    for &depth in &[2usize, 4, 6, 8, 10] {
        group.bench_with_input(BenchmarkId::from_parameter(depth), &depth, |b, &depth| {
            let engine = fresh_engine();
            let preds = [
                "dog", "animal", "alive", "big", "fast", "healthy", "thin", "eats", "goes",
                "person", "cat",
            ];
            for i in 0..depth.min(preds.len() - 1) {
                let text = format!("{}(every {}).", preds[i + 1], preds[i]);
                engine.assert_text(&text).unwrap();
            }
            engine.assert_text("dog(Adam).").unwrap();
            let last = preds[depth.min(preds.len() - 1)];
            let query = format!("{}(Adam).", last);
            // Guard: the chain must actually derive (same rule as query_latency —
            // never silently time a failure/limit path).
            assert!(
                matches!(engine.query_holds(&query).unwrap(), EngineQueryResult::True),
                "rule_chain bench must measure a successful derivation"
            );
            b.iter(|| {
                engine.query_holds(&query).unwrap();
            });
        });
    }
    group.finish();
}

// ─── Benchmark: Witness extraction ───────────────────────────────

fn bench_witness_extraction(c: &mut Criterion) {
    let mut group = c.benchmark_group("witness_extraction");
    for &n in &[10, 100, 500] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            let engine = fresh_engine();
            populate_kb(&engine, n);
            // Guard (same rule as query_latency/rule_chain): the find must
            // return witnesses, else we are timing the empty-find path.
            assert!(
                !engine.query_find_text("dog(?).").unwrap().is_empty(),
                "witness_extraction bench must find witnesses, not time a miss"
            );
            b.iter(|| {
                engine.query_find_text("dog(?).").unwrap();
            });
        });
    }
    group.finish();
}

// ─── Benchmark: Equality resolution (union-find) ─────────────────
//
// Measures the cost of RESOLVING a query through an equality chain, not the
// artifact the previous version timed (it asserted an unrelated relation and
// never queried the chain). Build `E0 = E1 = … = E{n-1}` plus a base fact
// `dog(E0)`, then repeatedly query the far end `dog(E{n-1})`, which must
// resolve TRUE through the union-find equivalence class. With path
// compression the resolved cost is effectively constant regardless of chain
// length — that is the property the table should show. Surface KR (not the
// direct-inject path) so the query is nameable and actually resolves — a
// direct-injected constant is unnameable from query text and would silently
// time a miss (the query_latency/rule_chain hit-guard lesson).

fn bench_equality(c: &mut Criterion) {
    let mut group = c.benchmark_group("equality_resolution");
    for &n in &[5, 20, 50] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            let engine = fresh_engine();
            engine.assert_text("dog(E0).").unwrap();
            for i in 0..n - 1 {
                engine
                    .assert_text(&format!("E{} = E{}.", i, i + 1))
                    .unwrap();
            }
            let query = format!("dog(E{}).", n - 1);
            // Guard: the far end must resolve TRUE through the equality chain,
            // else we are timing a miss instead of union-find resolution.
            assert!(
                matches!(engine.query_holds(&query).unwrap(), EngineQueryResult::True),
                "equality bench must resolve the chain (dog(E0) reaches E{}), not time a miss",
                n - 1
            );
            b.iter(|| {
                engine.query_holds(&query).unwrap();
            });
        });
    }
    group.finish();
}

// ─── Benchmark: Retraction ───────────────────────────────────────
//
// Two groups, one per retraction path. The COMMON case for any fact typed as
// nibli KR is the FULL REBUILD: `dog(Ent0).` event-decomposes to `∃e. (…)`, so
// its buffer carries an ExistsNode and `retract_fact_inner` takes the rebuild
// branch (replay every surviving record). The INCREMENTAL path is the narrow
// exception — flat direct-`:assert` ground facts with no ∃/rule/negation are
// removed from the fact store in place. The book's Table quotes both so the
// two-path story has honest numbers.

fn bench_retraction_rebuild(c: &mut Criterion) {
    let mut group = c.benchmark_group("retraction_rebuild");
    for &n in &[10, 100, 500] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_with_setup(
                || {
                    // Text-asserted facts (event-decomposed) → rebuild path.
                    let engine = fresh_engine();
                    for i in 0..n {
                        engine.assert_text(&format!("dog(Ent{}).", i)).unwrap();
                    }
                    engine
                },
                |engine| {
                    // Retract fact #0 → full rebuild replays the n-1 survivors.
                    let _ = engine.retract_fact(0);
                },
            );
        });
    }
    group.finish();
}

fn bench_retraction_incremental(c: &mut Criterion) {
    let mut group = c.benchmark_group("retraction_incremental");
    for &n in &[10, 100, 500] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_with_setup(
                || {
                    // Flat direct-inject ground facts (no ∃/rule) → incremental path.
                    let engine = fresh_engine();
                    populate_kb(&engine, n);
                    engine
                },
                |engine| {
                    let _ = engine.retract_fact(0);
                },
            );
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_assertion_throughput,
    bench_query_latency,
    bench_rule_chain,
    bench_witness_extraction,
    bench_equality,
    bench_retraction_rebuild,
    bench_retraction_incremental,
);
criterion_main!(benches);
