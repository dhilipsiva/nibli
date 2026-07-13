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

/// Assert N ground facts via direct assertion (bypasses parser).
fn populate_kb(engine: &NibliEngine, n: usize) {
    for i in 0..n {
        engine
            .assert_fact_direct(
                "gerku".to_string(),
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
                    "gerku".to_string(),
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
// Depth set is [2, 4, 5], NOT deeper: since commit 90b3f59 (predicate cache
// gated to definitive results + cross-depth tabling — a SOUNDNESS fix; the old
// cache reused non-definitive results across deepening passes, so a pass-d
// depth cut could poison pass d+1), per-hop cost on synthetic chains multiplies
// by roughly 30x. Measured 2026-07-03: depth 2 = 163 µs, depth 4 = 41 ms,
// depth 5 = 1.5 s, depth 6 = 47 s — so the former depth-10 configuration no
// longer completes in benchmark time (the April 2026 pre-90b3f59 engine ran it
// in ~1.3 s). If sound tabling ever recovers deep chains, re-extend the depth
// set and re-run; the book quotes this group (P3_C07 Table 7.2).

fn bench_rule_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("rule_chain_depth");
    for &depth in &[2usize, 4, 5] {
        group.bench_with_input(BenchmarkId::from_parameter(depth), &depth, |b, &depth| {
            let engine = fresh_engine();
            // Build rule chain: gerku→danlu→jmive→... via KR identity-gismu
            // spellings (raw dictionary words resolve as identity aliases, so
            // the chain vocabulary is unchanged from the pre-DROP bench).
            let preds = [
                "gerku", "danlu", "jmive", "cipni", "fenki", "lisri", "bangu", "prenu", "nixli",
                "nanmu", "mlatu",
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
            b.iter(|| {
                engine.query_find_text("dog(?).").unwrap();
            });
        });
    }
    group.finish();
}

// ─── Benchmark: Equality workload ────────────────────────────────

fn bench_equality(c: &mut Criterion) {
    let mut group = c.benchmark_group("equality_workload");
    for &n in &[5, 20, 50] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            let engine = fresh_engine();
            // Chain: du(e0,e1), du(e1,e2), ..., du(e{n-2},e{n-1})
            engine
                .assert_fact_direct(
                    "gerku".to_string(),
                    vec![
                        EngineLogicalTerm::Constant("e0".to_string()),
                        EngineLogicalTerm::Unspecified,
                    ],
                )
                .unwrap();
            for i in 0..n - 1 {
                engine
                    .assert_fact_direct(
                        "equals".to_string(),
                        vec![
                            EngineLogicalTerm::Constant(format!("e{}", i)),
                            EngineLogicalTerm::Constant(format!("e{}", i + 1)),
                        ],
                    )
                    .unwrap();
            }
            // Query gerku for the last entity in the chain.
            let last = format!("e{}", n - 1);
            b.iter(|| {
                engine
                    .assert_fact_direct(
                        "gerku_query".to_string(),
                        vec![
                            EngineLogicalTerm::Constant(last.clone()),
                            EngineLogicalTerm::Unspecified,
                        ],
                    )
                    .ok(); // Just measure assertion + equality lookup
            });
        });
    }
    group.finish();
}

// ─── Benchmark: Retraction ───────────────────────────────────────

fn bench_retraction(c: &mut Criterion) {
    let mut group = c.benchmark_group("retraction");
    for &n in &[10, 100, 500] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter_with_setup(
                || {
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
    bench_retraction,
);
criterion_main!(benches);
