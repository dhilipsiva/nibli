//! Criterion benchmarks for the Nibli reasoning engine.
//!
//! Run: `cargo bench -p nibli-engine --bench engine_bench`
//! Results stored in `target/criterion/`.

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use nibli_engine::{EngineLogicalTerm, EngineQueryResult, NibliEngine};

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
            let engine = NibliEngine::new();
            populate_kb(&engine, n);
            // Assert one target fact for a valid cmevla so the query RESOLVES (a
            // hit) instead of scanning all N facts to fail. `adam` is nameable from
            // surface-Lojban query text; the `entN` fillers are direct-injected
            // constants and are not valid Lojban names, so the query cannot target
            // them — which is why the old `.i la .adam. gerku` query was a guaranteed
            // miss (it timed the failure path, not real query resolution).
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
                    engine.query_holds("la .adam. cu gerku").unwrap(),
                    EngineQueryResult::True
                ),
                "query_latency bench must measure a hit, not a miss"
            );
            b.iter(|| {
                engine.query_holds("la .adam. cu gerku").unwrap();
            });
        });
    }
    group.finish();
}

// ─── Benchmark: Recursive rule chains ────────────────────────────

fn bench_rule_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("rule_chain_depth");
    for &depth in &[2, 5, 10] {
        group.bench_with_input(BenchmarkId::from_parameter(depth), &depth, |b, &depth| {
            let engine = NibliEngine::new();
            // Build rule chain: gerku→danlu→jmive→... via Lojban.
            let preds = [
                "gerku", "danlu", "jmive", "xanlu", "fenki", "lisri", "bangu", "prenu", "nixli",
                "nanmu", "mlatu",
            ];
            for i in 0..depth.min(preds.len() - 1) {
                let text = format!(".i ro lo {} cu {}", preds[i], preds[i + 1]);
                engine.assert_text(&text).unwrap();
            }
            engine.assert_text(".i la .adam. gerku").unwrap();
            let last = preds[depth.min(preds.len() - 1)];
            let query = format!("la .adam. {}", last);
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
            let engine = NibliEngine::new();
            populate_kb(&engine, n);
            b.iter(|| {
                engine.query_find_text("ma gerku").unwrap();
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
            let engine = NibliEngine::new();
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
                        "du".to_string(),
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
                    let engine = NibliEngine::new();
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
