//! nibli-bench-book — release-profile timing pins for the book's quoted figures.
//!
//! The book quotes three latency figures (Ch 13 "1 MB vs a Hundred Million
//! Dollars"; Ch 19 GDPR case study), all measured on the NATIVE in-process
//! engine (`nibli-engine`) in a release build — the same path as the pinned
//! `gdpr_full_corpus_lawful_basis_query_completes` test Ch 19 cites:
//!
//!   load    — assert every line of the shipped `gdpr.nibli` corpus
//!   query   — the Ch-19 headline lawful-basis query `permitted(Adam).`
//!             against the fully loaded corpus
//!   full    — the whole Ch-19 sequence: load + lawful-basis query + consent
//!             retraction + post-withdrawal lawful-basis re-query (the worst
//!             case: a definitive FALSE cannot short-circuit the search) +
//!             erasure re-query
//!
//! Every verdict is asserted each iteration — a timing figure attached to a
//! wrong verdict would be meaningless. Each iteration uses a fresh engine, so
//! no state leaks between runs. Prints min/median/max over `NIBLI_BENCH_RUNS`
//! iterations (default 10) after one untimed warm-up.
//!
//! Run via `just bench-book`. The recipe forces the release profile; a debug
//! build prints a loud warning and its figures must never be quoted.

use nibli_engine::NibliEngine;
use std::process::ExitCode;
use std::time::{Duration, Instant};

const CORPUS: &str = include_str!("../../../gdpr.nibli");
const CONSENT_LINE: &str = "approves(Adam).";
const LAWFUL_BASIS_QUERY: &str = "permitted(Adam).";
const ERASURE_QUERY: &str = "~permitted(Adam).";

/// One full Ch-19 GDPR sequence on a fresh engine. Returns (load, query, full).
fn run_once() -> Result<(Duration, Duration, Duration), String> {
    let t_start = Instant::now();

    // KR corpus since THE DROP (the .nibli twin is line-equal to the retired
    // gdpr.lojban corpus, so figures stay comparable; the book re-derives its
    // quoted numbers from this bench either way).
    let engine = NibliEngine::new();
    let mut consent_id = None;
    let mut asserted = 0u32;
    for (line_num, line) in CORPUS.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let id = engine
            .assert_text(trimmed)
            .map_err(|e| format!("gdpr.nibli line {}: {e:?}", line_num + 1))?;
        asserted += 1;
        if trimmed == CONSENT_LINE {
            // The consent line is a single sentence → exactly one fact id.
            consent_id = id.first().copied();
        }
    }
    let consent_id = consent_id.ok_or("consent line not found in gdpr.nibli")?;
    if asserted == 0 {
        return Err("empty corpus".into());
    }
    let t_load = t_start.elapsed();

    let t_query_start = Instant::now();
    let r = engine
        .query_holds(LAWFUL_BASIS_QUERY)
        .map_err(|e| format!("{e:?}"))?;
    let t_query = t_query_start.elapsed();
    if !r.is_true() {
        return Err(format!("lawful-basis query: expected TRUE, got {r:?}"));
    }

    engine
        .retract_fact(consent_id)
        .map_err(|e| format!("{e:?}"))?;
    let r = engine
        .query_holds(LAWFUL_BASIS_QUERY)
        .map_err(|e| format!("{e:?}"))?;
    if !r.is_false() {
        return Err(format!(
            "post-withdrawal lawful-basis query: expected FALSE, got {r:?}"
        ));
    }
    let r = engine
        .query_holds(ERASURE_QUERY)
        .map_err(|e| format!("{e:?}"))?;
    if !r.is_true() {
        return Err(format!("erasure query: expected TRUE, got {r:?}"));
    }
    let t_full = t_start.elapsed();

    Ok((t_load, t_query, t_full))
}

fn stats(mut xs: Vec<Duration>) -> (Duration, Duration, Duration) {
    xs.sort();
    let median = xs[xs.len() / 2];
    (xs[0], median, *xs.last().unwrap())
}

fn fmt(d: Duration) -> String {
    let ms = d.as_secs_f64() * 1000.0;
    if ms < 10.0 {
        format!("{ms:.1} ms")
    } else {
        format!("{ms:.0} ms")
    }
}

fn main() -> ExitCode {
    let profile = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    if cfg!(debug_assertions) {
        eprintln!(
            "WARNING: debug build — these figures are NOT quotable. \
             Run `just bench-book` (release profile)."
        );
    }

    let runs: usize = std::env::var("NIBLI_BENCH_RUNS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(10);

    // Warm-up (untimed result; still verdict-checked).
    if let Err(e) = run_once() {
        eprintln!("bench-book: sequence failed: {e}");
        return ExitCode::FAILURE;
    }

    let mut loads = Vec::with_capacity(runs);
    let mut queries = Vec::with_capacity(runs);
    let mut fulls = Vec::with_capacity(runs);
    for _ in 0..runs {
        match run_once() {
            Ok((l, q, f)) => {
                loads.push(l);
                queries.push(q);
                fulls.push(f);
            }
            Err(e) => {
                eprintln!("bench-book: sequence failed: {e}");
                return ExitCode::FAILURE;
            }
        }
    }

    println!(
        "nibli-bench-book — native in-process engine (nibli-engine), {profile} profile, \
         {runs} runs (fresh engine per run, 1 untimed warm-up)"
    );
    println!("  corpus: gdpr.nibli (all verdicts asserted every run)");
    for (label, xs) in [
        ("gdpr.nibli load", loads),
        ("lawful-basis query", queries),
        ("full Ch-20 sequence", fulls),
    ] {
        let (min, med, max) = stats(xs);
        println!(
            "  {label:<22} min {:>8}   median {:>8}   max {:>8}",
            fmt(min),
            fmt(med),
            fmt(max)
        );
    }
    println!("    (full sequence = load + lawful-basis query + consent retraction");
    println!("     + post-withdrawal re-query + erasure re-query, one engine)");
    ExitCode::SUCCESS
}
