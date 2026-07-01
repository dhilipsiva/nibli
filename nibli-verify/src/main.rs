//! `nibli-verify` CLI: run a differential soundness gate and print a report.
//!
//! Vampire (classical FOL) over the Horn/NAF-free fragment:
//!   nibli-verify                 — the curated Horn/NAF-free corpus
//!   nibli-verify --random N [S]  — N deterministically-generated random Horn cases (seeds
//!                                  S..S+N, default S=0)
//!
//! clingo (ASP) over the stratified-NAF + closed-world fragment:
//!   nibli-verify --asp           — the curated stratified-NAF corpus
//!   nibli-verify --asp --random N [S]  — N random stratified-NAF cases
//!
//! Exit codes: 0 = all checked cases agree; 1 = at least one divergence or harness error;
//! 2 = the required solver is unavailable (nothing was checked).

use nibli_verify::oracle_asp::AspConfig;
use nibli_verify::{
    Report, corpus, corpus_naf, oracle::OracleConfig, run_corpus, run_naf_corpus, run_random,
    run_random_naf,
};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    let report = if args.first().map(String::as_str) == Some("--asp") {
        run_asp(&args[1..])
    } else {
        run_vampire(&args)
    };

    report_and_exit(report);
}

/// The clingo (ASP) path — stratified-NAF + closed-world fragment.
fn run_asp(rest: &[String]) -> Report {
    let cfg = AspConfig::default();
    if !nibli_verify::oracle_asp::available(&cfg) {
        eprintln!(
            "nibli-verify: ASP solver '{}' not runnable (set NIBLI_CLINGO or add clingo to \
             PATH); nothing checked.",
            cfg.binary
        );
        std::process::exit(2);
    }
    if rest.first().map(String::as_str) == Some("--random") {
        let count: u64 = rest.get(1).and_then(|s| s.parse().ok()).unwrap_or(100);
        let seed: u64 = rest.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
        eprintln!(
            "nibli-verify --asp: {count} random NAF cases (seeds {seed}..{})",
            seed + count
        );
        run_random_naf(count, seed, &cfg)
    } else {
        let r = run_naf_corpus(corpus_naf::NAF_CASES, &cfg);
        for (case, outcome) in corpus_naf::NAF_CASES.iter().zip(&r.outcomes) {
            println!("[expect {}] {}", case.expect.label(), outcome.summary());
        }
        r
    }
}

/// The Vampire (classical FOL) path — Horn/NAF-free fragment.
fn run_vampire(args: &[String]) -> Report {
    let cfg = OracleConfig::default();
    if !nibli_verify::oracle::available(&cfg) {
        eprintln!(
            "nibli-verify: prover '{}' not runnable (set NIBLI_VAMPIRE or add it to PATH); \
             nothing checked.",
            cfg.binary
        );
        std::process::exit(2);
    }
    if args.first().map(String::as_str) == Some("--random") {
        let count: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(200);
        let seed: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
        eprintln!(
            "nibli-verify: {count} random cases (seeds {seed}..{})",
            seed + count
        );
        run_random(count, seed, &cfg)
    } else {
        let r = run_corpus(corpus::CASES, &cfg);
        for (case, outcome) in corpus::CASES.iter().zip(&r.outcomes) {
            println!("[expect {}] {}", case.expect.label(), outcome.summary());
        }
        r
    }
}

fn report_and_exit(report: Report) -> ! {
    let (agree, diverge, skip, error) = report.tally();
    println!(
        "\nnibli-verify: {agree} agree, {diverge} diverge, {skip} skipped, {error} error \
         ({} of {} cases checked)",
        report.checked(),
        report.outcomes.len()
    );

    for d in report.divergences() {
        if let nibli_verify::Outcome::Diverge { name, tptp, .. } = d {
            eprintln!("\n--- DIVERGENCE: {name} ---\n{tptp}");
        }
    }
    for e in report.errors() {
        eprintln!("{}", e.summary());
    }

    if diverge > 0 || error > 0 {
        std::process::exit(1);
    }
    std::process::exit(0);
}
