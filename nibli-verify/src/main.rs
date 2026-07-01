//! `nibli-verify` CLI: run the differential soundness gate (nibli vs Vampire) and print a
//! report.
//!
//!   nibli-verify                 — the curated Horn/NAF-free corpus
//!   nibli-verify --random N [S]  — N deterministically-generated random cases (seeds S..S+N,
//!                                  default S=0), for broad random-corpus coverage
//!
//! Exit codes: 0 = all checked cases agree; 1 = at least one divergence or harness error;
//! 2 = the prover is unavailable (nothing was checked).

use nibli_verify::{Report, corpus, oracle::OracleConfig, run_corpus, run_random};

fn main() {
    let cfg = OracleConfig::default();
    if !nibli_verify::oracle::available(&cfg) {
        eprintln!(
            "nibli-verify: prover '{}' not runnable (set NIBLI_VAMPIRE or add it to PATH); \
             nothing checked.",
            cfg.binary
        );
        std::process::exit(2);
    }

    let args: Vec<String> = std::env::args().skip(1).collect();
    let report: Report = if args.first().map(String::as_str) == Some("--random") {
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
    };

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
}
