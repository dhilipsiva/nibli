//! `nibli-verify` CLI: run the curated Horn/NAF-free corpus through the differential
//! soundness gate (nibli vs Vampire) and print a report.
//!
//! Exit codes: 0 = all checked cases agree; 1 = at least one divergence or harness
//! error; 2 = the prover is unavailable (nothing was checked).

use nibli_verify::{corpus, oracle::OracleConfig, run_corpus};

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

    let report = run_corpus(corpus::CASES, &cfg);

    for (case, outcome) in corpus::CASES.iter().zip(&report.outcomes) {
        println!("[expect {}] {}", case.expect.label(), outcome.summary());
    }

    let (agree, diverge, skip, error) = report.tally();
    println!(
        "\nnibli-verify: {agree} agree, {diverge} diverge, {skip} skipped, {error} error \
         ({} of {} cases checked)",
        report.checked(),
        corpus::CASES.len()
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
