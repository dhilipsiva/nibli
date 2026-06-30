//! CI gate: every curated Horn/NAF-free case must have nibli agree with Vampire.
//!
//! If the prover is unavailable the test skips cleanly (so `cargo test` is green in any
//! environment); inside the Nix dev shell Vampire is present, so it runs for real.

use nibli_verify::{corpus, oracle::OracleConfig, run_corpus};

/// The gate must actually compare a meaningful number of cases — otherwise a future
/// over-eager filter (or a broken oracle) could make it pass by skipping everything.
const MIN_CHECKED: usize = 10;

#[test]
fn horn_fragment_agrees_with_vampire() {
    let cfg = OracleConfig::default();
    if !nibli_verify::oracle::available(&cfg) {
        eprintln!(
            "nibli-verify gate SKIPPED: prover '{}' unavailable (set NIBLI_VAMPIRE / add to PATH).",
            cfg.binary
        );
        return;
    }

    let report = run_corpus(corpus::CASES, &cfg);
    for outcome in &report.outcomes {
        eprintln!("{}", outcome.summary());
    }
    let (agree, diverge, skip, error) = report.tally();
    eprintln!(
        "nibli-verify: {agree} agree / {diverge} diverge / {skip} skip / {error} error \
         ({} of {} checked)",
        report.checked(),
        corpus::CASES.len()
    );

    let errors: Vec<String> = report.errors().iter().map(|o| o.summary()).collect();
    assert!(errors.is_empty(), "harness errors:\n{}", errors.join("\n"));

    let divergences: Vec<String> = report.divergences().iter().map(|o| o.summary()).collect();
    assert!(
        divergences.is_empty(),
        "soundness divergences (nibli disagreed with Vampire):\n{}",
        divergences.join("\n")
    );

    assert!(
        report.checked() >= MIN_CHECKED,
        "only {} of {} cases reached the oracle (need >= {MIN_CHECKED}); gate is near-vacuous",
        report.checked(),
        corpus::CASES.len()
    );
}
