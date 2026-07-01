//! CI gate: every curated Horn/NAF-free case must have nibli agree with Vampire.
//!
//! If the prover is unavailable the test skips cleanly (so `cargo test` is green in any
//! environment); inside the Nix dev shell Vampire is present, so it runs for real.

use nibli_verify::{corpus, oracle::OracleConfig, run_corpus, run_random};

/// The gate must actually compare a meaningful number of cases — otherwise a future
/// over-eager filter (or a broken oracle) could make it pass by skipping everything.
const MIN_CHECKED: usize = 10;

/// How many random cases the CI gate runs (each drives Vampire, so keep it modest); override
/// with `NIBLI_VERIFY_RANDOM_COUNT` for a deeper local/nightly sweep.
const DEFAULT_RANDOM_COUNT: u64 = 200;

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

/// Random-corpus coverage: N deterministically-generated NAF-free definite-Horn programs must
/// each have nibli agree with Vampire. Broadens the differential gate far beyond the curated
/// cases; a divergence would flag a reasoner-soundness bug the curated set missed.
#[test]
fn random_horn_cases_agree_with_vampire() {
    let cfg = OracleConfig::default();
    if !nibli_verify::oracle::available(&cfg) {
        eprintln!(
            "nibli-verify random gate SKIPPED: prover '{}' unavailable.",
            cfg.binary
        );
        return;
    }

    let count: u64 = std::env::var("NIBLI_VERIFY_RANDOM_COUNT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_RANDOM_COUNT);
    let report = run_random(count, 0, &cfg);

    let (agree, diverge, skip, error) = report.tally();
    eprintln!(
        "nibli-verify random: {agree} agree / {diverge} diverge / {skip} skip / {error} error \
         ({} of {count} checked)",
        report.checked()
    );

    let errors: Vec<String> = report.errors().iter().map(|o| o.summary()).collect();
    assert!(
        errors.is_empty(),
        "harness errors on random cases:\n{}",
        errors.join("\n")
    );

    let divergences: Vec<String> = report.divergences().iter().map(|o| o.summary()).collect();
    assert!(
        divergences.is_empty(),
        "soundness divergences on random cases (nibli disagreed with Vampire):\n{}",
        divergences.join("\n")
    );

    // Horn-by-construction, so the vast majority must actually reach the oracle — guard against
    // a future generator/filter change quietly making the sweep vacuous.
    assert!(
        report.checked() as u64 >= count * 3 / 4,
        "only {} of {count} random cases reached the oracle; sweep near-vacuous",
        report.checked()
    );
}
