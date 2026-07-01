//! CI gate: every curated Horn/NAF-free case must have nibli agree with Vampire.
//!
//! If the prover is unavailable the test skips cleanly (so `cargo test` is green in any
//! environment); inside the Nix dev shell Vampire is present, so it runs for real.

use nibli_verify::oracle_asp::AspConfig;
use nibli_verify::{
    corpora, corpus, corpus_naf, oracle::OracleConfig, run_corpus, run_corpus_slice,
    run_naf_corpus, run_random, run_random_naf,
};

/// The gate must actually compare a meaningful number of cases — otherwise a future
/// over-eager filter (or a broken oracle) could make it pass by skipping everything.
const MIN_CHECKED: usize = 10;

/// How many random cases the CI gate runs (each drives Vampire, so keep it modest); override
/// with `NIBLI_VERIFY_RANDOM_COUNT` for a deeper local/nightly sweep.
const DEFAULT_RANDOM_COUNT: u64 = 200;

/// Minimum curated stratified-NAF cases the ASP gate must actually check.
const MIN_CHECKED_NAF: usize = 8;

/// How many random stratified-NAF cases the ASP gate runs; override with
/// `NIBLI_VERIFY_NAF_RANDOM_COUNT`.
const DEFAULT_NAF_RANDOM_COUNT: u64 = 100;

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

/// Real-vocabulary coverage: the mappable Horn/NAF-free sub-slice of each shipped case-study
/// corpus (`gdpr.lojban`, `drug-interactions.lojban`) must have nibli agree with Vampire on
/// every atomic query. The filter skips the deontic/NAF lines; the classical remainder — GDPR's
/// data-category rules, DDI's whole interaction chain — is checked against the oracle.
#[test]
fn gdpr_ddi_mappable_slices_agree_with_vampire() {
    let cfg = OracleConfig::default();
    if !nibli_verify::oracle::available(&cfg) {
        eprintln!(
            "nibli-verify corpora gate SKIPPED: prover '{}' unavailable.",
            cfg.binary
        );
        return;
    }

    let mut total_checked = 0usize;
    let mut all_div: Vec<String> = Vec::new();
    let mut all_err: Vec<String> = Vec::new();
    for (label, corpus) in [("gdpr", corpora::GDPR), ("ddi", corpora::DDI)] {
        let report = run_corpus_slice(label, corpus, &cfg);
        let (agree, diverge, skip, error) = report.tally();
        eprintln!(
            "nibli-verify {label} slice: {agree} agree / {diverge} diverge / {skip} skip /              {error} error ({} checked)",
            report.checked()
        );
        total_checked += report.checked();
        all_div.extend(report.divergences().iter().map(|o| o.summary()));
        all_err.extend(report.errors().iter().map(|o| o.summary()));
    }

    assert!(
        all_err.is_empty(),
        "harness errors on corpora slices:\n{}",
        all_err.join("\n")
    );
    assert!(
        all_div.is_empty(),
        "soundness divergences on gdpr/ddi mappable slices (nibli disagreed with Vampire):\n{}",
        all_div.join("\n")
    );
    assert!(
        total_checked >= 20,
        "only {total_checked} corpora-slice cases reached the oracle; gate near-vacuous"
    );
}

/// Stratified-NAF gate: every curated closed-world negation-as-failure case must have nibli
/// agree with **clingo** (ASP). This covers the fragment the Vampire gate deliberately skips
/// — nibli's closed-world verdict must equal the unique stable/perfect model. Skips cleanly
/// if clingo is unavailable.
#[test]
fn stratified_naf_agrees_with_clingo() {
    let cfg = AspConfig::default();
    if !nibli_verify::oracle_asp::available(&cfg) {
        eprintln!(
            "nibli-verify ASP gate SKIPPED: solver '{}' unavailable (set NIBLI_CLINGO / add to \
             PATH).",
            cfg.binary
        );
        return;
    }

    let report = run_naf_corpus(corpus_naf::NAF_CASES, &cfg);
    for outcome in &report.outcomes {
        eprintln!("{}", outcome.summary());
    }
    let (agree, diverge, skip, error) = report.tally();
    eprintln!(
        "nibli-verify NAF: {agree} agree / {diverge} diverge / {skip} skip / {error} error \
         ({} of {} checked)",
        report.checked(),
        corpus_naf::NAF_CASES.len()
    );

    let errors: Vec<String> = report.errors().iter().map(|o| o.summary()).collect();
    assert!(errors.is_empty(), "harness errors:\n{}", errors.join("\n"));

    let divergences: Vec<String> = report.divergences().iter().map(|o| o.summary()).collect();
    assert!(
        divergences.is_empty(),
        "soundness divergences (nibli disagreed with clingo on stratified NAF):\n{}",
        divergences.join("\n")
    );

    assert!(
        report.checked() >= MIN_CHECKED_NAF,
        "only {} of {} NAF cases reached the oracle (need >= {MIN_CHECKED_NAF}); gate near-vacuous",
        report.checked(),
        corpus_naf::NAF_CASES.len()
    );
}

/// Random-corpus NAF coverage: N deterministically-generated stratified-NAF programs must each
/// have nibli agree with clingo. Broadens the ASP gate far beyond the curated cases.
#[test]
fn random_naf_cases_agree_with_clingo() {
    let cfg = AspConfig::default();
    if !nibli_verify::oracle_asp::available(&cfg) {
        eprintln!(
            "nibli-verify random NAF gate SKIPPED: solver '{}' unavailable.",
            cfg.binary
        );
        return;
    }

    let count: u64 = std::env::var("NIBLI_VERIFY_NAF_RANDOM_COUNT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_NAF_RANDOM_COUNT);
    let report = run_random_naf(count, 0, &cfg);

    let (agree, diverge, skip, error) = report.tally();
    eprintln!(
        "nibli-verify random NAF: {agree} agree / {diverge} diverge / {skip} skip / {error} error \
         ({} of {count} checked)",
        report.checked()
    );

    let errors: Vec<String> = report.errors().iter().map(|o| o.summary()).collect();
    assert!(
        errors.is_empty(),
        "harness errors on random NAF cases:\n{}",
        errors.join("\n")
    );

    let divergences: Vec<String> = report.divergences().iter().map(|o| o.summary()).collect();
    assert!(
        divergences.is_empty(),
        "soundness divergences on random NAF cases (nibli disagreed with clingo):\n{}",
        divergences.join("\n")
    );

    // Stratified + mappable by construction, so most must actually reach the oracle.
    assert!(
        report.checked() as u64 >= count / 2,
        "only {} of {count} random NAF cases reached the oracle; sweep near-vacuous",
        report.checked()
    );
}
