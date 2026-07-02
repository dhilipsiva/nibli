//! CI gate: every curated Horn/NAF-free case must have nibli agree with Vampire.
//!
//! If the prover is unavailable the test skips cleanly (so `cargo test` is green in any
//! environment); inside the Nix dev shell Vampire is present, so it runs for real.

use nibli_types::logic::LogicNode;
use nibli_verify::oracle_asp::AspConfig;
use nibli_verify::{
    corpora, corpus, corpus_naf, oracle::OracleConfig, run_corpus, run_corpus_slice,
    run_naf_corpus, run_random, run_random_count, run_random_naf, seam,
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

/// How many random exact-count cases the ASP gate runs; override with
/// `NIBLI_VERIFY_COUNT_RANDOM_COUNT`.
const DEFAULT_COUNT_RANDOM_COUNT: u64 = 100;

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

/// Random exact-count coverage: N deterministically-generated ground-fact count cases
/// (`PA lo P1 cu P2` queries) must each have nibli agree with clingo's `#count` over the
/// stable model. The generator stays inside the guarded fragment (no rules, no `du`, no
/// tense — see `filter::count_case_guard`), so both TRUE and closed-world FALSE count
/// verdicts are exercised at scale.
#[test]
fn random_count_cases_agree_with_clingo() {
    let cfg = AspConfig::default();
    if !nibli_verify::oracle_asp::available(&cfg) {
        eprintln!(
            "nibli-verify random count gate SKIPPED: solver '{}' unavailable.",
            cfg.binary
        );
        return;
    }

    let count: u64 = std::env::var("NIBLI_VERIFY_COUNT_RANDOM_COUNT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_COUNT_RANDOM_COUNT);
    let report = run_random_count(count, 0, &cfg);

    let (agree, diverge, skip, error) = report.tally();
    eprintln!(
        "nibli-verify random count: {agree} agree / {diverge} diverge / {skip} skip / {error} \
         error ({} of {count} checked)",
        report.checked()
    );

    let errors: Vec<String> = report.errors().iter().map(|o| o.summary()).collect();
    assert!(
        errors.is_empty(),
        "harness errors on random count cases:\n{}",
        errors.join("\n")
    );

    let divergences: Vec<String> = report.divergences().iter().map(|o| o.summary()).collect();
    assert!(
        divergences.is_empty(),
        "soundness divergences on random count cases (nibli disagreed with clingo):\n{}",
        divergences.join("\n")
    );

    // Ground-fact + guarded-fragment by construction, so nearly all must reach the oracle.
    assert!(
        report.checked() as u64 >= count * 3 / 4,
        "only {} of {count} random count cases reached the oracle; sweep near-vacuous",
        report.checked()
    );
}

/// gerna→smuni compiler-seam gate: compile source Lojban end-to-end (parse + semantic compile)
/// and check the FOL against hand-verified structure (ground truth) + transformation invariants
/// (oracle-free). This is the FRONT-END analog of the Vampire/clingo oracle gates: the six proofs
/// + those gates verify logji against smuni's *already-compiled* IR, but nothing else verified that
/// gerna→smuni compiles the *source text* to the intended IR (the isolated smuni tests hand-build
/// ASTs, bypassing gerna). Needs no solver, so it never skips. See `nibli-verify/src/seam.rs`.
///
/// Honest scope: a corpus/property gate, not a proof. The structural golden cases catch a
/// *systematic* miscompilation (where the FOL is hand-verified); the metamorphic pairs catch
/// *transformation* bugs at scale. All words are in-tree fallback vocabulary, so it runs
/// identically with or without the dictionary data file.
#[test]
fn gerna_smuni_seam_conformance() {
    let mut structural = 0usize;
    let mut metamorphic = 0usize;

    // ── Structural golden (ground truth: the compiled FOL *shape* is hand-verified) ──

    // 1. Neo-Davidsonian event decomposition + arg→role mapping:
    //    `la .adam. cu gerku` → ∃ev. gerku(ev) ∧ gerku_x1(ev, adam) ∧ …
    {
        let b = seam::compile("la .adam. cu gerku").expect("compile fact");
        assert!(
            matches!(seam::root(&b), LogicNode::ExistsNode(_)),
            "fact root is ∃ (event existentially closed)"
        );
        assert!(
            seam::role_is_const(&b, "gerku_x1", "adam"),
            "x1 role is filled with the subject `adam`"
        );
        structural += 1;
    }

    // 2. Negation: `la .adam. cu na gerku` → ¬(∃ev. gerku…)
    {
        let b = seam::compile("la .adam. cu na gerku").expect("compile na");
        assert!(
            matches!(seam::root(&b), LogicNode::NotNode(_)),
            "`na` root is Not"
        );
        structural += 1;
    }

    // 3. Connectives map distinctly: `.e` → And, `.a` → Or (over two event groups).
    {
        let b_and = seam::compile("mi .e do gerku").expect("compile .e");
        assert!(
            matches!(seam::root(&b_and), LogicNode::AndNode(_)),
            "`.e` root is And"
        );
        let b_or = seam::compile("mi .a do gerku").expect("compile .a");
        assert!(
            matches!(seam::root(&b_or), LogicNode::OrNode(_)),
            "`.a` root is Or"
        );
        structural += 1;
    }

    // 4. Universal restriction is a material implication:
    //    `ro lo gerku cu danlu` → ∀v. (¬∃gerku(v) ∨ ∃danlu(v))
    {
        let b = seam::compile("ro lo gerku cu danlu").expect("compile ro lo");
        let LogicNode::ForAllNode((_, body)) = seam::root(&b) else {
            panic!("`ro lo` root is ∀, got {:?}", seam::root(&b));
        };
        let LogicNode::OrNode((left, _)) = seam::node(&b, *body) else {
            panic!(
                "∀ body is Or (implication), got {:?}",
                seam::node(&b, *body)
            );
        };
        assert!(
            matches!(seam::node(&b, *left), LogicNode::NotNode(_)),
            "implication antecedent (the restrictor) is negated"
        );
        structural += 1;
    }

    // 5. The ∃/∀ contrast: `lo gerku cu danlu` → ∃v. (∃gerku(v) ∧ ∃danlu(v)) — a conjunction,
    //    NOT the implication of case 4. (A bug swapping `lo`/`ro lo` would flip this.)
    {
        let b = seam::compile("lo gerku cu danlu").expect("compile lo");
        let LogicNode::ExistsNode((_, body)) = seam::root(&b) else {
            panic!("`lo` root is ∃, got {:?}", seam::root(&b));
        };
        assert!(
            matches!(seam::node(&b, *body), LogicNode::AndNode(_)),
            "∃ body is And (existential import), got {:?}",
            seam::node(&b, *body)
        );
        structural += 1;
    }

    // 6. `se` conversion swaps places x1↔x2 vs the plain form.
    {
        let plain = seam::compile("mi prami do").expect("compile plain");
        let conv = seam::compile("mi se prami do").expect("compile se");
        assert!(
            seam::role_is_const(&plain, "prami_x1", "mi")
                && seam::role_is_const(&plain, "prami_x2", "do"),
            "plain: x1=mi, x2=do"
        );
        assert!(
            seam::role_is_const(&conv, "prami_x1", "do")
                && seam::role_is_const(&conv, "prami_x2", "mi"),
            "se: x1=do, x2=mi (swapped)"
        );
        structural += 1;
    }

    // ── Metamorphic (oracle-free: two surface forms must compile to the SAME FOL) ──

    // A. `se` conversion cancels the place swap: `mi se prami do` ≡ `do prami mi`.
    {
        let a = seam::canonicalize(&seam::compile("mi se prami do").unwrap());
        let b = seam::canonicalize(&seam::compile("do prami mi").unwrap());
        assert_eq!(a, b, "metamorphic: `mi se prami do` ≡ `do prami mi`");
        metamorphic += 1;
    }

    // B. Seeded batch of `E se P F` ≡ `F P E` pairs over the fallback 2+-place vocab.
    const SEAM_BATCH: u64 = 60;
    for seed in 0..SEAM_BATCH {
        let (left, right) = seam::conversion_pair(seed);
        let lb = seam::canonicalize(
            &seam::compile(&left).unwrap_or_else(|e| panic!("compile '{left}': {e}")),
        );
        let rb = seam::canonicalize(
            &seam::compile(&right).unwrap_or_else(|e| panic!("compile '{right}': {e}")),
        );
        assert_eq!(lb, rb, "conversion pair seed {seed}: `{left}` ≢ `{right}`");
        metamorphic += 1;
    }

    eprintln!(
        "gerna→smuni seam: {structural} structural golden + {metamorphic} metamorphic checks passed"
    );

    // Non-vacuity: both families must have actually fired.
    assert!(
        structural >= 6,
        "structural family near-vacuous ({structural})"
    );
    assert!(
        metamorphic >= (SEAM_BATCH as usize),
        "metamorphic family near-vacuous ({metamorphic})"
    );
}
