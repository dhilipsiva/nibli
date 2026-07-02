//! CI gate: the gerna ↔ camxes parse-differential (see `nibli_verify::parser_diff`).
//!
//! One-directional by design: every sentence gerna ACCEPTS must parse under the
//! official Lojban grammar (ilmentufa camxes). gerna implements a fragment, so a
//! gerna-reject carries no signal; a gerna-accept that camxes rejects means the
//! engine reasons over text that is not Lojban — the front-end over-acceptance
//! this gate exists to catch.
//!
//! Skips cleanly when the reference parser is unavailable (needs `node` + an
//! ilmentufa checkout via `NIBLI_CAMXES_DIR`; the Nix dev shell provides both).

use std::collections::HashSet;

use nibli_verify::parser_diff::{self, CamxesConfig, ParseOutcome};
use nibli_verify::{corpora, generator};

/// Seeds per generator for the random batch; override with
/// `NIBLI_VERIFY_PARSER_RANDOM_COUNT`. Each seed contributes a whole case's lines
/// (KB + query), deduplicated before hitting the reference parser.
const DEFAULT_PARSER_RANDOM_COUNT: u64 = 40;

/// The gate must actually compare a meaningful number of unique sentences.
const MIN_CHECKED: usize = 100;

/// Known gerna over-acceptances shipped in a corpus. EMPTY since the corpus fixes:
/// the gate's first run found five (four DDI lines with the invalid cmevla
/// `.fenituin.` — a rising diphthong after a consonant, renamed `.fenitoin.`; one
/// readme line using the relaxed `je na` selbri-connective negation, rewritten to
/// the official `jenai`, which gerna now parses). Note gerna's GRAMMAR still accepts
/// both relaxed forms — this gate guarantees no shipped or generated line USES them.
///
/// INVARIANT (enforced below): every entry must STILL diverge — once a line is
/// fixed, its entry must be deleted, so this list can never go stale.
const KNOWN_DIVERGENCES: &[&str] = &[];

#[test]
fn gerna_accepted_sentences_are_camxes_parseable() {
    let cfg = CamxesConfig::default();
    if !parser_diff::available(&cfg) {
        eprintln!(
            "nibli-verify parser gate SKIPPED: camxes unavailable (need `node` on PATH and \
             NIBLI_CAMXES_DIR pointing at an ilmentufa checkout — the Nix shell provides both)."
        );
        return;
    }

    // 1. Every unique non-comment line of the shipped corpora…
    let mut lines: Vec<String> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    for corpus in [corpora::GDPR, corpora::DDI, corpora::README] {
        for line in corpora::lines(corpus) {
            if seen.insert(line.to_string()) {
                lines.push(line.to_string());
            }
        }
    }
    // 2. …plus a seeded random batch from all three case generators (facts, rules,
    //    du links, tensed facts, NAF restrictors, count queries — every surface shape
    //    the differential gates exercise).
    let n: u64 = std::env::var("NIBLI_VERIFY_PARSER_RANDOM_COUNT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_PARSER_RANDOM_COUNT);
    for seed in 0..n {
        for case in [
            generator::random_case(seed),
            generator::random_naf_case(seed),
            generator::random_count_case(seed),
        ] {
            for line in case.kb.iter().chain(std::iter::once(&case.query)) {
                if seen.insert(line.clone()) {
                    lines.push(line.clone());
                }
            }
        }
    }

    let outcomes: Vec<ParseOutcome> = lines
        .iter()
        .map(|l| parser_diff::run_line(&cfg, l))
        .collect();

    let checked = outcomes.iter().filter(|o| o.is_checked()).count();
    let mut known_diverging = 0usize;
    let mut new_diverging: Vec<String> = Vec::new();
    for o in outcomes.iter().filter(|o| o.is_divergence()) {
        let ParseOutcome::Diverge { line, .. } = o else {
            unreachable!()
        };
        if KNOWN_DIVERGENCES.contains(&line.as_str()) {
            known_diverging += 1;
            eprintln!(
                "known-diverge (allowlisted, pending corpus fix): {}",
                o.summary()
            );
        } else {
            new_diverging.push(o.summary());
        }
    }
    let errors: Vec<String> = outcomes
        .iter()
        .filter(|o| o.is_error())
        .map(|o| o.summary())
        .collect();
    let skipped = outcomes.len() - checked - errors.len();
    eprintln!(
        "nibli-verify parser: {} agree / {} new-diverge / {known_diverging} known-diverge / \
         {skipped} skip / {} error ({checked} of {} unique lines checked)",
        checked - new_diverging.len() - known_diverging,
        new_diverging.len(),
        errors.len(),
        outcomes.len()
    );

    assert!(
        errors.is_empty(),
        "parser-differential harness errors:\n{}",
        errors.join("\n")
    );
    assert!(
        new_diverging.is_empty(),
        "gerna accepts sentences the official grammar rejects (front-end over-acceptance):\n{}",
        new_diverging.join("\n")
    );
    // The allowlist must never go stale: every entry still diverges (a fixed or
    // removed line forces its entry's deletion here).
    assert_eq!(
        known_diverging,
        KNOWN_DIVERGENCES.len(),
        "an allowlisted divergence no longer diverges (or its line left the corpora) — \
         remove the stale entry from KNOWN_DIVERGENCES"
    );
    assert!(
        checked >= MIN_CHECKED,
        "only {checked} unique lines reached the reference parser (need >= {MIN_CHECKED}); \
         gate near-vacuous"
    );
}
