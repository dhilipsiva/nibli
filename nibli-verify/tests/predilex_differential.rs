//! Dictionary-arity differential — the `verify-dict` gate (`just verify-dict`).
//!
//! Cross-validates the SHIPPED `smuni-dictionary` arities (the values that
//! drive event decomposition and strict-mode arity rejection) against
//! Predilex, an independent human-curated CC0 thesaurus of sememes-as-
//! predicates (vendored + pinned in `nibli-verify/vendor/predilex/`).
//!
//! THE INVARIANT IS A LOWER BOUND (see `nibli_verify::predilex`'s module doc):
//! a Predilex mapping proves the places it uses exist, never that no more do —
//! the sememes are systematically coarser than Lojban's place structures. So
//! the gate flags UNDERCOUNTS only: `dictionary arity < Predilex bound` means
//! the shipped dictionary truncates places an independent source proves the
//! word supports (the bug class the lujvo component-letter arity fix
//! addressed, and what this gate's first run caught for `cusku`). Overcounts
//! are the expected sememe coarseness and pass (tallied as `coarser`), which
//! makes the historical spike's "known place-deletion cases" structural
//! instead of a curated allowlist.
//!
//! Two modes, detected from the dictionary artifact itself:
//! - FULL (local `just fetch-dict` build, ~10.9k entries). First-run tallies
//!   (pinned vendor SHA 3dab179): 198 words checked — 107 exact + 86 coarser +
//!   5 allowlisted undercounts, 0 new (after the cusku 3→4 fix this gate
//!   caught on its very first run), 55 unmapped.
//! - FALLBACK (CI build, ~140 curated entries, no lujvo): the same check over
//!   whatever resolves — the fallback arities are hand-written constants, so
//!   cross-checking even the small set has value.
//!
//! The dictionary size is a COMPILE-TIME property of the PHF; checking the
//! json file's presence at run time could lie about a stale build, so the mode
//! detector reads `DICTIONARY.len()` — the same artifact under test.

use nibli_verify::predilex::{self, RowJudgment, SkipReason};
use std::collections::BTreeMap;

/// Full-build detector: the fallback PHF has ~140 entries, the full lensisku
/// build ~10.9k. Anything past this floor is a data build.
const FULL_DICT_MIN: usize = 1000;

/// Non-vacuity floors, derived from the first real runs: full mode checked
/// 198 words, fallback mode 15 (the ~62 curated fallback gismu ∩ Predilex's
/// signal-bearing lemmas). A rule change that silently shrinks the checked set
/// below these trips the gate.
const MIN_CHECKED_FULL: usize = 150;
const MIN_CHECKED_FALLBACK: usize = 10;

/// Known, hand-verified UNDERCOUNTS: `(word, nibli_arity, predilex_bound)`.
///
/// An entry belongs here only when nibli's arity FAITHFULLY mirrors its
/// primary source (the lensisku definition's `$x_N$` place markers) while
/// Predilex maps the word onto a richer sememe — a lensisku definition-text
/// gap, not a derivation bug. A genuine derivation/override bug gets FIXED
/// instead (precedent: this gate's first run caught the `cusku` 3→4 override
/// pin; the lujvo component-letter fix caught `flubisli`).
/// INVARIANT (enforced below, value-pinned): in a FULL build every entry must
/// resolve AND still undercount with exactly the recorded pair — a fixed
/// arity, a vendored re-pin, or a rule change forces the stale entry out.
const KNOWN_UNDERCOUNTS: &[(&str, usize, usize)] = &[
    // All five: the lensisku definition marks only $x_1$, so the dictionary
    // (faithfully) derives arity 1; Predilex maps each onto a 2-place sememe.
    // jibykai — "$x_1$ does their job / works" (Predilex: VT capici, works-at).
    ("jibykai", 1, 2),
    // nonydza — "$x_1$ (property) is not satisfied by anything in the domain"
    // (Predilex: VT guvoga — property × domain).
    ("nonydza", 1, 2),
    // retyju'a — "$x_1$ is an interrogative sentence" (Predilex: V putive, asks).
    ("retyju'a", 1, 2),
    // roldza — "$x_1$ (property) is common to everything in the domain"
    // (Predilex: VT konuza).
    ("roldza", 1, 2),
    // suzdza — "$x_1$ (property) is satisfied by at least one member of the
    // domain" (Predilex: VT saruyo).
    ("suzdza", 1, 2),
];

#[test]
fn dictionary_arities_cover_predilex_bounds() {
    let dict_size = smuni_dictionary::DICTIONARY.len();
    let full_mode = dict_size >= FULL_DICT_MIN;
    if !full_mode {
        eprintln!(
            "predilex gate: FALLBACK MODE — dictionary has {dict_size} entries (curated \
             fallback build). Full validation needs `just fetch-dict` + rebuild."
        );
    }

    // Row-level skip tallies (bounds are per-word; skips are per-row).
    let mut skip_tally: BTreeMap<&'static str, usize> = BTreeMap::new();
    for (_, judgment) in predilex::judged_rows() {
        if let RowJudgment::Skip(reason) = judgment {
            let key = match reason {
                SkipReason::UnofficialLemma => "unofficial-lemma",
                SkipReason::SubLemma => "sub-lemma",
                SkipReason::EmptySememe => "empty-sememe",
                SkipReason::NonVerbal => "non-verbal",
                SkipReason::MasterArityUnavailable => "master-arity-unavailable",
                SkipReason::PermInvalid => "perm-invalid",
                SkipReason::OutOfRange => "out-of-range",
            };
            *skip_tally.entry(key).or_default() += 1;
        }
    }

    let bounds = predilex::arity_bounds_by_word();
    let mut exact = 0usize;
    let mut coarser = 0usize; // nibli arity > bound: expected sememe coarseness
    let mut unmapped = 0usize;
    let mut known_undercounts: Vec<&str> = Vec::new();
    let mut new_undercounts: Vec<String> = Vec::new();

    for (word, wb) in &bounds {
        let Some(nibli_arity) = smuni_dictionary::get_arity(word) else {
            // Not in the dictionary under this build — no judgment possible;
            // never trips floors or the invariant.
            unmapped += 1;
            continue;
        };
        if nibli_arity > wb.bound {
            coarser += 1;
        } else if nibli_arity == wb.bound {
            exact += 1;
        } else if KNOWN_UNDERCOUNTS
            .iter()
            .any(|(w, n, b)| *w == word.as_str() && *n == nibli_arity && *b == wb.bound)
        {
            known_undercounts.push(word);
        } else {
            new_undercounts.push(format!(
                "{word}: nibli={nibli_arity} < predilex bound {} (rows: {})",
                wb.bound,
                wb.provenance.join("; ")
            ));
        }
    }

    let checked = exact + coarser + known_undercounts.len() + new_undercounts.len();
    eprintln!(
        "predilex gate [{}]: {exact} exact + {coarser} coarser / {} known-undercount / \
         {} NEW-undercount / {unmapped} unmapped ({checked} checked of {} word bounds; \
         row skips: {:?})",
        if full_mode { "full" } else { "fallback" },
        known_undercounts.len(),
        new_undercounts.len(),
        bounds.len(),
        skip_tally,
    );
    for d in &new_undercounts {
        eprintln!("NEW UNDERCOUNT {d}");
    }

    assert!(
        new_undercounts.is_empty(),
        "dictionary arities UNDERCOUNT independent Predilex bounds (the dictionary \
         truncates places the word supports — fix the arity; allowlist only a verified \
         intentional cap):\n{}",
        new_undercounts.join("\n")
    );

    if full_mode {
        // Value-pinned still-undercounting invariant.
        assert_eq!(
            known_undercounts.len(),
            KNOWN_UNDERCOUNTS.len(),
            "an allowlisted undercount no longer holds as recorded (dictionary fix, \
             vendored re-pin, or rule change) — delete or re-verify the stale entry"
        );
        assert!(
            checked >= MIN_CHECKED_FULL,
            "only {checked} words checked in full mode (need >= {MIN_CHECKED_FULL}); \
             gate near-vacuous"
        );
    } else {
        assert!(
            checked >= MIN_CHECKED_FALLBACK,
            "only {checked} words checked in fallback mode (need >= {MIN_CHECKED_FALLBACK}); \
             gate near-vacuous"
        );
    }
}
