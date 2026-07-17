//! Dictionary-arity differential — the `verify-dict` gate (`just verify-dict`).
//!
//! Cross-validates the SHIPPED corpus arities (the values that drive event
//! decomposition and strict-mode arity rejection) against Predilex, an
//! independent human-curated CC0 thesaurus of sememes-as-predicates (vendored
//! + pinned in `nibli-verify/vendor/predilex/`). Predilex lemmas are Lojban;
//! the corpus is English-keyed, so the gate keys each lemma through the
//! PERMANENT provenance bridge (`nibli_lexicon::by_provenance`) — exactly the
//! mapping the corpus records for every entry.
//!
//! THE INVARIANT IS A LOWER BOUND (see `nibli_verify::predilex`'s module doc):
//! a Predilex mapping proves the places it uses exist, never that no more do —
//! the sememes are systematically coarser than Lojban's place structures. So
//! the gate flags UNDERCOUNTS only: `corpus arity < Predilex bound` means the
//! corpus truncates places an independent source proves the word supports
//! (this gate's first run caught the `cusku` 3→4 fix). Overcounts are the
//! expected sememe coarseness and pass (tallied as `coarser`).
//!
//! ONE mode since the committed-corpus milestone: the corpus is committed Rust,
//! identical in every build. The corpus carries the gismu-derived predicates
//! (lujvo arrive as curated compound entries instead), so Predilex's lujvo
//! lemmas are structurally unmapped — the historical 5-entry lujvo undercount
//! allowlist retired with them.

use nibli_verify::predilex::{self, RowJudgment, SkipReason};
use std::collections::BTreeMap;

/// Non-vacuity floor: the gismu ∩ Predilex signal-bearing set (measured on the
/// committed corpus; a rule change that silently shrinks the checked set below
/// this trips the gate).
const MIN_CHECKED: usize = 120;

#[test]
fn dictionary_arities_cover_predilex_bounds() {
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
    let mut coarser = 0usize; // corpus arity > bound: expected sememe coarseness
    let mut unmapped = 0usize;
    let mut new_undercounts: Vec<String> = Vec::new();

    for (word, wb) in &bounds {
        // Lojban lemma → English corpus entry via the provenance bridge.
        let Some(entry) = nibli_lexicon::by_provenance(word) else {
            // Not corpus provenance under this lemma (lujvo, or an unported
            // word) — no judgment possible; never trips the floor.
            unmapped += 1;
            continue;
        };
        let corpus_arity = entry.places.len();
        if corpus_arity > wb.bound {
            coarser += 1;
        } else if corpus_arity == wb.bound {
            exact += 1;
        } else {
            new_undercounts.push(format!(
                "{word} ({}): corpus={corpus_arity} < predilex bound {} (rows: {})",
                entry.name,
                wb.bound,
                wb.provenance.join("; ")
            ));
        }
    }

    let checked = exact + coarser + new_undercounts.len();
    eprintln!(
        "predilex gate: {exact} exact + {coarser} coarser / {} NEW-undercount / \
         {unmapped} unmapped ({checked} checked of {} word bounds; row skips: {:?})",
        new_undercounts.len(),
        bounds.len(),
        skip_tally,
    );
    for d in &new_undercounts {
        eprintln!("NEW UNDERCOUNT {d}");
    }

    assert!(
        new_undercounts.is_empty(),
        "corpus arities UNDERCOUNT independent Predilex bounds (the corpus truncates \
         places the word supports — fix the entry's places):\n{}",
        new_undercounts.join("\n")
    );
    assert!(
        checked >= MIN_CHECKED,
        "only {checked} words checked (need >= {MIN_CHECKED}); gate near-vacuous"
    );
}
