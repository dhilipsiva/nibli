//! Predilex arity cross-validation — the data layer of the `verify-dict` gate.
//!
//! Predilex (<https://github.com/Ntsekees/Predilex>, CC0 1.0) is a thesaurus of
//! language-neutral sememes-as-predicates. Its `conlangs/Lojban.csv` maps 459
//! Lojban lemmas to sememes, giving an independent, human-curated arity signal
//! to cross-check `nibli-lexicon`'s per-word arities against (the arities
//! that drive event decomposition and strict-mode rejection). Vendored bytes +
//! pinned upstream commit live in `nibli-verify/vendor/predilex/` (VENDOR.md).
//!
//! ## The signal is a LOWER BOUND, not an equality
//!
//! A Predilex row maps a Lojban lemma onto a language-neutral sememe. The
//! sememes are systematically COARSER than Lojban's place structures (the
//! first full run showed ~90 gismu whose by-standard/via-medium places have no
//! sememe counterpart — `bangu` x1-language-of-x2-used-by-x3 maps to a
//! 1-place "is a language" sememe). A mapping therefore proves only that the
//! lemma HAS the places the mapping uses — never that it has no more:
//!
//! - With a slot-permutation token (`vatuli 132`), the digits name the Lojban
//!   places that fill the sememe's slots, so the lemma has at least
//!   `max(digits)` places. `X` marks a sememe slot no Lojban place fills (the
//!   sole instance is the copula row `me → digowi 1X`) and contributes
//!   nothing.
//! - With no token, the mapping is the identity over the sememe's slots, so
//!   the lemma has at least the master sememe arity (the `arity` column of the
//!   vendored `predilex-arity.csv` projection; about half the master rows
//!   carry no arity — those yield no identity signal).
//! - The `Features` column is NOT an arity and is deliberately unused: it
//!   pattern-matches the index of the abstraction-taking place, not valency —
//!   counter-example `cfipu` has `Features=1` but permutation `21` and true
//!   arity 2 (`ckaji`=2/x2-ka, `ckini`=3/x3-relation follow the same pattern).
//! - The coarse Supertype hints (`VI`/`VT`/`VD`) classify the sememe-side
//!   frame loosely (upstream `imsa` is `VT` over an arity-3 sememe) and are
//!   not used as signals.
//! - A word can have several rows (`cusku`: `V3T qekama 1324` → ≥4 and a `◇`
//!   dialect row `VD daraki 132` → ≥3): row bounds MAX-combine per word (the
//!   strongest requirement wins).
//!
//! The gate then checks `dictionary arity >= bound`: an UNDERCOUNT means the
//! shipped dictionary truncates places an independent source proves the word
//! supports (the bug class the lujvo component-letter fix addressed);
//! overcounts are the expected sememe coarseness and pass. This makes the
//! spike's "known place-deletion cases" structural instead of a curated list.
//!
//! Lemma normalization for dictionary lookup: the CSV uses the typographic
//! apostrophe U+2019 (`dumvi’a`) where nibli uses ASCII `'`, and prefixes
//! vowel-initial lemmas with a pause dot (`.utce`); both are normalized.
//! `*`-prefixed lemmas (unofficial words) and `lemma/N` sub-lemma variants are
//! skipped outright.

use std::collections::BTreeMap;

/// Vendored `conlangs/Lojban.csv` (verbatim upstream bytes, pinned SHA in VENDOR.md).
pub const LOJBAN_CSV: &str = include_str!("../vendor/predilex/Lojban.csv");
/// Vendored `id,arity` projection of the master `predilex.csv` (same pinned SHA).
pub const ARITY_CSV: &str = include_str!("../vendor/predilex/predilex-arity.csv");
/// Vendored `id,hypernyms` projection of the master `predilex.csv` (same pinned SHA).
pub const HYPERNYMS_CSV: &str = include_str!("../vendor/predilex/predilex-hypernyms.csv");

/// Supertype codes that denote a verbal (predicate) lemma. Anything else —
/// including the empty string and upstream data slips like a permutation
/// string in the Supertype column — carries no arity claim about the lemma.
const VERBAL_SUPERTYPES: &[&str] = &["V", "VI", "VT", "VD", "V3T", "VI_fi", "VT_fo", "VI_fi_fo"];

/// Record-level RFC-4180 reader: quoted fields may contain commas, doubled-quote
/// escapes, and embedded newlines; CR is tolerated at record boundaries. No
/// external `csv` dependency — the two vendored files are the only inputs.
pub fn parse_csv(input: &str) -> Vec<Vec<String>> {
    let mut records: Vec<Vec<String>> = Vec::new();
    let mut record: Vec<String> = Vec::new();
    let mut field = String::new();
    let mut in_quotes = false;
    let mut chars = input.chars().peekable();
    while let Some(c) = chars.next() {
        if in_quotes {
            if c == '"' {
                if chars.peek() == Some(&'"') {
                    chars.next();
                    field.push('"');
                } else {
                    in_quotes = false;
                }
            } else {
                field.push(c);
            }
        } else {
            match c {
                '"' => in_quotes = true,
                ',' => record.push(std::mem::take(&mut field)),
                '\r' => {}
                '\n' => {
                    record.push(std::mem::take(&mut field));
                    // A lone empty field is a blank line, not a record.
                    if record.len() > 1 || !record[0].is_empty() {
                        records.push(std::mem::take(&mut record));
                    } else {
                        record.clear();
                    }
                }
                _ => field.push(c),
            }
        }
    }
    if !field.is_empty() || !record.is_empty() {
        record.push(field);
        records.push(record);
    }
    records
}

/// One `Lojban.csv` data row, reduced to the columns the gate consumes.
#[derive(Debug, Clone)]
pub struct LexRow {
    /// Lemma normalized for dictionary lookup (U+2019 → `'`, leading `.` stripped).
    pub lemma: String,
    /// The lemma exactly as vendored (drives the `*`/`/` shape skips).
    pub raw_lemma: String,
    pub dialect: String,
    pub supertype: String,
    pub sememe_id: String,
    /// The slot-permutation token, if any (`132`, `1X`, …).
    pub perm: Option<String>,
}

const EXPECTED_HEADER: [&str; 14] = [
    "Lemma",
    "Discriminator",
    "Dialect",
    "Supertype",
    "Morphotype",
    "Features",
    "Sememe",
    "Definition",
    "Examples",
    "Synonyms",
    "Gloss",
    "Frequency",
    "Etymology",
    "Etymological notes",
];

/// Parse the vendored `Lojban.csv` into rows, asserting the exact upstream
/// header so a silent upstream schema change on a re-pin fails loudly.
pub fn lojban_rows() -> Vec<LexRow> {
    let records = parse_csv(LOJBAN_CSV);
    assert!(
        records[0].iter().map(String::as_str).eq(EXPECTED_HEADER),
        "vendored Lojban.csv header changed — re-verify the column mapping \
         before trusting the gate (got: {:?})",
        records[0]
    );
    records[1..]
        .iter()
        .map(|r| {
            assert_eq!(r.len(), 14, "malformed Lojban.csv record: {r:?}");
            let sememe_cell = r[6].trim();
            let mut parts = sememe_cell.split_whitespace();
            let sememe_id = parts.next().unwrap_or("").to_string();
            let perm = parts.next().map(str::to_string);
            LexRow {
                lemma: normalize_lemma(&r[0]),
                raw_lemma: r[0].clone(),
                dialect: r[2].clone(),
                supertype: r[3].clone(),
                sememe_id,
                perm,
            }
        })
        .collect()
}

/// U+2019 (the CSV's typographic apostrophe) → ASCII `'`; strip the leading
/// pause dot from vowel-initial lemmas. Matches the lensisku `word` keys the
/// dictionary PHF is built from.
fn normalize_lemma(raw: &str) -> String {
    raw.trim_start_matches('.').replace('\u{2019}', "'")
}

/// Sememe id → master arity. `None` = the master row has no usable scalar
/// arity (empty cell, `∞` variadic, or any other non-integer token).
pub fn master_arities() -> BTreeMap<String, Option<u32>> {
    let records = parse_csv(ARITY_CSV);
    assert!(
        records[0].iter().map(String::as_str).eq(["id", "arity"]),
        "predilex-arity.csv projection header changed: {:?}",
        records[0]
    );
    records[1..]
        .iter()
        .map(|r| (r[0].clone(), r[1].parse::<u32>().ok()))
        .collect()
}

/// Why a row yields no arity bound. Every reason is tallied by the gate so a
/// silent rule change shows up as a tally shift, not a vanished check.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SkipReason {
    /// `*`-prefixed lemma (unofficial/proposed word).
    UnofficialLemma,
    /// `lemma/N` place-variant sub-lemma.
    SubLemma,
    /// Empty Sememe cell.
    EmptySememe,
    /// Non-verbal (or unrecognized) Supertype — no arity claim.
    NonVerbal,
    /// No permutation token AND the sememe is missing from the master table
    /// (or its arity cell is empty/`∞`/junk) — no identity signal.
    MasterArityUnavailable,
    /// Permutation token has no usable digits (or a non-digit/non-X char).
    PermInvalid,
    /// Bound of 0 or > 5 (the dictionary caps arities to 1..=5).
    OutOfRange,
}

/// A row's judgment: a lower BOUND on the lemma's arity, or a reasoned skip.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RowJudgment {
    /// The lemma has at least this many places.
    Bound(usize),
    Skip(SkipReason),
}

/// Derive the arity lower bound for one row (the rule in the module doc).
pub fn row_arity_bound(row: &LexRow, master: &BTreeMap<String, Option<u32>>) -> RowJudgment {
    use RowJudgment::{Bound, Skip};
    if row.raw_lemma.starts_with('*') {
        return Skip(SkipReason::UnofficialLemma);
    }
    if row.raw_lemma.contains('/') {
        return Skip(SkipReason::SubLemma);
    }
    if row.sememe_id.is_empty() {
        return Skip(SkipReason::EmptySememe);
    }
    if !VERBAL_SUPERTYPES.contains(&row.supertype.as_str()) {
        return Skip(SkipReason::NonVerbal);
    }

    let bound = match &row.perm {
        Some(perm) => {
            // The digits name the Lojban places filling the sememe's slots —
            // the lemma has at least max(digits) places. `X` (a sememe slot no
            // Lojban place fills) contributes nothing. A perm carries its own
            // signal even when the master row has no arity.
            let mut max_digit = 0usize;
            for c in perm.chars() {
                match c.to_digit(10) {
                    Some(d) => max_digit = max_digit.max(d as usize),
                    None if c == 'X' => {}
                    None => return Skip(SkipReason::PermInvalid),
                }
            }
            if max_digit == 0 {
                return Skip(SkipReason::PermInvalid);
            }
            max_digit
        }
        None => {
            // Identity mapping over the sememe's slots.
            let Some(Some(master_arity)) = master.get(&row.sememe_id) else {
                return Skip(SkipReason::MasterArityUnavailable);
            };
            *master_arity as usize
        }
    };

    if bound == 0 || bound > 5 {
        return Skip(SkipReason::OutOfRange);
    }
    Bound(bound)
}

/// A word-level bound: the MAX over its rows' lower bounds (the strongest
/// requirement), with per-row provenance for the gate's divergence report.
#[derive(Debug, Clone)]
pub struct WordBound {
    pub bound: usize,
    pub provenance: Vec<String>,
}

/// All row judgments, paired with their rows (the gate tallies skips from this).
pub fn judged_rows() -> Vec<(LexRow, RowJudgment)> {
    let master = master_arities();
    lojban_rows()
        .into_iter()
        .map(|row| {
            let j = row_arity_bound(&row, &master);
            (row, j)
        })
        .collect()
}

/// Sememe id → hypernym sememe ids (the master's `hypernyms` column: sememe A
/// entails sememe B — first-order, monotone implications). The 208 `definition`
/// formulas in the master are, by contrast, higher-order lambda calculus with
/// arithmetic (second-order variables, limits, `∄ ≼ ⟛` operators — mostly
/// mathematical sememes) and are NOT translatable into nibli's FOL fragment;
/// the hypernym links are the mechanizable logical content.
pub fn hypernym_links() -> Vec<(String, String)> {
    let records = parse_csv(HYPERNYMS_CSV);
    assert!(
        records[0]
            .iter()
            .map(String::as_str)
            .eq(["id", "hypernyms"]),
        "predilex-hypernyms.csv projection header changed: {:?}",
        records[0]
    );
    let mut links = Vec::new();
    for r in &records[1..] {
        for h in r[1].split([';', ',', ' ']).filter(|s| !s.is_empty()) {
            links.push((r[0].clone(), h.to_string()));
        }
    }
    links
}

/// Lojban taxonomy edges derived from the Predilex hypernym links:
/// `(lemma_a, lemma_b)` meaning `∀x. lemma_a(x) ⇒ lemma_b(x)` — real-vocabulary
/// monotone Horn rules from an independent human-curated source (`cukta` ⇒
/// `rutni`, `bloti` ⇒ `marce` ⇒ `rutni`, …), consumed by the Track-A taxonomy
/// differential in `tests/differential_gate.rs`.
///
/// Conservative admission rule: both sememes must be mapped to VERBAL Lojban
/// lemmas (usual `*`/`/` shape skips) AND both must have master arity 1 — a
/// unary implication has no slot-mapping ambiguity (multi-place hypernym slot
/// semantics are not documented upstream). Reflexive links (upstream contains
/// e.g. `rutni ⇒ rutni`-shaped self-rows) are dropped. Every (lemma_a,
/// lemma_b) combination of a link's mapped lemmas is emitted — the caller
/// prunes lemmas that don't compile as brivla (e.g. the vowel-initial `ukta`).
/// Deduped and sorted for determinism.
pub fn taxonomy_edges() -> Vec<(String, String)> {
    let master = master_arities();
    let mut sem_to_lemmas: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for row in lojban_rows() {
        if row.raw_lemma.starts_with('*')
            || row.raw_lemma.contains('/')
            || row.sememe_id.is_empty()
            || !VERBAL_SUPERTYPES.contains(&row.supertype.as_str())
        {
            continue;
        }
        let lemmas = sem_to_lemmas.entry(row.sememe_id.clone()).or_default();
        if !lemmas.contains(&row.lemma) {
            lemmas.push(row.lemma.clone());
        }
    }
    let unary = |sem: &str| matches!(master.get(sem), Some(Some(1)));

    let mut edges: Vec<(String, String)> = Vec::new();
    for (sem_a, sem_b) in hypernym_links() {
        if sem_a == sem_b || !unary(&sem_a) || !unary(&sem_b) {
            continue;
        }
        let (Some(as_), Some(bs)) = (sem_to_lemmas.get(&sem_a), sem_to_lemmas.get(&sem_b)) else {
            continue;
        };
        for a in as_ {
            for b in bs {
                if a != b && !edges.contains(&(a.clone(), b.clone())) {
                    edges.push((a.clone(), b.clone()));
                }
            }
        }
    }
    edges.sort();
    edges
}

/// Per-word arity lower bounds: rows with a concrete bound, grouped by
/// normalized lemma, MAX-combined.
pub fn arity_bounds_by_word() -> BTreeMap<String, WordBound> {
    let mut by_word: BTreeMap<String, WordBound> = BTreeMap::new();
    for (row, judgment) in judged_rows() {
        let RowJudgment::Bound(bound) = judgment else {
            continue;
        };
        let prov = format!(
            "{} [{} {}{}{}]",
            row.raw_lemma,
            row.supertype,
            row.sememe_id,
            row.perm
                .as_deref()
                .map(|p| format!(" {p}"))
                .unwrap_or_default(),
            if row.dialect.is_empty() {
                String::new()
            } else {
                format!(" dialect={}", row.dialect)
            },
        );
        by_word
            .entry(row.lemma.clone())
            .and_modify(|w| {
                w.bound = w.bound.max(bound);
                w.provenance.push(prov.clone());
            })
            .or_insert(WordBound {
                bound,
                provenance: vec![prov],
            });
    }
    by_word
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn splitter_handles_quotes_commas_escapes_and_newlines() {
        let input = "\"a,b\",\"say \"\"hi\"\"\",plain\r\n\"multi\nline\",2\n";
        let recs = parse_csv(input);
        assert_eq!(recs.len(), 2);
        assert_eq!(recs[0], vec!["a,b", "say \"hi\"", "plain"]);
        assert_eq!(recs[1], vec!["multi\nline", "2"]);
    }

    #[test]
    fn splitter_skips_blank_lines_and_handles_missing_final_newline() {
        let recs = parse_csv("a,b\n\nc,d");
        assert_eq!(recs, vec![vec!["a", "b"], vec!["c", "d"]]);
    }

    #[test]
    fn vendored_files_parse_with_expected_shape() {
        let rows = lojban_rows();
        assert_eq!(rows.len(), 459, "Lojban.csv data-row count changed");
        let master = master_arities();
        assert!(
            master.len() > 9000,
            "arity projection truncated: {}",
            master.len()
        );
        // Projection sanity: nearly every referenced sememe id must resolve in
        // the master slice (catches a wrong-column or truncated projection).
        let referenced: Vec<&str> = rows
            .iter()
            .filter(|r| !r.sememe_id.is_empty())
            .map(|r| r.sememe_id.as_str())
            .collect();
        let resolved = referenced
            .iter()
            .filter(|id| master.contains_key(**id))
            .count();
        assert!(
            resolved * 100 >= referenced.len() * 95,
            "only {resolved}/{} referenced sememes resolve — projection out of sync",
            referenced.len()
        );
    }

    #[test]
    fn lemma_normalization() {
        assert_eq!(normalize_lemma("dumvi\u{2019}a"), "dumvi'a");
        assert_eq!(normalize_lemma(".utce"), "utce");
        assert_eq!(normalize_lemma("citka"), "citka");
    }

    /// The permutation/bound-derivation matrix.
    #[test]
    fn bound_derivation_matrix() {
        let mut master = BTreeMap::new();
        master.insert("s2".to_string(), Some(2));
        master.insert("s3".to_string(), Some(3));
        master.insert("svar".to_string(), None);
        let row = |sememe: &str, perm: Option<&str>| LexRow {
            lemma: "broda".into(),
            raw_lemma: "broda".into(),
            dialect: String::new(),
            supertype: "V".into(),
            sememe_id: sememe.into(),
            perm: perm.map(str::to_string),
        };
        use RowJudgment::{Bound, Skip};
        use SkipReason::*;
        // Perm → max digit is the bound (independent of master arity).
        assert_eq!(row_arity_bound(&row("s2", Some("21")), &master), Bound(2));
        assert_eq!(row_arity_bound(&row("s3", Some("132")), &master), Bound(3));
        assert_eq!(row_arity_bound(&row("s3", Some("312")), &master), Bound(3));
        // A perm names specific places even when the master row has no arity.
        assert_eq!(row_arity_bound(&row("svar", Some("21")), &master), Bound(2));
        // X contributes nothing: `1X` bounds at 1.
        assert_eq!(row_arity_bound(&row("s2", Some("1X")), &master), Bound(1));
        // Identity (no perm) → master arity.
        assert_eq!(row_arity_bound(&row("s2", None), &master), Bound(2));
        // Junk perms.
        assert_eq!(
            row_arity_bound(&row("s2", Some("ab")), &master),
            Skip(PermInvalid)
        );
        assert_eq!(
            row_arity_bound(&row("s2", Some("XX")), &master),
            Skip(PermInvalid)
        );
        // Variadic / missing master arity with no perm → no identity signal.
        assert_eq!(
            row_arity_bound(&row("svar", None), &master),
            Skip(MasterArityUnavailable)
        );
        assert_eq!(
            row_arity_bound(&row("nosuch", None), &master),
            Skip(MasterArityUnavailable)
        );
    }

    /// Taxonomy extraction: pinned real edges + shape guarantees. Runs without
    /// any solver, so a vendored re-pin that guts the hypernym join fails
    /// loudly even outside the Nix shell.
    #[test]
    fn taxonomy_edges_pinned_and_sane() {
        let edges = taxonomy_edges();
        // Pinned real edges from the 3dab179 vendored data.
        for want in [
            ("cukta", "rutni"),
            ("skami", "minji"),
            ("bloti", "marce"),
            ("cakyjukni", "danlu"),
        ] {
            assert!(
                edges.iter().any(|(a, b)| (a.as_str(), b.as_str()) == want),
                "expected taxonomy edge {want:?} missing (vendored data re-pinned?)"
            );
        }
        // No reflexive edges (upstream contains rutni ⇒ rutni-shaped self-links).
        assert!(edges.iter().all(|(a, b)| a != b), "reflexive edge leaked");
        // Non-vacuity floor: a re-pin or join regression that guts the set
        // must fail here, not silently shrink the differential.
        assert!(
            edges.len() >= 20,
            "only {} taxonomy edges extracted (need >= 20)",
            edges.len()
        );
        // Determinism: sorted, deduped.
        let mut sorted = edges.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(edges, sorted, "edges must be sorted + deduped");
    }

    /// Pinned REAL rows from the vendored bytes — these fail loudly if a
    /// re-pin changes the rows the rule's documentation is anchored on.
    #[test]
    fn pinned_real_rows() {
        let judged = judged_rows();
        let find = |raw: &str| -> Vec<&(LexRow, RowJudgment)> {
            judged.iter().filter(|(r, _)| r.raw_lemma == raw).collect()
        };
        use RowJudgment::{Bound, Skip};

        // cusku ×2: V3T qekama 1324 → ≥4; ◇ VD daraki 132 → ≥3; MAX = 4.
        let cusku = find("cusku");
        assert_eq!(cusku.len(), 2);
        let mut bounds: Vec<_> = cusku
            .iter()
            .filter_map(|(_, j)| match j {
                Bound(n) => Some(*n),
                _ => None,
            })
            .collect();
        bounds.sort_unstable();
        assert_eq!(bounds, vec![3, 4]);
        assert_eq!(arity_bounds_by_word().get("cusku").unwrap().bound, 4);

        // ckaji: identity mapping, arity-2 sememe → Bound(2).
        assert_eq!(find("ckaji")[0].1, Bound(2));

        // cabmoi: V davedo 1342 → Bound(4) (Features column deliberately unused).
        assert_eq!(find("cabmoi")[0].1, Bound(4));

        // cfipu: the Features≠arity counter-example — V rusese 21 → Bound(2).
        assert_eq!(find("cfipu")[0].1, Bound(2));

        // me: COP (non-verbal) — skipped before its 1X perm is even considered.
        assert_eq!(find("me")[0].1, Skip(SkipReason::NonVerbal));

        // Shape skips.
        assert_eq!(find("*kokcinela")[0].1, Skip(SkipReason::UnofficialLemma));
        assert_eq!(find("jmive/1")[0].1, Skip(SkipReason::SubLemma));
    }
}
