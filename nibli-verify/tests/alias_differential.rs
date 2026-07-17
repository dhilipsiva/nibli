//! Corpus differential — the `verify-alias-map` gate (`just verify-alias-map`).
//!
//! Since the committed-corpus milestone the dictionary is ONE committed Rust
//! table (`nibli-lexicon/src/corpus/`), const-validated at compile time and
//! identical in every build (the FULL/FALLBACK dual mode is gone). This gate
//! re-asserts the invariants from the SHIPPED artifact — independent of the
//! const guards that produced it — plus an end-to-end behavioral battery:
//!
//! 1. `alias_map_differential` — structural: per-entry arity/shape integrity,
//!    provenance round-trips (`by_provenance`/`canonical_alias`), swap validity
//!    (`2..=arity`, involution, base resolution), reserved-word exclusion and
//!    label totality/integrity, coverage floors.
//! 2. `alias_behavioral_battery` — for EVERY corpus entry, `name(A, B, …)`
//!    compiled through nibli-kr+nibli-semantics must equal its twin at the
//!    canonicalized-LogicBuffer level: a PLAIN entry twins with ITSELF under
//!    explicit `xN:` labels (named ≡ positional routing), a CONVERTED entry
//!    twins with its `swap.base` entry under the permuted labels — the
//!    cross-entry conversion oracle. (Swap-VALUE mutations are pinned by the
//!    seam gate's hand-written converted golden, not here — both battery sides
//!    derive from the same entry.)

use nibli_verify::nibli_kr_battery::{canonical, kompile};

/// Argument constants for the behavioral battery.
const ARG_NAMES: [&str; 5] = ["Adam", "Bob", "Kim", "Tom", "Sam"];

// Mirrors of the corpus const rules — the gate re-asserts label/name shape
// from the SHIPPED artifact, independent of the const validation.
fn ident_ok(s: &str) -> bool {
    let mut chars = s.chars();
    matches!(chars.next(), Some('a'..='z'))
        && chars.all(|c| matches!(c, 'a'..='z' | '0'..='9' | '_'))
}

fn looks_like_place_tag(s: &str) -> bool {
    s.len() == 2 && s.starts_with('x') && matches!(s.as_bytes()[1], b'1'..=b'5')
}

#[test]
fn alias_map_differential() {
    let mut offenders: Vec<String> = Vec::new();

    for entry in nibli_lexicon::corpus::corpus_entries() {
        let name = entry.name;

        // ── name + label integrity (totality is structural; re-assert shape) ──
        if !ident_ok(name) {
            offenders.push(format!("{name}: name is not ident-shaped"));
        }
        if nibli_lexicon::reserved::is_reserved(name) {
            offenders.push(format!("{name}: collides with a nibli KR keyword"));
        }
        if entry.places.is_empty() || entry.places.len() > 5 {
            offenders.push(format!(
                "{name}: arity {} outside 1..=5",
                entry.places.len()
            ));
        }
        for (i, label) in entry.places.iter().enumerate() {
            if label.is_empty() {
                offenders.push(format!("{name}: place x{} is unnamed", i + 1));
            }
            if !ident_ok(label) {
                offenders.push(format!("{name}: label {label:?} not ident-shaped"));
            }
            if nibli_lexicon::reserved::is_reserved(label) {
                offenders.push(format!("{name}: label {label:?} is a keyword"));
            }
            if looks_like_place_tag(label) {
                offenders.push(format!(
                    "{name}: label {label:?} shadows the raw x1..x5 escape hatch"
                ));
            }
            if entry.places[..i].contains(label) {
                offenders.push(format!("{name}: duplicate label {label:?}"));
            }
        }

        // ── provenance round-trips + swap validity ──
        match entry.swap {
            None => {
                // A canonical entry round-trips through the provenance bridge.
                match nibli_lexicon::canonical_alias(entry.source_gismu) {
                    Some(back) if back == name => {}
                    other => offenders.push(format!(
                        "{name}: canonical_alias({:?}) = {other:?}, expected the entry itself",
                        entry.source_gismu
                    )),
                }
            }
            Some(swap) => {
                if !(2..=entry.arity()).contains(&swap.with) {
                    offenders.push(format!(
                        "{name}: swap x1↔x{} outside 2..=arity({})",
                        swap.with,
                        entry.arity()
                    ));
                }
                // Swap twice = identity on the surface permutation (involution).
                let arity = entry.places.len();
                let mut perm: Vec<usize> = (0..arity).collect();
                perm.swap(0, swap.with as usize - 1);
                perm.swap(0, swap.with as usize - 1);
                if perm != (0..arity).collect::<Vec<usize>>() {
                    offenders.push(format!(
                        "{name}: swap x1↔x{} applied twice != identity",
                        swap.with
                    ));
                }
                // The base must exist, be unswapped, and share the provenance.
                match nibli_lexicon::alias(swap.base) {
                    None => offenders.push(format!("{name}: swap.base {:?} absent", swap.base)),
                    Some(base) => {
                        if base.swap.is_some() {
                            offenders.push(format!(
                                "{name}: swap.base {:?} is itself swapped",
                                swap.base
                            ));
                        }
                        if base.source_gismu != entry.source_gismu {
                            offenders.push(format!(
                                "{name}: swap.base {:?} gismu {:?} != {:?}",
                                swap.base, base.source_gismu, entry.source_gismu
                            ));
                        }
                    }
                }
            }
        }
    }

    // ── compound integrity from the shipped artifact ──
    for c in nibli_lexicon::corpus::corpus_compounds() {
        if !c.name.contains('+') {
            offenders.push(format!("compound {:?}: name lacks '+'", c.name));
        }
        if c.relation != c.name.replace('+', "_") {
            offenders.push(format!(
                "compound {:?}: relation {:?} != '+'->'_' derivation",
                c.name, c.relation
            ));
        }
        if nibli_lexicon::alias(c.relation).is_some() {
            offenders.push(format!(
                "compound relation {:?} shadows an atomic corpus entry",
                c.relation
            ));
        }
    }

    println!(
        "corpus gate: {} predicate entries + {} compounds checked",
        nibli_lexicon::corpus::corpus_entries().count(),
        nibli_lexicon::corpus::corpus_compounds().count()
    );
    assert!(
        offenders.is_empty(),
        "{} corpus offender(s):\n{}",
        offenders.len(),
        offenders.join("\n")
    );

    // ── coverage floors (the committed corpus is always the full table) ──
    let entries = nibli_lexicon::corpus::corpus_entries().count();
    assert!(
        entries >= 1300,
        "corpus hollowed out: {entries} entries (floor 1300)"
    );
    let converted = nibli_lexicon::corpus::corpus_entries()
        .filter(|e| e.swap.is_some())
        .count();
    assert!(
        converted >= 3,
        "converted-entry coverage collapsed: {converted} (floor 3)"
    );
}

#[test]
fn alias_behavioral_battery() {
    let mut checked = 0usize;
    let mut failures: Vec<String> = Vec::new();

    for entry in nibli_lexicon::corpus::corpus_entries() {
        let name = entry.name;
        let arity = entry.places.len();
        let nibli_kr_text = format!("{name}({}).", ARG_NAMES[..arity].join(", "));

        // A PLAIN entry twins with ITSELF under explicit `xN:` labels; a
        // CONVERTED entry twins with its swap.base under the permuted labels
        // its surface order implies (x1↔xk).
        let place_of = |pos: usize| -> usize {
            match entry.swap {
                None => pos,
                Some(swap) => {
                    let k = swap.with as usize;
                    if pos == 1 {
                        k
                    } else if pos == k {
                        1
                    } else {
                        pos
                    }
                }
            }
        };
        let twin_head: &str = match entry.swap {
            None => name,
            Some(swap) => swap.base,
        };
        let twin_args: Vec<String> = ARG_NAMES[..arity]
            .iter()
            .enumerate()
            .map(|(i, a)| format!("x{}: {a}", place_of(i + 1)))
            .collect();
        let twin_text = format!("{twin_head}({}).", twin_args.join(", "));

        let nibli_kr_buf = match kompile(&nibli_kr_text) {
            Ok(buf) => buf,
            Err(e) => {
                failures.push(format!("{name}: entry side failed: {nibli_kr_text}\n  {e}"));
                continue;
            }
        };
        let twin_buf = match kompile(&twin_text) {
            Ok(buf) => buf,
            Err(e) => {
                failures.push(format!("{name}: twin failed: {twin_text}\n  {e}"));
                continue;
            }
        };
        if canonical(&nibli_kr_buf) != canonical(&twin_buf) {
            failures.push(format!(
                "{name}: buffer mismatch\n  entry: {nibli_kr_text}\n  twin:  {twin_text}"
            ));
            continue;
        }
        checked += 1;
    }

    println!("alias behavioral battery: {checked} entries checked");
    assert!(
        failures.is_empty(),
        "{} behavioral failure(s):\n{}",
        failures.len(),
        failures.join("\n---\n")
    );
    assert!(
        checked >= 1300,
        "behavioral battery hollowed out: {checked} entries checked (floor 1300)"
    );
}
