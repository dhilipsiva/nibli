//! The two Klaro conformance gates (`just verify-klaro`, part of `ci`) —
//! oracle-free and never skipping, the klaro analog of
//! `gerna_smuni_seam_conformance`:
//!
//! 1. `klaro_seam_conformance` — parity layer 2: the CONSTRUCT_INVENTORY sweep
//!    (every SURFACE_SYNTAX §3–§9 construct kompiles; Lojban twins compile
//!    canonically EQUAL), structural goldens (the O3 wrapper-order pin, the O7
//!    block-determiner pin, exact-count roots, independent `?` witnesses),
//!    metamorphic pairs, and the fail-closed negative battery.
//! 2. `klaro_lojban_translation_battery` — parity layer 3: every line of the
//!    shipped corpora (+ seeded generator programs + conversion pairs) that the
//!    Lojban front-end compiles must render to Klaro that compiles to the SAME
//!    canonicalized LogicBuffer. Render failures are gate failures unless the
//!    exact line is in KNOWN_UNRENDERABLE (value-pinned, still-failing
//!    invariant — the KNOWN_DIVERGENCES pattern). DUAL-MODE: a fallback build
//!    (CI) lacks the generated long-tail aliases, so corpus vocabulary beyond
//!    the curated core cannot render there — those `dictionary-unknown` lines
//!    are tallied as fallback-vocab skips, the same disclosed degradation as
//!    every dual-mode gate; the full local build checks every line.

use nibli_verify::klaro_battery::{CONSTRUCT_INVENTORY, battery_line, canonical, kompile};
use nibli_verify::{corpora, generator, seam};

use nibli_types::logic::LogicNode;

// ─────────────────────────────────────────────────────────────────────────────
// Gate 1: seam conformance
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn klaro_seam_conformance() {
    // ── inventory sweep (parity layer 2) ──
    let mut per_section: std::collections::BTreeMap<&str, usize> = Default::default();
    for case in CONSTRUCT_INVENTORY {
        let klaro_buf =
            kompile(case.klaro).unwrap_or_else(|e| panic!("[{}] {e}", case.spec_section));
        if let Some(lojban) = case.lojban {
            let lojban_buf = seam::compile(lojban)
                .unwrap_or_else(|e| panic!("[{}] twin {e}", case.spec_section));
            assert_eq!(
                canonical(&klaro_buf),
                canonical(&lojban_buf),
                "[{}] twin mismatch\n  klaro:  {}\n  lojban: {}",
                case.spec_section,
                case.klaro,
                lojban
            );
        }
        *per_section.entry(case.spec_section).or_default() += 1;
    }
    // Non-vacuity floors: every section populated, total can't hollow out.
    for section in ["§3", "§4", "§5", "§6", "§7", "§8", "§9"] {
        assert!(
            per_section.get(section).copied().unwrap_or(0) >= 1,
            "inventory lost its {section} rows"
        );
    }
    let total: usize = per_section.values().sum();
    assert!(total >= 30, "inventory shrank: {total} rows");

    // ── structural goldens (direct LogicBuffer probes) ──

    // THE O3 PIN: deontic outermost, tense inside, matching smuni's verified
    // wrapper emission (Attitudinal(Tense(…))).
    let buf = kompile("must past goes(me).").unwrap();
    let root = *buf.roots.last().expect("root") as usize;
    let LogicNode::ObligatoryNode(inner) = &buf.nodes[root] else {
        panic!(
            "must past P root is not ObligatoryNode: {:?}",
            buf.nodes[root]
        );
    };
    assert!(
        matches!(&buf.nodes[*inner as usize], LogicNode::PastNode(_)),
        "must past P second layer is not PastNode: {:?}",
        buf.nodes[*inner as usize]
    );

    // Exact-count roots: `no dog` is CountNode with count 0.
    let buf = kompile("goes(no dog).").unwrap();
    let root = *buf.roots.last().unwrap() as usize;
    let LogicNode::CountNode((_, count, _)) = &buf.nodes[root] else {
        panic!("no-dog root is not CountNode: {:?}", buf.nodes[root]);
    };
    assert_eq!(*count, 0, "`no dog` must be the exactly-0 CountNode");

    // THE O7 PIN (CI edition): the block-every form IS the ro-da prenex shape.
    assert_eq!(
        canonical(&kompile("every dog $d: animal($d).").unwrap()),
        canonical(&seam::compile("ro da zo'u ganai da gerku gi da danlu").unwrap()),
        "O7: block-every must lower to the prenex implication shape"
    );

    // Independent `?` witnesses (exact ma semantics — never co-referring).
    assert_eq!(
        canonical(&kompile("loves(?, ?).").unwrap()),
        canonical(&seam::compile("ma prami ma").unwrap()),
        "`?` occurrences must be independent witnesses, like ma"
    );

    // Selbri-connective expansion (2026-07-12): the bridi-level Klaro spelling
    // of a connected selbri must equal the Lojban connective compilation —
    // block form for a universal subject, operator claim for a constant.
    assert_eq!(
        canonical(&kompile("every obligated $d: permitted($d) & ~prevents(x2: $d).").unwrap()),
        canonical(&seam::compile("ro lo se bilga cu se curmi jenai se fanta").unwrap()),
        "jenai expansion (universal subject) must equal the connective form"
    );
    assert_eq!(
        canonical(&kompile("every obligated $d: permitted($d) | prevents(x2: $d).").unwrap()),
        canonical(&seam::compile("ro lo se bilga cu se curmi ja se fanta").unwrap()),
        "ja expansion must equal the connective form"
    );
    assert_eq!(
        canonical(&kompile("permitted(Adam) & ~prevents(x2: Adam).").unwrap()),
        canonical(&seam::compile("la .adam. cu se curmi jenai se fanta").unwrap()),
        "jenai expansion (constant subject) must equal the connective form"
    );

    // Conversions inside tanru units (2026-07-12, with the smuni fidelity
    // fix): the curated converted alias is the Klaro spelling, and the swap
    // must be semantically live through the tanru.
    assert_eq!(
        canonical(&kompile("tends(me, some owned data).").unwrap()),
        canonical(&seam::compile("mi kurji lo se ponse datni").unwrap()),
        "converted alias as a tanru MODIFIER must equal `se ponse datni`"
    );
    assert_eq!(
        canonical(&kompile("dog owned(Adam).").unwrap()),
        canonical(&seam::compile("la .adam. cu gerku se ponse").unwrap()),
        "converted alias as a tanru HEAD must equal `gerku se ponse`"
    );

    // ── metamorphic pairs (canonicalized equality) ──
    let pairs: &[(&str, &str)] = &[
        // named ≡ positional ≡ reordered labels
        (
            "goes(me, some market).",
            "goes(me, destination: some market).",
        ),
        (
            "goes(me, destination: some market).",
            "goes(destination: some market, goer: me).",
        ),
        // converted alias ≡ explicit surface reorder ≡ direct gismu
        (
            "metabolized_by(Varfarin, Siptucin).",
            "cuts(x2: Varfarin, x1: Siptucin).",
        ),
        (
            "cuts(x2: Varfarin, x1: Siptucin).",
            "katna(x2: Varfarin, x1: Siptucin).",
        ),
        // selector ≡ linked named-it
        ("goes(every loves.loved).", "goes(every loves(x2: it))."),
    ];
    for (a, b) in pairs {
        assert_eq!(
            canonical(&kompile(a).unwrap()),
            canonical(&kompile(b).unwrap()),
            "metamorphic pair diverged:\n  a: {a}\n  b: {b}"
        );
    }
    // Cross-front-end leg of the conversion chain.
    assert_eq!(
        canonical(&kompile("metabolized_by(Varfarin, Siptucin).").unwrap()),
        canonical(&seam::compile("la .varfarin. cu se katna la .siptucin.").unwrap()),
        "converted alias must equal the Lojban se-conversion"
    );

    // ── fail-closed negatives (message-substring pins at the gate level) ──
    let negatives: &[(&str, &str)] = &[
        ("zzq(me).", "unknown predicate"),
        (
            "dog($a) & dog($b) & dog($c) & dog($d).",
            "4th distinct variable",
        ),
        ("goes(me, x1: you).", "filled twice"),
        ("dog(Adam, x3: you).", "unknown place label"),
        // The Python rule, both argument paths (build_args is shared):
        // a positional argument after a named argument is a compile error.
        ("goes(destination: some market, me).", "must come before"),
        ("goes(every loves(x2: it, me)).", "must come before"),
        ("goes(some dog where goes(me)).", "must mention `it`"),
        ("goes(slot).", "property"),
        ("~past goes(me).", "past ~P"),
        ("~~goes(me).", "double negation"),
        ("past (goes(me) & eats(you)).", "single predication"),
    ];
    for (text, needle) in negatives {
        let err = kompile(text).expect_err(text);
        assert!(err.contains(needle), "{text}: {err}");
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Gate 2: the translation battery
// ─────────────────────────────────────────────────────────────────────────────

/// Corpus lines that CANNOT yet render to Klaro, each with the reason. Exact
/// text, value-pinned: every entry must STILL fail (staleness check below),
/// and every failing line must be listed. CURRENTLY EMPTY — the first sweep
/// (2026-07-12) froze 7 lines in 3 classes, all lifted the same day by the
/// renderer-coverage bullet: conversions inside tanru units render via
/// curated converted aliases (with the smuni tanru-swap fidelity fix), selbri
/// connectives render via bridi-level expansion, and the two coined
/// words (`insekto`, `flaselcu'u` — absent from the lensisku export, so no
/// alias path can ever cover them) were replaced in readme.lojban with the
/// real gismu `cinki`/`pulji`. The mechanism stays: any future render
/// regression must be listed here with a reason or it fails the gate.
const KNOWN_UNRENDERABLE: &[(&str, &str)] = &[];

#[test]
fn klaro_lojban_translation_battery() {
    let mut lines: Vec<String> = Vec::new();
    for corpus in [corpora::GDPR, corpora::DDI, corpora::README] {
        lines.extend(corpora::lines(corpus).into_iter().map(str::to_owned));
    }
    for seed in 0..40u64 {
        let case = generator::random_case(seed);
        lines.extend(case.kb.iter().cloned());
        lines.push(case.query.clone());
        let (a, b) = seam::conversion_pair(seed);
        lines.push(a);
        lines.push(b);
    }

    let allowed: std::collections::HashMap<&str, &str> =
        KNOWN_UNRENDERABLE.iter().copied().collect();

    // Mode read from the artifact under test (the predilex-gate convention): a
    // fallback klaro-dictionary has ~96 gismu aliased, a full build ~1,338.
    let full_mode = klaro_dictionary::GISMU_TO_ALIAS.len() >= 1000;

    let mut checked = 0usize;
    let mut skipped = 0usize;
    let mut allowlisted = 0usize;
    let mut fallback_vocab_skipped = 0usize;
    let mut failures: Vec<String> = Vec::new();
    let mut stale_allowlist: Vec<&str> = Vec::new();

    for line in &lines {
        // Lines the Lojban front-end itself rejects never reach the seam —
        // nothing to translate (matches the parse-differential's scoping).
        if gerna::parse_checked(line).is_err() || seam::compile(line).is_err() {
            skipped += 1;
            continue;
        }
        match battery_line(line) {
            Ok(_) => {
                checked += 1;
                if allowed.contains_key(line.as_str()) {
                    stale_allowlist.push(Box::leak(line.clone().into_boxed_str()));
                }
            }
            Err(e) => {
                if allowed.contains_key(line.as_str()) {
                    allowlisted += 1;
                } else if !full_mode && e.contains("dictionary-unknown") {
                    // Long-tail vocabulary outside the curated fallback core —
                    // renderable only with the generated aliases (full build).
                    fallback_vocab_skipped += 1;
                } else {
                    failures.push(e);
                }
            }
        }
    }

    println!(
        "klaro battery: {checked} checked, {skipped} lojban-skipped, {allowlisted} allowlisted, \
         {fallback_vocab_skipped} fallback-vocab-skipped"
    );
    if !full_mode {
        eprintln!(
            "klaro battery: FALLBACK MODE — {fallback_vocab_skipped} corpus lines use vocabulary \
             beyond the curated core. Full validation needs `just fetch-dict` + rebuild."
        );
    }
    assert!(
        stale_allowlist.is_empty(),
        "allowlist entries now PASS — remove them: {stale_allowlist:?}"
    );
    assert_eq!(
        allowlisted,
        KNOWN_UNRENDERABLE.len(),
        "allowlist count drifted (an entry no longer appears in the corpus?)"
    );
    assert!(
        failures.is_empty(),
        "{} battery failure(s):\n{}",
        failures.len(),
        failures.join("\n---\n")
    );
    assert!(
        checked >= 100,
        "battery hollowed out: only {checked} lines checked"
    );
}
