//! Curated alias tables — the fallback-mode data, ALL IN RUST SOURCE (no data
//! files). Shared with `build.rs` via `#[path]` so the same tables drive codegen
//! and stay unit-testable in-crate.
//!
//! These entries double as the PIN TABLE once full lensisku generation lands
//! (KLARO_TODO "klaro-dictionary full generation"): pins win in BOTH build modes,
//! so the spellings below can never flap between the data and no-data builds —
//! the same cross-mode discipline smuni-dictionary's CORE_GISMU_ARITIES pins
//! exist for.
//!
//! Naming policy (user decision, 2026-07-12): HONEST-GENERIC ONLY — each alias is
//! the honest generic English of its gismu, never a domain overlay (`zanru` is
//! `approves`, not the GDPR corpus reading "consents"; `ckape` is `dangerous`,
//! not "at_risk"). Verbal predicates use third-person-singular form so claim
//! position reads as English (`eats(Adam)` = "Adam eats"); noun/adjective class
//! predicates stay bare (`dog`, `person`, `red`).
//!
//! Direction-correctness notes (deviations from early draft examples, both in the
//! honest direction): `bilga` → `obliged` (bilga x1 IS the obliged party;
//! "obligates" would invert the reading — the surface-flipped `obligated` lives in
//! [`CONVERTED_ALIASES`]); `ckape` → `dangerous` (jbovlaste: x1 is the peril
//! SOURCE, dangerous to x2 — not "endangered").

/// Plain aliases: `(alias, gismu, arity, place_labels)`.
///
/// Covers the full `FALLBACK_GISMU_ENTRIES` word set
/// (smuni-dictionary/build.rs — arities copied verbatim) plus `bilga`/`curmi`
/// (which reach smuni's no-data build via its gloss-override table). Place labels
/// are curated only where the jbovlaste place structure is unambiguous; `""`
/// means positional (named-arg authors fall back to `x1..x5`). Labels are
/// SURFACE-order (identity here — swaps live only in [`CONVERTED_ALIASES`]).
pub const CURATED_ALIASES: &[(&str, &str, u8, [&str; 5])] = &[
    // ── Motion / transfer ──
    (
        "goes",
        "klama",
        5,
        ["goer", "destination", "origin", "route", "means"],
    ),
    (
        "carries",
        "bevri",
        5,
        ["carrier", "cargo", "destination", "origin", "route"],
    ),
    ("mails", "mrilu", 5, ["sender", "item", "recipient", "", ""]),
    ("walks", "cadzu", 3, ["walker", "surface", "", "", ""]),
    (
        "runs",
        "bajra",
        4,
        ["runner", "surface", "limbs", "gait", ""],
    ),
    (
        "sells",
        "vecnu",
        4,
        ["seller", "goods", "buyer", "price", ""],
    ),
    ("gives", "dunda", 3, ["giver", "gift", "recipient", "", ""]),
    // ── Mental / communicative ──
    ("loves", "prami", 2, ["lover", "loved", "", "", ""]),
    ("likes", "nelci", 2, ["liker", "liked", "", "", ""]),
    (
        "desires",
        "djica",
        3,
        ["desirer", "desired", "purpose", "", ""],
    ),
    ("needs", "nitcu", 3, ["needer", "needed", "purpose", "", ""]),
    (
        "knows",
        "djuno",
        4,
        ["knower", "known", "subject", "standard", ""],
    ),
    (
        "understands",
        "jimpe",
        2,
        ["understander", "understood", "", "", ""],
    ),
    ("sees", "viska", 3, ["seer", "seen", "conditions", "", ""]),
    ("hears", "tirna", 3, ["hearer", "heard", "", "", ""]),
    (
        "talks",
        "tavla",
        4,
        ["speaker", "listener", "topic", "language", ""],
    ),
    (
        "expresses",
        "cusku",
        4,
        ["speaker", "statement", "audience", "medium", ""],
    ),
    (
        "teaches",
        "ctuca",
        5,
        ["teacher", "student", "lesson", "subject", "method"],
    ),
    (
        "writes",
        "ciska",
        5,
        ["writer", "text", "surface", "tool", ""],
    ),
    ("meets", "penmi", 3, ["meeter", "met", "place", "", ""]),
    ("able", "kakne", 2, ["", "act", "", "", ""]),
    // ── Actions ──
    ("does", "gasnu", 2, ["agent", "act", "", "", ""]),
    ("eats", "citka", 2, ["eater", "food", "", "", ""]),
    ("drinks", "pinxe", 2, ["drinker", "beverage", "", "", ""]),
    ("kills", "catra", 2, ["killer", "killed", "", "", ""]),
    ("uses", "pilno", 3, ["user", "tool", "purpose", "", ""]),
    ("cuts", "katna", 3, ["cutter", "cut", "tool", "", ""]),
    (
        "removes",
        "vimcu",
        4,
        ["remover", "removed", "source", "result", ""],
    ),
    ("governs", "turni", 2, ["governor", "governed", "", "", ""]),
    // ── Deontic / regulatory ──
    ("obliged", "bilga", 3, ["", "duty", "standard", "", ""]),
    (
        "permits",
        "curmi",
        3,
        ["permitter", "act", "conditions", "", ""],
    ),
    ("approves", "zanru", 2, ["approver", "approved", "", "", ""]),
    ("rule", "javni", 3, ["", "act", "community", "", ""]),
    // ── Class predicates (x1 is a …) ──
    ("dog", "gerku", 2, ["", "breed", "", "", ""]),
    ("cat", "mlatu", 2, ["", "breed", "", "", ""]),
    ("animal", "danlu", 2, ["", "species", "", "", ""]),
    ("person", "prenu", 1, ["", "", "", "", ""]),
    ("name", "cmene", 3, ["name", "named", "user", "", ""]),
    ("bed", "ckana", 2, ["", "", "", "", ""]),
    ("home", "zdani", 2, ["", "resident", "", "", ""]),
    ("market", "zarci", 3, ["", "goods", "operator", "", ""]),
    ("predicate", "bridi", 3, ["", "", "", "", ""]),
    ("data", "datni", 3, ["", "topic", "gatherer", "", ""]),
    // ── Properties / states ──
    ("born", "jbena", 4, ["child", "parent", "date", "place", ""]),
    ("dead", "morsi", 1, ["", "", "", "", ""]),
    ("alive", "jmive", 1, ["", "", "", "", ""]),
    ("fast", "sutra", 2, ["", "", "", "", ""]),
    ("beautiful", "melbi", 3, ["", "observer", "aspect", "", ""]),
    ("big", "barda", 3, ["", "dimension", "standard", "", ""]),
    ("small", "cmalu", 3, ["", "dimension", "standard", "", ""]),
    ("good", "xamgu", 3, ["", "beneficiary", "standard", "", ""]),
    ("bad", "xlali", 3, ["", "victim", "standard", "", ""]),
    (
        "dangerous",
        "ckape",
        3,
        ["", "victim", "conditions", "", ""],
    ),
    ("thin", "cinla", 3, ["", "direction", "standard", "", ""]),
    ("increases", "zenba", 3, ["", "quality", "extent", "", ""]),
    ("blue", "blanu", 1, ["", "", "", "", ""]),
    ("red", "xunre", 1, ["", "", "", "", ""]),
    ("yellow", "pelxu", 1, ["", "", "", "", ""]),
    ("green", "crino", 1, ["", "", "", "", ""]),
    // ── Numeric / compute (x1 = result; SURFACE_SYNTAX §5 names) ──
    (
        "product",
        "pilji",
        3,
        ["result", "multiplicand", "multiplier", "", ""],
    ),
    ("sum", "sumji", 3, ["result", "augend", "addend", "", ""]),
    (
        "quotient",
        "dilcu",
        3,
        ["result", "dividend", "divisor", "", ""],
    ),
];

/// Converted-form aliases: `(alias, gismu, swap)` where `swap = n` means the
/// surface argument order is the gismu's with x1 ↔ xn exchanged (the se/te/ve/xe
/// family — the only permutations the AstBuffer's `Selbri::Converted` expresses).
/// NEVER generated — curated only (SURFACE_SYNTAX §13). Labels are positional:
/// auto-swapping the plain entry's curated labels risks silent place rerouting,
/// the exact failure class the alias differential gate exists to catch.
pub const CONVERTED_ALIASES: &[(&str, &str, u8)] = &[
    ("metabolized_by", "katna", 2),
    ("permitted", "curmi", 2),
    ("obligated", "bilga", 2),
];
