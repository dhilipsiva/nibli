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
    ("alive", "jmive", 2, ["", "standard", "", "", ""]),
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
        4,
        ["result", "dividend", "divisor", "remainder", ""],
    ),
    // ── GISMU_PLACE_TEMPLATES word set (smuni's curated render frames) + the
    // remaining shipped-corpus/spec vocabulary — curated so the whole set the
    // renderer and corpora rely on carries pinned 3rd-person spellings and
    // labels. Arities are checked against smuni-dictionary AT BUILD TIME in
    // data mode (drift fails the build), so these numbers cannot silently rot.
    ("acts", "zukte", 3, ["agent", "means", "goal", "", ""]),
    ("makes", "zbasu", 3, ["maker", "made", "material", "", ""]),
    ("studies", "tadni", 2, ["student", "studied", "", "", ""]),
    ("tends", "kurji", 2, ["carer", "charge", "", "", ""]),
    ("owns", "ponse", 3, ["owner", "owned", "basis", "", ""]),
    (
        "prevents",
        "fanta",
        2,
        ["preventer", "prevented", "", "", ""],
    ),
    ("warns", "kajde", 3, ["warner", "warned", "danger", "", ""]),
    ("law", "flalu", 5, ["", "act", "community", "", ""]),
    (
        "entails",
        "nibli",
        3,
        ["premise", "conclusion", "logic", "", ""],
    ),
    ("reason", "krinu", 2, ["", "outcome", "", "", ""]),
    ("bird", "cipni", 2, ["", "species", "", "", ""]),
    ("fish", "finpe", 2, ["", "species", "", "", ""]),
    ("man", "nanmu", 1, ["", "", "", "", ""]),
    ("woman", "ninmu", 1, ["", "", "", "", ""]),
    ("child", "verba", 3, ["", "age", "standard", "", ""]),
    ("human", "remna", 1, ["", "", "", "", ""]),
    ("chemical", "xukmi", 3, ["", "substance", "purity", "", ""]),
    ("building", "dinju", 2, ["", "purpose", "", "", ""]),
    (
        "vehicle",
        "marce",
        4,
        ["", "cargo", "surface", "propulsion", ""],
    ),
    ("food", "cidja", 2, ["", "eater", "", "", ""]),
    (
        "liquid",
        "litki",
        3,
        ["", "composition", "conditions", "", ""],
    ),
    (
        "system",
        "ciste",
        4,
        ["", "structure", "components", "function", ""],
    ),
    ("logical", "logji", 2, ["", "conclusion", "", "", ""]),
    ("slow", "masno", 2, ["", "act", "", "", ""]),
    ("healthy", "kanro", 2, ["", "standard", "", "", ""]),
    ("certain", "birti", 2, ["", "belief", "", "", ""]),
    ("imaginary", "xanri", 2, ["", "imaginer", "", "", ""]),
    (
        "greater",
        "zmadu",
        4,
        ["", "exceeded", "quality", "margin", ""],
    ),
    (
        "less",
        "mleca",
        4,
        ["", "compared", "quality", "margin", ""],
    ),
    ("num_equal", "dunli", 3, ["", "compared", "quality", "", ""]),
    (
        "discovers",
        "facki",
        3,
        ["discoverer", "discovered", "subject", "", ""],
    ),
    (
        "correct",
        "drani",
        4,
        ["", "quality", "situation", "standard", ""],
    ),
    ("flaw", "cfila", 3, ["", "host", "effect", "", ""]),
    (
        "message",
        "notci",
        4,
        ["", "topic", "recipient", "sender", ""],
    ),
];

/// Long-tail alias pins: `(gismu, alias)` — generation overrides for words whose
/// derived first-gloss alias would fail the fail-closed build checks. Unlike
/// [`CURATED_ALIASES`] entries, pinned words take arity + place labels from the
/// normal generation chain (smuni arity; place_keywords → prose → positional).
/// Every pin exists for a listed reason; removing one re-breaks the build.
pub const ALIAS_PINS: &[(&str, &str)] = &[
    // First-gloss collisions (5 dump-wide groups; both sides pinned so intent
    // is explicit): account, gain, hold, lead, represent.
    ("janta", "bill"),
    ("jaspu", "passport"),
    ("lebna", "seize"),
    ("prali", "profit"),
    ("ralte", "retain"),
    ("sorcu", "store"),
    ("cnisa", "lead_metal"),
    ("lidne", "precede"),
    ("krati", "represent"),
    ("sinxa", "sign"),
    // SI-prefix scalar gismu — lensisku's first gloss is the numeric value
    // (".01", "1E-15", …), which is not ident-shaped; the metric prefix name is
    // the honest alias.
    ("centi", "centi"),
    ("decti", "deci"),
    ("dekto", "deka"),
    ("femti", "femto"),
    ("gigdo", "giga"),
    ("gocti", "yocto"),
    ("gotro", "yotta"),
    ("kilto", "kilo"),
    ("megdo", "mega"),
    ("mikri", "micro"),
    ("milti", "milli"),
    ("nanvi", "nano"),
    ("petso", "peta"),
    ("picti", "pico"),
    ("terto", "tera"),
    ("xatsi", "atto"),
    ("xecto", "hecto"),
    ("xexso", "exa"),
    ("zepti", "zepto"),
    ("zetro", "zetta"),
    // First gloss is a Klaro keyword.
    ("balvi", "later"),      // gloss "future"
    ("fasnu", "occurrence"), // gloss "event"
    ("fatci", "actual"),     // gloss "fact"
    ("klani", "quantity"),   // gloss "amount"
    ("purci", "earlier"),    // gloss "past"
    // No gloss_keywords in the export at all.
    ("jegvo", "abrahamic"),
    ("jukni", "spider"),
    ("tirxu", "tiger"),
    // First gloss shadows a Lojban word ("curve" is itself a gismu) — an alias
    // equal to a dictionary word would shadow the identity-gismu passthrough.
    ("kruvi", "bend"),
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
