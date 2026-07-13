//! KR conformance helpers — the data + plumbing behind the KR seam gate
//! (`tests/nibli_kr_seam_gate.rs`; parity layer 1 is `nibli_kr::render`'s compile-time
//! exhaustiveness guard).
//!
//! - [`kompile`] compiles KR text to its FOL `LogicBuffer` through the shipped
//!   post-parse stages (smuni + `transform_compute_nodes` with the default
//!   compute set).
//! - [`CONSTRUCT_INVENTORY`] is the acceptance inventory: one row per
//!   NIBLI_KR §3–§9 construct; every row must `kompile` (per-section
//!   floors in the gate). Vocabulary is FALLBACK-SAFE (the gate never needs
//!   `dictionary-en.json`). The Lojban-twin equality column and the
//!   translation-battery step retired with the Lojban front-end at THE DROP
//!   (their coverage re-anchored in the KR seam gate's structural goldens +
//!   metamorphic relations).
//!
//! Recorded decision (2026-07-12, was "decide when this gate lands"): the two
//! emitter limitations — `exactly N`/`the` BLOCK determiners and block
//! restrictors carrying relative clauses — stay DOCUMENTED fail-closed forms:
//! KR authors get targeted errors with the inline-form workaround
//! (NIBLI_KR O7).

use nibli_types::logic::LogicBuffer;

use crate::seam;

/// Compile nibli KR text end-to-end: `nibli_kr::parse_checked` (parse + resolve +
/// emit) → smuni → compute-node marking with logji's default compute set —
/// the shipped engine runs after its parse step.
pub fn kompile(text: &str) -> Result<LogicBuffer, String> {
    let ast = nibli_kr::parse_checked(text).map_err(|e| format!("nibli-kr parse '{text}': {e}"))?;
    let mut buf = nibli_semantics::compile_from_gerna_ast(ast)
        .map_err(|e| format!("smuni(nibli-kr) '{text}': {e}"))?;
    nibli_reason::transform_compute_nodes(&mut buf, &nibli_reason::default_compute_predicates());
    Ok(buf)
}

/// Canonicalized Debug form — the comparison key for buffer equality.
pub fn canonical(buf: &LogicBuffer) -> String {
    format!("{:?}", seam::canonicalize(buf))
}

/// One inventory row: a KR spelling for a spec construct. (The Lojban twin
/// column retired with the twin battery at THE DROP; the rows are now pinned
/// by the KR seam gate's structural goldens + metamorphic relations instead.)
pub struct ConstructCase {
    pub spec_section: &'static str,
    pub nibli_kr: &'static str,
}

const fn case(spec_section: &'static str, nibli_kr: &'static str) -> ConstructCase {
    ConstructCase {
        spec_section,
        nibli_kr,
    }
}

/// Parity layer 2: one row per NIBLI_KR §3–§9 construct. The gate
/// asserts every row kompiles, every twin matches, and per-section floors.
pub const CONSTRUCT_INVENTORY: &[ConstructCase] = &[
    // ── §3 terms ──
    case("§3", "person(Adam)."),
    case("§3", "goes(Djan_Smit)."),
    case("§3", "loves(me, you)."),
    case("§3", "big(this)."),
    case("§3", "dog(it_a)."),
    case("§3", "dog($x)."),
    case("§3", "goes(?)."),
    case("§3", "loves(me, _)."),
    case("§3", "product(50, 5, 10)."),
    case("§3", "name(\"any text\", Adam)."),
    // ── §4 determiners / restrictors ──
    case("§4", "goes(some dog)."),
    case("§4", "goes(the dog)."),
    case("§4", "animal(every dog)."),
    case("§4", "goes(every the dog)."),
    case("§4", "red(exactly 2 red)."),
    case("§4", "goes(no dog)."),
    case("§4", "permitted(every loves.loved)."),
    case("§4", "permitted(every tends(some data))."),
    case("§4", "goes(every loves(x2: it))."),
    case("§4", "goes(some ~dog)."),
    // ── §5 predications ──
    case("§5", "goes(me, destination: some market)."),
    case("§5", "goes(x2: some market)."),
    case("§5", "healthy data(Kanrek)."),
    case("§5", "[big fast] dog(Rex)."),
    case("§5", "dog+cat(me)."),
    case("§5", "Kim = Adam."),
    case("§5", "goes(me) via uses(this)."),
    case("§5", "desires(me, event { goes(you) })."),
    case("§5", "knows(me, fact { dog(Adam) })."),
    case("§5", "able(me, property { fast(slot) })."),
    case("§5", "likes(me, amount { fast(you) })."),
    case("§5", "likes(me, concept { goes(you) })."),
    // ── §6 claims ──
    case("§6", "~goes(me)."),
    case("§6", "past dog(Dan)."),
    case("§6", "now goes(me)."),
    case("§6", "future goes(me)."),
    case("§6", "must goes(me)."),
    case("§6", "may goes(me)."),
    case("§6", "past ~goes(me)."),
    case("§6", "goes(me) & eats(you)."),
    case("§6", "goes(me) | eats(you)."),
    case("§6", "goes(me) <-> eats(you)."),
    case("§6", "goes(me) ^ eats(you)."),
    case("§6", "dog(Rex) -> animal(Rex)."),
    case("§6", "(goes(me) | eats(you)) -> big(this)."),
    case("§6", "all $x: dog($x) -> animal($x)."),
    case("§6", "every dog $d: animal($d)."),
    case("§6", "some dog $d: big($d) & goes($d)."),
    // ── §7 relative clauses ──
    case("§7", "permitted(every person where approves)."),
    case("§7", "beautiful(every person where ~cat)."),
    case("§7", "goes(some dog also big)."),
    case(
        "§7",
        "dangerous(every chemical where increases where thin).",
    ),
    case("§7", "goes(Adam where dog)."),
    case("§7", "goes(some dog where big(it))."),
    // ── §8 queries ──
    case("§8", "goes(?, destination: some market)."),
    // ── §9 files / statements ──
    case("§9", "goes(me). eats(you)."),
];
