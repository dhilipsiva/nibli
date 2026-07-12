//! Klaro conformance helpers — the data + plumbing behind the two klaro gates
//! in `tests/klaro_gate.rs` (parity layers 2 and 3 of the Klaro 100%-sync
//! guarantee; layer 1 is `klaro::render`'s compile-time exhaustiveness guard).
//!
//! - [`kompile`] compiles KLARO text to its FOL `LogicBuffer` through the same
//!   post-parse stages as [`crate::seam::compile`] does for Lojban (smuni +
//!   `transform_compute_nodes` with the default compute set), so the two
//!   front-ends' buffers are comparable.
//! - [`battery_line`] is one step of the Klaro↔Lojban translation battery:
//!   Lojban → gerna AST → `klaro::render` → `klaro::parse_checked` → both
//!   sides through smuni → canonicalized LogicBuffer equality. Render totality
//!   over the shipped corpora is parity layer 3: a render failure is a gate
//!   failure unless the exact line is allowlisted in the gate.
//! - [`CONSTRUCT_INVENTORY`] is parity layer 2: one row per SURFACE_SYNTAX
//!   §3–§9 construct; every row must `kompile`, rows with a Lojban twin must
//!   compile EQUAL (canonicalized). Vocabulary is FALLBACK-SAFE (the gates
//!   never need `dictionary-en.json`, like the seam gate).
//!
//! Recorded decision (2026-07-12, was "decide when this gate lands"): the two
//! emitter limitations — `exactly N`/`the` BLOCK determiners and block
//! restrictors carrying relative clauses — stay DOCUMENTED fail-closed forms
//! rather than being lifted: the battery direction (Lojban→Klaro) can never
//! produce them, and Klaro authors get targeted errors with the inline-form
//! workaround (SURFACE_SYNTAX O7).

use nibli_types::logic::LogicBuffer;

use crate::seam;

/// Compile KLARO text end-to-end: `klaro::parse_checked` (parse + resolve +
/// emit) → smuni → compute-node marking with logji's default compute set —
/// the same post-parse stages `seam::compile` applies to Lojban text.
pub fn kompile(text: &str) -> Result<LogicBuffer, String> {
    let ast = klaro::parse_checked(text).map_err(|e| format!("klaro parse '{text}': {e}"))?;
    let mut buf =
        smuni::compile_from_gerna_ast(ast).map_err(|e| format!("smuni(klaro) '{text}': {e}"))?;
    logji::transform_compute_nodes(&mut buf, &logji::default_compute_predicates());
    Ok(buf)
}

/// Canonicalized Debug form — the comparison key for buffer equality.
pub fn canonical(buf: &LogicBuffer) -> String {
    format!("{:?}", seam::canonicalize(buf))
}

/// One translation-battery step for a Lojban line that BOTH gerna and the
/// engine front-end accept. Returns the rendered Klaro on success (for
/// reporting); errors carry enough context to act on.
pub fn battery_line(lojban: &str) -> Result<String, String> {
    let lojban_buf = seam::compile(lojban)?;
    let gerna_ast = gerna::parse_checked(lojban).map_err(|e| format!("gerna '{lojban}': {e}"))?;
    let klaro_text =
        klaro::render::render(&gerna_ast).map_err(|e| format!("render of '{lojban}': {e}"))?;
    let klaro_buf = kompile(&klaro_text).map_err(|e| format!("{e} (rendered from '{lojban}')"))?;
    let lojban_canon = canonical(&lojban_buf);
    let klaro_canon = canonical(&klaro_buf);
    if lojban_canon != klaro_canon {
        return Err(format!(
            "compiled LogicBuffers differ\n  lojban: {lojban}\n  klaro:  {klaro_text}"
        ));
    }
    Ok(klaro_text)
}

/// One inventory row: a Klaro spelling for a spec construct, optionally with a
/// Lojban twin whose compiled buffer must be canonically EQUAL.
pub struct ConstructCase {
    pub spec_section: &'static str,
    pub klaro: &'static str,
    pub lojban: Option<&'static str>,
}

const fn case(
    spec_section: &'static str,
    klaro: &'static str,
    lojban: Option<&'static str>,
) -> ConstructCase {
    ConstructCase {
        spec_section,
        klaro,
        lojban,
    }
}

/// Parity layer 2: one row per SURFACE_SYNTAX §3–§9 construct. The gate
/// asserts every row kompiles, every twin matches, and per-section floors.
pub const CONSTRUCT_INVENTORY: &[ConstructCase] = &[
    // ── §3 terms ──
    case("§3", "person(Adam).", Some("la .adam. cu prenu")),
    case("§3", "goes(Djan_Smit).", None),
    case("§3", "loves(me, you).", Some("mi prami do")),
    case("§3", "big(this).", Some("ti barda")),
    case("§3", "dog(it_a).", Some("ko'a gerku")),
    case("§3", "dog($x).", Some("da gerku")),
    case("§3", "goes(?).", Some("ma klama")),
    case("§3", "loves(me, _).", Some("mi prami zo'e")),
    case("§3", "product(50, 5, 10).", None),
    case("§3", "name(\"any text\", Adam).", None),
    // ── §4 determiners / restrictors ──
    case("§4", "goes(some dog).", Some("lo gerku cu klama")),
    case("§4", "goes(the dog).", Some("le gerku cu klama")),
    case("§4", "animal(every dog).", Some("ro lo gerku cu danlu")),
    case("§4", "goes(every the dog).", Some("ro le gerku cu klama")),
    case("§4", "red(exactly 2 red).", Some("re lo xunre cu xunre")),
    case("§4", "goes(no dog).", Some("no lo gerku cu klama")),
    case(
        "§4",
        "permitted(every loves.loved).",
        Some("ro lo se prami cu se curmi"),
    ),
    case(
        "§4",
        "permitted(every tends(some data)).",
        Some("ro lo kurji be lo datni cu se curmi"),
    ),
    case(
        "§4",
        "goes(every loves(x2: it)).",
        Some("ro lo se prami cu klama"),
    ),
    case("§4", "goes(some ~dog).", Some("lo na gerku cu klama")),
    // ── §5 predications ──
    case(
        "§5",
        "goes(me, destination: some market).",
        Some("mi klama lo zarci"),
    ),
    case("§5", "goes(x2: some market).", Some("klama fe lo zarci")),
    case(
        "§5",
        "healthy data(Kanrek).",
        Some("la .kanrek. cu kanro datni"),
    ),
    case("§5", "[big fast] dog(Rex).", None),
    case("§5", "dog+cat(me).", None),
    case("§5", "Kim = Adam.", Some("la .kim. cu du la .adam.")),
    case("§5", "goes(me) via uses(this).", None),
    case(
        "§5",
        "desires(me, event { goes(you) }).",
        Some("mi djica lo nu do klama"),
    ),
    case(
        "§5",
        "knows(me, fact { dog(Adam) }).",
        Some("mi djuno lo du'u la .adam. cu gerku"),
    ),
    case(
        "§5",
        "able(me, property { fast(slot) }).",
        Some("mi kakne lo ka ce'u sutra"),
    ),
    case(
        "§5",
        "likes(me, amount { fast(you) }).",
        Some("mi nelci lo ni do sutra"),
    ),
    case(
        "§5",
        "likes(me, concept { goes(you) }).",
        Some("mi nelci lo si'o do klama"),
    ),
    // ── §6 claims ──
    case("§6", "~goes(me).", Some("mi na klama")),
    case("§6", "past dog(Dan).", Some("pu la .dan. cu gerku")),
    case("§6", "now goes(me).", Some("mi ca klama")),
    case("§6", "future goes(me).", Some("mi ba klama")),
    case("§6", "must goes(me).", None),
    case("§6", "may goes(me).", None),
    case("§6", "past ~goes(me).", None),
    case(
        "§6",
        "goes(me) & eats(you).",
        Some("mi klama .ije do citka"),
    ),
    case(
        "§6",
        "goes(me) | eats(you).",
        Some("mi klama .ija do citka"),
    ),
    case(
        "§6",
        "goes(me) <-> eats(you).",
        Some("mi klama .ijo do citka"),
    ),
    case(
        "§6",
        "goes(me) ^ eats(you).",
        Some("mi klama .iju do citka"),
    ),
    case(
        "§6",
        "dog(Rex) -> animal(Rex).",
        Some("ganai la .rex. cu gerku gi la .rex. cu danlu"),
    ),
    case("§6", "(goes(me) | eats(you)) -> big(this).", None),
    case(
        "§6",
        "all $x: dog($x) -> animal($x).",
        Some("ro da zo'u ganai da gerku gi da danlu"),
    ),
    case(
        "§6",
        "every dog $d: animal($d).",
        Some("ro da zo'u ganai da gerku gi da danlu"),
    ),
    case("§6", "some dog $d: big($d) & goes($d).", None),
    // ── §7 relative clauses ──
    case(
        "§7",
        "permitted(every person where approves).",
        Some("ro lo prenu poi zanru cu se curmi"),
    ),
    case(
        "§7",
        "beautiful(every person where ~cat).",
        Some("ro lo prenu poi na mlatu cu melbi"),
    ),
    case(
        "§7",
        "goes(some dog also big).",
        Some("lo gerku noi barda cu klama"),
    ),
    case(
        "§7",
        "dangerous(every chemical where increases where thin).",
        Some("ro lo xukmi poi zenba poi cinla cu ckape"),
    ),
    case(
        "§7",
        "goes(Adam where dog).",
        Some("la .adam. poi gerku cu klama"),
    ),
    case(
        "§7",
        "goes(some dog where big(it)).",
        Some("lo gerku poi ke'a barda cu klama"),
    ),
    // ── §8 queries ──
    case(
        "§8",
        "goes(?, destination: some market).",
        Some("ma klama lo zarci"),
    ),
    // ── §9 files / statements ──
    case("§9", "goes(me). eats(you).", Some("mi klama .i do citka")),
];
