//! The KR→smuni seam-conformance gate (`just verify-kr-seam`, part of `ci`) —
//! the KR front-end's independent correctness oracle, built to OUTLIVE the
//! Lojban front-end (KR_TODO.md: THE DROP deletes the Klaro↔Lojban twin
//! battery, whose equality oracle currently carries this role). NO LOJBAN
//! ANYWHERE in this file: coverage is re-anchored on
//!
//! 1. **Structural FOL goldens** — hand-verified `LogicBuffer` shapes for the
//!    core construct classes (the `gerna_smuni_seam_conformance` pattern from
//!    differential_gate.rs, re-anchored on KR spellings), probing nodes
//!    directly via `seam::{root, node, pred_args, role_is_const}`.
//! 2. **The construct-inventory acceptance sweep** — every
//!    `CONSTRUCT_INVENTORY` KR spelling must compile (the Lojban twin column
//!    is ignored here; its equality leg lives in klaro_gate until THE DROP).
//! 3. **KR-internal metamorphic relations** — curated pairs (incl. the O7
//!    block-every ≡ prenex pin, re-anchored KR≡KR) + a seeded batch from
//!    `kr_seam::metamorphic_pair`, compared by canonicalized-buffer equality.
//! 4. **The re-homed Klaro determinism leg** (`determinism_corpus_klaro_native`,
//!    moved from klaro_twins.rs, which dies at THE DROP): the `.klaro`
//!    determinism corpus replayed natively against the pinned `# =>` verdicts.
//!
//! Vocabulary is curated-core only, so the gate is FULL-STRENGTH in both
//! dictionary modes and NEVER skips.

use nibli_types::logic::{LogicNode, LogicalTerm};
use nibli_verify::klaro_battery::{CONSTRUCT_INVENTORY, canonical, kompile};
use nibli_verify::{kr_seam, seam};

/// Seeded metamorphic batch size (mirrors the Lojban seam gate's SEAM_BATCH).
const SEAM_BATCH: u64 = 60;

#[test]
fn kr_smuni_seam_conformance() {
    let mut structural = 0usize;
    let mut metamorphic = 0usize;

    // ── 1. structural FOL goldens (hand-verified shapes, direct probes) ──

    // Ground fact: Neo-Davidsonian event decomposition —
    // `dog(Adam).` → ∃ev. gerku(ev) ∧ gerku_x1(ev, adam) ∧ …
    {
        let b = kompile("dog(Adam).").unwrap();
        assert!(
            matches!(seam::root(&b), LogicNode::ExistsNode(_)),
            "ground fact must be event-existential: {:?}",
            seam::root(&b)
        );
        assert!(
            seam::role_is_const(&b, "gerku_x1", "adam"),
            "x1 role must carry the constant"
        );
        structural += 1;
    }

    // Negation: `~P` → NotNode root.
    {
        let b = kompile("~dog(Adam).").unwrap();
        assert!(
            matches!(seam::root(&b), LogicNode::NotNode(_)),
            "~P root is not NotNode: {:?}",
            seam::root(&b)
        );
        structural += 1;
    }

    // Operators: `&` → AndNode, `|` → OrNode.
    {
        let b = kompile("dog(Adam) & cat(Betis).").unwrap();
        assert!(matches!(seam::root(&b), LogicNode::AndNode(_)));
        let b = kompile("dog(Adam) | cat(Betis).").unwrap();
        assert!(matches!(seam::root(&b), LogicNode::OrNode(_)));
        structural += 1;
    }

    // The rule shape: `every` compiles to ∀-implication —
    // ForAll(v, Or(Not(restrictor), matrix)).
    {
        let b = kompile("animal(every dog).").unwrap();
        let LogicNode::ForAllNode((_, body)) = seam::root(&b) else {
            panic!("every-rule root is not ForAllNode: {:?}", seam::root(&b));
        };
        let LogicNode::OrNode((l, _)) = seam::node(&b, *body) else {
            panic!("every-rule body is not OrNode: {:?}", seam::node(&b, *body));
        };
        assert!(
            matches!(seam::node(&b, *l), LogicNode::NotNode(_)),
            "every-rule antecedent is not negated: {:?}",
            seam::node(&b, *l)
        );
        structural += 1;
    }

    // The ∃-conjunction contrast: `some` is Exists(v, And(restrictor, matrix))
    // — NOT an implication (the some/every semantic split, spec §4).
    {
        let b = kompile("goes(some dog).").unwrap();
        let LogicNode::ExistsNode((_, body)) = seam::root(&b) else {
            panic!("some root is not ExistsNode: {:?}", seam::root(&b));
        };
        assert!(
            matches!(seam::node(&b, *body), LogicNode::AndNode(_)),
            "some body is not AndNode: {:?}",
            seam::node(&b, *body)
        );
        structural += 1;
    }

    // Converted-alias argument routing: `owned` = se ponse, so
    // `owned(Rex, Adam).` must land Adam in ponse_x1 (owner) and Rex in
    // ponse_x2 (owned) — a wrong permutation silently reroutes arguments.
    {
        let b = kompile("owned(Rex, Adam).").unwrap();
        assert!(
            seam::role_is_const(&b, "ponse_x1", "adam"),
            "converted alias must route the owner to ponse_x1"
        );
        assert!(
            seam::role_is_const(&b, "ponse_x2", "rex"),
            "converted alias must route the owned to ponse_x2"
        );
        structural += 1;
    }

    // Named-argument place routing: `destination:` is klama's x2.
    {
        let b = kompile("goes(me, destination: some market).").unwrap();
        let args = seam::pred_args(&b, "klama_x2").expect("klama_x2 role present");
        assert!(
            matches!(&args[1], LogicalTerm::Variable(_)),
            "named destination must fill x2 with the description's variable: {args:?}"
        );
        // And the description's restrictor is the market predicate.
        assert!(
            seam::pred_args(&b, "zarci_x1").is_some(),
            "the market description must decompose to zarci roles"
        );
        structural += 1;
    }

    // Tense: `past P` → PastNode root.
    {
        let b = kompile("past dog(Dan).").unwrap();
        assert!(
            matches!(seam::root(&b), LogicNode::PastNode(_)),
            "past P root is not PastNode: {:?}",
            seam::root(&b)
        );
        structural += 1;
    }

    // Equality: `=` is the flat 2-arg identity predicate (union-find keyed),
    // never event-decomposed.
    {
        let b = kompile("Kim = Adam.").unwrap();
        let args = seam::pred_args(&b, "du").expect("flat du predicate");
        assert!(
            matches!(
                args.as_slice(),
                [LogicalTerm::Constant(a), LogicalTerm::Constant(b)]
                    if a == "kim" && b == "adam"
            ),
            "= must compile to flat du(kim, adam): {args:?}"
        );
        structural += 1;
    }

    // Prenex: `all $x: A -> B` → ForAll over a material implication.
    {
        let b = kompile("all $x: dog($x) -> animal($x).").unwrap();
        let LogicNode::ForAllNode((_, body)) = seam::root(&b) else {
            panic!("prenex root is not ForAllNode: {:?}", seam::root(&b));
        };
        let LogicNode::OrNode((l, _)) = seam::node(&b, *body) else {
            panic!("prenex body is not OrNode: {:?}", seam::node(&b, *body));
        };
        assert!(
            matches!(seam::node(&b, *l), LogicNode::NotNode(_)),
            "prenex implication antecedent is not negated"
        );
        structural += 1;
    }

    // Abstractions are opaque: `event { … }` compiles to a content-hash
    // marker, never an inlined sub-proof obligation.
    {
        let b = kompile("desires(me, event { goes(you) }).").unwrap();
        assert!(
            canonical(&b).contains("__abs_"),
            "event abstraction must compile to an opaque __abs_ marker"
        );
        structural += 1;
    }

    // THE O3 PIN (re-hosted from klaro_gate so it survives THE DROP):
    // deontic outermost, tense inside — Obligatory(Past(…)).
    {
        let b = kompile("must past goes(me).").unwrap();
        let LogicNode::ObligatoryNode(inner) = seam::root(&b) else {
            panic!(
                "must past P root is not ObligatoryNode: {:?}",
                seam::root(&b)
            );
        };
        assert!(
            matches!(seam::node(&b, *inner), LogicNode::PastNode(_)),
            "must past P second layer is not PastNode"
        );
        structural += 1;
    }

    // Exact-count roots (re-hosted): `no dog` is the exactly-0 CountNode.
    {
        let b = kompile("goes(no dog).").unwrap();
        let LogicNode::CountNode((_, count, _)) = seam::root(&b) else {
            panic!("no-dog root is not CountNode: {:?}", seam::root(&b));
        };
        assert_eq!(*count, 0, "`no dog` must be the exactly-0 CountNode");
        structural += 1;
    }

    // `?` independence (Lojban-free re-anchoring of the ma-semantics pin):
    // two `?` occurrences never co-refer, so the buffer must DIFFER from the
    // explicitly co-referring `$x … $x` spelling.
    {
        assert_ne!(
            canonical(&kompile("loves(?, ?).").unwrap()),
            canonical(&kompile("loves($x, $x).").unwrap()),
            "`?` occurrences must be independent witnesses, not co-referring"
        );
        structural += 1;
    }

    // ── 2. construct-inventory acceptance sweep (KR side only) ──
    let mut per_section = std::collections::BTreeMap::<&str, usize>::new();
    for case in CONSTRUCT_INVENTORY {
        kompile(case.klaro).unwrap_or_else(|e| {
            panic!(
                "inventory {} {:?} does not compile: {e}",
                case.spec_section, case.klaro
            )
        });
        *per_section.entry(case.spec_section).or_default() += 1;
    }
    for section in ["§3", "§4", "§5", "§6", "§7", "§8", "§9"] {
        assert!(
            per_section.get(section).copied().unwrap_or(0) >= 1,
            "inventory lost its {section} rows"
        );
    }
    let inventory: usize = per_section.values().sum();
    assert!(inventory >= 30, "inventory shrank: {inventory} rows");

    // ── 3. KR-internal metamorphic relations ──

    // THE O7 PIN, re-anchored KR≡KR (was pinned against the Lojban prenex):
    // the block-every form IS the prenex implication shape.
    assert_eq!(
        canonical(&kompile("every dog $d: animal($d).").unwrap()),
        canonical(&kompile("all $x: dog($x) -> animal($x).").unwrap()),
        "O7: block-every must lower to the prenex implication shape"
    );
    metamorphic += 1;

    // Named ≡ positional.
    assert_eq!(
        canonical(&kompile("goes(me, some market).").unwrap()),
        canonical(&kompile("goes(me, destination: some market).").unwrap()),
        "named argument must equal its positional spelling"
    );
    metamorphic += 1;

    // Converted alias ≡ raw gismu with explicit xN labels.
    assert_eq!(
        canonical(&kompile("owned(Rex, Adam).").unwrap()),
        canonical(&kompile("ponse(x2: Rex, x1: Adam).").unwrap()),
        "converted alias must equal the label-permuted base predicate"
    );
    metamorphic += 1;

    // Seeded batch: three metamorphic families over curated vocabulary.
    for seed in 0..SEAM_BATCH {
        let (a, b) = kr_seam::metamorphic_pair(seed);
        assert_eq!(
            canonical(&kompile(&a).unwrap_or_else(|e| panic!("{a:?}: {e}"))),
            canonical(&kompile(&b).unwrap_or_else(|e| panic!("{b:?}: {e}"))),
            "metamorphic pair diverged (seed {seed}):\n  a: {a}\n  b: {b}"
        );
        metamorphic += 1;
    }

    // ── non-vacuity floors ──
    eprintln!(
        "kr→smuni seam: {structural} structural golden + {inventory} inventory + \
         {metamorphic} metamorphic checks passed"
    );
    assert!(
        structural >= 10,
        "structural family near-vacuous ({structural})"
    );
    assert!(
        metamorphic >= (SEAM_BATCH as usize) + 3,
        "metamorphic family near-vacuous ({metamorphic})"
    );
}

/// The Klaro determinism leg — RE-HOMED from klaro_twins.rs (which dies with
/// the Lojban twins at THE DROP): the `.klaro` determinism corpus replayed
/// through the native engine in Klaro mode against the SAME byte-identical
/// `# =>` verdict annotations as the other runtimes (Wasmtime via
/// `smoke-gasnu-determinism`, node/V8 via `verify-wasm-node`). The corpus is
/// curated-core vocabulary only, so this leg is full-strength in BOTH
/// dictionary modes. The parser is deliberately re-rolled, not shared — the
/// determinism legs must not share code paths beyond the engine.
#[test]
fn determinism_corpus_klaro_native() {
    use nibli_engine::{Language, NibliEngine};

    enum COp {
        Assert(String),
        Query(String, String),
        Retract(usize),
    }

    let corpus = include_str!("../../determinism-corpus.klaro");
    let mut ops: Vec<COp> = Vec::new();
    let mut pending_q: Option<String> = None;
    for raw in corpus.lines() {
        let line = raw.trim();
        if let Some(ann) = line.strip_prefix("# =>") {
            let q = pending_q
                .take()
                .expect("`# =>` annotation without a preceding query");
            ops.push(COp::Query(q, ann.trim().to_string()));
        } else if line.is_empty() || line.starts_with('#') {
            continue;
        } else if let Some(q) = line.strip_prefix("? ") {
            assert!(pending_q.is_none(), "unannotated query before: {q}");
            pending_q = Some(q.to_string());
        } else if let Some(k) = line.strip_prefix(":retract ") {
            ops.push(COp::Retract(k.trim().parse().expect("retract index")));
        } else {
            ops.push(COp::Assert(line.to_string()));
        }
    }
    assert!(pending_q.is_none(), "trailing unannotated query");

    let engine = NibliEngine::new();
    engine.set_language(Language::Klaro);
    let mut ids: Vec<Vec<u64>> = Vec::new();
    let mut checked = 0usize;
    for op in &ops {
        match op {
            COp::Assert(l) => {
                let fact_ids = engine
                    .assert_text(l)
                    .unwrap_or_else(|e| panic!("assert '{l}': {e}"));
                ids.push(fact_ids);
            }
            COp::Retract(k) => {
                for fid in &ids[*k] {
                    engine
                        .retract_fact(*fid)
                        .unwrap_or_else(|e| panic!("retract #{k}: {e}"));
                }
            }
            COp::Query(q, expected) => {
                let (verdict, _) = engine
                    .query_text_raw_proof(q)
                    .unwrap_or_else(|e| panic!("query '{q}': {e}"));
                let got = nibli_engine::display_query_result(&verdict);
                assert_eq!(
                    &got, expected,
                    "KLARO native verdict for '{q}' diverges from the pinned annotation"
                );
                checked += 1;
            }
        }
    }
    assert!(
        checked >= 15,
        "determinism klaro leg hollowed out: {checked}"
    );
}
