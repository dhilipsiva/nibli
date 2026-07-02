//! Curated `(KB, query)` cases in the **stratified negation-as-failure + closed-world**
//! fragment — the fragment the classical Vampire gate skips and the clingo (ASP) oracle
//! covers. Each is hand-checked to be stratified: the negated predicate `R` is always a
//! BASE fact predicate (never a rule head), so no negative edge lies inside an SCC.
//!
//! The NAF mechanism is the negated restrictor `poi na R` ("… that is not R"): with no
//! `R`-witness the restrictor holds (closed-world) and the rule fires; with a witness it
//! does not. Most cases use plain-gismu heads (`cu morsi` etc.); the `gdpr_erasure_*`
//! pair at the end exercises the REAL GDPR rule verbatim (`se bilga` is a plain gismu and
//! the `lo nu` abstraction maps as an opaque constant — see `filter::buffer_asp_mappable`).
//! The `naf_du_*` cases mix in ground `du` identity links, which the translator
//! canonicalizes away (`asp::DuClasses`) — including the NAF-THROUGH-EQUALITY shape where
//! a witness blocks the rule for a merged entity.
//!
//! `expect` documents the intended nibli verdict (printed by `nibli-verify --asp`); the CI
//! gate checks nibli's verdict against clingo, not against `expect`.

use crate::{Case, Expect};

/// gismu used below (all in the in-tree FALLBACK dictionary, so cases resolve in CI with no
/// data file): prenu=person (the domain), gerku=dog, mlatu=cat, morsi=dead (BASE / negated);
/// danlu=animal, jmive=alive, melbi=beautiful (DERIVED / rule heads).
pub const NAF_CASES: &[Case] = &[
    // ── No witness → the NAF restrictor holds → the rule fires. ──
    Case {
        name: "naf_no_witness_fires",
        kb: &["ro lo prenu poi na gerku cu morsi", "la .adam. cu prenu"],
        query: "la .adam. cu morsi",
        expect: Expect::True,
    },
    // ── Witness present → the NAF restrictor is false → closed-world FALSE. ──
    Case {
        name: "naf_witness_blocks",
        kb: &[
            "ro lo prenu poi na gerku cu morsi",
            "la .adam. cu prenu",
            "la .adam. cu gerku",
        ],
        query: "la .adam. cu morsi",
        expect: Expect::False,
    },
    // ── The domain restrictor still binds: a non-person is out of the rule's reach. ──
    Case {
        name: "naf_other_entity_out_of_domain",
        kb: &[
            "ro lo prenu poi na gerku cu morsi",
            "la .adam. cu prenu",
            "la .bel. cu gerku",
        ],
        query: "la .bel. cu morsi",
        expect: Expect::False,
    },
    Case {
        name: "naf_domain_required",
        kb: &["ro lo prenu poi na gerku cu morsi", "la .kim. cu gerku"],
        query: "la .kim. cu morsi",
        expect: Expect::False,
    },
    // ── Baseline: a plain fact still resolves through the ASP path. ──
    Case {
        name: "naf_plain_fact_baseline",
        kb: &["la .adam. cu prenu"],
        query: "la .adam. cu prenu",
        expect: Expect::True,
    },
    // ── Taxonomy through NAF: NAF rule feeds a Horn rule (stratified: morsi is base). ──
    Case {
        name: "naf_taxonomy_through_naf",
        kb: &[
            "ro lo danlu cu jmive",
            "ro lo prenu poi na morsi cu danlu",
            "la .adam. cu prenu",
        ],
        query: "la .adam. cu jmive",
        expect: Expect::True,
    },
    Case {
        name: "naf_taxonomy_blocked_by_witness",
        kb: &[
            "ro lo danlu cu jmive",
            "ro lo prenu poi na morsi cu danlu",
            "la .adam. cu prenu",
            "la .adam. cu morsi",
        ],
        query: "la .adam. cu jmive",
        expect: Expect::False,
    },
    // ── Two independent NAF rules: one blocked, one fires. ──
    Case {
        name: "naf_two_rules_jmive_fires",
        kb: &[
            "ro lo prenu poi na gerku cu morsi",
            "ro lo prenu poi na mlatu cu jmive",
            "la .adam. cu prenu",
            "la .adam. cu gerku",
        ],
        query: "la .adam. cu jmive",
        expect: Expect::True,
    },
    Case {
        name: "naf_two_rules_morsi_blocked",
        kb: &[
            "ro lo prenu poi na gerku cu morsi",
            "ro lo prenu poi na mlatu cu jmive",
            "la .adam. cu prenu",
            "la .adam. cu gerku",
        ],
        query: "la .adam. cu morsi",
        expect: Expect::False,
    },
    // ── Positive + negative restrictor together: person AND dog AND not-cat → melbi. ──
    Case {
        name: "naf_positive_and_negative_restrictor",
        kb: &[
            "ro lo prenu poi gerku poi na mlatu cu melbi",
            "la .adam. cu prenu",
            "la .adam. cu gerku",
        ],
        query: "la .adam. cu melbi",
        expect: Expect::True,
    },
    Case {
        name: "naf_positive_and_negative_restrictor_blocked",
        kb: &[
            "ro lo prenu poi gerku poi na mlatu cu melbi",
            "la .adam. cu prenu",
            "la .adam. cu gerku",
            "la .adam. cu mlatu",
        ],
        query: "la .adam. cu melbi",
        expect: Expect::False,
    },
    // ── The REAL GDPR erasure rule (deontic head + `lo nu` abstraction): a person who has not
    // consented is obligated to be erased. `se bilga` is a plain gismu; the `lo nu se vimcu`
    // abstraction is modeled as an opaque constant keyed by its content hash, so the head +
    // query resolve to the same obligation atom. This is `gdpr.lojban:101`. ──
    Case {
        name: "gdpr_erasure_no_consent",
        kb: &[
            "ro lo prenu poi na zanru cu se bilga lo nu se vimcu",
            "la .adam. cu prenu",
        ],
        query: "la .adam. cu se bilga lo nu se vimcu",
        expect: Expect::True,
    },
    Case {
        name: "gdpr_erasure_with_consent",
        kb: &[
            "ro lo prenu poi na zanru cu se bilga lo nu se vimcu",
            "la .adam. cu prenu",
            "la .adam. cu zanru",
        ],
        query: "la .adam. cu se bilga lo nu se vimcu",
        expect: Expect::False,
    },
    // ── du identity × NAF: the equivalence index must be visible to the NAF check. ──
    Case {
        name: "naf_du_blocked_through_equality",
        // adam and bel are the SAME entity; bel carries the gerku witness, so the NAF
        // restrictor `poi na gerku` must be blocked for adam too. A NAF prover that
        // consulted the raw fact store and missed the equivalence index would wrongly
        // fire the rule here (TRUE) — the highest-value du probe shape.
        kb: &[
            "ro lo prenu poi na gerku cu morsi",
            "la .adam. cu prenu",
            "la .adam. cu du la .bel.",
            "la .bel. cu gerku",
        ],
        query: "la .adam. cu morsi",
        expect: Expect::False,
    },
    Case {
        name: "naf_du_unlinked_witness_fires",
        // Same KB WITHOUT the identity link (the post-retraction state): bel's witness
        // no longer reaches adam, so the rule fires.
        kb: &[
            "ro lo prenu poi na gerku cu morsi",
            "la .adam. cu prenu",
            "la .bel. cu gerku",
        ],
        query: "la .adam. cu morsi",
        expect: Expect::True,
    },
    Case {
        name: "naf_du_domain_through_equality",
        // The DOMAIN restrictor also resolves through the identity link: bel is a prenu
        // only via `bel du adam`, and the (unblocked) rule must still reach bel.
        kb: &[
            "ro lo prenu poi na gerku cu morsi",
            "la .adam. cu prenu",
            "la .adam. cu du la .bel.",
        ],
        query: "la .bel. cu morsi",
        expect: Expect::True,
    },
    Case {
        name: "naf_du_derived_chain_through_equality",
        // Full mix: identity + NAF rule + positive Horn chain. bel (merged with adam)
        // has no witness → danlu(bel) → jmive(bel).
        kb: &[
            "ro lo prenu poi na gerku cu danlu",
            "ro lo danlu cu jmive",
            "la .adam. cu prenu",
            "la .adam. cu du la .bel.",
        ],
        query: "la .bel. cu jmive",
        expect: Expect::True,
    },
    Case {
        name: "naf_du_query_identity_true",
        kb: &["la .adam. cu prenu", "la .adam. cu du la .bel."],
        query: "la .adam. cu du la .bel.",
        expect: Expect::True,
    },
    Case {
        name: "naf_du_query_identity_false",
        kb: &["la .adam. cu prenu", "la .bel. cu prenu"],
        query: "la .adam. cu du la .bel.",
        expect: Expect::False,
    },
];
