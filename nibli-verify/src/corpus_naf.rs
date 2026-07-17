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
        kb: &["dead(every person where ~dog).", "person(Adam)."],
        query: "dead(Adam).",
        expect: Expect::True,
    },
    // ── Witness present → the NAF restrictor is false → closed-world FALSE. ──
    Case {
        name: "naf_witness_blocks",
        kb: &[
            "dead(every person where ~dog).",
            "person(Adam).",
            "dog(Adam).",
        ],
        query: "dead(Adam).",
        expect: Expect::False,
    },
    // ── The domain restrictor still binds: a non-person is out of the rule's reach. ──
    Case {
        name: "naf_other_entity_out_of_domain",
        kb: &[
            "dead(every person where ~dog).",
            "person(Adam).",
            "dog(Bel).",
        ],
        query: "dead(Bel).",
        expect: Expect::False,
    },
    Case {
        name: "naf_domain_required",
        kb: &["dead(every person where ~dog).", "dog(Kim)."],
        query: "dead(Kim).",
        expect: Expect::False,
    },
    // ── Baseline: a plain fact still resolves through the ASP path. ──
    Case {
        name: "naf_plain_fact_baseline",
        kb: &["person(Adam)."],
        query: "person(Adam).",
        expect: Expect::True,
    },
    // ── Taxonomy through NAF: NAF rule feeds a Horn rule (stratified: morsi is base). ──
    Case {
        name: "naf_taxonomy_through_naf",
        kb: &[
            "alive(every animal).",
            "animal(every person where ~dead).",
            "person(Adam).",
        ],
        query: "alive(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "naf_taxonomy_blocked_by_witness",
        kb: &[
            "alive(every animal).",
            "animal(every person where ~dead).",
            "person(Adam).",
            "dead(Adam).",
        ],
        query: "alive(Adam).",
        expect: Expect::False,
    },
    // ── Two independent NAF rules: one blocked, one fires. ──
    Case {
        name: "naf_two_rules_jmive_fires",
        kb: &[
            "dead(every person where ~dog).",
            "alive(every person where ~cat).",
            "person(Adam).",
            "dog(Adam).",
        ],
        query: "alive(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "naf_two_rules_morsi_blocked",
        kb: &[
            "dead(every person where ~dog).",
            "alive(every person where ~cat).",
            "person(Adam).",
            "dog(Adam).",
        ],
        query: "dead(Adam).",
        expect: Expect::False,
    },
    // ── Positive + negative restrictor together: person AND dog AND not-cat → melbi. ──
    Case {
        name: "naf_positive_and_negative_restrictor",
        kb: &[
            "beautiful(every person where dog where ~cat).",
            "person(Adam).",
            "dog(Adam).",
        ],
        query: "beautiful(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "naf_positive_and_negative_restrictor_blocked",
        kb: &[
            "beautiful(every person where dog where ~cat).",
            "person(Adam).",
            "dog(Adam).",
            "cat(Adam).",
        ],
        query: "beautiful(Adam).",
        expect: Expect::False,
    },
    // ── The REAL GDPR erasure rule (deontic head + `lo nu` abstraction): a person who has not
    // consented is obligated to be erased. `se bilga` is a plain gismu; the `lo nu se vimcu`
    // abstraction is modeled as an opaque constant keyed by its content hash, so the head +
    // query resolve to the same obligation atom. This is `gdpr.nibli:101`. ──
    Case {
        name: "gdpr_erasure_no_consent",
        kb: &[
            "obligated(every person where ~approves, event { removes() }).",
            "person(Adam).",
        ],
        query: "obligated(Adam, event { removes() }).",
        expect: Expect::True,
    },
    Case {
        name: "gdpr_erasure_with_consent",
        kb: &[
            "obligated(every person where ~approves, event { removes() }).",
            "person(Adam).",
            "approves(Adam).",
        ],
        query: "obligated(Adam, event { removes() }).",
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
            "dead(every person where ~dog).",
            "person(Adam).",
            "Adam = Bel.",
            "dog(Bel).",
        ],
        query: "dead(Adam).",
        expect: Expect::False,
    },
    Case {
        name: "naf_du_unlinked_witness_fires",
        // Same KB WITHOUT the identity link (the post-retraction state): bel's witness
        // no longer reaches adam, so the rule fires.
        kb: &[
            "dead(every person where ~dog).",
            "person(Adam).",
            "dog(Bel).",
        ],
        query: "dead(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "naf_du_domain_through_equality",
        // The DOMAIN restrictor also resolves through the identity link: bel is a prenu
        // only via `bel du adam`, and the (unblocked) rule must still reach bel.
        kb: &[
            "dead(every person where ~dog).",
            "person(Adam).",
            "Adam = Bel.",
        ],
        query: "dead(Bel).",
        expect: Expect::True,
    },
    Case {
        name: "naf_du_derived_chain_through_equality",
        // Full mix: identity + NAF rule + positive Horn chain. bel (merged with adam)
        // has no witness → danlu(bel) → jmive(bel).
        kb: &[
            "animal(every person where ~dog).",
            "alive(every animal).",
            "person(Adam).",
            "Adam = Bel.",
        ],
        query: "alive(Bel).",
        expect: Expect::True,
    },
    Case {
        name: "naf_du_query_identity_true",
        kb: &["person(Adam).", "Adam = Bel."],
        query: "Adam = Bel.",
        expect: Expect::True,
    },
    Case {
        name: "naf_du_query_identity_false",
        kb: &["person(Adam).", "person(Bel)."],
        query: "Adam = Bel.",
        expect: Expect::False,
    },
    // ── Tense flavors through the ASP translator (positive programs only — a program
    // that mixes tense with a NAF rule is conservatively SKIPPED by `tense::flavorize`:
    // the engine's NegatedExistsGroup is tenseless (audit U1), and the gate must not
    // canonize that behavior as oracle expectation). ──
    Case {
        name: "tense_asp_diag_pu_true",
        kb: &["past person(Adam)."],
        query: "past person(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "tense_asp_offdiag_false",
        kb: &["past person(Adam)."],
        query: "person(Adam).",
        expect: Expect::False,
    },
    Case {
        name: "tense_asp_polymorphic_rule_true",
        kb: &["animal(every dog).", "past dog(Kim)."],
        query: "past animal(Kim).",
        expect: Expect::True,
    },
    Case {
        name: "tense_asp_consequent_explicit_true",
        kb: &["all $da: dog($da) -> past animal($da).", "dog(Kim)."],
        query: "past animal(Kim).",
        expect: Expect::True,
    },
    // ── Exact-count queries (`PA lo X cu Y`) → clingo `#count` aggregates. Guarded to
    // ground-fact KBs: with a rule in the KB the existential-import import witness gets counted, and
    // `du` classes are not collapsed by the engine count (both engine-probed) — those
    // combinations are SKIPPED pending the count-semantics decision, not canonized. ──
    Case {
        name: "count_exact_two_true",
        kb: &["dog(Adam).", "dog(Bel)."],
        query: "dog(exactly 2 dog).",
        expect: Expect::True,
    },
    Case {
        name: "count_exact_one_false",
        kb: &["dog(Adam).", "dog(Bel)."],
        query: "dog(exactly 1 dog).",
        expect: Expect::False,
    },
    Case {
        name: "count_exact_three_false",
        kb: &["dog(Adam).", "dog(Bel)."],
        query: "dog(exactly 3 dog).",
        expect: Expect::False,
    },
    Case {
        name: "count_body_restricts_true",
        // Two dogs, one of them an (asserted) animal: exactly ONE dog is an animal.
        kb: &["dog(Adam).", "dog(Bel).", "animal(Adam)."],
        query: "animal(exactly 1 dog).",
        expect: Expect::True,
    },
    Case {
        name: "count_body_restricts_false",
        kb: &["dog(Adam).", "dog(Bel).", "animal(Adam)."],
        query: "animal(exactly 2 dog).",
        expect: Expect::False,
    },
    Case {
        name: "count_three_entities_true",
        kb: &["dog(Adam).", "dog(Bel).", "dog(Kim).", "cat(Dan)."],
        query: "dog(exactly 3 dog).",
        expect: Expect::True,
    },
];
