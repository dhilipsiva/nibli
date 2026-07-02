//! Curated `(KB, query)` cases in the Horn / NAF-free fragment. Each is hand-checked
//! to be definite-Horn (facts + single-condition universal rules, no negation, no
//! compute/tense/deontic/abstraction), so nibli's verdict and classical entailment
//! must coincide. The set doubles as the harness self-check and the CI gate; `expect`
//! documents the intended nibli verdict.

use crate::{Case, Expect};

/// All gismu used below are plain taxonomy/property predicates (no special handling):
/// gerku=dog, mlatu=cat, cipni=bird, danlu=animal, jmive=alive, nanmu=man,
/// prenu=person, remna=human.
pub const CASES: &[Case] = &[
    // ── Ground fact lookup ──
    Case {
        name: "fact_lookup_true",
        kb: &["la .adam. cu gerku"],
        query: "la .adam. cu gerku",
        expect: Expect::True,
    },
    Case {
        name: "fact_lookup_false",
        kb: &["la .adam. cu gerku"],
        query: "la .adam. cu mlatu",
        expect: Expect::False,
    },
    // ── One-step modus ponens (syllogism) ──
    Case {
        name: "syllogism_true",
        kb: &["ro lo gerku cu danlu", "la .adam. cu gerku"],
        query: "la .adam. cu danlu",
        expect: Expect::True,
    },
    Case {
        name: "syllogism_false_other_predicate",
        kb: &["ro lo gerku cu danlu", "la .adam. cu gerku"],
        query: "la .adam. cu cipni",
        expect: Expect::False,
    },
    Case {
        name: "no_rule_so_false",
        kb: &["la .adam. cu gerku", "la .bel. cu mlatu"],
        query: "la .adam. cu danlu",
        expect: Expect::False,
    },
    // ── Two-step chain ──
    Case {
        name: "chain_two_true",
        kb: &[
            "ro lo gerku cu danlu",
            "ro lo danlu cu jmive",
            "la .adam. cu gerku",
        ],
        query: "la .adam. cu jmive",
        expect: Expect::True,
    },
    Case {
        name: "chain_two_false_other",
        kb: &[
            "ro lo gerku cu danlu",
            "ro lo danlu cu jmive",
            "la .adam. cu gerku",
        ],
        query: "la .adam. cu cipni",
        expect: Expect::False,
    },
    // ── Three-step chain ──
    Case {
        name: "chain_three_true",
        kb: &[
            "ro lo nanmu cu prenu",
            "ro lo prenu cu remna",
            "ro lo remna cu danlu",
            "la .kim. cu nanmu",
        ],
        query: "la .kim. cu danlu",
        expect: Expect::True,
    },
    // ── Two rules, two entities (no cross-talk) ──
    Case {
        name: "two_rules_entity_a_true",
        kb: &[
            "ro lo gerku cu danlu",
            "ro lo mlatu cu danlu",
            "la .adam. cu gerku",
            "la .bel. cu mlatu",
        ],
        query: "la .adam. cu danlu",
        expect: Expect::True,
    },
    Case {
        name: "two_rules_entity_b_true",
        kb: &[
            "ro lo gerku cu danlu",
            "ro lo mlatu cu danlu",
            "la .adam. cu gerku",
            "la .bel. cu mlatu",
        ],
        query: "la .bel. cu danlu",
        expect: Expect::True,
    },
    Case {
        name: "unknown_entity_false",
        kb: &["ro lo gerku cu danlu", "la .adam. cu gerku"],
        query: "la .bel. cu danlu",
        expect: Expect::False,
    },
    // ── Disjoint chains share the alive rule ──
    Case {
        name: "disjoint_chain_cat_alive_true",
        kb: &[
            "ro lo gerku cu danlu",
            "ro lo mlatu cu danlu",
            "ro lo danlu cu jmive",
            "la .adam. cu gerku",
            "la .bel. cu mlatu",
        ],
        query: "la .bel. cu jmive",
        expect: Expect::True,
    },
    Case {
        name: "disjoint_chain_dog_alive_true",
        kb: &[
            "ro lo gerku cu danlu",
            "ro lo mlatu cu danlu",
            "ro lo danlu cu jmive",
            "la .adam. cu gerku",
            "la .bel. cu mlatu",
        ],
        query: "la .adam. cu jmive",
        expect: Expect::True,
    },
    Case {
        name: "disjoint_chain_false_other",
        kb: &[
            "ro lo gerku cu danlu",
            "ro lo mlatu cu danlu",
            "ro lo danlu cu jmive",
            "la .adam. cu gerku",
            "la .bel. cu mlatu",
        ],
        query: "la .bel. cu cipni",
        expect: Expect::False,
    },
    // ── du identity: ground equality maps to native TPTP `=` (congruence closure over a
    // definite theory = nibli's union-find, in both directions). Broken-chain cases double
    // as the post-retraction state: retracting a `du` link rebuilds the equivalence index
    // from survivors, which is by construction the program that never asserted it (the
    // session-level retraction path itself is engine-tested; see logji's du suites). ──
    Case {
        name: "du_reflexive_true",
        kb: &["la .adam. cu gerku"],
        query: "la .adam. cu du la .adam.",
        expect: Expect::True,
    },
    Case {
        name: "du_symmetric_true",
        kb: &["la .adam. cu du la .bel."],
        query: "la .bel. cu du la .adam.",
        expect: Expect::True,
    },
    Case {
        name: "du_chain_transitive_true",
        kb: &[
            "la .adam. cu du la .bel.",
            "la .bel. cu du la .kim.",
            "la .kim. cu du la .dan.",
        ],
        query: "la .adam. cu du la .dan.",
        expect: Expect::True,
    },
    Case {
        name: "du_chain_broken_false",
        // The chain above MINUS its middle link — the post-retraction state of
        // `du_chain_transitive_true` after retracting `bel du kim`.
        kb: &["la .adam. cu du la .bel.", "la .kim. cu du la .dan."],
        query: "la .adam. cu du la .dan.",
        expect: Expect::False,
    },
    Case {
        name: "du_no_link_false",
        kb: &["la .adam. cu gerku", "la .bel. cu gerku"],
        query: "la .adam. cu du la .bel.",
        expect: Expect::False,
    },
    Case {
        name: "du_substitutivity_fact_true",
        kb: &["la .adam. cu du la .bel.", "la .adam. cu gerku"],
        query: "la .bel. cu gerku",
        expect: Expect::True,
    },
    Case {
        name: "du_substitutivity_broken_chain_false",
        // Substitutivity must NOT leak across the broken (post-retraction) chain.
        kb: &[
            "la .adam. cu du la .bel.",
            "la .kim. cu du la .dan.",
            "la .adam. cu gerku",
        ],
        query: "la .dan. cu gerku",
        expect: Expect::False,
    },
    Case {
        name: "du_rule_fires_through_identity",
        // Substitutivity feeds RULE FIRING, not just fact lookup: bel is a dog only via
        // the identity link, and the rule must still derive danlu(bel).
        kb: &[
            "ro lo gerku cu danlu",
            "la .adam. cu du la .bel.",
            "la .adam. cu gerku",
        ],
        query: "la .bel. cu danlu",
        expect: Expect::True,
    },
    Case {
        name: "du_transitive_substitutivity_through_rule_true",
        // Three-entity class + a rule: the full mix (chain, substitutivity, firing).
        kb: &[
            "ro lo gerku cu danlu",
            "la .adam. cu du la .bel.",
            "la .bel. cu du la .kim.",
            "la .kim. cu gerku",
        ],
        query: "la .adam. cu danlu",
        expect: Expect::True,
    },
    // ── Tense flavors (pu/ca/ba): flavor-exact facts, flavor-polymorphic unmarked
    // rules, flavor-constant explicit tenses — the engine-probed matrix that
    // `tense::flavorize` mirrors (every expect below is a verbatim engine probe). ──
    Case {
        name: "tense_diag_pu_true",
        kb: &["pu la .adam. cu gerku"],
        query: "pu la .adam. cu gerku",
        expect: Expect::True,
    },
    Case {
        name: "tense_diag_ca_true",
        kb: &["ca la .adam. cu gerku"],
        query: "ca la .adam. cu gerku",
        expect: Expect::True,
    },
    Case {
        name: "tense_diag_ba_true",
        kb: &["ba la .adam. cu gerku"],
        query: "ba la .adam. cu gerku",
        expect: Expect::True,
    },
    Case {
        name: "tense_offdiag_pu_fact_bare_query_false",
        kb: &["pu la .adam. cu gerku"],
        query: "la .adam. cu gerku",
        expect: Expect::False,
    },
    Case {
        name: "tense_offdiag_bare_fact_pu_query_false",
        kb: &["la .adam. cu gerku"],
        query: "pu la .adam. cu gerku",
        expect: Expect::False,
    },
    Case {
        name: "tense_offdiag_ca_fact_pu_query_false",
        kb: &["ca la .adam. cu gerku"],
        query: "pu la .adam. cu gerku",
        expect: Expect::False,
    },
    Case {
        name: "tense_offdiag_bare_fact_ca_query_false",
        kb: &["la .adam. cu gerku"],
        query: "ca la .adam. cu gerku",
        expect: Expect::False,
    },
    Case {
        name: "tense_rule_polymorphic_chain_past_true",
        // Unmarked rules fire within the query's flavor: pu gerku → pu danlu → pu jmive.
        kb: &[
            "ro lo gerku cu danlu",
            "ro lo danlu cu jmive",
            "pu la .kim. cu gerku",
        ],
        query: "pu la .kim. cu jmive",
        expect: Expect::True,
    },
    Case {
        name: "tense_rule_polymorphic_bare_blocked_false",
        // The past fact must not feed a BARE conclusion.
        kb: &[
            "ro lo gerku cu danlu",
            "ro lo danlu cu jmive",
            "pu la .kim. cu gerku",
        ],
        query: "la .kim. cu jmive",
        expect: Expect::False,
    },
    Case {
        name: "tense_rule_polymorphic_other_flavor_blocked_false",
        kb: &["ro lo gerku cu danlu", "pu la .kim. cu gerku"],
        query: "ba la .kim. cu danlu",
        expect: Expect::False,
    },
    Case {
        name: "tense_rule_polymorphic_present_true",
        kb: &["ro lo gerku cu danlu", "ca la .kim. cu gerku"],
        query: "ca la .kim. cu danlu",
        expect: Expect::True,
    },
    Case {
        name: "tense_antecedent_explicit_fires_true",
        // `poi pu citka` is a flavor CONSTANT: a Past witness + a bare domain fact
        // fire the BARE conclusion.
        kb: &[
            "ro lo gerku poi pu citka cu xagji",
            "la .kim. cu gerku",
            "pu la .kim. cu citka",
        ],
        query: "la .kim. cu xagji",
        expect: Expect::True,
    },
    Case {
        name: "tense_antecedent_explicit_query_flavor_blocked_false",
        // Under a pu query the UNMARKED domain literal needs a pu witness — absent.
        kb: &[
            "ro lo gerku poi pu citka cu xagji",
            "la .kim. cu gerku",
            "pu la .kim. cu citka",
        ],
        query: "pu la .kim. cu xagji",
        expect: Expect::False,
    },
    Case {
        name: "tense_antecedent_bare_witness_blocked_false",
        // A bare witness must not satisfy the explicit Past antecedent.
        kb: &[
            "ro lo gerku poi pu citka cu xagji",
            "la .kim. cu gerku",
            "la .kim. cu citka",
        ],
        query: "la .kim. cu xagji",
        expect: Expect::False,
    },
    Case {
        name: "tense_consequent_explicit_fires_true",
        // `ganai … gi pu …`: the explicit Past conclusion fires from a BARE condition.
        kb: &[
            "ro da zo'u ganai da gerku gi pu da danlu",
            "la .kim. cu gerku",
        ],
        query: "pu la .kim. cu danlu",
        expect: Expect::True,
    },
    Case {
        name: "tense_consequent_bare_query_blocked_false",
        kb: &[
            "ro da zo'u ganai da gerku gi pu da danlu",
            "la .kim. cu gerku",
        ],
        query: "la .kim. cu danlu",
        expect: Expect::False,
    },
    Case {
        name: "tense_consequent_past_fact_blocked_false",
        // The explicit-conclusion rule's unmarked condition evaluates BARE: a Past
        // fact does not satisfy it (engine-probed).
        kb: &[
            "ro da zo'u ganai da gerku gi pu da danlu",
            "pu la .kim. cu gerku",
        ],
        query: "pu la .kim. cu danlu",
        expect: Expect::False,
    },
];
