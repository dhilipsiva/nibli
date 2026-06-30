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
];
