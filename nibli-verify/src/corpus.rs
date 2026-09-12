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
        kb: &["dog(Adam)."],
        query: "dog(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "fact_lookup_false",
        kb: &["dog(Adam)."],
        query: "cat(Adam).",
        expect: Expect::False,
    },
    // ── Query-side named-variable join (the oracle must translate the exact
    //    query IR that nibli evaluates, not assertion-mode sibling Exists) ──
    Case {
        name: "named_query_join_split_false",
        kb: &["dog(Adam).", "animal(Bel)."],
        query: "dog($x) & animal($x).",
        expect: Expect::False,
    },
    Case {
        name: "named_query_join_joint_true",
        kb: &["dog(Adam).", "animal(Adam)."],
        query: "dog($x) & animal($x).",
        expect: Expect::True,
    },
    // ── One-step modus ponens (syllogism) ──
    Case {
        name: "syllogism_true",
        kb: &["animal(every dog).", "dog(Adam)."],
        query: "animal(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "syllogism_false_other_predicate",
        kb: &["animal(every dog).", "dog(Adam)."],
        query: "bird(Adam).",
        expect: Expect::False,
    },
    Case {
        name: "no_rule_so_false",
        kb: &["dog(Adam).", "cat(Bel)."],
        query: "animal(Adam).",
        expect: Expect::False,
    },
    // ── Two-step chain ──
    Case {
        name: "chain_two_true",
        kb: &["animal(every dog).", "alive(every animal).", "dog(Adam)."],
        query: "alive(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "chain_two_false_other",
        kb: &["animal(every dog).", "alive(every animal).", "dog(Adam)."],
        query: "bird(Adam).",
        expect: Expect::False,
    },
    // ── Three-step chain ──
    Case {
        name: "chain_three_true",
        kb: &[
            "person(every man).",
            "human(every person).",
            "animal(every human).",
            "man(Kim).",
        ],
        query: "animal(Kim).",
        expect: Expect::True,
    },
    // ── Two rules, two entities (no cross-talk) ──
    Case {
        name: "two_rules_entity_a_true",
        kb: &[
            "animal(every dog).",
            "animal(every cat).",
            "dog(Adam).",
            "cat(Bel).",
        ],
        query: "animal(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "two_rules_entity_b_true",
        kb: &[
            "animal(every dog).",
            "animal(every cat).",
            "dog(Adam).",
            "cat(Bel).",
        ],
        query: "animal(Bel).",
        expect: Expect::True,
    },
    Case {
        name: "unknown_entity_false",
        kb: &["animal(every dog).", "dog(Adam)."],
        query: "animal(Bel).",
        expect: Expect::False,
    },
    // ── Disjoint chains share the alive rule ──
    Case {
        name: "disjoint_chain_cat_alive_true",
        kb: &[
            "animal(every dog).",
            "animal(every cat).",
            "alive(every animal).",
            "dog(Adam).",
            "cat(Bel).",
        ],
        query: "alive(Bel).",
        expect: Expect::True,
    },
    Case {
        name: "disjoint_chain_dog_alive_true",
        kb: &[
            "animal(every dog).",
            "animal(every cat).",
            "alive(every animal).",
            "dog(Adam).",
            "cat(Bel).",
        ],
        query: "alive(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "disjoint_chain_false_other",
        kb: &[
            "animal(every dog).",
            "animal(every cat).",
            "alive(every animal).",
            "dog(Adam).",
            "cat(Bel).",
        ],
        query: "bird(Bel).",
        expect: Expect::False,
    },
    // ── du identity: ground equality maps to native TPTP `=` (congruence closure over a
    // definite theory = nibli's union-find, in both directions). Broken-chain cases double
    // as the post-retraction state: retracting a `du` link rebuilds the equivalence index
    // from survivors, which is by construction the program that never asserted it (the
    // session-level retraction path itself is engine-tested; see nibli-reason's du suites). ──
    Case {
        name: "du_reflexive_true",
        kb: &["dog(Adam)."],
        query: "Adam = Adam.",
        expect: Expect::True,
    },
    Case {
        name: "du_symmetric_true",
        kb: &["Adam = Bel."],
        query: "Bel = Adam.",
        expect: Expect::True,
    },
    Case {
        name: "du_chain_transitive_true",
        kb: &["Adam = Bel.", "Bel = Kim.", "Kim = Dan."],
        query: "Adam = Dan.",
        expect: Expect::True,
    },
    Case {
        name: "du_chain_broken_false",
        // The chain above MINUS its middle link — the post-retraction state of
        // `du_chain_transitive_true` after retracting `bel du kim`.
        kb: &["Adam = Bel.", "Kim = Dan."],
        query: "Adam = Dan.",
        expect: Expect::False,
    },
    Case {
        name: "du_no_link_false",
        kb: &["dog(Adam).", "dog(Bel)."],
        query: "Adam = Bel.",
        expect: Expect::False,
    },
    Case {
        name: "du_substitutivity_fact_true",
        kb: &["Adam = Bel.", "dog(Adam)."],
        query: "dog(Bel).",
        expect: Expect::True,
    },
    Case {
        name: "du_substitutivity_broken_chain_false",
        // Substitutivity must NOT leak across the broken (post-retraction) chain.
        kb: &["Adam = Bel.", "Kim = Dan.", "dog(Adam)."],
        query: "dog(Dan).",
        expect: Expect::False,
    },
    Case {
        name: "du_rule_fires_through_identity",
        // Substitutivity feeds RULE FIRING, not just fact lookup: bel is a dog only via
        // the identity link, and the rule must still derive danlu(bel).
        kb: &["animal(every dog).", "Adam = Bel.", "dog(Adam)."],
        query: "animal(Bel).",
        expect: Expect::True,
    },
    Case {
        name: "du_ground_rule_chain_alternative_true",
        // The named ground heads do not unify with Bel directly. Equality
        // alternatives must retain depth exhaustion until this chain resolves.
        kb: &[
            "dog(Adam).",
            "dog(Adam) -> cat(Adam).",
            "cat(Adam) -> animal(Adam).",
            "Adam = Bel.",
        ],
        query: "animal(Bel).",
        expect: Expect::True,
    },
    Case {
        name: "du_ground_rule_chain_reversed_alias_true",
        kb: &[
            "Bel = Adam.",
            "dog(Adam).",
            "dog(Adam) -> cat(Adam).",
            "cat(Adam) -> animal(Adam).",
        ],
        query: "animal(Bel).",
        expect: Expect::True,
    },
    Case {
        name: "du_transitive_substitutivity_through_rule_true",
        // Three-entity class + a rule: the full mix (chain, substitutivity, firing).
        kb: &[
            "animal(every dog).",
            "Adam = Bel.",
            "Bel = Kim.",
            "dog(Kim).",
        ],
        query: "animal(Adam).",
        expect: Expect::True,
    },
    // ── Tense flavors (pu/ca/ba): flavor-exact facts and rule literals. Bare
    // rules are Bare-only; explicit tenses declare same- or cross-flavor mappings — the matrix that
    // `tense::flavorize` mirrors (every expect below is a verbatim engine probe). ──
    Case {
        name: "tense_diag_pu_true",
        kb: &["past dog(Adam)."],
        query: "past dog(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "tense_diag_ca_true",
        kb: &["now dog(Adam)."],
        query: "now dog(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "tense_diag_ba_true",
        kb: &["future dog(Adam)."],
        query: "future dog(Adam).",
        expect: Expect::True,
    },
    Case {
        name: "tense_offdiag_pu_fact_bare_query_false",
        kb: &["past dog(Adam)."],
        query: "dog(Adam).",
        expect: Expect::False,
    },
    Case {
        name: "tense_offdiag_bare_fact_pu_query_false",
        kb: &["dog(Adam)."],
        query: "past dog(Adam).",
        expect: Expect::False,
    },
    Case {
        name: "tense_offdiag_ca_fact_pu_query_false",
        kb: &["now dog(Adam)."],
        query: "past dog(Adam).",
        expect: Expect::False,
    },
    Case {
        name: "tense_offdiag_bare_fact_ca_query_false",
        kb: &["dog(Adam)."],
        query: "now dog(Adam).",
        expect: Expect::False,
    },
    Case {
        name: "tense_bare_taxonomy_chain_past_false",
        // Even a plausible taxonomy stays Bare unless its temporal mapping is declared.
        kb: &[
            "animal(every dog).",
            "alive(every animal).",
            "past dog(Kim).",
        ],
        query: "past alive(Kim).",
        expect: Expect::False,
    },
    Case {
        name: "tense_past_fact_bare_query_false",
        // The past fact must not feed a BARE conclusion.
        kb: &[
            "animal(every dog).",
            "alive(every animal).",
            "past dog(Kim).",
        ],
        query: "alive(Kim).",
        expect: Expect::False,
    },
    Case {
        name: "tense_other_flavor_blocked_false",
        kb: &["animal(every dog).", "past dog(Kim)."],
        query: "future animal(Kim).",
        expect: Expect::False,
    },
    Case {
        name: "tense_bare_taxonomy_rule_present_false",
        kb: &["animal(every dog).", "now dog(Kim)."],
        query: "now animal(Kim).",
        expect: Expect::False,
    },
    Case {
        name: "tense_explicit_taxonomy_chain_past_true",
        kb: &[
            "all $x: past dog($x) -> past animal($x).",
            "all $x: past animal($x) -> past alive($x).",
            "past dog(Kim).",
        ],
        query: "past alive(Kim).",
        expect: Expect::True,
    },
    Case {
        name: "tense_bare_taxonomy_rule_future_false",
        kb: &["animal(every dog).", "future dog(Kim)."],
        query: "future animal(Kim).",
        expect: Expect::False,
    },
    Case {
        name: "tense_explicit_taxonomy_rule_future_true",
        kb: &[
            "all $x: future dog($x) -> future animal($x).",
            "future dog(Kim).",
        ],
        query: "future animal(Kim).",
        expect: Expect::True,
    },
    Case {
        name: "tense_bare_causal_rule_past_false",
        kb: &["all $x: eats($x) -> be_hungry($x).", "past eats(Kim)."],
        query: "past be_hungry(Kim).",
        expect: Expect::False,
    },
    Case {
        name: "tense_explicit_causal_cross_flavor_true",
        kb: &[
            "all $x: past eats($x) -> now be_hungry($x).",
            "past eats(Kim).",
        ],
        query: "now be_hungry(Kim).",
        expect: Expect::True,
    },
    Case {
        name: "tense_antecedent_explicit_fires_true",
        // `poi pu citka` is a flavor CONSTANT: a Past witness + a bare domain fact
        // fire the BARE conclusion.
        kb: &[
            "be_hungry(every dog where past eats(it)).",
            "dog(Kim).",
            "past eats(Kim).",
        ],
        query: "be_hungry(Kim).",
        expect: Expect::True,
    },
    Case {
        name: "tense_antecedent_explicit_query_flavor_blocked_false",
        // The rule conclusion is Bare, so it cannot answer a Past query.
        kb: &[
            "be_hungry(every dog where past eats(it)).",
            "dog(Kim).",
            "past eats(Kim).",
        ],
        query: "past be_hungry(Kim).",
        expect: Expect::False,
    },
    Case {
        name: "tense_antecedent_bare_witness_blocked_false",
        // A bare witness must not satisfy the explicit Past antecedent.
        kb: &[
            "be_hungry(every dog where past eats(it)).",
            "dog(Kim).",
            "eats(Kim).",
        ],
        query: "be_hungry(Kim).",
        expect: Expect::False,
    },
    Case {
        name: "tense_consequent_explicit_fires_true",
        // `ganai … gi pu …`: the explicit Past conclusion fires from a BARE condition.
        kb: &["all $da: dog($da) -> past animal($da).", "dog(Kim)."],
        query: "past animal(Kim).",
        expect: Expect::True,
    },
    Case {
        name: "tense_consequent_bare_query_blocked_false",
        kb: &["all $da: dog($da) -> past animal($da).", "dog(Kim)."],
        query: "animal(Kim).",
        expect: Expect::False,
    },
    Case {
        name: "tense_consequent_past_fact_blocked_false",
        // The explicit-conclusion rule's unmarked condition evaluates BARE: a Past
        // fact does not satisfy it (engine-probed).
        kb: &["all $da: dog($da) -> past animal($da).", "past dog(Kim)."],
        query: "past animal(Kim).",
        expect: Expect::False,
    },
];
