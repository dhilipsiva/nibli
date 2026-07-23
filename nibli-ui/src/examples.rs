//! Preloaded examples for the header "example" dropdown.
//!
//! Each [`Example`] bundles a knowledge base (English `source` + nibli KR `kb`)
//! and a set of preset queries (English label + nibli KR query). Selecting one in
//! the header loads it read-only into the Transparency Triad; the query box
//! becomes a dropdown of that example's queries. "Custom" (the default,
//! `None`) keeps the editable behavior. Examples compile with the nibli KR
//! front-end.
//!
//! The KB corpora are the SAME committed `.nibli` files the engine's
//! regression tests pin (`gdpr_*` / `ddi_*` / `utopia_*` in
//! `nibli-engine/tests/integration.rs`), pulled in via `include_str!` so
//! the UI examples cannot drift from the tested corpora. The `shipped_examples_compile` guard test below
//! pins every KB line + query through the nibli KR front-end.
//!
//! NOTE: Syllogism/GDPR/Drug `name` strings are quoted by the book (Ch 18/19/20)
//! — keep them byte-stable. Extra playground corpora (if any) are not book chapters.

/// One preset query: an English note shown beside its nibli KR in the dropdown.
pub struct ExampleQuery {
    pub label: &'static str,
    pub query: &'static str,
}

/// A preloaded knowledge base + its queries.
pub struct Example {
    /// Dropdown label.
    pub name: &'static str,
    /// KB rendered as plain English (read-only Source tab).
    pub source: &'static str,
    /// KB as nibli KR. The full commented corpus is fine: `run_query` skips
    /// `#`-comment and blank lines at assert time.
    pub kb: &'static str,
    /// The preset queries offered for this KB.
    pub queries: &'static [ExampleQuery],
    /// Domain-term overlay for this curated corpus's proof rendering (the
    /// documented reader's overlay — "prevents" -> "inhibits", `varfarin` ->
    /// "warfarin"). `None` keeps the engine's literal glosses. Applied only to the
    /// proof "why"/tree, never the back-translation tab.
    pub overlay: Option<&'static nibli_render::DomainGloss>,
}

// ── Syllogism — the minimal worked example, inlined ──
const SYLLOGISM_SOURCE: &str = "\
All dogs are animals.
All animals eat.
Adam is a dog.";

const SYLLOGISM_KB: &str = "\
# All dogs are animals.
animal(every dog).
# All animals eat.
eats(every animal).
# Adam is a dog.
dog(Adam).
";

// ── GDPR — English rendering of `gdpr.nibli` ──
const GDPR_SOURCE: &str = "\
Names, addresses, and special-category data (health, religion, ethnicity) are personal data.
Personal data must be accurate, kept secure, and limited to what is necessary (Art 5).
Special-category data needs a stricter, specific basis (Art 9).
A subject who has consented — or is bound by a contract or a legal obligation — has a lawful basis for processing (Art 6).
Every data subject has the right to access their data (Art 15).
A controller that has suffered a breach must notify (Art 33).

Adam is a data subject. AkmeCorp and Google are controllers.
AkmeCorp holds Adam's health record and an ordinary record.
Adam has given consent. AkmeCorp suffered a breach; Google did not.";

// ── Extra playground corpus (utopia.nibli) — not a book chapter ──
// Clinical Source-tab prose. Book legal case study is GDPR (Ch 19) only.
const LEGAL_SOURCE: &str = "\
Every person is owed a secure environment, food, shelter, health, learning, and expression — duties, not logistics.
A prisoner is still a person, may still express, and free persons may travel.
Teachers and workers mint merit only when their standing is not voided.
Voiding requires multi-sig: two independent Review-credentialed auditors (not kin, not the same person, not suspended), each with adjudicator role, a recorded catch, and no established false accusation; false accusers are themselves voided on Review.
Judging your own child voids your standing (kinship conflict).
Imprisonment requires adjudicated harm, no successful appeal, a non-suspended Court, and that the offender is not whistleblower-protected; home confinement is for non-domestic cases; domestic offenses route to high- or low-security facilities by severity.
Article 7: suspended office (broken), multi-sig void, and whistleblower protection (show → defend) resist capture of Court/Review.

Scenario cast: Adam is a prisoner. Bela taught Cira and was voided by Gia and Hex dual-sign. Dev judged child Esa and is voided. Mira teaches honestly; Lupo falsely accused her and is voided. Hano is home-confined; Jala harmed without court and stays free; Nia is freed on appeal. Lalo (severe domestic) and Nando (non-severe domestic) are placed by grade. Quin works the Census and is rewarded. Boss fails to solo-void or imprison Rebel (whistleblower shield; Boss suspended by recall).";

// ── Drug interactions — English rendering of `drug-interactions.nibli` ──
const DRUG_SOURCE: &str = "\
Warfarin, fluconazole, apixaban, and phenytoin are drugs.
Fluconazole inhibits the CYP2C9 enzyme.
Warfarin and phenytoin are metabolized by CYP2C9; apixaban is metabolized by CYP3A4.
Warfarin and phenytoin have a narrow therapeutic index.
Adam is co-prescribed warfarin and fluconazole.
When an inhibited enzyme metabolizes a drug, that drug's blood concentration rises.
A drug whose concentration rises and has a narrow therapeutic index is at toxicity risk.
Any drug at toxicity risk warrants a safety alert.";

/// The preloaded examples, in dropdown order.
pub const EXAMPLES: &[Example] = &[
    Example {
        name: "Syllogism (Ch 18)",
        source: SYLLOGISM_SOURCE,
        kb: SYLLOGISM_KB,
        queries: &[
            ExampleQuery {
                label: "does Adam eat?—a 2-hop proof",
                query: "eats(Adam).",
            },
            ExampleQuery {
                label: "is Adam an animal?—1 hop",
                query: "animal(Adam).",
            },
            ExampleQuery {
                label: "is Adam a bird?—a real FALSE",
                query: "bird(Adam).",
            },
        ],
        overlay: None,
    },
    Example {
        name: "GDPR compliance (Ch 19)",
        source: GDPR_SOURCE,
        kb: include_str!("../../gdpr.nibli"),
        queries: &[
            ExampleQuery {
                label: "lawful basis? (Art 6)",
                query: "permitted(Adam).",
            },
            ExampleQuery {
                label: "right to erasure? (Art 17)",
                query: "~permitted(Adam).",
            },
            ExampleQuery {
                label: "a controller is not a consenting person—exhaustive FALSE",
                query: "permitted(Gugli).",
            },
            ExampleQuery {
                label: "health record → personal data (Art 4/9, derived)",
                query: "data(Kanrek).",
            },
        ],
        overlay: Some(&nibli_render::GDPR_OVERLAY),
    },
    Example {
        name: "Constitutional core (utopia)",
        source: LEGAL_SOURCE,
        kb: include_str!("../../utopia.nibli"),
        queries: &[
            ExampleQuery {
                label: "floor duty—Adam is owed food",
                query: "obligated(Adam, event { eats() }).",
            },
            ExampleQuery {
                label: "prisoner may express",
                query: "expresses(Adam).",
            },
            ExampleQuery {
                label: "free person travels (Bela)",
                query: "travel(Bela).",
            },
            ExampleQuery {
                label: "voided teacher—Bela standing voided",
                query: "false(Bela).",
            },
            ExampleQuery {
                label: "honest auditor rewarded (Gia)",
                query: "reward(Gia).",
            },
            ExampleQuery {
                label: "false accuser voided (Lupo)",
                query: "false(Lupo).",
            },
            ExampleQuery {
                label: "honest teacher still rewarded (Mira)",
                query: "reward(Mira).",
            },
            ExampleQuery {
                label: "kin-judge voided (Dev judged child Esa)",
                query: "false(Dev).",
            },
            ExampleQuery {
                label: "capture without adjudicator does not void (Esa)",
                query: "false(Esa).",
            },
            ExampleQuery {
                label: "home confinement dwells (Hano)",
                query: "dwell(Hano).",
            },
            ExampleQuery {
                label: "harm without court—still free (Jala)",
                query: "prisoner(Jala).",
            },
            ExampleQuery {
                label: "appeal frees (Nia not prisoner)",
                query: "prisoner(Nia).",
            },
            ExampleQuery {
                label: "severe domestic → HighSec (Lalo)",
                query: "building(HighSec, Lalo).",
            },
            ExampleQuery {
                label: "contributor mints (Quin)",
                query: "reward(Quin).",
            },
        ],
        overlay: Some(&nibli_render::UTOPIA_OVERLAY),
    },
    Example {
        name: "Drug interactions (Ch 20)",
        source: DRUG_SOURCE,
        kb: include_str!("../../drug-interactions.nibli"),
        queries: &[
            ExampleQuery {
                label: "concentration rising?",
                query: "increases(Varfarin).",
            },
            ExampleQuery {
                label: "toxicity risk?",
                query: "dangerous(Varfarin).",
            },
            ExampleQuery {
                label: "safety alert?—a 3-hop proof",
                query: "warns(Varfarin).",
            },
            ExampleQuery {
                label: "negative control—no alert",
                query: "warns(Apiksaban).",
            },
        ],
        overlay: Some(&nibli_render::DRUG_INTERACTIONS_OVERLAY),
    },
];

/// nibli-ui's first native test: every shipped example must actually work in
/// the UI's own compile path. Dual-mode like the engine corpus gates: the CI
/// fallback dictionary build may lack generated aliases for long-tail corpus
/// words, so KB lines failing with a dictionary-unknown resolve error are
/// vocab-skipped there (with a floor so the test can't silently check
/// nothing); preset QUERIES use curated-core vocabulary only and must compile
/// in BOTH modes — a query that dies in the deployed bundle is a broken
/// dropdown entry.
#[cfg(test)]
mod tests {
    use super::EXAMPLES;

    fn compile_nibli_kr(line: &str) -> Result<(), String> {
        let ast = nibli_kr::parse_checked(line).map_err(|e| e.to_string())?;
        nibli_semantics::compile_from_ast(ast).map_err(|e| e.to_string())?;
        Ok(())
    }

    #[test]
    fn shipped_examples_compile() {
        // ONE mode since the committed-corpus milestone: every KB line and
        // every preset query must compile — the vocab-skip discipline died
        // with the FULL/FALLBACK build split.
        let mut checked = 0usize;
        for ex in EXAMPLES {
            for (i, raw) in ex.kb.lines().enumerate() {
                let line = raw.trim();
                if line.is_empty() || line.starts_with('#') {
                    continue;
                }
                compile_nibli_kr(line).unwrap_or_else(|e| {
                    panic!(
                        "example {:?} KB line {} does not compile: {line:?} — {e}",
                        ex.name,
                        i + 1
                    )
                });
                checked += 1;
            }
            for q in ex.queries {
                compile_nibli_kr(q.query).unwrap_or_else(|e| {
                    panic!(
                        "example {:?} query {:?} does not compile: {e}",
                        ex.name, q.query
                    )
                });
                checked += 1;
            }
        }
        assert!(
            checked >= 40,
            "example coverage collapsed: only {checked} lines checked"
        );
    }
}
