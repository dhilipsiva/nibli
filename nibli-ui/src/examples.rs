//! Preloaded examples for the header "example" dropdown.
//!
//! Each [`Example`] bundles a knowledge base (English `source` + Lojban) and a
//! set of preset queries (English label + Lojban). Selecting one in the header
//! loads it read-only into the Transparency Triad; the query box becomes a
//! dropdown of that example's queries. "Custom" (the default, `None`) keeps the
//! editable/translatable behavior.
//!
//! The KB corpora are the SAME files the engine's regression tests pin
//! (`gdpr_*` / `ddi_*` in `nibli-engine/tests/integration.rs` and
//! `pipeline_*_lojban_all_lines_parse` in gerna), pulled in via `include_str!`
//! so the UI examples cannot drift from the tested corpora. The query verdicts
//! are likewise pinned by those tests. Query sets mirror the live demo
//! (`dhilipsiva.com/static/nibli/app/nibli.js`).

/// One preset query: an English note shown beside its Lojban in the dropdown.
pub struct ExampleQuery {
    pub label: &'static str,
    pub lojban: &'static str,
}

/// A preloaded knowledge base + its queries.
pub struct Example {
    /// Dropdown label.
    pub name: &'static str,
    /// KB rendered as plain English (read-only Source tab).
    pub source: &'static str,
    /// KB as Lojban. The full commented corpus is fine: `run_query` skips
    /// `#`-comment and blank lines at assert time.
    pub lojban: &'static str,
    /// The preset queries offered for this KB.
    pub queries: &'static [ExampleQuery],
    /// Domain-term overlay for this curated corpus's proof rendering (the
    /// documented reader's overlay — `fanta` -> "inhibits", `varfarin` ->
    /// "warfarin"). `None` keeps the engine's literal glosses. Applied only to the
    /// proof "why"/tree, never the back-translation tab.
    pub overlay: Option<&'static nibli_render::DomainGloss>,
}

// ── Syllogism (Chapter 19) — the minimal worked example, inlined ──
const SYLLOGISM_SOURCE: &str = "\
All dogs are animals.
All animals eat.
Adam is a dog.";

const SYLLOGISM_LOJBAN: &str = "\
# All dogs are animals.
ro lo gerku cu danlu
# All animals eat.
ro lo danlu cu citka
# Adam is a dog.
la .adam. cu gerku
";

// ── GDPR (Chapter 20) — English rendering of `gdpr.lojban` ──
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

// ── Drug interactions (Chapter 21) — English rendering of `drug-interactions.lojban` ──
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
        name: "Syllogism (Ch 19)",
        source: SYLLOGISM_SOURCE,
        lojban: SYLLOGISM_LOJBAN,
        queries: &[
            ExampleQuery {
                label: "does Adam eat?—a 2-hop proof",
                lojban: "la .adam. cu citka",
            },
            ExampleQuery {
                label: "is Adam an animal?—1 hop",
                lojban: "la .adam. cu danlu",
            },
            ExampleQuery {
                label: "is Adam a bird?—a real FALSE",
                lojban: "la .adam. cu cipni",
            },
        ],
        overlay: None,
    },
    Example {
        name: "GDPR compliance (Ch 20)",
        source: GDPR_SOURCE,
        lojban: include_str!("../../gdpr.lojban"),
        queries: &[
            ExampleQuery {
                label: "lawful basis? (Art 6)",
                lojban: "la .adam. cu se curmi",
            },
            ExampleQuery {
                label: "right to erasure? (Art 17)",
                lojban: "la .adam. na se curmi",
            },
            ExampleQuery {
                label: "a controller is not a consenting person—exhaustive FALSE",
                lojban: "la .gugli. cu se curmi",
            },
            ExampleQuery {
                label: "health record → personal data (Art 4/9, derived)",
                lojban: "la .kanrek. cu datni",
            },
        ],
        overlay: Some(&nibli_render::GDPR_OVERLAY),
    },
    Example {
        name: "Drug interactions (Ch 21)",
        source: DRUG_SOURCE,
        lojban: include_str!("../../drug-interactions.lojban"),
        queries: &[
            ExampleQuery {
                label: "concentration rising?",
                lojban: "la .varfarin. cu zenba",
            },
            ExampleQuery {
                label: "toxicity risk?",
                lojban: "la .varfarin. cu ckape",
            },
            ExampleQuery {
                label: "safety alert?—a 3-hop proof",
                lojban: "la .varfarin. cu kajde",
            },
            ExampleQuery {
                label: "negative control—no alert",
                lojban: "la .apiksaban. cu kajde",
            },
        ],
        overlay: Some(&nibli_render::DRUG_INTERACTIONS_OVERLAY),
    },
];
