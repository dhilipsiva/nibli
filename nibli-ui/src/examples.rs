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
//! regression tests pin (`gdpr_*` / `ddi_*` in
//! `nibli-engine/tests/integration.rs`), pulled in via `include_str!` so
//! the UI examples cannot drift from the tested corpora. The `shipped_examples_compile` guard test below
//! pins every KB line + query through the nibli KR front-end.
//!
//! NOTE: the `name` and `label` strings are quoted VERBATIM by the book
//! (Ch 19) — keep them byte-stable (a book↔UI desync has no gate).

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

// ── Syllogism (Chapter 19) — the minimal worked example, inlined ──
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

// ── GDPR (Chapter 20) — English rendering of `gdpr.nibli` ──
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

// ── Drug interactions (Chapter 21) — English rendering of `drug-interactions.nibli` ──
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
        name: "GDPR compliance (Ch 20)",
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
        name: "Drug interactions (Ch 21)",
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

    fn full_mode() -> bool {
        // Same probe as nibli-verify's alias-map differential: the generated
        // map only exists in a full (dictionary-en.json) build.
        nibli_kr_dictionary::GISMU_TO_ALIAS.len() >= 1000
    }

    fn compile_nibli_kr(line: &str) -> Result<(), String> {
        let ast = nibli_kr::parse_checked(line).map_err(|e| e.to_string())?;
        smuni::compile_from_gerna_ast(ast).map_err(|e| e.to_string())?;
        Ok(())
    }

    #[test]
    fn shipped_examples_compile() {
        let full = full_mode();
        let mut checked = 0usize;
        let mut skipped = 0usize;
        for ex in EXAMPLES {
            for (i, raw) in ex.kb.lines().enumerate() {
                let line = raw.trim();
                if line.is_empty() || line.starts_with('#') {
                    continue;
                }
                match compile_nibli_kr(line) {
                    Ok(()) => checked += 1,
                    // The fail-closed resolve error for a word only the full
                    // (generated) alias map knows — same key as the
                    // the fallback-build vocab skips.
                    Err(e) if !full && e.contains("unknown predicate") => skipped += 1,
                    Err(e) => panic!(
                        "example {:?} KB line {} does not compile: {line:?} — {e}",
                        ex.name,
                        i + 1
                    ),
                }
            }
            for q in ex.queries {
                // Queries never skip: curated-core vocabulary by policy, so the
                // dropdown works even in a fallback-built bundle.
                compile_nibli_kr(q.query).unwrap_or_else(|e| {
                    panic!(
                        "example {:?} query {:?} does not compile: {e}",
                        ex.name, q.query
                    )
                });
                checked += 1;
            }
        }
        if !full {
            println!(
                "shipped_examples_compile: FALLBACK MODE — {skipped} long-tail KB lines vocab-skipped"
            );
        }
        assert!(
            checked >= if full { 40 } else { 20 },
            "example coverage collapsed: only {checked} lines checked (full={full})"
        );
        assert!(
            full || skipped < 40,
            "fallback build skipped too much ({skipped}) — curate more corpus vocabulary"
        );
    }
}
