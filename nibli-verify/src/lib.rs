//! `nibli-verify` — a differential soundness gate for the reasoner.
//!
//! For each `(KB, query)` case in the cleanly-mappable Horn / NAF-free fragment, it
//! drives nibli to a definitive verdict, exports the same compiled FOL IR to TPTP, and
//! checks the verdict against classical entailment as decided by Vampire. A mismatch is
//! a soundness signal: a bug in the reasoner (logji) produced a verdict the declared
//! semantics of smuni's IR does not support. Cases outside the fragment are skipped
//! conservatively — never mis-judged.
//!
//! Scope (Track A, phase 1): the negation-free definite-Horn fragment, where nibli's
//! derivation = the least Herbrand model = classical entailment in BOTH directions. The
//! stratified-NAF + closed-domain fragment (an ASP/Datalog oracle) and mechanized proof
//! are later, separate items.

pub mod corpus;
pub mod filter;
pub mod oracle;
pub mod tptp;

use nibli_engine::NibliEngine;
use oracle::{Oracle, OracleConfig};

/// The intended nibli verdict for a curated case (documentation + report cross-check).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expect {
    True,
    False,
}

impl Expect {
    pub fn label(self) -> &'static str {
        match self {
            Expect::True => "TRUE",
            Expect::False => "FALSE",
        }
    }
}

/// A differential test case: a knowledge base (one Lojban statement per line) and a
/// query, with the intended nibli verdict.
pub struct Case {
    pub name: &'static str,
    pub kb: &'static [&'static str],
    pub query: &'static str,
    pub expect: Expect,
}

/// The result of running one case.
#[derive(Debug)]
pub enum Outcome {
    /// nibli's verdict matched the oracle (both entailed, or both not).
    Agree { name: String, nibli_true: bool },
    /// nibli and the oracle DISAGREE — a soundness signal.
    Diverge {
        name: String,
        nibli_true: bool,
        oracle_entailed: bool,
        tptp: String,
    },
    /// Skipped: the case is outside the mappable classical fragment.
    SkipNonMappable { name: String, reason: String },
    /// Skipped: nibli gave a non-definitive verdict (Unknown / ResourceExceeded).
    SkipIndefinite { name: String, verdict: String },
    /// Skipped: the oracle could not decide (timeout / gave up).
    SkipOracle { name: String, status: String },
    /// A harness error (parse / compile / prover invocation failure).
    Error { name: String, error: String },
}

impl Outcome {
    pub fn name(&self) -> &str {
        match self {
            Outcome::Agree { name, .. }
            | Outcome::Diverge { name, .. }
            | Outcome::SkipNonMappable { name, .. }
            | Outcome::SkipIndefinite { name, .. }
            | Outcome::SkipOracle { name, .. }
            | Outcome::Error { name, .. } => name,
        }
    }

    /// True for the two outcomes where nibli and the oracle were actually compared.
    pub fn is_checked(&self) -> bool {
        matches!(self, Outcome::Agree { .. } | Outcome::Diverge { .. })
    }

    pub fn is_divergence(&self) -> bool {
        matches!(self, Outcome::Diverge { .. })
    }

    pub fn is_error(&self) -> bool {
        matches!(self, Outcome::Error { .. })
    }

    /// One-line human summary.
    pub fn summary(&self) -> String {
        match self {
            Outcome::Agree { name, nibli_true } => {
                format!(
                    "AGREE   {name}: nibli={} == oracle",
                    verdict_word(*nibli_true)
                )
            }
            Outcome::Diverge {
                name,
                nibli_true,
                oracle_entailed,
                ..
            } => format!(
                "DIVERGE {name}: nibli={} but oracle={}",
                verdict_word(*nibli_true),
                entail_word(*oracle_entailed)
            ),
            Outcome::SkipNonMappable { name, reason } => {
                format!("skip    {name}: non-mappable ({reason})")
            }
            Outcome::SkipIndefinite { name, verdict } => {
                format!("skip    {name}: nibli {verdict}")
            }
            Outcome::SkipOracle { name, status } => {
                format!("skip    {name}: oracle {status}")
            }
            Outcome::Error { name, error } => format!("ERROR   {name}: {error}"),
        }
    }
}

fn verdict_word(t: bool) -> &'static str {
    if t { "TRUE" } else { "FALSE" }
}

fn entail_word(e: bool) -> &'static str {
    if e { "entailed" } else { "not-entailed" }
}

/// Run a single case end-to-end (filter → nibli → translate → oracle → compare).
/// Resets the engine first, so cases are independent.
pub fn run_case(engine: &NibliEngine, case: &Case, cfg: &OracleConfig) -> Outcome {
    let name = case.name.to_string();
    engine.reset();

    // 1. Source-level negation pre-filter (KB + query). A rule's implication arrow and
    //    a genuine `na` both flatten to `Not`, so genuine negation is caught here.
    for line in case.kb.iter().chain(std::iter::once(&case.query)) {
        if filter::source_has_negation(line) {
            return Outcome::SkipNonMappable {
                name,
                reason: format!("negation cmavo in source: '{line}'"),
            };
        }
    }

    // 2. Assert the KB, capturing each statement's compiled buffer for translation.
    let mut kb_buffers = Vec::with_capacity(case.kb.len());
    for line in case.kb {
        if let Err(e) = engine.assert_text(line) {
            return Outcome::Error {
                name,
                error: format!("assert '{line}': {e}"),
            };
        }
        match engine.compile_debug(line) {
            Ok(b) => kb_buffers.push(b),
            Err(e) => {
                return Outcome::Error {
                    name,
                    error: format!("compile '{line}': {e}"),
                };
            }
        }
    }
    let query_buf = match engine.compile_debug(case.query) {
        Ok(b) => b,
        Err(e) => {
            return Outcome::Error {
                name,
                error: format!("compile query '{}': {e}", case.query),
            };
        }
    };

    // 3. Buffer-level non-classical filter (compute / tense / deontic / count / abstraction).
    for b in kb_buffers.iter().chain(std::iter::once(&query_buf)) {
        if let Some(reason) = filter::buffer_non_classical(b) {
            return Outcome::SkipNonMappable {
                name,
                reason: reason.to_string(),
            };
        }
    }

    // 4. nibli's verdict + proof (the proof tells us if NAF was used).
    let (verdict, trace) = match engine.query_text_raw_proof(case.query) {
        Ok(x) => x,
        Err(e) => {
            return Outcome::Error {
                name,
                error: format!("query '{}': {e}", case.query),
            };
        }
    };
    if !verdict.is_definitive() {
        return Outcome::SkipIndefinite {
            name,
            verdict: nibli_engine::display_query_result(&verdict),
        };
    }
    if trace.naf_dependent {
        return Outcome::SkipNonMappable {
            name,
            reason: "naf-dependent proof".to_string(),
        };
    }
    let nibli_true = verdict.is_true();

    // 5. Translate the same IR to TPTP and ask the oracle.
    let problem = match tptp::render_problem(&kb_buffers, &query_buf) {
        Ok(t) => t,
        Err(e) => {
            return Outcome::Error {
                name,
                error: format!("tptp translation: {e}"),
            };
        }
    };
    let oracle_entailed = match oracle::decide(&problem, cfg) {
        Ok(Oracle::Entailed) => true,
        Ok(Oracle::NotEntailed) => false,
        Ok(Oracle::Inconclusive(status)) => return Outcome::SkipOracle { name, status },
        Err(e) => {
            return Outcome::Error {
                name,
                error: format!("oracle: {e}"),
            };
        }
    };

    if nibli_true == oracle_entailed {
        Outcome::Agree { name, nibli_true }
    } else {
        Outcome::Diverge {
            name,
            nibli_true,
            oracle_entailed,
            tptp: problem,
        }
    }
}

/// Aggregate report over a corpus run.
pub struct Report {
    pub outcomes: Vec<Outcome>,
}

impl Report {
    pub fn checked(&self) -> usize {
        self.outcomes.iter().filter(|o| o.is_checked()).count()
    }

    pub fn divergences(&self) -> Vec<&Outcome> {
        self.outcomes.iter().filter(|o| o.is_divergence()).collect()
    }

    pub fn errors(&self) -> Vec<&Outcome> {
        self.outcomes.iter().filter(|o| o.is_error()).collect()
    }

    pub fn skipped(&self) -> usize {
        self.outcomes
            .iter()
            .filter(|o| !o.is_checked() && !o.is_error())
            .count()
    }

    /// `agree / diverge / skip / error` tallies.
    pub fn tally(&self) -> (usize, usize, usize, usize) {
        let agree = self
            .outcomes
            .iter()
            .filter(|o| matches!(o, Outcome::Agree { .. }))
            .count();
        (
            agree,
            self.divergences().len(),
            self.skipped(),
            self.errors().len(),
        )
    }
}

/// Run the whole corpus on a fresh engine.
pub fn run_corpus(cases: &[Case], cfg: &OracleConfig) -> Report {
    let engine = NibliEngine::new();
    let outcomes = cases.iter().map(|c| run_case(&engine, c, cfg)).collect();
    Report { outcomes }
}
