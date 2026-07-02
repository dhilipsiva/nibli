//! `nibli-verify` — a differential soundness gate for the reasoner.
//!
//! For each `(KB, query)` case in the cleanly-mappable Horn / NAF-free fragment, it
//! drives nibli to a definitive verdict, exports the same compiled FOL IR to TPTP, and
//! checks the verdict against classical entailment as decided by Vampire. A mismatch is
//! a soundness signal: a bug in the reasoner (logji) produced a verdict the declared
//! semantics of smuni's IR does not support. Cases outside the fragment are skipped
//! conservatively — never mis-judged.
//!
//! Two oracles, two fragments:
//!   - **Vampire** (classical FOL, [`run_lines`]) — the negation-free definite-Horn fragment,
//!     where nibli's derivation = the least Herbrand model = classical entailment in BOTH
//!     directions.
//!   - **clingo** (ASP, [`run_lines_asp`]) — the stratified negation-as-failure + closed-world
//!     fragment the classical prover cannot cover, where nibli's closed-world verdict = the
//!     unique perfect model = clingo's unique stable model (see `proofs/Stratification.lean`).

pub mod asp;
pub mod corpora;
pub mod corpus;
pub mod corpus_naf;
pub mod filter;
pub mod generator;
pub mod oracle;
pub mod oracle_asp;
pub mod parser_diff;
pub mod seam;
pub mod strat_diff;
pub mod tense;
pub mod tptp;

use nibli_engine::NibliEngine;
use oracle::{Oracle, OracleConfig};
use oracle_asp::{AspConfig, AspVerdict};

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

/// Run a single `(name, kb, query)` end-to-end (filter → nibli → translate → oracle →
/// compare). Resets the engine first, so cases are independent. Shared by the curated
/// `run_case` and the generated `run_random`.
pub fn run_lines(
    engine: &NibliEngine,
    name: &str,
    kb: &[&str],
    query: &str,
    cfg: &OracleConfig,
) -> Outcome {
    let name = name.to_string();
    engine.reset();

    // 1. Source-level negation pre-filter (KB + query). A rule's implication arrow and
    //    a genuine `na` both flatten to `Not`, so genuine negation is caught here.
    for line in kb.iter().chain(std::iter::once(&query)) {
        if filter::source_has_negation(line) {
            return Outcome::SkipNonMappable {
                name,
                reason: format!("negation cmavo in source: '{line}'"),
            };
        }
    }

    // 2. Assert the KB, capturing each statement's compiled buffer for translation.
    let mut kb_buffers = Vec::with_capacity(kb.len());
    for line in kb {
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
    let query_buf = match engine.compile_debug(query) {
        Ok(b) => b,
        Err(e) => {
            return Outcome::Error {
                name,
                error: format!("compile query '{}': {e}", query),
            };
        }
    };

    // 3. Buffer-level non-classical filter (compute / deontic / count / abstraction / du shape).
    for b in kb_buffers.iter().chain(std::iter::once(&query_buf)) {
        if let Some(reason) = filter::buffer_non_classical(b) {
            return Outcome::SkipNonMappable {
                name,
                reason: reason.to_string(),
            };
        }
    }

    // 3b. Tense flavorization: rewrite tensed buffers into flavor-suffixed tense-free
    //     buffers (identity when no tense occurs; see `tense::flavorize`). An
    //     unsupported tense shape (tense×NAF, tense×abstraction, nested wrappers) is
    //     a conservative skip — never mis-judged.
    let (kb_buffers, query_buf) = match tense::flavorize(&kb_buffers, &query_buf) {
        Ok(x) => x,
        Err(e) => return Outcome::SkipNonMappable { name, reason: e },
    };

    // 4. nibli's verdict + proof (the proof tells us if NAF was used).
    let (verdict, trace) = match engine.query_text_raw_proof(query) {
        Ok(x) => x,
        Err(e) => {
            return Outcome::Error {
                name,
                error: format!("query '{}': {e}", query),
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

/// Run a single curated [`Case`].
pub fn run_case(engine: &NibliEngine, case: &Case, cfg: &OracleConfig) -> Outcome {
    run_lines(engine, case.name, case.kb, case.query, cfg)
}

/// Run the whole curated corpus on a fresh engine.
pub fn run_corpus(cases: &[Case], cfg: &OracleConfig) -> Report {
    let engine = NibliEngine::new();
    let outcomes = cases.iter().map(|c| run_case(&engine, c, cfg)).collect();
    Report { outcomes }
}

/// Run the **mappable sub-slice** of a case-study corpus through the differential gate: filter
/// the corpus to its classical Horn/NAF-free lines (the gate's own filter decides — no
/// hand-picked list), mine the entities and type-predicates from the compiled buffers, and check
/// every atomic `la .E. cu P` query against Vampire. Real case-study vocabulary; the deontic/NAF
/// lines are skipped (they need the Track A (c) ASP oracle), never mis-judged.
pub fn run_corpus_slice(label: &str, corpus: &str, cfg: &OracleConfig) -> Report {
    use nibli_types::logic::{LogicNode, LogicalTerm};
    use std::collections::BTreeSet;

    let engine = NibliEngine::new();

    // 1. Keep the mappable lines; mine entities (constants) + candidate type-predicates.
    let mut kb_lines: Vec<String> = Vec::new();
    let mut entities: BTreeSet<String> = BTreeSet::new();
    let mut preds: BTreeSet<String> = BTreeSet::new();
    for line in corpora::lines(corpus) {
        if filter::source_has_negation(line) {
            continue;
        }
        let buf = match engine.compile_debug(line) {
            Ok(b) => b,
            Err(_) => continue,
        };
        if filter::buffer_non_classical(&buf).is_some() {
            continue;
        }
        kb_lines.push(line.to_string());
        for node in &buf.nodes {
            if let LogicNode::Predicate((rel, args)) = node {
                // A type predicate is the event-typing atom `rel(ev)`; role predicates are
                // `rel_xN(ev, arg)`, and `du` stays flat (not a type predicate).
                if args.len() == 1
                    && matches!(args[0], LogicalTerm::Variable(_))
                    && !rel.contains("_x")
                    && rel != "du"
                {
                    preds.insert(rel.clone());
                }
                for a in args {
                    if let LogicalTerm::Constant(c) = a {
                        entities.insert(c.clone());
                    }
                }
            }
        }
    }

    // 2. Keep only predicates that form a parseable, mappable atomic query (drops any
    //    tanru-derived compound name cleanly — it won't compile as a bare selbri).
    let queryable: Vec<String> = preds
        .into_iter()
        .filter(|p| {
            let q = format!("la .adam. cu {p}");
            engine
                .compile_debug(&q)
                .map(|b| filter::buffer_non_classical(&b).is_none())
                .unwrap_or(false)
        })
        .collect();

    // 3. Enumerate atomic queries entity × predicate through the gate.
    let kb_refs: Vec<&str> = kb_lines.iter().map(String::as_str).collect();
    let mut outcomes = Vec::new();
    for e in &entities {
        for p in &queryable {
            let query = format!("la .{e}. cu {p}");
            outcomes.push(run_lines(
                &engine,
                &format!("{label}:{e}:{p}"),
                &kb_refs,
                &query,
                cfg,
            ));
        }
    }
    Report { outcomes }
}

/// Run `count` deterministically-generated random cases (seeds `base_seed .. base_seed+count`)
/// through the differential gate on a fresh engine. Each case is a NAF-free definite-Horn
/// program by construction (see [`generator`]); the filter still skips any that fall outside
/// the mappable fragment, so this only broadens coverage — it can never mis-judge.
pub fn run_random(count: u64, base_seed: u64, cfg: &OracleConfig) -> Report {
    let engine = NibliEngine::new();
    let outcomes = (0..count)
        .map(|i| {
            let case = generator::random_case(base_seed.wrapping_add(i));
            let kb: Vec<&str> = case.kb.iter().map(String::as_str).collect();
            run_lines(&engine, &case.name, &kb, &case.query, cfg)
        })
        .collect();
    Report { outcomes }
}

// ── The clingo (ASP) oracle path: the stratified-NAF + closed-world fragment ──────────────

/// Run a single `(name, kb, query)` against the **clingo (ASP)** oracle end-to-end. Mirrors
/// [`run_lines`] but for the stratified-NAF + closed-world fragment, with four deliberate
/// differences: (a) NO source-negation pre-filter — negation-as-failure is the whole point;
/// (b) the buffer gate is [`filter::buffer_asp_mappable`] (accepts NAF, still rejects
/// compute/tense/deontic/count/abstraction/`du`); (c) NO `naf_dependent` skip — NAF-dependent
/// verdicts are exactly what this oracle checks; (d) it translates to ASP and asks clingo.
///
/// Correspondence (closed-world, both directions): nibli `is_true()` ⟺ clingo `Entailed`
/// (`goal` in the unique stable model); nibli definitive-FALSE ⟺ clingo `NotEntailed`.
/// Indefinite verdicts (Unknown / ResourceExceeded, incl. a cut cycle) are skipped before the
/// oracle, so nibli's conservatism never becomes a false divergence.
pub fn run_lines_asp(
    engine: &NibliEngine,
    name: &str,
    kb: &[&str],
    query: &str,
    cfg: &AspConfig,
) -> Outcome {
    let name = name.to_string();
    engine.reset();

    // 1. Assert the KB, capturing each statement's compiled buffer for translation. (An
    //    unstratifiable rule errors here — nibli rejects it at assert time — so only
    //    stratified, unique-model programs ever reach clingo.)
    let mut kb_buffers = Vec::with_capacity(kb.len());
    for line in kb {
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
    let query_buf = match engine.compile_debug(query) {
        Ok(b) => b,
        Err(e) => {
            return Outcome::Error {
                name,
                error: format!("compile query '{query}': {e}"),
            };
        }
    };

    // 2. ASP-mappable filter (accepts NAF; rejects compute/deontic + non-ground du; a
    //    sole-root exact-count QUERY is accepted — count assertions are not).
    for b in &kb_buffers {
        if let Some(reason) = filter::buffer_asp_mappable(b) {
            return Outcome::SkipNonMappable {
                name,
                reason: reason.to_string(),
            };
        }
    }
    if let Some(reason) = filter::buffer_asp_mappable_query(&query_buf) {
        return Outcome::SkipNonMappable {
            name,
            reason: reason.to_string(),
        };
    }
    // 2a. Count-query case guard: the engine's count and clingo's #count agree only on
    //     ground-fact KBs (rules inject countable import witnesses; du classes are not
    //     collapsed) — skip the disagreeing combinations rather than canonize them.
    if let Some(reason) = filter::count_case_guard(&kb_buffers, &query_buf) {
        return Outcome::SkipNonMappable {
            name,
            reason: reason.to_string(),
        };
    }

    // 2b. Tense flavorization (identity when no tense occurs). Tense×NAF is a
    //     conservative skip: the engine's NegatedExistsGroup is tenseless (audit U1),
    //     and the gate must not canonize that behavior as oracle expectation.
    let (kb_buffers, query_buf) = match tense::flavorize(&kb_buffers, &query_buf) {
        Ok(x) => x,
        Err(e) => return Outcome::SkipNonMappable { name, reason: e },
    };

    // 3. nibli's verdict. We do NOT skip naf-dependent proofs — that is the point.
    let (verdict, _trace) = match engine.query_text_raw_proof(query) {
        Ok(x) => x,
        Err(e) => {
            return Outcome::Error {
                name,
                error: format!("query '{query}': {e}"),
            };
        }
    };
    if !verdict.is_definitive() {
        return Outcome::SkipIndefinite {
            name,
            verdict: nibli_engine::display_query_result(&verdict),
        };
    }
    let nibli_true = verdict.is_true();

    // 4. Translate the same IR to ASP and ask clingo. An unsafe/domain-open program is a
    //    genuine fragment boundary → skip; any other translation error is a filter bug → Error.
    let program = match asp::render_program(&kb_buffers, &query_buf) {
        Ok(p) => p,
        Err(e) if e.contains("unsafe") || e.contains("domain-open") => {
            return Outcome::SkipNonMappable { name, reason: e };
        }
        Err(e) => {
            return Outcome::Error {
                name,
                error: format!("asp translation: {e}"),
            };
        }
    };
    let oracle_entailed = match oracle_asp::decide(&program, cfg) {
        Ok(AspVerdict::Entailed) => true,
        Ok(AspVerdict::NotEntailed) => false,
        Ok(AspVerdict::Inconclusive(status)) => return Outcome::SkipOracle { name, status },
        Err(e) => {
            return Outcome::Error {
                name,
                error: format!("asp oracle: {e}"),
            };
        }
    };

    if nibli_true == oracle_entailed {
        Outcome::Agree { name, nibli_true }
    } else {
        // Reuse the `tptp` field to carry the `.lp` program for the report dump.
        Outcome::Diverge {
            name,
            nibli_true,
            oracle_entailed,
            tptp: program,
        }
    }
}

/// Run the curated stratified-NAF corpus against clingo on a fresh engine.
pub fn run_naf_corpus(cases: &[Case], cfg: &AspConfig) -> Report {
    let engine = NibliEngine::new();
    let outcomes = cases
        .iter()
        .map(|c| run_lines_asp(&engine, c.name, c.kb, c.query, cfg))
        .collect();
    Report { outcomes }
}

/// Run `count` deterministically-generated random **stratified-NAF** cases (seeds
/// `base_seed .. base_seed+count`) against clingo on a fresh engine. Each case is stratified
/// and ASP-mappable by construction (see [`generator::random_naf_case`]); the filter is still
/// the final arbiter, so this only broadens coverage — it can never mis-judge.
pub fn run_random_naf(count: u64, base_seed: u64, cfg: &AspConfig) -> Report {
    let engine = NibliEngine::new();
    let outcomes = (0..count)
        .map(|i| {
            let case = generator::random_naf_case(base_seed.wrapping_add(i));
            let kb: Vec<&str> = case.kb.iter().map(String::as_str).collect();
            run_lines_asp(&engine, &case.name, &kb, &case.query, cfg)
        })
        .collect();
    Report { outcomes }
}

/// Run `count` deterministically-generated random **exact-count** cases (seeds
/// `base_seed .. base_seed+count`) against clingo on a fresh engine. Each case is a
/// ground-fact KB plus a `PA lo P1 cu P2` query — the guarded fragment where the
/// engine's per-member count equals clingo's `#count` over the stable model (see
/// [`filter::count_case_guard`]).
pub fn run_random_count(count: u64, base_seed: u64, cfg: &AspConfig) -> Report {
    let engine = NibliEngine::new();
    let outcomes = (0..count)
        .map(|i| {
            let case = generator::random_count_case(base_seed.wrapping_add(i));
            let kb: Vec<&str> = case.kb.iter().map(String::as_str).collect();
            run_lines_asp(&engine, &case.name, &kb, &case.query, cfg)
        })
        .collect();
    Report { outcomes }
}
