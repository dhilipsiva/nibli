//! The nibli KR lint catalog (NIBLI_KR §12 + the 2026-07-12 review's
//! L8/L9) — NON-BLOCKING compile notes. "The linter is part of the design,
//! not an afterthought": the grammar is deterministic, but a handful of
//! hazards are semantic, and each lint makes one of them visible instead of
//! silent.
//!
//! Design: a DATA-RETURNING pass, separate from `parse_checked` (which stays
//! fail-closed and note-free — no caller changes). Surfaces opt in: the nibli
//! REPL and the nibli-pipeline session print each note as `[Note: …]` (the
//! `[Skolem]`/`[Rule]` guest-echo precedent, verbose-gated); nibli-ui carries
//! them per KB line on `nibli_protocol::LineResult::notes`. Surfaces whose
//! stdout is data (nibli-validate, the verify harness) simply
//! never call the linter.
//!
//! [`Linter`] is stateful ON PURPOSE: L1 (what `some`/`every` introduced),
//! L4 (first-use converted-alias echo), and L7 (mixing, fired once) are
//! per-FILE or per-SESSION judgments. A REPL holds one `Linter` across lines and resets
//! it with the KB; batch surfaces lint a whole text through a fresh one.
//!
//! The pass parses with per-statement RECOVERY and lints whatever parsed —
//! reporting errors is the compiler's job, not the linter's.

use std::collections::BTreeSet;

use crate::ast::{
    Claim, ClauseBody, Det, Predication, RelClause, Restr, RestrKind, Statement, Term,
};
use crate::parser::{self, line_col};

/// One non-blocking compile note. `code` is the spec's catalog id
/// ("L1"–"L9") — for tests and tooling; user-facing rendering shows only
/// `[Note: {message}]`. 1-based line/column of the nearest enclosing span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LintNote {
    pub code: &'static str,
    pub message: String,
    pub line: u32,
    pub column: u32,
}

/// The stateful lint pass. One instance per session (REPL) or per file
/// (batch): state carries across [`Linter::lint`] calls until [`Linter::reset`].
#[derive(Debug, Default)]
pub struct Linter {
    /// L4: converted aliases already echoed this session.
    seen_aliases: BTreeSet<String>,
    /// L1: restrictor heads introduced by a `some`/`every`/`exactly`
    /// determiner (in walk order, so `owns(some dog, the dog)` is quiet).
    introduced: BTreeSet<String>,
    /// L7 state: a `must`/`may` prefix has appeared / an
    /// `obligated`/`permitted`-class predicate ([`DEONTIC_PREDICATES`]) has
    /// appeared / the note already fired (once per session).
    deontic_prefix_seen: bool,
    norm_pred_seen: bool,
    l7_fired: bool,
}

impl Linter {
    pub fn new() -> Self {
        Self::default()
    }

    /// Forget all session state (the REPL couples this to `:reset`).
    pub fn reset(&mut self) {
        *self = Self::default();
    }

    /// Lint `input`, updating session state. Parses with per-statement
    /// recovery and lints the statements that parsed; parse errors are
    /// ignored here (the compiler reports them). Notes come back in
    /// statement order, walk order within a statement.
    pub fn lint(&mut self, input: &str) -> Vec<LintNote> {
        let (statements, _errors) = parser::parse_text_with_errors(input);
        let mut notes = Vec::new();
        for (i, st) in statements.iter().enumerate() {
            self.lint_statement_shape(input, st, &mut notes);
            let mut w = Walk {
                linter: self,
                input,
                notes: &mut notes,
            };
            w.claim(&st.claim, st.span.start);
            // L7 latch: fire once, as soon as both idioms have appeared.
            if self.deontic_prefix_seen && self.norm_pred_seen && !self.l7_fired {
                self.l7_fired = true;
                push(
                    &mut notes,
                    input,
                    st.span.start,
                    "L7",
                    "this KB mixes must/may prefixes with the obligated()/permitted() \
                     predicate idiom — both are engine-faithful, but they don't chain \
                     with each other"
                        .to_string(),
                );
            }
            // L9: the digit-split hazard at the statement driver.
            if let Some(next) = statements.get(i + 1) {
                self.lint_digit_split(input, st, next, &mut notes);
            }
        }
        notes
    }

    /// L5 — a universal with a disjunctive consequent registers as an
    /// integrity constraint, not a rule (message pinned by NIBLI_KR §6).
    fn lint_statement_shape(&self, input: &str, st: &Statement, notes: &mut Vec<LintNote>) {
        // The consequent of a block is its body (the restrictor is the
        // antecedent); an explicit `->` inside pushes the consequent right.
        fn disjunctive_consequent(c: &Claim) -> bool {
            match c {
                Claim::Or(..) => true,
                Claim::Impl(_, rhs) => matches!(rhs.as_ref(), Claim::Or(..)),
                _ => false,
            }
        }
        let is_constraint = match &st.claim {
            Claim::DetBlock {
                det: Det::Every | Det::EveryThe,
                body,
                ..
            } => disjunctive_consequent(body),
            Claim::Prenex { body, .. } => {
                matches!(body.as_ref(), Claim::Impl(_, rhs) if matches!(rhs.as_ref(), Claim::Or(..)))
            }
            _ => false,
        };
        if is_constraint {
            push(
                notes,
                input,
                st.span.start,
                "L5",
                "registered as integrity constraint".to_string(),
            );
        }
    }

    /// L9 — `X = 2 .5 = $y.` silently splits: the terminating `.` is
    /// whitespace-separated from the claim AND the next statement starts
    /// with a digit (a space inside what was meant as one decimal number).
    fn lint_digit_split(
        &self,
        input: &str,
        st: &Statement,
        next: &Statement,
        notes: &mut Vec<LintNote>,
    ) {
        let bytes = input.as_bytes();
        // `Statement.span` runs through the terminating `.`.
        let dot = st.span.end.wrapping_sub(1);
        let before = st.span.end.wrapping_sub(2);
        let split = dot < bytes.len()
            && bytes[dot] == b'.'
            && before < dot
            && bytes[before].is_ascii_whitespace()
            && bytes.get(next.span.start).is_some_and(u8::is_ascii_digit);
        if split {
            push(
                notes,
                input,
                dot,
                "L9",
                "this '.' is whitespace-separated from the claim and the next statement \
                 starts with a digit — the input splits into two statements here (a \
                 decimal like '2.5' must be written without spaces)"
                    .to_string(),
            );
        }
    }
}

fn push(notes: &mut Vec<LintNote>, input: &str, at: usize, code: &'static str, message: String) {
    let (line, column) = line_col(input, at);
    notes.push(LintNote {
        code,
        message,
        line,
        column,
    });
}

/// L7 — the English corpus names of the obligated/permitted predicate idiom.
/// The runtime keys ONLY on these names (never on gismu provenance — that
/// field is metadata, not a classifier); the
/// `deontic_predicates_match_the_corpus_family` test keeps this set honest
/// against the corpus.
const DEONTIC_PREDICATES: &[&str] = &["obligated", "obliged", "permits", "permitted"];

/// Is this determiner an introducing quantifier for L1 purposes?
fn introduces(det: Det) -> bool {
    matches!(det, Det::Some | Det::Every | Det::Exactly(_))
}

/// The tree walk: one statement, threading the nearest enclosing span start.
struct Walk<'a> {
    linter: &'a mut Linter,
    input: &'a str,
    notes: &'a mut Vec<LintNote>,
}

impl Walk<'_> {
    fn claim(&mut self, claim: &Claim, at: usize) {
        match claim {
            Claim::Prenex { body, .. } => self.claim(body, at),
            Claim::DetBlock { restr, body, .. } => {
                // The block binder introduces its head like `every X` does.
                self.restr_head_introduce(restr);
                self.restr(restr);
                self.claim(body, at);
            }
            Claim::Impl(a, b)
            | Claim::Iff(a, b)
            | Claim::Xor(a, b)
            | Claim::Or(a, b)
            | Claim::And(a, b) => {
                self.claim(a, at);
                self.claim(b, at);
            }
            Claim::Not(inner) => self.claim(inner, at),
            Claim::Prefixed {
                deontic,
                tense,
                atom,
            } => {
                if deontic.is_some() {
                    self.linter.deontic_prefix_seen = true;
                }
                // L6 — tense over a negated claim: the tense-outside-negation reading.
                if tense.is_some() && matches!(atom.as_ref(), Claim::Not(_)) {
                    push(
                        self.notes,
                        self.input,
                        at,
                        "L6",
                        "tense over a negated claim ('past ~P') reads as tense OUTSIDE \
                         the negation ('Past(not P)', 'it was not the case that P') — the \
                         one legal tense×NAF composition, and flavor-exact: a Past witness \
                         blocks it, a bare/future one does not (symmetric with 'past P')"
                            .to_string(),
                    );
                }
                self.claim(atom, at);
            }
            Claim::Equality(a, b) => {
                self.term(a, at);
                self.term(b, at);
            }
            Claim::Predication(p) => self.predication(p),
        }
    }

    fn predication(&mut self, p: &Predication) {
        let at = p.span.start;
        self.seq_words(&p.seq, at);
        // L3 — two or more quantified arguments in one call: scope is
        // written order, so reordering args flips the reading.
        let quantified = p
            .args
            .iter()
            .filter(|a| matches!(&a.term, Term::Det { det, .. } if introduces(*det) || matches!(det, Det::EveryThe | Det::ExactlyThe(_))))
            .count();
        if quantified >= 2 {
            push(
                self.notes,
                self.input,
                at,
                "L3",
                format!(
                    "{quantified} quantified arguments in one call — scope is written \
                     order (∃ before ∀ here; reordering the arguments changes the \
                     meaning)"
                ),
            );
        }
        for arg in &p.args {
            self.term(&arg.term, arg.span.start);
        }
        for tag in &p.tags {
            self.words(&tag.pred, tag.span.start);
            self.term(&tag.term, tag.span.start);
        }
    }

    fn term(&mut self, term: &Term, at: usize) {
        match term {
            Term::Name { rel_clauses, .. } => {
                for rc in rel_clauses {
                    self.rel_clause(rc);
                }
            }
            Term::Abstraction { body, .. } => self.claim(body, at),
            Term::Det { det, restr } => {
                if introduces(*det) {
                    self.restr_head_introduce(restr);
                } else if *det == Det::The {
                    // L1 — the-trap: `the X` is the opaque designator (le),
                    // not a quantifier; warn when nothing introduced X.
                    let head = restr_head(restr);
                    if !self.linter.introduced.contains(head) {
                        let msg = format!(
                            "'the {head}' names an opaque individual (le) — NOT a \
                             quantifier, and no 'some/every {head}' statement \
                             introduced one; write 'some {head}' for \"a/some {head}\""
                        );
                        push(self.notes, self.input, restr.span.start, "L1", msg);
                    }
                }
                self.restr(restr);
            }
            _ => {}
        }
    }

    fn restr_head_introduce(&mut self, restr: &Restr) {
        self.linter.introduced.insert(restr_head(restr).to_string());
    }

    fn restr(&mut self, restr: &Restr) {
        let at = restr.span.start;
        match &restr.kind {
            RestrKind::Seq { seq, linked_args } => {
                self.seq_words(seq, at);
                for arg in linked_args {
                    self.term(&arg.term, arg.span.start);
                }
            }
            RestrKind::Selected { pred, .. } => self.words(std::slice::from_ref(pred), at),
        }
        for rc in &restr.rel_clauses {
            self.rel_clause(rc);
        }
    }

    fn rel_clause(&mut self, rc: &RelClause) {
        let at = rc.span.start;
        match &rc.body {
            ClauseBody::Bare { seq, .. } => {
                // L2 — a multi-unit bare pair in a clause body is ONE
                // shared-event predicate on `it`, not two conjuncts.
                if seq.0.len() >= 2 {
                    push(
                        self.notes,
                        self.input,
                        at,
                        "L2",
                        format!(
                            "this bare clause body is ONE shared-event pair applied \
                             to 'it' (head '{}') — write the predicates joined with \
                             '&' for separate restrictor conjuncts",
                            seq.head_word()
                        ),
                    );
                }
                self.seq_words(seq, at);
            }
            ClauseBody::Full(claim) => {
                // L8 (O9) — a clause-body equality whose RHS term carries its
                // own rel clause: attachment is innermost-wins.
                if let Claim::Equality(_, rhs) = claim.as_ref() {
                    let (attached, rhs_name) = match rhs {
                        Term::Name { name, rel_clauses } if !rel_clauses.is_empty() => {
                            (true, name.clone())
                        }
                        Term::Det { restr, .. } if !restr.rel_clauses.is_empty() => {
                            (true, restr_head(restr).to_string())
                        }
                        _ => (false, String::new()),
                    };
                    if attached {
                        push(
                            self.notes,
                            self.input,
                            at,
                            "L8",
                            format!(
                                "the trailing where/also clause attaches to '{rhs_name}' \
                                 — the equality's right-hand term (innermost-wins, O9) — \
                                 not to the outer restrictor; parenthesize the equality \
                                 for outer attachment"
                            ),
                        );
                    }
                }
                self.claim(claim, at);
            }
        }
    }

    fn seq_words(&mut self, seq: &crate::ast::PredSeq, at: usize) {
        for unit in &seq.0 {
            match unit {
                crate::ast::PredUnit::Word(parts) => self.words(parts, at),
                crate::ast::PredUnit::Group(inner) => self.seq_words(inner, at),
            }
        }
    }

    /// Per predicate word: L4 (first-use converted-alias / compound echo) +
    /// the L7 predicate side.
    fn words(&mut self, parts: &[String], at: usize) {
        if parts.len() > 1 {
            // L4 — echo a COMPOUND's committed place structure on first use:
            // `a+b` resolves only via its corpus entry, whose relation ident
            // and places are conventional (never derivable from the parts) —
            // make them visible. An uncurated compound is a compile error;
            // the linter stays quiet. (Resolution rides the same lookup seam
            // as the emit walk — `crate::resolve`.)
            if let Ok(info) = crate::resolve::lookup_compound(parts)
                && let crate::resolve::ResolvedEntry::Compound(entry) = info.entry
                && self.linter.seen_aliases.insert(info.surface.clone())
            {
                let msg = format!(
                    "{} \u{21a6} {}({})",
                    info.surface,
                    entry.relation,
                    entry.places.join(", ")
                );
                push(self.notes, self.input, at, "L4", msg);
            }
            return;
        }
        let word = &parts[0];
        if DEONTIC_PREDICATES.contains(&word.as_str()) {
            self.linter.norm_pred_seen = true;
        }
        // L4 — echo a CONVERTED alias's canonical predicate + permutation on
        // first use: the alias map is trusted base, and a wrong permutation
        // silently reroutes arguments; make it visible. Plain (unswapped)
        // aliases are quiet — they resolve to themselves since the
        // predicate-name flip, so there is nothing to disclose.
        if let Ok(info) = crate::resolve::lookup(word)
            && let crate::resolve::ResolvedEntry::Atomic(entry) = info.entry
            && let Some(swap) = entry.swap
            && self.linter.seen_aliases.insert(word.clone())
        {
            let msg = format!(
                "{word} \u{21a6} {}\u{27e8}x1\u{2194}x{}\u{27e9}",
                swap.base, swap.with
            );
            push(self.notes, self.input, at, "L4", msg);
        }
    }
}

/// One-shot convenience: lint `input` through a fresh session.
pub fn lint_once(input: &str) -> Vec<LintNote> {
    Linter::new().lint(input)
}

fn restr_head(restr: &Restr) -> &str {
    match &restr.kind {
        RestrKind::Seq { seq, .. } => seq.head_word(),
        RestrKind::Selected { pred, .. } => pred,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn codes(input: &str) -> Vec<&'static str> {
        lint_once(input).into_iter().map(|n| n.code).collect()
    }

    fn messages_for(input: &str, code: &str) -> Vec<String> {
        lint_once(input)
            .into_iter()
            .filter(|n| n.code == code)
            .map(|n| n.message)
            .collect()
    }

    // ── L1 — the-trap ──

    #[test]
    fn l1_fires_on_unintroduced_the() {
        let notes = lint_once("big(the dog).");
        assert!(notes.iter().any(|n| n.code == "L1"), "{notes:?}");
    }

    #[test]
    fn l1_quiet_after_some_introduction() {
        assert!(!codes("eats(some dog).\nbig(the dog).").contains(&"L1"));
        assert!(!codes("animal(every dog).\nbig(the dog).").contains(&"L1"));
    }

    #[test]
    fn l1_order_matters_across_session_calls() {
        let mut linter = Linter::new();
        // `the` before any introduction → fires.
        assert!(linter.lint("big(the dog).").iter().any(|n| n.code == "L1"));
        // Introduce, then `the` is quiet — session state persists.
        linter.lint("eats(some dog).");
        assert!(!linter.lint("big(the dog).").iter().any(|n| n.code == "L1"));
        // reset() forgets the introduction.
        linter.reset();
        assert!(linter.lint("big(the dog).").iter().any(|n| n.code == "L1"));
    }

    // ── L2 — pair vs & in clause bodies ──

    #[test]
    fn l2_fires_on_bare_multiword_pair_body() {
        assert!(codes("beautiful(every person where big fast).").contains(&"L2"));
    }

    #[test]
    fn l2_quiet_on_single_word_and_on_conjunction() {
        assert!(!codes("beautiful(every person where big).").contains(&"L2"));
        assert!(!codes("beautiful(every person where ~cat).").contains(&"L2"));
        assert!(!codes("beautiful(every person where big(it) & fast(it)).").contains(&"L2"));
    }

    // ── L3 — scope by written order ──

    #[test]
    fn l3_fires_on_two_quantified_args() {
        assert!(codes("eats(some dog, every cat).").contains(&"L3"));
    }

    #[test]
    fn l3_quiet_on_one_quantified_arg() {
        assert!(!codes("eats(Adam, every cat).").contains(&"L3"));
    }

    // ── L4 — converted-alias echo, first use per session ──

    #[test]
    fn l4_echoes_converted_alias_swap_once() {
        let mut linter = Linter::new();
        let notes = linter.lint("dog(Adam).\nmetabolized_by(Adam, Betis).");
        let l4: Vec<_> = notes.iter().filter(|n| n.code == "L4").collect();
        // The converted alias discloses its ENGLISH canonical base + the
        // permutation — Lojban-free (the plain base alias of katna is `cuts`).
        assert!(
            l4.iter()
                .any(|n| n.message == "metabolized_by \u{21a6} cuts\u{27e8}x1\u{2194}x2\u{27e9}"),
            "{l4:?}"
        );
        // A PLAIN alias is quiet — it resolves to itself since the
        // predicate-name flip; there is nothing to disclose.
        assert_eq!(l4.len(), 1, "plain `dog` must not echo: {l4:?}");
        // Second use: no re-echo.
        assert!(
            !linter
                .lint("metabolized_by(Betis, Kim).")
                .iter()
                .any(|n| n.code == "L4"),
            "a converted alias must echo only on first use per session"
        );
    }

    #[test]
    fn l4_echoes_compound_place_structure_once() {
        let mut linter = Linter::new();
        let notes = linter.lint("computer+user(me).");
        let l4: Vec<_> = notes.iter().filter(|n| n.code == "L4").collect();
        // A compound discloses its relation ident + committed places —
        // they are conventional, never derivable from the parts.
        assert_eq!(l4.len(), 1, "{l4:?}");
        assert_eq!(
            l4[0].message,
            "computer+user \u{21a6} computer_user(user, computer, purpose)"
        );
        // Second use: no re-echo.
        assert!(
            !linter
                .lint("computer+user(you).")
                .iter()
                .any(|n| n.code == "L4"),
            "a compound must echo only on first use per session"
        );
    }

    #[test]
    fn l4_quiet_on_identity_gismu() {
        // A raw word passes through the identity path — no alias entry, no echo.
        assert!(!codes("gerku(Adam).").contains(&"L4"));
    }

    // ── L5 — constraint echo (spec-pinned message) ──

    #[test]
    fn l5_fires_on_disjunctive_universal_block() {
        let msgs = messages_for("every dog $d: big($d) | fast($d).", "L5");
        assert_eq!(msgs, vec!["registered as integrity constraint".to_string()]);
    }

    #[test]
    fn l5_quiet_on_plain_rule() {
        assert!(!codes("animal(every dog).").contains(&"L5"));
        assert!(!codes("every dog $d: big($d) & fast($d).").contains(&"L5"));
    }

    // ── L6 — tense-over-negation informational note (`past ~P`) ──

    #[test]
    fn l6_fires_on_past_not() {
        assert!(codes("past ~eats(Adam).").contains(&"L6"));
    }

    #[test]
    fn l6_quiet_on_plain_tense_and_plain_negation() {
        assert!(!codes("past eats(Adam).").contains(&"L6"));
        assert!(!codes("~eats(Adam).").contains(&"L6"));
    }

    // ── L7 — norm-idiom mixing, once per session ──

    #[test]
    fn l7_fires_once_when_both_idioms_appear() {
        let mut linter = Linter::new();
        assert!(
            !linter
                .lint("must eats(Adam).")
                .iter()
                .any(|n| n.code == "L7")
        );
        let second = linter.lint("permitted(Adam).");
        assert_eq!(second.iter().filter(|n| n.code == "L7").count(), 1);
        // Latched: never again this session.
        assert!(
            !linter
                .lint("may eats(Betis).")
                .iter()
                .any(|n| n.code == "L7")
        );
    }

    #[test]
    fn deontic_predicates_match_the_corpus_family() {
        // Test-ONLY provenance use (the bridge's sanctioned role): the runtime
        // set must equal every corpus entry derived from the deontic source
        // family, so a corpus re-key or a new deontic entry breaks THIS test
        // instead of silently disabling L7. corpus_entries() is name-sorted,
        // matching the const's alphabetical order.
        let family: Vec<&str> = nibli_lexicon::corpus::corpus_entries()
            .filter(|e| matches!(e.source_gismu, "bilga" | "curmi"))
            .map(|e| e.name)
            .collect();
        assert_eq!(family, DEONTIC_PREDICATES);
    }

    #[test]
    fn l7_quiet_on_either_idiom_alone() {
        assert!(!codes("must eats(Adam).\nmay eats(Betis).").contains(&"L7"));
        assert!(!codes("permitted(Adam).\nobligated(Adam).").contains(&"L7"));
    }

    // ── L8 — O9 attachment echo ──

    #[test]
    fn l8_fires_on_equality_rhs_rel_clause() {
        let notes = lint_once("beautiful(every person where it = Boss also big).");
        let l8: Vec<_> = notes.iter().filter(|n| n.code == "L8").collect();
        assert_eq!(l8.len(), 1, "{notes:?}");
        assert!(l8[0].message.contains("'Boss'"), "{}", l8[0].message);
    }

    #[test]
    fn l8_quiet_without_rhs_clause() {
        assert!(!codes("beautiful(every person where it = Boss).").contains(&"L8"));
    }

    // ── L9 — the digit-split hazard ──

    #[test]
    fn l9_fires_on_whitespace_dot_before_digit_statement() {
        // `$x = 2 .5 = $y.` splits into `$x = 2.` and `5 = $y.` today.
        let notes = lint_once("$x = 2 .5 = $y.");
        assert!(notes.iter().any(|n| n.code == "L9"), "{notes:?}");
    }

    #[test]
    fn l9_quiet_on_adjacent_dot_and_non_digit_follow() {
        // One statement — `2.5` is a single number.
        assert!(!codes("$x = 2.5.").contains(&"L9"));
        // Whitespace-separated dot but the next statement starts with a letter.
        assert!(!codes("$x = 2 .\ndog(Adam).").contains(&"L9"));
    }

    // ── The shipped corpus lints clean of panics ──

    #[test]
    fn acceptance_corpus_lints_without_panicking() {
        let corpus = include_str!("../tests/acceptance.nibli");
        let notes = lint_once(corpus);
        // The corpus exercises CONVERTED aliases (metabolized_by, obligated,
        // permitted), so at minimum L4 echoes fire.
        assert!(
            notes.iter().any(|n| n.code == "L4"),
            "expected converted-alias echoes over the acceptance corpus"
        );
    }
}
