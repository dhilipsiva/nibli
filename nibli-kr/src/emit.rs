//! The nibli KR emitter: tree AST → `nibli_types::ast::AstBuffer` — the sole
//! producer of the flat buffer `nibli_semantics::compile_from_ast` (and
//! everything below it: logji, the oracles, the Lean-bridged conformance
//! surface) consumes. Flattener discipline: child indices come from
//! push-return values, never from length arithmetic.
//!
//! Emission map (NIBLI_KR §13; design-review decisions):
//! - predicate names resolve HERE to gismu (alias → gismu, identity words pass
//!   through); an alias with a place swap emits `Predicate::Converted`
//! - `$x`/`$y`/`$z` lower to `da`/`de`/`di` by first emission encounter per
//!   statement (resolve guarantees ≤3); `?`→`ma`, `it`→`ke'a`, `slot`→`ce'u`
//! - named args → `Argument::Tagged((place_index, arg))` (the u8 index
//!   addresses SURFACE places — those of the possibly-Converted predicate)
//! - operators emit at SENTENCE level (`Afterthought`/`Implies`); operand
//!   negation/prefixes live in the operand `Proposition`'s fields
//! - abstractions → `Description((Indefinite, Abstraction(kind, body)))`
//! - linked args → `Predicate::WithArgs` with `Unspecified` gap-fill from x2; a
//!   named `it` marker at surface place p emits `Converted(x1↔p)` first
//! - `every`/`some` BLOCK determiners lower via `Prenex + Implies` / `And`
//!   (spec O7 forbids description-headed conjunction; the seam gate pins the
//!   resulting LogicBuffer shape); `exactly`/`the` blocks and block restrs
//!   with relative clauses are NOT yet lowerable and fail closed with a
//!   targeted message (recorded emitter limitation)
//! - `via` tags emit uniformly as `ModalTag::Custom(gismu)` — the modal is a
//!   fi'o-style tag over the mapped predicate (spec §5 collapse)

use nibli_types::ast::{
    AbstractionKind, Argument, AstBuffer, Conversion, Determiner, ModalTag, Predicate, Proposition,
    RelClause, RelClauseKind, Sentence, SentenceConnective,
};
use nibli_types::ast::{Connective, DeonticMood, Tense as AstTense};

use crate::ast::{
    AbsKind, Arg, Claim, ClauseBody, Deontic, Det, KeyTerm, PredSeq, PredUnit, Predication,
    RelKind, Restr, RestrKind, Statement, Tense, Term,
};
use crate::parser::{ParseError, err_at};
use crate::resolve::{PredInfo, label_index, lookup};

/// Emit resolved statements into an `AstBuffer` (one root per statement).
pub fn emit(input: &str, statements: &[Statement]) -> Result<AstBuffer, ParseError> {
    let mut emitter = Emitter {
        input,
        buffer: AstBuffer {
            predicates: Vec::new(),
            arguments: Vec::new(),
            sentences: Vec::new(),
            roots: Vec::new(),
        },
        vars: Vec::new(),
    };
    for statement in statements {
        emitter.vars.clear();
        let root = emitter.claim(&statement.claim, statement.span.start)?;
        emitter.buffer.roots.push(root);
    }
    Ok(emitter.buffer)
}

struct Emitter<'a> {
    input: &'a str,
    buffer: AstBuffer,
    /// Per-statement `$var` names in first-encounter order → da/de/di.
    vars: Vec<String>,
}

const VAR_NAMES: [&str; 3] = ["da", "de", "di"];

impl<'a> Emitter<'a> {
    fn fail(&self, at: usize, message: impl Into<String>) -> ParseError {
        err_at(self.input, at, message)
    }

    fn push_selbri(&mut self, s: Predicate) -> u32 {
        self.buffer.predicates.push(s);
        (self.buffer.predicates.len() - 1) as u32
    }

    fn push_sumti(&mut self, s: Argument) -> u32 {
        self.buffer.arguments.push(s);
        (self.buffer.arguments.len() - 1) as u32
    }

    fn push_sentence(&mut self, s: Sentence) -> u32 {
        self.buffer.sentences.push(s);
        (self.buffer.sentences.len() - 1) as u32
    }

    fn var_cmavo(&mut self, name: &str, at: usize) -> Result<&'static str, ParseError> {
        if let Some(i) = self.vars.iter().position(|v| v == name) {
            return Ok(VAR_NAMES[i]);
        }
        if self.vars.len() >= 3 {
            // resolve.rs enforces the cap; defensive.
            return Err(self.fail(
                at,
                format!("internal: variable `${name}` exceeds the da/de/di lowering pool"),
            ));
        }
        self.vars.push(name.to_owned());
        Ok(VAR_NAMES[self.vars.len() - 1])
    }

    fn resolved(&self, word: &str, at: usize) -> Result<PredInfo, ParseError> {
        lookup(word).map_err(|m| self.fail(at, format!("internal (post-resolve): {m}")))
    }

    // ── claims ──

    fn claim(&mut self, claim: &Claim, at: usize) -> Result<u32, ParseError> {
        match claim {
            Claim::Prenex { vars, body } => {
                let mut lowered = Vec::new();
                for v in vars {
                    lowered.push(self.var_cmavo(v, at)?.to_owned());
                }
                let body_idx = self.claim(body, at)?;
                Ok(self.push_sentence(Sentence::Prenex((lowered, body_idx))))
            }
            Claim::DetBlock {
                det,
                restr,
                var,
                body,
            } => self.det_block(*det, restr, var, body, at),
            Claim::Impl(a, b) => {
                let l = self.claim(a, at)?;
                let r = self.claim(b, at)?;
                Ok(self.push_sentence(Sentence::Connected((SentenceConnective::Implies, l, r))))
            }
            Claim::Iff(a, b) => self.afterthought(Connective::Iff, a, b, at),
            Claim::Xor(a, b) => self.afterthought(Connective::Whether, a, b, at),
            Claim::Or(a, b) => self.afterthought(Connective::Or, a, b, at),
            Claim::And(a, b) => self.afterthought(Connective::And, a, b, at),
            Claim::Not(inner) => self.simple(inner, true, None, None, at),
            Claim::Prefixed {
                deontic,
                tense,
                atom,
            } => {
                let (negated, inner) = match atom.as_ref() {
                    Claim::Not(inner) => (true, inner.as_ref()),
                    other => (false, other),
                };
                self.simple(inner, negated, *tense, *deontic, at)
            }
            simple @ (Claim::Equality(..) | Claim::Predication(_)) => {
                self.simple(simple, false, None, None, at)
            }
        }
    }

    fn afterthought(
        &mut self,
        conn: Connective,
        a: &Claim,
        b: &Claim,
        at: usize,
    ) -> Result<u32, ParseError> {
        let l = self.claim(a, at)?;
        let r = self.claim(b, at)?;
        Ok(self.push_sentence(Sentence::Connected((
            SentenceConnective::Afterthought(conn),
            l,
            r,
        ))))
    }

    /// A single-bridi sentence: Predication or Equality, with the bridi-level
    /// flags (parser invariant: nothing else reaches here).
    fn simple(
        &mut self,
        claim: &Claim,
        negated: bool,
        tense: Option<Tense>,
        deontic: Option<Deontic>,
        at: usize,
    ) -> Result<u32, ParseError> {
        let tense = tense.map(|t| match t {
            Tense::Past => AstTense::Past,
            Tense::Now => AstTense::Now,
            Tense::Future => AstTense::Future,
        });
        let deontic = deontic.map(|d| match d {
            Deontic::Must => DeonticMood::Obligation,
            Deontic::May => DeonticMood::Permission,
        });
        let bridi = match claim {
            Claim::Predication(p) => self.predication_bridi(p, negated, tense, deontic)?,
            Claim::Equality(lhs, rhs) => {
                let relation = self.push_selbri(Predicate::Root("du".into()));
                let head = self.term(lhs, at)?;
                let tail = self.term(rhs, at)?;
                Proposition {
                    relation,
                    head_terms: vec![head],
                    tail_terms: vec![tail],
                    negated,
                    tense,
                    deontic,
                }
            }
            other => unreachable!("simple() over a compound claim: {other:?}"),
        };
        Ok(self.push_sentence(Sentence::Simple(bridi)))
    }

    fn predication_bridi(
        &mut self,
        p: &Predication,
        negated: bool,
        tense: Option<AstTense>,
        deontic: Option<DeonticMood>,
    ) -> Result<Proposition, ParseError> {
        let info = self.resolved(p.seq.head_word(), p.span.start)?;
        let relation = self.pred_seq(&p.seq, p.span.start)?;

        let mut head_terms = Vec::new();
        let mut tail_terms = Vec::new();
        let mut first_positional = true;
        for arg in &p.args {
            match &arg.label {
                None => {
                    let idx = self.term(&arg.term, arg.span.start)?;
                    if first_positional {
                        head_terms.push(idx);
                        first_positional = false;
                    } else {
                        tail_terms.push(idx);
                    }
                }
                Some(label) => {
                    let place = label_index(&info, label).ok_or_else(|| {
                        self.fail(
                            arg.span.start,
                            format!("internal (post-resolve): label {label:?} did not resolve"),
                        )
                    })?;
                    let inner = self.term(&arg.term, arg.span.start)?;
                    tail_terms.push(self.push_sumti(Argument::Tagged((place as u8, inner))));
                }
            }
        }
        for tag in &p.tags {
            let gismu = self
                .resolved(tag.pred.last().expect("tag pred non-empty"), tag.span.start)?
                .entry
                .map(|e| e.gismu.to_owned())
                .unwrap_or_else(|| tag.pred.last().unwrap().clone());
            let modal_selbri = self.push_selbri(Predicate::Root(gismu));
            let inner = self.term(&tag.term, tag.span.start)?;
            tail_terms.push(self.push_sumti(Argument::ModalTagged((
                ModalTag::Custom(modal_selbri),
                inner,
            ))));
        }
        Ok(Proposition {
            relation,
            head_terms,
            tail_terms,
            negated,
            tense,
            deontic,
        })
    }

    // ── block determiners (spec O7) ──

    fn det_block(
        &mut self,
        det: Det,
        restr: &Restr,
        var: &str,
        body: &Claim,
        at: usize,
    ) -> Result<u32, ParseError> {
        if !restr.rel_clauses.is_empty() {
            return Err(self.fail(
                restr.span.start,
                "relative clauses on a BLOCK determiner's restrictor are not yet lowerable — \
                 use the inline argument form, or fold the condition into the body \
                 (emitter limitation, NIBLI_KR O7)",
            ));
        }
        match det {
            Det::Every => {
                let cmavo = self.var_cmavo(var, at)?.to_owned();
                let restr_sentence = self.restr_bridi_sentence(restr, &cmavo)?;
                let body_idx = self.claim(body, at)?;
                let impl_idx = self.push_sentence(Sentence::Connected((
                    SentenceConnective::Implies,
                    restr_sentence,
                    body_idx,
                )));
                Ok(self.push_sentence(Sentence::Prenex((vec![cmavo], impl_idx))))
            }
            Det::Some => {
                let cmavo = self.var_cmavo(var, at)?.to_owned();
                let restr_sentence = self.restr_bridi_sentence(restr, &cmavo)?;
                let body_idx = self.claim(body, at)?;
                // Bare da/de/di closes existentially at its first occurrence
                // (the restrictor bridi) — the ge…gi conjunction keeps both
                // conjuncts in one fact, matching lo-with-restrictor.
                Ok(self.push_sentence(Sentence::Connected((
                    SentenceConnective::And,
                    restr_sentence,
                    body_idx,
                ))))
            }
            Det::The | Det::EveryThe | Det::Exactly(_) | Det::ExactlyThe(_) => Err(self.fail(
                at,
                "only `every` and `some` block determiners are lowerable today — write the \
                 inline argument form (`pred(exactly 2 dog)`) instead (emitter limitation, \
                 NIBLI_KR O7)",
            )),
        }
    }

    /// `<restr>(<var>)` as a Simple sentence — the antecedent/witness bridi of
    /// a block determiner.
    fn restr_bridi_sentence(&mut self, restr: &Restr, cmavo: &str) -> Result<u32, ParseError> {
        let relation = self.restr_selbri(restr)?;
        let head = self.push_sumti(Argument::Pronoun(cmavo.to_owned()));
        Ok(self.push_sentence(Sentence::Simple(Proposition {
            relation,
            head_terms: vec![head],
            tail_terms: vec![],
            negated: false,
            tense: None,
            deontic: None,
        })))
    }

    // ── predicate sequences ──

    /// Predicate-pair right-grouping: `[a, b, c]` → Pair(a, Pair(b, c)); the
    /// LAST unit is the head.
    fn pred_seq(&mut self, seq: &PredSeq, at: usize) -> Result<u32, ParseError> {
        let mut ids: Vec<u32> = Vec::new();
        for unit in &seq.0 {
            ids.push(self.pred_unit(unit, at)?);
        }
        let mut acc = ids.pop().expect("pred_seq non-empty");
        while let Some(modifier) = ids.pop() {
            acc = self.push_selbri(Predicate::Pair((modifier, acc)));
        }
        Ok(acc)
    }

    fn pred_unit(&mut self, unit: &PredUnit, at: usize) -> Result<u32, ParseError> {
        match unit {
            PredUnit::Group(inner) => {
                let inner_idx = self.pred_seq(inner, at)?;
                Ok(self.push_selbri(Predicate::Grouped(inner_idx)))
            }
            PredUnit::Word(parts) => {
                if parts.len() > 1 {
                    // zei compound: each part resolves to its gismu; compiles
                    // under the last component (engine behavior).
                    let mut gismu_parts = Vec::new();
                    for part in parts {
                        let info = self.resolved(part, at)?;
                        gismu_parts.push(
                            info.entry
                                .map(|e| e.gismu.to_owned())
                                .unwrap_or_else(|| part.clone()),
                        );
                    }
                    return Ok(self.push_selbri(Predicate::Compound(gismu_parts)));
                }
                let word = &parts[0];
                let info = self.resolved(word, at)?;
                let (gismu, swap) = match info.entry {
                    Some(entry) => (entry.gismu.to_owned(), entry.swap),
                    None => (word.clone(), None),
                };
                let root = self.push_selbri(Predicate::Root(gismu));
                Ok(match swap {
                    None => root,
                    Some(p) => self.push_selbri(Predicate::Converted((conversion_for(p), root))),
                })
            }
        }
    }

    // ── terms ──

    fn term(&mut self, term: &Term, at: usize) -> Result<u32, ParseError> {
        let sumti = match term {
            Term::Unspecified => Argument::Unspecified,
            Term::Witness => Argument::Pronoun("ma".into()),
            Term::Number(n) => Argument::Number(*n),
            Term::Str(s) => Argument::QuotedLiteral(s.clone()),
            Term::Var(v) => Argument::Pronoun(self.var_cmavo(v, at)?.to_owned()),
            Term::Key(k) => Argument::Pronoun(keyterm_cmavo(*k).into()),
            Term::Name { name, rel_clauses } => {
                let mut idx =
                    self.push_sumti(Argument::Name(name.to_lowercase().replace('_', " ")));
                for rc in rel_clauses {
                    let clause = self.rel_clause(rc)?;
                    idx = self.push_sumti(Argument::Restricted((idx, clause)));
                }
                return Ok(idx);
            }
            Term::Abstraction { kind, body } => {
                let body_idx = self.claim(body, at)?;
                let selbri =
                    self.push_selbri(Predicate::Abstraction((abstraction_kind(*kind), body_idx)));
                Argument::Description((Determiner::Indefinite, selbri))
            }
            Term::Det { det, restr } => {
                let selbri = self.restr_selbri(restr)?;
                let base = match det {
                    Det::Some => Argument::Description((Determiner::Indefinite, selbri)),
                    Det::The => Argument::Description((Determiner::Definite, selbri)),
                    Det::Every => Argument::Description((Determiner::UniversalIndefinite, selbri)),
                    Det::EveryThe => Argument::Description((Determiner::UniversalDefinite, selbri)),
                    Det::Exactly(n) => {
                        Argument::QuantifiedDescription((*n, Determiner::Indefinite, selbri))
                    }
                    Det::ExactlyThe(n) => {
                        Argument::QuantifiedDescription((*n, Determiner::Definite, selbri))
                    }
                };
                let mut idx = self.push_sumti(base);
                for rc in &restr.rel_clauses {
                    let clause = self.rel_clause(rc)?;
                    idx = self.push_sumti(Argument::Restricted((idx, clause)));
                }
                return Ok(idx);
            }
        };
        Ok(self.push_sumti(sumti))
    }

    // ── restrictors ──

    /// The restrictor's selbri (negation, selector conversion, linked args) —
    /// WITHOUT its relative clauses (the caller wraps those around the sumti,
    /// or rejects them for block determiners).
    fn restr_selbri(&mut self, restr: &Restr) -> Result<u32, ParseError> {
        let at = restr.span.start;
        let core = match &restr.kind {
            RestrKind::Selected { pred, label } => {
                let info = self.resolved(pred, at)?;
                let (gismu, alias_swap) = match info.entry {
                    Some(entry) => (entry.gismu.to_owned(), entry.swap),
                    None => (pred.clone(), None),
                };
                let mut idx = self.push_selbri(Predicate::Root(gismu));
                if let Some(p) = alias_swap {
                    idx = self.push_selbri(Predicate::Converted((conversion_for(p), idx)));
                }
                let place = label_index(&info, label).ok_or_else(|| {
                    self.fail(
                        at,
                        format!("internal (post-resolve): selector {label:?} did not resolve"),
                    )
                })? + 1;
                if place > 1 {
                    idx =
                        self.push_selbri(Predicate::Converted((conversion_for(place as u8), idx)));
                }
                idx
            }
            RestrKind::Seq { seq, linked_args } => {
                let mut idx = self.pred_seq(seq, at)?;
                if !linked_args.is_empty() {
                    let info = self.resolved(seq.head_word(), at)?;
                    // Surface place of the bound variable: 1 unless a NAMED
                    // `it` marks another place (resolve enforced the shape).
                    let mut bound_place = 1usize;
                    let mut placed: Vec<(usize, &Arg)> = Vec::new();
                    let mut next_positional = 2usize;
                    for arg in linked_args {
                        let surface_place = match &arg.label {
                            None => {
                                let p = next_positional;
                                next_positional += 1;
                                p
                            }
                            Some(label) => {
                                label_index(&info, label).ok_or_else(|| {
                                    self.fail(
                                        arg.span.start,
                                        format!(
                                            "internal (post-resolve): label {label:?} did \
                                             not resolve"
                                        ),
                                    )
                                })? + 1
                            }
                        };
                        if matches!(arg.term, Term::Key(KeyTerm::It)) {
                            bound_place = surface_place;
                        } else {
                            placed.push((surface_place, arg));
                        }
                    }
                    if bound_place > 1 {
                        idx = self.push_selbri(Predicate::Converted((
                            conversion_for(bound_place as u8),
                            idx,
                        )));
                    }
                    // Map each linked arg's SURFACE place through the bound
                    // swap (x1 ↔ bound_place relabels: surface 1 → converted
                    // bound_place; everything else keeps its number), then
                    // fill be/bei positions x2.. with Unspecified gaps.
                    let mut by_converted: Vec<(usize, &Arg)> = placed
                        .into_iter()
                        .map(|(q, arg)| (if q == 1 { bound_place } else { q }, arg))
                        .collect();
                    by_converted.sort_by_key(|(p, _)| *p);
                    let max_place = by_converted.last().map(|(p, _)| *p).unwrap_or(1);
                    let mut be_args: Vec<u32> = Vec::new();
                    let mut iter = by_converted.into_iter().peekable();
                    for place in 2..=max_place {
                        if iter.peek().map(|(p, _)| *p) == Some(place) {
                            let (_, arg) = iter.next().unwrap();
                            let idx = self.term(&arg.term, arg.span.start)?;
                            be_args.push(idx);
                        } else {
                            be_args.push(self.push_sumti(Argument::Unspecified));
                        }
                    }
                    idx = self.push_selbri(Predicate::WithArgs((idx, be_args)));
                }
                idx
            }
        };
        Ok(if restr.negated {
            self.push_selbri(Predicate::Negated(core))
        } else {
            core
        })
    }

    fn rel_clause(&mut self, rc: &crate::ast::RelClause) -> Result<RelClause, ParseError> {
        let kind = match rc.kind {
            RelKind::Where => RelClauseKind::Restrictive,
            RelKind::Also => RelClauseKind::Incidental,
        };
        let body_sentence = match &rc.body {
            ClauseBody::Bare { negated, seq } => {
                let relation = self.pred_seq(seq, rc.span.start)?;
                let head = self.push_sumti(Argument::Pronoun("ke'a".into()));
                self.push_sentence(Sentence::Simple(Proposition {
                    relation,
                    head_terms: vec![head],
                    tail_terms: vec![],
                    negated: *negated,
                    tense: None,
                    deontic: None,
                }))
            }
            ClauseBody::Full(claim) => self.claim(claim, rc.span.start)?,
        };
        Ok(RelClause {
            kind,
            body_sentence,
        })
    }
}

fn conversion_for(place: u8) -> Conversion {
    match place {
        2 => Conversion::Swap12,
        3 => Conversion::Swap13,
        4 => Conversion::Swap14,
        5 => Conversion::Swap15,
        other => unreachable!("conversion place {other} (resolve bounds places to 2..=5)"),
    }
}

fn keyterm_cmavo(k: KeyTerm) -> &'static str {
    match k {
        KeyTerm::Me => "mi",
        KeyTerm::You => "do",
        KeyTerm::We => "mi'o",
        KeyTerm::WeAll => "ma'a",
        KeyTerm::WeOthers => "mi'a",
        KeyTerm::YouAll => "do'o",
        KeyTerm::This => "ti",
        KeyTerm::That => "ta",
        KeyTerm::Yonder => "tu",
        KeyTerm::ItA => "ko'a",
        KeyTerm::ItE => "ko'e",
        KeyTerm::ItI => "ko'i",
        KeyTerm::ItO => "ko'o",
        KeyTerm::ItU => "ko'u",
        KeyTerm::It => "ke'a",
        KeyTerm::Slot => "ce'u",
    }
}

fn abstraction_kind(kind: AbsKind) -> AbstractionKind {
    match kind {
        AbsKind::Event => AbstractionKind::Event,
        AbsKind::Fact => AbstractionKind::Fact,
        AbsKind::Property => AbstractionKind::Property,
        AbsKind::Amount => AbstractionKind::Amount,
        AbsKind::Concept => AbstractionKind::Concept,
    }
}

#[cfg(test)]
mod tests {
    //! Golden tests. The load-bearing property: a nibli KR statement and its
    //! smuni acceptance (compared via Debug formatting; smuni's variable
    //! naming is deterministic, so structurally-equal ASTs give byte-equal
    //! buffers). The Lojban-twin equality leg these pins carried retired with
    //! the front-end at THE DROP — the structural-equality coverage lives in
    //! the KR seam gate (nibli-verify) now; these remain the in-crate
    //! acceptance pins. All vocabulary is fallback-safe (CI has no
    //! dictionary-en.json).

    use crate::parse_checked;

    fn nibli_kr_lb(text: &str) -> String {
        let buffer = parse_checked(text).unwrap_or_else(|e| panic!("nibli-kr {text:?}: {e}"));
        let lb = nibli_semantics::compile_from_ast(buffer)
            .unwrap_or_else(|e| panic!("smuni rejected nibli-kr buffer for {text:?}: {e}"));
        format!("{lb:?}")
    }

    fn twins(kr: &str) {
        let _ = nibli_kr_lb(kr);
    }

    // ── ground facts / terms ──

    #[test]
    fn ground_fact_twins() {
        twins("person(Adam).");
        twins("dog(Rex).");
        twins("goes(me, some market).");
        twins("loves(me, _).");
        twins("removes().");
    }

    #[test]
    fn named_args_equal_positional() {
        // Tagged(Fe) routes to the same place as the positional spelling.
        assert_eq!(
            nibli_kr_lb("goes(me, destination: some market)."),
            nibli_kr_lb("goes(me, some market)."),
        );
        assert_eq!(
            nibli_kr_lb("goes(destination: some market, goer: me)."),
            nibli_kr_lb("goes(me, some market)."),
        );
    }

    #[test]
    fn named_args_equal_positional_in_where_body() {
        // All-named args in a where-body lower as empty head + FA-tagged tail;
        // nibli-semantics's implicit-ke'a x1 injection must SKIP when the body
        // carries an explicit `it` (regression: the named spelling used to
        // reject with "Place tag `fa` targets place x1, which is already
        // filled").
        assert_eq!(
            nibli_kr_lb("animal(every dog where loves(lover: Alis, loved: it))."),
            nibli_kr_lb("animal(every dog where loves(Alis, it))."),
        );
        // x1 omitted: the lone fe-tagged `it` must leave x1 Unspecified, equal to
        // the explicit-placeholder twin (regression: it used to silently compile
        // prami(dog, dog) — "a dog that loves itself" — instead of prami(zo'e, dog)).
        assert_eq!(
            nibli_kr_lb("animal(every dog where loves(loved: it))."),
            nibli_kr_lb("animal(every dog where loves(_, it))."),
        );
    }

    // ── determiners ──

    #[test]
    fn determiner_twins() {
        twins("animal(every dog).");
        twins("goes(the dog).");
        twins("red(exactly 2 red).");
        twins("goes(no dog).");
    }

    // ── equality, negation, prefixes ──

    #[test]
    fn equality_negation_prefix_twins() {
        twins("Kim = Adam.");
        twins("~goes(me).");
        twins("past dog(Dan).");
    }

    // ── operators ──

    #[test]
    fn operator_twins() {
        twins("goes(me) & eats(you).");
        twins("goes(me) | eats(you).");
        twins("dog(Rex) -> animal(Rex).");
    }

    // ── quantification ──

    #[test]
    fn prenex_twins() {
        twins("all $x: dog($x) -> animal($x).");
    }

    #[test]
    fn block_every_twin() {
        // O7 preview: the block-every form lowers to the prenex shape.
        twins("every dog $d: animal($d).");
    }

    // ── abstractions ──

    #[test]
    fn abstraction_twins() {
        twins("desires(me, event { goes(you) }).");
        twins("able(me, property { fast(slot) }).");
    }

    // ── conversions, rel clauses, tanru, linked args ──

    #[test]
    fn converted_alias_and_selector_twins() {
        twins("permitted(every person where approves).");
        twins("permitted(every loves.loved).");
    }

    #[test]
    fn tanru_and_linked_arg_twins() {
        twins("healthy data(Kanrek).");
        twins("permitted(every tends(some data)).");
        twins("goes(Adam where dog).");
    }

    // ── acceptance-only shapes (no clean Lojban twin; smuni must accept) ──

    #[test]
    fn emitted_buffers_are_smuni_valid() {
        for text in [
            "some dog $d: big($d) & goes($d).",
            "goes(every loves(x2: it)).",
            "animal(every dog where loves(lover: Alis, loved: it)).",
            "computer+user(me).",
            "goes(me) via uses(this).",
            "goes(every drug where increases where thin).",
            "goes(some dog where it = Adam).",
            "thinks(me, fact { dog(Adam) }).",
            "must past ~goes(me).",
            "[big fast] dog(Rex).",
        ] {
            // computer/user/drug are full-mode-only aliases; keep this list
            // fallback-safe by resolving availability first.
            if crate::parse_checked(text).is_err() {
                // Only acceptable failure: unknown vocabulary in fallback mode.
                let e = crate::parse_checked(text).unwrap_err();
                assert!(
                    format!("{e}").contains("unknown predicate"),
                    "unexpected failure for {text:?}: {e}"
                );
                continue;
            }
            nibli_kr_lb(text); // panics if smuni rejects
        }
    }

    // ── emitter limitations fail closed ──

    #[test]
    fn unlowerable_blocks_fail_closed() {
        let e = parse_checked("exactly 2 dog $d: goes($d).").unwrap_err();
        assert!(format!("{e}").contains("block determiners"), "{e}");
        let e = parse_checked("every dog where big $d: goes($d).").unwrap_err();
        assert!(format!("{e}").contains("not yet lowerable"), "{e}");
    }

    // ── errata pins survive through parse_checked (spec bullet requirement) ──

    #[test]
    fn errata_rejects_via_parse_checked() {
        for (text, needle) in [
            ("~past goes(me).", "past ~P"),
            ("~~goes(me).", "double negation"),
            ("past (a(A) & b(A)).", "single predication"),
        ] {
            let e = parse_checked(text).unwrap_err();
            assert!(format!("{e}").contains(needle), "{text}: {e}");
        }
    }
}
