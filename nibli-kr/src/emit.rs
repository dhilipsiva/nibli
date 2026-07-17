//! The nibli KR emitter: tree AST → `nibli_types::ast::AstBuffer` — the sole
//! producer of the flat buffer `nibli_semantics::compile_from_ast` (and
//! everything below it: nibli-reason, the oracles, the Lean-bridged conformance
//! surface) consumes. Flattener discipline: child indices come from
//! push-return values, never from length arithmetic.
//!
//! Emission map (NIBLI_KR §13; design-review decisions):
//! - predicate names resolve to their corpus entry's canonical BASE name
//!   (`emit_name`: a converted entry's `swap.base`, a plain entry itself, a
//!   compound entry its relation ident); a place-swapped entry emits
//!   `Predicate::Converted`. No identity passthrough — an unknown name (or
//!   uncurated `a+b` compound) is a compile error (NIBLI_KR §13, §5)
//! - logic variables pass through verbatim as `Pronoun("$name")` — the `$`
//!   sigil IS the variable signal, so the user's own names survive into the IR
//!   (no fixed `da`/`de`/`di` pool, no 3-variable cap); pronoun keyterms emit
//!   their KR spellings verbatim (`me`, `you`, `this`, `it_a`…; `?`, `it`, and
//!   `slot` are consumed by nibli-semantics as witness/bound-entity/open-place
//!   markers, never constants). Resolve fail-closes a capitalized Name that
//!   would lower onto a pronoun constant (`Me` vs `me`)
//! - named args → `Argument::Tagged((place_index, arg))` (the u8 index
//!   addresses SURFACE places — those of the possibly-Converted predicate)
//! - operators emit at SENTENCE level (`Afterthought`/`Implies`); operand
//!   negation/prefixes live in the operand `Proposition`'s fields
//! - abstractions → `Description((Indefinite, Abstraction(kind, body)))`
//! - linked args → `Predicate::WithArgs` with `Unspecified` gap-fill from x2; a
//!   named `it` marker at surface place p emits `Converted(x1↔p)` first
//! - BLOCK determiners all lower (the 2026-07-12 fail-closed limitation was
//!   superseded 2026-07-17): `every`/`some` via `Prenex + Implies` / `And`
//!   (spec O7), `exactly N [the]` and `every the` via `Sentence::Quantified`
//!   (canonically equal to their term-position twins — seam-pinned), and
//!   `the X $v:` desugars by SUBSTITUTION (definite let-binding — the block
//!   form never reaches the AST). Block-restrictor rel-clauses fold `where`
//!   on the domain side and `also` on the matrix side
//! - `via` tags emit uniformly as `ModalTag::Custom(word)` — the modal is a
//!   fi'o-style tag over the mapped predicate (spec §5 collapse)

use nibli_types::ast::{
    AbstractionKind, Argument, AstBuffer, Conversion, Determiner, ModalTag, Predicate, Proposition,
    RelClause, RelClauseKind, Sentence, SentenceConnective,
};
use nibli_types::ast::{Connective, DeonticMood, Tense as AstTense};

use crate::ast::{
    AbsKind, Arg, Claim, ClauseBody, Deontic, Det, KeyTerm, PredSeq, PredUnit, Predication,
    RelKind, Restr, RestrKind, Statement, Tag, Tense, Term,
};
use crate::parser::{ParseError, err_at};
use crate::resolve::{PredInfo, ResolvedEntry, label_index, lookup, lookup_compound};
use nibli_types::ast::BlockQuant;

/// The canonical BASE relation name + swap place for a resolved corpus entry:
/// a swapped (converted) entry names its base sibling by type; a plain entry
/// is its own canonical name; a compound emits its relation ident
/// (`computer_user`) and never swaps. `Root` always takes the PLAIN form —
/// the `Converted` wrapper carries the swap.
fn emit_name(entry: &ResolvedEntry) -> (String, Option<u8>) {
    match entry {
        ResolvedEntry::Atomic(e) => (
            e.swap.map(|s| s.base).unwrap_or(e.name).to_owned(),
            e.swap.map(|s| s.with),
        ),
        ResolvedEntry::Compound(c) => (c.relation.to_owned(), None),
    }
}

/// Emit resolved statements into an `AstBuffer` (one root per statement).
pub fn emit(input: &str, statements: &[Statement]) -> Result<AstBuffer, ParseError> {
    let mut emitter = Emitter {
        input,
        block_it_var: None,
        buffer: AstBuffer {
            predicates: Vec::new(),
            arguments: Vec::new(),
            sentences: Vec::new(),
            roots: Vec::new(),
        },
    };
    for statement in statements {
        let root = emitter.claim(&statement.claim, statement.span.start)?;
        emitter.buffer.roots.push(root);
    }
    Ok(emitter.buffer)
}

struct Emitter<'a> {
    input: &'a str,
    buffer: AstBuffer,
    /// While emitting a BLOCK determiner rel-clause's Full body, `it` maps to
    /// the block's `$var` (the block binds the relativized entity by name);
    /// nested term-position clauses suspend it so their `it` still binds the
    /// inner entity.
    block_it_var: Option<String>,
}

impl<'a> Emitter<'a> {
    fn fail(&self, at: usize, message: impl Into<String>) -> ParseError {
        err_at(self.input, at, message)
    }

    fn push_predicate(&mut self, s: Predicate) -> u32 {
        self.buffer.predicates.push(s);
        (self.buffer.predicates.len() - 1) as u32
    }

    fn push_argument(&mut self, s: Argument) -> u32 {
        self.buffer.arguments.push(s);
        (self.buffer.arguments.len() - 1) as u32
    }

    fn push_sentence(&mut self, s: Sentence) -> u32 {
        self.buffer.sentences.push(s);
        (self.buffer.sentences.len() - 1) as u32
    }

    /// Preserve the user's `$var` name — the logic variable IS `$name`, so proof
    /// traces read `$x = adam` (no da/de/di lowering, no 3-variable cap).
    fn var_particle(&mut self, name: &str, _at: usize) -> Result<String, ParseError> {
        Ok(format!("${name}"))
    }

    fn resolved(&self, word: &str, at: usize) -> Result<PredInfo, ParseError> {
        lookup(word).map_err(|m| self.fail(at, format!("internal (post-resolve): {m}")))
    }

    /// The head unit's PredInfo (label/arity source): last unit, descending
    /// through groups; a multi-part unit resolves as a compound entry —
    /// NEVER as its last part (mirrors the resolve pass's `seq`).
    fn resolved_head(&self, seq: &PredSeq, at: usize) -> Result<PredInfo, ParseError> {
        match seq.0.last().expect("pred_seq is non-empty") {
            PredUnit::Word(parts) if parts.len() > 1 => lookup_compound(parts)
                .map_err(|m| self.fail(at, format!("internal (post-resolve): {m}"))),
            PredUnit::Word(parts) => self.resolved(&parts[0], at),
            PredUnit::Group(inner) => self.resolved_head(inner, at),
        }
    }

    // ── claims ──

    fn claim(&mut self, claim: &Claim, at: usize) -> Result<u32, ParseError> {
        match claim {
            Claim::Prenex { vars, body } => {
                let mut lowered = Vec::new();
                for v in vars {
                    lowered.push(self.var_particle(v, at)?);
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

    /// A single-proposition sentence: Predication or Equality, with the proposition-level
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
        let proposition = match claim {
            Claim::Predication(p) => self.predication_proposition(p, negated, tense, deontic)?,
            Claim::Equality(lhs, rhs) => {
                let relation = self.push_predicate(Predicate::Root("equals".into()));
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
        Ok(self.push_sentence(Sentence::Simple(proposition)))
    }

    fn predication_proposition(
        &mut self,
        p: &Predication,
        negated: bool,
        tense: Option<AstTense>,
        deontic: Option<DeonticMood>,
    ) -> Result<Proposition, ParseError> {
        let info = self.resolved_head(&p.seq, p.span.start)?;
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
                    tail_terms.push(self.push_argument(Argument::Tagged((place as u8, inner))));
                }
            }
        }
        for tag in &p.tags {
            let info = if tag.pred.len() > 1 {
                lookup_compound(&tag.pred).map_err(|m| {
                    self.fail(tag.span.start, format!("internal (post-resolve): {m}"))
                })?
            } else {
                self.resolved(&tag.pred[0], tag.span.start)?
            };
            let (word, _) = emit_name(&info.entry);
            let modal_predicate = self.push_predicate(Predicate::Root(word));
            let inner = self.term(&tag.term, tag.span.start)?;
            tail_terms.push(self.push_argument(Argument::ModalTagged((
                ModalTag::Custom(modal_predicate),
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
        // `the X $v:` — definite LET-BINDING sugar (NIBLI_KR §6): `the X` is
        // a rigid designator with no quantifier to bind, so the block
        // substitutes the description for every `$v` in the body and emits
        // the result (occurrences co-refer because the Description constant
        // is keyed by head name). The block form does not survive into the
        // AST — render yields the substituted spelling.
        if det == Det::The {
            let desugared = substitute_var_in_claim(body, var, restr);
            return self.claim(&desugared, at);
        }

        let particle = self.var_particle(var, at)?;
        // Restrictor rel-clauses: `where` folds on the DOMAIN side, `also`
        // on the BODY (matrix) side — mirroring close_quantifier's
        // term-position placement.
        let mut where_sents = Vec::new();
        let mut also_sents = Vec::new();
        for rc in &restr.rel_clauses {
            let s = self.block_clause_sentence(rc, &particle)?;
            match rc.kind {
                RelKind::Where => where_sents.push(s),
                RelKind::Also => also_sents.push(s),
            }
        }

        match det {
            Det::Every => {
                let restr_sentence = self.restr_proposition_sentence(restr, &particle)?;
                let antecedent = self.and_chain(restr_sentence, &where_sents);
                let body_idx = self.claim(body, at)?;
                let matrix = self.and_chain(body_idx, &also_sents);
                let impl_idx = self.push_sentence(Sentence::Connected((
                    SentenceConnective::Implies,
                    antecedent,
                    matrix,
                )));
                Ok(self.push_sentence(Sentence::Prenex((vec![particle], impl_idx))))
            }
            Det::Some => {
                let restr_sentence = self.restr_proposition_sentence(restr, &particle)?;
                // A free `$v` closes existentially at its first occurrence
                // (the restrictor proposition) — one flat conjunction keeps
                // every conjunct in one fact; where/also placement is
                // logically identical under ∃∧.
                let with_wheres = self.and_chain(restr_sentence, &where_sents);
                let body_idx = self.claim(body, at)?;
                let with_body = self.push_sentence(Sentence::Connected((
                    SentenceConnective::And,
                    with_wheres,
                    body_idx,
                )));
                Ok(self.and_chain(with_body, &also_sents))
            }
            Det::Exactly(_) | Det::ExactlyThe(_) | Det::EveryThe => {
                let kind = match det {
                    Det::Exactly(n) => BlockQuant::ExactCount(n),
                    Det::ExactlyThe(n) => BlockQuant::ExactCountDefinite(n),
                    Det::EveryThe => BlockQuant::UniversalDefinite,
                    _ => unreachable!("matched above"),
                };
                let restr_pred = self.restr_predicate_for_block(restr)?;
                let clause = match where_sents.len() {
                    0 => None,
                    _ => {
                        let first = where_sents[0];
                        Some(self.and_chain(first, &where_sents[1..]))
                    }
                };
                let body_idx = self.claim(body, at)?;
                let matrix = self.and_chain(body_idx, &also_sents);
                Ok(self.push_sentence(Sentence::Quantified((
                    kind, particle, restr_pred, clause, matrix,
                ))))
            }
            Det::The => unreachable!("handled by the substitution desugar above"),
        }
    }

    /// And-chain `extra` sentences onto `base` (left-fold).
    fn and_chain(&mut self, mut base: u32, extra: &[u32]) -> u32 {
        for &s in extra {
            base = self.push_sentence(Sentence::Connected((SentenceConnective::And, base, s)));
        }
        base
    }

    /// A block rel-clause body as a sentence whose relativized entity is the
    /// block's `$var`: the Bare sugar applies the (possibly negated) pair to
    /// `$var` at x1; a Full claim emits with `it` mapped to `$var`
    /// (the `block_it_var` context — nested term-position clauses suspend it,
    /// so their `it` still binds the inner entity).
    fn block_clause_sentence(
        &mut self,
        rc: &crate::ast::RelClause,
        particle: &str,
    ) -> Result<u32, ParseError> {
        match &rc.body {
            ClauseBody::Bare { negated, seq } => {
                let mut relation = self.pred_seq(seq, rc.span.start)?;
                if *negated {
                    relation = self.push_predicate(Predicate::Negated(relation));
                }
                let head = self.push_argument(Argument::Pronoun(particle.to_owned()));
                Ok(self.push_sentence(Sentence::Simple(Proposition {
                    relation,
                    head_terms: vec![head],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    deontic: None,
                })))
            }
            ClauseBody::Full(claim) => {
                let prev = self.block_it_var.replace(particle.to_owned());
                let idx = self.claim(claim, rc.span.start);
                self.block_it_var = prev;
                idx
            }
        }
    }

    /// The restrictor PREDICATE of a Quantified block (negation, selectors,
    /// linked args — everything `restr_predicate` supports; rel-clauses are
    /// handled by the caller).
    fn restr_predicate_for_block(&mut self, restr: &Restr) -> Result<u32, ParseError> {
        self.restr_predicate(restr)
    }

    /// `<restr>(<var>)` as a Simple sentence — the antecedent/witness proposition of
    /// a block determiner.
    fn restr_proposition_sentence(
        &mut self,
        restr: &Restr,
        particle: &str,
    ) -> Result<u32, ParseError> {
        let relation = self.restr_predicate(restr)?;
        let head = self.push_argument(Argument::Pronoun(particle.to_owned()));
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
            acc = self.push_predicate(Predicate::Pair((modifier, acc)));
        }
        Ok(acc)
    }

    fn pred_unit(&mut self, unit: &PredUnit, at: usize) -> Result<u32, ParseError> {
        match unit {
            PredUnit::Group(inner) => {
                let inner_idx = self.pred_seq(inner, at)?;
                Ok(self.push_predicate(Predicate::Grouped(inner_idx)))
            }
            PredUnit::Word(parts) => {
                if parts.len() > 1 {
                    // `a+b` compound: resolves ONLY via its committed corpus
                    // entry; emits the entry's relation ident as a plain Root.
                    let info = lookup_compound(parts)
                        .map_err(|m| self.fail(at, format!("internal (post-resolve): {m}")))?;
                    let (word, _) = emit_name(&info.entry);
                    return Ok(self.push_predicate(Predicate::Root(word)));
                }
                let word = &parts[0];
                let info = self.resolved(word, at)?;
                let (word, swap) = emit_name(&info.entry);
                let root = self.push_predicate(Predicate::Root(word));
                Ok(match swap {
                    None => root,
                    Some(p) => self.push_predicate(Predicate::Converted((conversion_for(p), root))),
                })
            }
        }
    }

    // ── terms ──

    fn term(&mut self, term: &Term, at: usize) -> Result<u32, ParseError> {
        let argument = match term {
            Term::Unspecified => Argument::Unspecified,
            Term::Witness => Argument::Pronoun("?".into()),
            Term::Number(n) => Argument::Number(*n),
            Term::Str(s) => Argument::QuotedLiteral(s.clone()),
            Term::Var(v) => Argument::Pronoun(self.var_particle(v, at)?),
            Term::Key(KeyTerm::It) if self.block_it_var.is_some() => {
                // Inside a block rel-clause body, `it` IS the block's `$var`.
                Argument::Pronoun(self.block_it_var.clone().expect("checked above"))
            }
            Term::Key(k) => Argument::Pronoun(keyterm_particle(*k).into()),
            Term::Name { name, rel_clauses } => {
                let mut idx =
                    self.push_argument(Argument::Name(name.to_lowercase().replace('_', " ")));
                for rc in rel_clauses {
                    let clause = self.rel_clause(rc)?;
                    idx = self.push_argument(Argument::Restricted((idx, clause)));
                }
                return Ok(idx);
            }
            Term::Abstraction { kind, body } => {
                let body_idx = self.claim(body, at)?;
                let predicate = self
                    .push_predicate(Predicate::Abstraction((abstraction_kind(*kind), body_idx)));
                Argument::Description((Determiner::Indefinite, predicate))
            }
            Term::Det { det, restr } => {
                let predicate = self.restr_predicate(restr)?;
                let base = match det {
                    Det::Some => Argument::Description((Determiner::Indefinite, predicate)),
                    Det::The => Argument::Description((Determiner::Definite, predicate)),
                    Det::Every => {
                        Argument::Description((Determiner::UniversalIndefinite, predicate))
                    }
                    Det::EveryThe => {
                        Argument::Description((Determiner::UniversalDefinite, predicate))
                    }
                    Det::Exactly(n) => {
                        Argument::QuantifiedDescription((*n, Determiner::Indefinite, predicate))
                    }
                    Det::ExactlyThe(n) => {
                        Argument::QuantifiedDescription((*n, Determiner::Definite, predicate))
                    }
                };
                let mut idx = self.push_argument(base);
                for rc in &restr.rel_clauses {
                    let clause = self.rel_clause(rc)?;
                    idx = self.push_argument(Argument::Restricted((idx, clause)));
                }
                return Ok(idx);
            }
        };
        Ok(self.push_argument(argument))
    }

    // ── restrictors ──

    /// The restrictor's predicate (negation, selector conversion, linked args) —
    /// WITHOUT its relative clauses (the caller wraps those around the argument,
    /// or rejects them for block determiners).
    fn restr_predicate(&mut self, restr: &Restr) -> Result<u32, ParseError> {
        let at = restr.span.start;
        let core = match &restr.kind {
            RestrKind::Selected { pred, label } => {
                let info = self.resolved(pred, at)?;
                let (word, alias_swap) = emit_name(&info.entry);
                let mut idx = self.push_predicate(Predicate::Root(word));
                if let Some(p) = alias_swap {
                    idx = self.push_predicate(Predicate::Converted((conversion_for(p), idx)));
                }
                let place = label_index(&info, label).ok_or_else(|| {
                    self.fail(
                        at,
                        format!("internal (post-resolve): selector {label:?} did not resolve"),
                    )
                })? + 1;
                if place > 1 {
                    idx = self
                        .push_predicate(Predicate::Converted((conversion_for(place as u8), idx)));
                }
                idx
            }
            RestrKind::Seq { seq, linked_args } => {
                let mut idx = self.pred_seq(seq, at)?;
                if !linked_args.is_empty() {
                    let info = self.resolved_head(seq, at)?;
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
                        idx = self.push_predicate(Predicate::Converted((
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
                            be_args.push(self.push_argument(Argument::Unspecified));
                        }
                    }
                    idx = self.push_predicate(Predicate::WithArgs((idx, be_args)));
                }
                idx
            }
        };
        Ok(if restr.negated {
            self.push_predicate(Predicate::Negated(core))
        } else {
            core
        })
    }

    fn rel_clause(&mut self, rc: &crate::ast::RelClause) -> Result<RelClause, ParseError> {
        let kind = match rc.kind {
            RelKind::Where => RelClauseKind::Restrictive,
            RelKind::Also => RelClauseKind::Incidental,
        };
        // A term-position clause's `it` binds ITS OWN entity (nibli-semantics'
        // rel_clause_var) — suspend any enclosing block's `it` mapping.
        let suspended = self.block_it_var.take();
        let body_sentence = match &rc.body {
            ClauseBody::Bare { negated, seq } => {
                let relation = self.pred_seq(seq, rc.span.start)?;
                let head = self.push_argument(Argument::Pronoun("it".into()));
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
        self.block_it_var = suspended;
        Ok(RelClause {
            kind,
            body_sentence,
        })
    }
}

/// Substitute every `$var` occurrence in `claim` with the definite
/// description `the <restr>` — the `the X $v:` block's let-binding desugar.
/// An inner binder that re-binds the same name (a prenex var or another
/// block's `$var`) SHADOWS: its body is left untouched.
fn substitute_var_in_claim(claim: &Claim, var: &str, the_restr: &Restr) -> Claim {
    let sub = |c: &Claim| Box::new(substitute_var_in_claim(c, var, the_restr));
    match claim {
        Claim::Prenex { vars, body } => {
            if vars.iter().any(|v| v == var) {
                claim.clone() // shadowed
            } else {
                Claim::Prenex {
                    vars: vars.clone(),
                    body: sub(body),
                }
            }
        }
        Claim::DetBlock {
            det,
            restr,
            var: inner_var,
            body,
        } => Claim::DetBlock {
            det: *det,
            restr: substitute_var_in_restr(restr, var, the_restr),
            var: inner_var.clone(),
            body: if inner_var == var {
                body.clone() // shadowed
            } else {
                sub(body)
            },
        },
        Claim::Impl(a, b) => Claim::Impl(sub(a), sub(b)),
        Claim::Iff(a, b) => Claim::Iff(sub(a), sub(b)),
        Claim::Xor(a, b) => Claim::Xor(sub(a), sub(b)),
        Claim::Or(a, b) => Claim::Or(sub(a), sub(b)),
        Claim::And(a, b) => Claim::And(sub(a), sub(b)),
        Claim::Not(inner) => Claim::Not(sub(inner)),
        Claim::Prefixed {
            deontic,
            tense,
            atom,
        } => Claim::Prefixed {
            deontic: *deontic,
            tense: *tense,
            atom: sub(atom),
        },
        Claim::Equality(a, b) => Claim::Equality(
            substitute_var_in_term(a, var, the_restr),
            substitute_var_in_term(b, var, the_restr),
        ),
        Claim::Predication(p) => Claim::Predication(Predication {
            seq: p.seq.clone(),
            args: p
                .args
                .iter()
                .map(|a| Arg {
                    label: a.label.clone(),
                    term: substitute_var_in_term(&a.term, var, the_restr),
                    span: a.span.clone(),
                })
                .collect(),
            tags: p
                .tags
                .iter()
                .map(|t| Tag {
                    pred: t.pred.clone(),
                    term: substitute_var_in_term(&t.term, var, the_restr),
                    span: t.span.clone(),
                })
                .collect(),
            span: p.span.clone(),
        }),
    }
}

fn substitute_var_in_term(term: &Term, var: &str, the_restr: &Restr) -> Term {
    match term {
        Term::Var(v) if v == var => Term::Det {
            det: Det::The,
            restr: the_restr.clone(),
        },
        Term::Abstraction { kind, body } => Term::Abstraction {
            kind: *kind,
            body: Box::new(substitute_var_in_claim(body, var, the_restr)),
        },
        Term::Name { name, rel_clauses } => Term::Name {
            name: name.clone(),
            rel_clauses: rel_clauses
                .iter()
                .map(|rc| substitute_var_in_rel_clause(rc, var, the_restr))
                .collect(),
        },
        Term::Det { det, restr } => Term::Det {
            det: *det,
            restr: substitute_var_in_restr(restr, var, the_restr),
        },
        other => other.clone(),
    }
}

fn substitute_var_in_restr(restr: &Restr, var: &str, the_restr: &Restr) -> Restr {
    Restr {
        negated: restr.negated,
        kind: match &restr.kind {
            RestrKind::Seq { seq, linked_args } => RestrKind::Seq {
                seq: seq.clone(),
                linked_args: linked_args
                    .iter()
                    .map(|a| Arg {
                        label: a.label.clone(),
                        term: substitute_var_in_term(&a.term, var, the_restr),
                        span: a.span.clone(),
                    })
                    .collect(),
            },
            selected @ RestrKind::Selected { .. } => selected.clone(),
        },
        rel_clauses: restr
            .rel_clauses
            .iter()
            .map(|rc| substitute_var_in_rel_clause(rc, var, the_restr))
            .collect(),
        span: restr.span.clone(),
    }
}

fn substitute_var_in_rel_clause(
    rc: &crate::ast::RelClause,
    var: &str,
    the_restr: &Restr,
) -> crate::ast::RelClause {
    crate::ast::RelClause {
        kind: rc.kind,
        body: match &rc.body {
            bare @ ClauseBody::Bare { .. } => bare.clone(),
            ClauseBody::Full(claim) => {
                ClauseBody::Full(Box::new(substitute_var_in_claim(claim, var, the_restr)))
            }
        },
        span: rc.span.clone(),
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

fn keyterm_particle(k: KeyTerm) -> &'static str {
    match k {
        KeyTerm::Me => "me",
        KeyTerm::You => "you",
        KeyTerm::We => "we",
        KeyTerm::WeAll => "we_all",
        KeyTerm::WeOthers => "we_others",
        KeyTerm::YouAll => "you_all",
        KeyTerm::This => "this",
        KeyTerm::That => "that",
        KeyTerm::Yonder => "yonder",
        KeyTerm::ItA => "it_a",
        KeyTerm::ItE => "it_e",
        KeyTerm::ItI => "it_i",
        KeyTerm::ItO => "it_o",
        KeyTerm::ItU => "it_u",
        KeyTerm::It => "it",
        KeyTerm::Slot => "slot",
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
    //! nibli-semantics acceptance (compared via Debug formatting; nibli-semantics's variable
    //! naming is deterministic, so structurally-equal ASTs give byte-equal
    //! buffers). The Lojban-twin equality leg these pins carried retired with
    //! the front-end at THE DROP — the structural-equality coverage lives in
    //! the KR seam gate (nibli-verify) now; these remain the in-crate
    //! acceptance pins. All vocabulary is fallback-safe (CI has no
    //! dictionary-en.json).

    use crate::parse_checked;

    fn nibli_kr_lb(text: &str) -> String {
        let buffer = parse_checked(text).unwrap_or_else(|e| panic!("nibli-kr {text:?}: {e}"));
        let lb = nibli_semantics::compile_from_ast(buffer).unwrap_or_else(|e| {
            panic!("nibli-semantics rejected nibli-kr buffer for {text:?}: {e}")
        });
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
        // nibli-semantics's implicit-`it` x1 injection must SKIP when the body
        // carries an explicit `it` (regression: the named spelling used to
        // reject with "Place tag `fa` targets place x1, which is already
        // filled").
        assert_eq!(
            nibli_kr_lb("animal(every dog where loves(lover: Alis, loved: it))."),
            nibli_kr_lb("animal(every dog where loves(Alis, it))."),
        );
        // x1 omitted: the lone fe-tagged `it` must leave x1 Unspecified, equal to
        // the explicit-placeholder twin (regression: it used to silently compile
        // loves(dog, dog) — "a dog that loves itself" — instead of loves(unspecified, dog)).
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

    // ── conversions, rel clauses, pair, linked args ──

    #[test]
    fn converted_alias_and_selector_twins() {
        twins("permitted(every person where approves).");
        twins("permitted(every loves.loved).");
    }

    #[test]
    fn pair_and_linked_arg_twins() {
        twins("healthy data(Kanrek).");
        twins("permitted(every tends(some data)).");
        twins("goes(Adam where dog).");
    }

    // ── acceptance-only shapes (no clean Lojban twin; nibli-semantics must accept) ──

    #[test]
    fn emitted_buffers_are_semantics_valid() {
        for text in [
            "some dog $d: big($d) & goes($d).",
            "goes(every loves(x2: it)).",
            "animal(every dog where loves(lover: Alis, loved: it)).",
            "computer+user(me).",
            "goes(me) via uses(this).",
            "goes(every chemical where increases where thin).",
            "goes(some dog where it = Adam).",
            "knows(me, fact { dog(Adam) }).",
            "must past ~goes(me).",
            "[big fast] dog(Rex).",
        ] {
            nibli_kr_lb(text); // panics if resolve/emit/nibli-semantics rejects
        }
    }

    #[test]
    fn uncurated_compound_fails_closed() {
        // Compounds resolve ONLY via a committed corpus entry — no silent
        // last-part semantics (NIBLI_KR §5).
        let e = parse_checked("dog+cat(me).").unwrap_err();
        let msg = format!("{e}");
        assert!(
            msg.contains("unknown compound predicate \"dog+cat\""),
            "{msg}"
        );
        assert!(msg.contains("committed corpus entry"), "{msg}");
    }

    #[test]
    fn compound_emits_relation_ident() {
        // `computer+user` emits its entry's relation ident as a plain Root
        // (arity 3 — the committed place structure, not the head part's).
        let b = parse_checked("computer+user(me, this).").unwrap();
        assert!(
            b.predicates
                .iter()
                .any(|p| matches!(p, nibli_types::ast::Predicate::Root(w) if w == "computer_user")),
            "compound must emit Root(\"computer_user\"): {:?}",
            b.predicates
        );
    }

    // ── block-determiner lowerings (the former emitter limitations) ──

    #[test]
    fn quantified_blocks_lower_and_compile() {
        // Every previously-fail-closed block form now lowers and is
        // nibli-semantics-valid (the canonical-equality twins live in the
        // seam gate, which owns the variable-renaming canonicalizer).
        for text in [
            "exactly 2 dog $d: goes($d).",
            "exactly 2 dog $d: big($d) & goes($d).",
            "exactly 0 dog $d: goes($d).",
            "exactly 2 the dog $d: goes($d).",
            "every the dog $d: goes($d).",
            "every dog where big $d: goes($d).",
            "every dog where owns(it, some data) $d: goes($d).",
            "every dog also big $d: goes($d).",
            "some dog where big $d: goes($d).",
            "exactly 2 dog where big $d: goes($d).",
        ] {
            nibli_kr_lb(text); // panics if resolve/emit/smuni rejects
        }
    }

    #[test]
    fn exactly_block_emits_quantified_sentence() {
        let b = parse_checked("exactly 2 dog $d: goes($d).").unwrap();
        assert!(
            b.sentences.iter().any(|s| matches!(
                s,
                nibli_types::ast::Sentence::Quantified((
                    nibli_types::ast::BlockQuant::ExactCount(2), v, _, None, _
                ))
                    if v == "$d"
            )),
            "exactly-block must emit Sentence::Quantified(ExactCount(2), $d): {:?}",
            b.sentences
        );
    }

    #[test]
    fn the_block_desugars_by_substitution() {
        // `the X $v:` is definite let-binding sugar: the emitted buffer is the
        // SUBSTITUTED form — every `$d` became `the dog` (a Definite
        // description; occurrences co-refer by head name) and no Quantified
        // sentence exists.
        let b = parse_checked("the dog $d: big($d) & goes($d).").unwrap();
        assert!(
            !b.sentences
                .iter()
                .any(|s| matches!(s, nibli_types::ast::Sentence::Quantified(_))),
            "the-block must desugar away, not bind"
        );
        let definite_count = b
            .arguments
            .iter()
            .filter(|a| {
                matches!(
                    a,
                    nibli_types::ast::Argument::Description((
                        nibli_types::ast::Determiner::Definite,
                        _
                    ))
                )
            })
            .count();
        assert_eq!(definite_count, 2, "both $d occurrences become `the dog`");
        // And the substituted spelling is what renders back.
        let rendered = crate::render::render(&b).unwrap();
        assert_eq!(rendered, "big(the dog) & goes(the dog).");
    }

    #[test]
    fn where_clause_on_every_block_folds_into_antecedent() {
        // `every dog where big $d: goes($d).` ≡ the hand-written prenex
        // `all $d: dog($d) & big($d) -> goes($d).` — identical buffers
        // (same variable names, so plain Debug equality works here).
        assert_eq!(
            nibli_kr_lb("every dog where big $d: goes($d)."),
            nibli_kr_lb("all $d: dog($d) & big($d) -> goes($d)."),
            "the where-clause must fold into the rule antecedent"
        );
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
