//! The nibli KR resolve pass — dictionary-driven static checks over the parsed
//! tree (NIBLI_KR §13): everything that needs vocabulary knowledge and
//! therefore cannot live in the grammar or the walker.
//!
//! Checks (all fail closed, targeted positioned errors):
//! 1. NAME RESOLUTION — every predicate word (predication heads incl. all
//!    tanru units and zei parts, restrictors, selected preds, bare clause
//!    bodies, `via` tag preds) must be a nibli-kr-dictionary alias or an
//!    identity-passthrough Lojban word (`nibli_lexicon::get_arity` hit).
//!    Anything else is a compile error — the deliberate tightening over
//!    gerna's arity-2 default: an unknown word NEVER silently mints a
//!    relation.
//! 2. PLACE CHECKS against the head's arity (tanru arity = the LAST unit's
//!    last word): positional overflow, unknown labels, refills. Labels
//!    address SURFACE places (a converted alias's swap applies at emission).
//! 3. LINKED ARGS on restrictors: positionals fill x2.. (the bound variable
//!    takes x1, like be/bei); a NAMED `it` marks the bound place instead; at
//!    most one `it`; x1 must stay free for the bound variable otherwise.
//! 4. VARIABLE CAP: ≤3 distinct `$var` names per STATEMENT — bound
//!    prenex/det_block vars share smuni's da/de/di pool with free vars; the
//!    4th distinct name is an error (the smuni lowering cap; never merged).
//! 5. POSITION RULES: `it` only inside rel-clause bodies or as a named
//!    linked-arg marker; `slot` only inside `property { }` bodies.
//!
//! Tag (`via`) predicates additionally need arity ≥ 2, mirroring smuni's
//! fail-closed modal check (spec §5).

use std::collections::BTreeSet;

use crate::ast::{
    AbsKind, Arg, Claim, ClauseBody, KeyTerm, PredSeq, PredUnit, Restr, RestrKind, Statement, Term,
};
use crate::parser::{ParseError, err_at};

/// Resolve every statement; first (source-order) error fails closed.
pub fn resolve(input: &str, statements: &[Statement]) -> Result<(), ParseError> {
    match resolve_all(input, statements).into_iter().next() {
        None => Ok(()),
        Some(e) => Err(e),
    }
}

/// All resolve errors, in source order (per-statement recovery consumers).
pub fn resolve_all(input: &str, statements: &[Statement]) -> Vec<ParseError> {
    let mut errors = Vec::new();
    for statement in statements {
        let mut ctx = Ctx {
            input,
            statement_start: statement.span.start,
            vars: BTreeSet::new(),
            in_clause_body: false,
            in_property: false,
        };
        if let Err(e) = ctx.claim(&statement.claim) {
            errors.push(e);
        }
    }
    errors
}

/// A resolved predicate: its arity plus the alias entry when the name came
/// from the alias map (identity-passthrough gismu/lujvo have no entry — raw
/// `xN` labels only).
pub(crate) struct PredInfo {
    pub(crate) surface: String,
    pub(crate) arity: u8,
    pub(crate) entry: Option<&'static nibli_kr_dictionary::AliasEntry>,
}

pub(crate) fn lookup(word: &str) -> Result<PredInfo, String> {
    if let Some(entry) = nibli_kr_dictionary::alias(word) {
        return Ok(PredInfo {
            surface: word.to_owned(),
            arity: entry.arity,
            entry: Some(entry),
        });
    }
    if let Some(arity) = nibli_lexicon::get_arity(word) {
        return Ok(PredInfo {
            surface: word.to_owned(),
            arity: arity.clamp(1, 5) as u8,
            entry: None,
        });
    }
    Err(format!(
        "unknown predicate {word:?}: not a nibli KR alias and not a dictionary word — \
         unknown names are a compile error, never an arity-2 guess (NIBLI_KR §13)"
    ))
}

/// Resolve a named-argument label to a 0-based SURFACE place index.
pub(crate) fn label_index(info: &PredInfo, label: &str) -> Option<usize> {
    match info.entry {
        Some(entry) => nibli_kr_dictionary::label_index(entry, label),
        None => {
            // Identity passthrough: raw x1..x5 only.
            let rest = label.strip_prefix('x')?;
            if rest.len() != 1 {
                return None;
            }
            let d = rest.chars().next()?.to_digit(10)?;
            if (1..=5).contains(&d) && d as u8 <= info.arity {
                Some((d - 1) as usize)
            } else {
                None
            }
        }
    }
}

struct Ctx<'a> {
    input: &'a str,
    statement_start: usize,
    vars: BTreeSet<String>,
    in_clause_body: bool,
    in_property: bool,
}

impl<'a> Ctx<'a> {
    fn fail(&self, at: usize, message: impl Into<String>) -> ParseError {
        err_at(self.input, at, message)
    }

    fn var(&mut self, name: &str) -> Result<(), ParseError> {
        if self.vars.contains(name) {
            return Ok(());
        }
        if self.vars.len() >= 3 {
            return Err(self.fail(
                self.statement_start,
                format!(
                    "`${name}` is the 4th distinct variable in this statement — smuni \
                     currently lowers bare variables onto da/de/di (3 per statement); \
                     split the statement or reuse a variable (never silently merged)"
                ),
            ));
        }
        self.vars.insert(name.to_owned());
        Ok(())
    }

    /// Resolve every word of a pred_seq; return the HEAD's info (arity/name
    /// source — the last unit's last zei part, descending through groups).
    fn seq(&self, seq: &PredSeq, at: usize) -> Result<PredInfo, ParseError> {
        let mut head: Option<PredInfo> = None;
        for unit in &seq.0 {
            head = Some(self.unit(unit, at)?);
        }
        Ok(head.expect("pred_seq is non-empty"))
    }

    fn unit(&self, unit: &PredUnit, at: usize) -> Result<PredInfo, ParseError> {
        match unit {
            PredUnit::Word(parts) => {
                let mut info: Option<PredInfo> = None;
                for part in parts {
                    info = Some(lookup(part).map_err(|m| self.fail(at, m))?);
                }
                Ok(info.expect("pred_name is non-empty"))
            }
            PredUnit::Group(inner) => self.seq(inner, at),
        }
    }

    /// Ordinary argument list (main predications): positionals fill x1.. .
    fn args(&mut self, args: &[Arg], info: &PredInfo) -> Result<(), ParseError> {
        let mut filled = [false; 5];
        let mut next_positional = 0usize;
        for arg in args {
            let index = match &arg.label {
                None => {
                    let i = next_positional;
                    next_positional += 1;
                    if i >= info.arity as usize {
                        return Err(self.fail(
                            arg.span.start,
                            format!(
                                "too many arguments for {:?} (arity {})",
                                info.surface, info.arity
                            ),
                        ));
                    }
                    i
                }
                Some(label) => label_index(info, label).ok_or_else(|| {
                    self.fail(
                        arg.span.start,
                        format!(
                            "unknown place label {label:?} for {:?} (arity {}; dictionary \
                             labels or raw x1..x{} only)",
                            info.surface, info.arity, info.arity
                        ),
                    )
                })?,
            };
            if filled[index] {
                return Err(self.fail(
                    arg.span.start,
                    format!(
                        "place x{} of {:?} is filled twice (NIBLI_KR §5 fail-closed)",
                        index + 1,
                        info.surface
                    ),
                ));
            }
            filled[index] = true;
            self.term(&arg.term)?;
        }
        Ok(())
    }

    /// Restrictor linked args (be/bei): positionals fill x2.. — the bound
    /// variable takes x1 — and a NAMED `it` marks the bound place instead.
    fn linked_args(&mut self, args: &[Arg], info: &PredInfo, at: usize) -> Result<(), ParseError> {
        let mut filled = [false; 5];
        let mut it_place: Option<usize> = None;
        let mut next_positional = 1usize; // x2 onward
        for arg in args {
            let is_it = matches!(arg.term, Term::Key(KeyTerm::It));
            let index = match &arg.label {
                None => {
                    if is_it {
                        return Err(self.fail(
                            arg.span.start,
                            "mark the bound place with a NAMED `it` (e.g. `x2: it` or \
                             `loved: it`) — a positional `it` is ambiguous",
                        ));
                    }
                    let i = next_positional;
                    next_positional += 1;
                    if i >= info.arity as usize {
                        return Err(self.fail(
                            arg.span.start,
                            format!(
                                "too many linked arguments for {:?} (arity {}; positional \
                                 links fill x2 onward — the bound variable takes x1)",
                                info.surface, info.arity
                            ),
                        ));
                    }
                    i
                }
                Some(label) => label_index(info, label).ok_or_else(|| {
                    self.fail(
                        arg.span.start,
                        format!(
                            "unknown place label {label:?} for {:?} (arity {})",
                            info.surface, info.arity
                        ),
                    )
                })?,
            };
            if filled[index] {
                return Err(self.fail(
                    arg.span.start,
                    format!("place x{} of {:?} is filled twice", index + 1, info.surface),
                ));
            }
            filled[index] = true;
            if is_it {
                if it_place.is_some() {
                    return Err(self.fail(
                        arg.span.start,
                        "at most one `it` may mark the bound place of a restrictor",
                    ));
                }
                it_place = Some(index);
            } else {
                self.term(&arg.term)?;
            }
        }
        if it_place.is_none() && filled[0] {
            return Err(self.fail(
                at,
                "these linked arguments fill x1, but the bound variable needs it — mark \
                 the bound place explicitly with `it` (e.g. `x2: it`)",
            ));
        }
        Ok(())
    }

    fn claim(&mut self, claim: &Claim) -> Result<(), ParseError> {
        match claim {
            Claim::Prenex { vars, body } => {
                for v in vars {
                    self.var(v)?;
                }
                self.claim(body)
            }
            Claim::DetBlock {
                restr, var, body, ..
            } => {
                self.restr(restr)?;
                self.var(var)?;
                self.claim(body)
            }
            Claim::Impl(a, b)
            | Claim::Iff(a, b)
            | Claim::Xor(a, b)
            | Claim::Or(a, b)
            | Claim::And(a, b) => {
                self.claim(a)?;
                self.claim(b)
            }
            Claim::Not(a) | Claim::Prefixed { atom: a, .. } => self.claim(a),
            Claim::Equality(a, b) => {
                self.term(a)?;
                self.term(b)
            }
            Claim::Predication(p) => {
                let info = self.seq(&p.seq, p.span.start)?;
                self.args(&p.args, &info)?;
                for tag in &p.tags {
                    let mut tag_info: Option<PredInfo> = None;
                    for part in &tag.pred {
                        tag_info = Some(lookup(part).map_err(|m| self.fail(tag.span.start, m))?);
                    }
                    let tag_info = tag_info.expect("tag pred is non-empty");
                    if tag_info.arity < 2 {
                        return Err(self.fail(
                            tag.span.start,
                            format!(
                                "modal tag predicate {:?} has arity {} — `via` predicates \
                                 need arity >= 2 to link the tagged term (NIBLI_KR §5)",
                                tag_info.surface, tag_info.arity
                            ),
                        ));
                    }
                    self.term(&tag.term)?;
                }
                Ok(())
            }
        }
    }

    fn term(&mut self, term: &Term) -> Result<(), ParseError> {
        match term {
            Term::Key(KeyTerm::It) => {
                if self.in_clause_body {
                    Ok(())
                } else {
                    Err(self.fail(
                        self.statement_start,
                        "`it` (the relativized entity) is only meaningful inside a \
                         where/also clause body, or as a named bound-place marker in \
                         restrictor linked args (NIBLI_KR §7)",
                    ))
                }
            }
            Term::Key(KeyTerm::Slot) => {
                if self.in_property {
                    Ok(())
                } else {
                    Err(self.fail(
                        self.statement_start,
                        "`slot` (the open place) is only meaningful inside a \
                         `property { … }` body (NIBLI_KR §3 — like ce'u outside ka)",
                    ))
                }
            }
            Term::Var(v) => self.var(v),
            Term::Name { rel_clauses, .. } => {
                for rc in rel_clauses {
                    self.rel_clause(rc)?;
                }
                Ok(())
            }
            Term::Abstraction { kind, body } => {
                let saved = self.in_property;
                if *kind == AbsKind::Property {
                    self.in_property = true;
                }
                let result = self.claim(body);
                self.in_property = saved;
                result
            }
            Term::Det { restr, .. } => self.restr(restr),
            Term::Unspecified | Term::Witness | Term::Number(_) | Term::Str(_) | Term::Key(_) => {
                Ok(())
            }
        }
    }

    fn restr(&mut self, restr: &Restr) -> Result<(), ParseError> {
        match &restr.kind {
            RestrKind::Seq { seq, linked_args } => {
                let info = self.seq(seq, restr.span.start)?;
                if !linked_args.is_empty() {
                    self.linked_args(linked_args, &info, restr.span.start)?;
                }
            }
            RestrKind::Selected { pred, label } => {
                let info = lookup(pred).map_err(|m| self.fail(restr.span.start, m))?;
                if label_index(&info, label).is_none() {
                    return Err(self.fail(
                        restr.span.start,
                        format!(
                            "unknown selector place {label:?} for {pred:?} (arity {}; \
                             dictionary labels or raw x1..x{} only)",
                            info.arity, info.arity
                        ),
                    ));
                }
            }
        }
        for rc in &restr.rel_clauses {
            self.rel_clause(rc)?;
        }
        Ok(())
    }

    fn rel_clause(&mut self, rc: &crate::ast::RelClause) -> Result<(), ParseError> {
        match &rc.body {
            ClauseBody::Bare { seq, .. } => {
                self.seq(seq, rc.span.start)?;
                Ok(())
            }
            ClauseBody::Full(claim) => {
                let saved = self.in_clause_body;
                self.in_clause_body = true;
                let result = self.claim(claim);
                self.in_clause_body = saved;
                result
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_statements;

    // FALLBACK-SAFE VOCABULARY ONLY: CI builds without dictionary-en.json, so
    // every word here must come from nibli-kr-dictionary's curated tables or
    // nibli-lexicon's fallback core (identity passthrough).

    fn ok(input: &str) {
        let statements = parse_statements(input).unwrap_or_else(|e| panic!("parse {input:?}: {e}"));
        if let Err(e) = resolve(input, &statements) {
            panic!("resolve failed for {input:?}: {e}");
        }
    }

    fn bad(input: &str) -> ParseError {
        let statements = parse_statements(input).unwrap_or_else(|e| panic!("parse {input:?}: {e}"));
        match resolve(input, &statements) {
            Ok(()) => panic!("expected resolve error for {input:?}"),
            Err(e) => e,
        }
    }

    #[test]
    fn aliases_and_identity_passthrough() {
        ok("goes(me, destination: some market).");
        ok("animal(every dog).");
        // Lojban words pass through with smuni's arity.
        ok("klama(me, x2: some market).");
        // Converted aliases resolve.
        ok("obligated(every data, x2: this).");
    }

    #[test]
    fn unknown_names_fail_closed() {
        let e = bad("zzq(me).");
        assert!(e.message.contains("unknown predicate"), "{e}");
        let e = bad("goes(every zzq dog).");
        assert!(e.message.contains("unknown predicate"), "{e}");
        let e = bad("goes(some dog where zzq).");
        assert!(e.message.contains("unknown predicate"), "{e}");
    }

    #[test]
    fn place_checks() {
        // gerku is 2-place: 3 positionals overflow.
        let e = bad("dog(Adam, you, me).");
        assert!(e.message.contains("too many arguments"), "{e}");
        let e = bad("goes(me, zzlabel: you).");
        assert!(e.message.contains("unknown place label"), "{e}");
        let e = bad("goes(me, x1: you).");
        assert!(e.message.contains("filled twice"), "{e}");
        // Raw labels are arity-bounded.
        let e = bad("dog(Adam, x3: you).");
        assert!(e.message.contains("unknown place label"), "{e}");
        // Dictionary labels work: goer/destination on klama via the alias.
        ok("goes(goer: me, destination: some market).");
    }

    #[test]
    fn selector_places() {
        // loved = prami x2 label.
        ok("permitted(every loves.loved).");
        ok("permitted(every loves.x2).");
        let e = bad("permitted(every loves.zzplace).");
        assert!(e.message.contains("unknown selector place"), "{e}");
    }

    #[test]
    fn linked_args_and_the_bound_place() {
        // Positional links fill x2.. (bound var takes x1): tends = kurji
        // [carer, charge].
        ok("permitted(every tends(some data)).");
        ok("permitted(every tends(charge: some data)).");
        // Named `it` moves the bound place.
        ok("goes(every loves(x2: it)).");
        ok("goes(every loves(loved: it)).");
        // x1 filled with no `it` marker: the bound variable has nowhere to go.
        let e = bad("goes(every loves(x1: you)).");
        assert!(e.message.contains("bound variable needs it"), "{e}");
        // Positional `it` is ambiguous; two `it`s are worse.
        let e = bad("goes(every loves(it)).");
        assert!(e.message.contains("NAMED `it`"), "{e}");
        let e = bad("goes(every loves(x1: it, x2: it)).");
        assert!(e.message.contains("at most one `it`"), "{e}");
    }

    #[test]
    fn variable_cap() {
        ok("all $x, $y, $z: loves($x, $y) & dog($z).");
        let e = bad("dog($a) & dog($b) & dog($c) & dog($d).");
        assert!(e.message.contains("4th distinct variable"), "{e}");
        assert!(e.message.contains("$d"), "{e}");
        // Bound binders share the pool with free vars.
        let e = bad("all $x, $y, $z: loves($x, $w).");
        assert!(e.message.contains("4th distinct variable"), "{e}");
    }

    #[test]
    fn it_and_slot_positions() {
        let e = bad("goes(it).");
        assert!(e.message.contains("where/also clause body"), "{e}");
        let e = bad("goes(slot).");
        assert!(e.message.contains("property"), "{e}");
        ok("able(me, property { fast(slot) }).");
        // `slot` in a non-property abstraction is still an error.
        let e = bad("desires(me, event { fast(slot) }).");
        assert!(e.message.contains("property"), "{e}");
        // `it` in a clause body is fine, incl. through an abstraction.
        ok("goes(some dog where big(it)).");
        ok("goes(some dog where desires(me, event { eats(it) })).");
    }

    #[test]
    fn tag_predicates() {
        ok("goes(me) via uses(this).");
        ok("goes(me) via reason(this) via entails(this).");
        // person is 1-place — cannot link a tagged term.
        let e = bad("goes(me) via person(this).");
        assert!(e.message.contains("arity >= 2"), "{e}");
        let e = bad("goes(me) via zzq(this).");
        assert!(e.message.contains("unknown predicate"), "{e}");
    }

    #[test]
    fn bare_clause_bodies_resolve() {
        ok("goes(every person where approves).");
        ok("goes(every chemical where increases where thin).");
        // Tanru in restr and clause bodies resolve every unit.
        ok("goes(every healthy data).");
        let e = bad("goes(every person where zzq big).");
        assert!(e.message.contains("unknown predicate"), "{e}");
    }
}
