//! nibli KR parser: pest-generated from `src/nibli_kr.pest` (THE executable grammar
//! — NIBLI_KR §15, full v0.1 surface), plus the walker that builds the
//! tree AST ([`crate::ast`]) and enforces the §6/§7 errata as targeted,
//! positioned errors.
//!
//! Division of labor:
//! - `nibli_kr.pest` owns SYNTAX. It parses modifiers permissively and knows
//!   nothing about the errata, argument ordering, count integrality, or the
//!   mandatory-`it` rule — encoding those as grammar would bury the spec
//!   guidance under generic "expected …" messages.
//! - The walker (this file) owns the FAIL-CLOSED PARSE-TIME SHAPE: ≤1 deontic,
//!   ≤1 tense, deontic-before-tense, `~` innermost and single, prefixes/`~`
//!   only over a single predication/equality, positionals-before-named,
//!   `exactly N` integrality and u32 range, number finiteness, string
//!   unescaping, and mandatory-`it` in full-claim clause bodies.
//! - Dictionary-driven checks (name resolution, place checks, variable cap,
//!   `it`/`slot` position) live in [`crate::resolve`].
//!
//! Error recovery is per-statement, like gerna: `parse_text_with_errors`
//! parses statement-by-statement, and on an error skips (string/comment-aware)
//! past the next `.` so later statements still parse.

use std::fmt;

use pest::Parser as _;
use pest::iterators::Pair;

use crate::ast::{
    AbsKind, Arg, Claim, ClauseBody, Deontic, Det, KeyTerm, PredSeq, PredUnit, Predication,
    RelClause, RelKind, Restr, RestrKind, Statement, Tag, Tense, Term,
};

#[derive(pest_derive::Parser)]
#[grammar = "nibli_kr.pest"]
struct NibliKrPest;

/// A positioned parse error. 1-based line/column; columns count CHARACTERS.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub line: u32,
    pub column: u32,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} (line {}, column {})",
            self.message, self.line, self.column
        )
    }
}

/// 1-based (line, column) of a byte offset; columns count characters.
pub fn line_col(input: &str, offset: usize) -> (u32, u32) {
    let prefix = &input[..offset.min(input.len())];
    let line = prefix.bytes().filter(|&b| b == b'\n').count() as u32 + 1;
    let column = match prefix.rfind('\n') {
        Some(nl) => prefix[nl + 1..].chars().count() as u32 + 1,
        None => prefix.chars().count() as u32 + 1,
    };
    (line, column)
}

pub(crate) fn err_at(input: &str, offset: usize, message: impl Into<String>) -> ParseError {
    let (line, column) = line_col(input, offset);
    ParseError {
        message: message.into(),
        line,
        column,
    }
}

/// Parse a whole input with PER-STATEMENT error recovery. Errors come back in
/// source order.
pub fn parse_text_with_errors(input: &str) -> (Vec<Statement>, Vec<ParseError>) {
    let mut statements = Vec::new();
    let mut errors = Vec::new();
    let mut pos = 0usize;

    loop {
        pos = skip_trivia(input, pos);
        if pos >= input.len() {
            break;
        }
        match NibliKrPest::parse(Rule::statement, &input[pos..]) {
            Ok(mut pairs) => {
                let pair = pairs.next().expect("statement rule yields one pair");
                let end = pos + pair.as_span().end();
                match build_statement(pair, input, pos) {
                    Ok(statement) => statements.push(statement),
                    Err(e) => {
                        // The statement PARSED (the walker rejected it) —
                        // resume after its terminating dot.
                        errors.push(e);
                    }
                }
                pos = end;
            }
            Err(e) => {
                errors.push(convert_pest_error(e, input, pos));
                pos = skip_past_dot(input, pos);
            }
        }
    }
    (statements, errors)
}

/// FAIL CLOSED: statements, or the first (source-order) error.
pub fn parse_statements(input: &str) -> Result<Vec<Statement>, ParseError> {
    let (statements, errors) = parse_text_with_errors(input);
    match errors.into_iter().next() {
        None => Ok(statements),
        Some(e) => Err(e),
    }
}

// ── trivia / recovery scanners (used only between statement parses) ──

/// Skip whitespace and comments. An UNTERMINATED `/*` is deliberately not
/// skipped — it is left in place so the statement parse fails on it (fail
/// closed, never silently swallowed).
fn skip_trivia(input: &str, mut pos: usize) -> usize {
    let bytes = input.as_bytes();
    loop {
        while pos < bytes.len() && matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
            pos += 1;
        }
        if bytes[pos..].starts_with(b"#") {
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }
        if bytes[pos..].starts_with(b"/*") {
            match input[pos + 2..].find("*/") {
                Some(close) => {
                    pos = pos + 2 + close + 2;
                    continue;
                }
                None => return pos, // unterminated — let the parser report it
            }
        }
        return pos;
    }
}

/// Recovery: advance past the next statement-terminating `.` (skipping dots
/// inside strings and comments). Always makes progress when input remains.
fn skip_past_dot(input: &str, mut pos: usize) -> usize {
    let bytes = input.as_bytes();
    while pos < bytes.len() {
        match bytes[pos] {
            b'.' => return pos + 1,
            b'"' => {
                pos += 1;
                while pos < bytes.len() && bytes[pos] != b'"' && bytes[pos] != b'\n' {
                    if bytes[pos] == b'\\' {
                        pos += 1;
                    }
                    pos += 1;
                }
                pos += 1;
            }
            b'#' => {
                while pos < bytes.len() && bytes[pos] != b'\n' {
                    pos += 1;
                }
            }
            b'/' if bytes[pos..].starts_with(b"/*") => match input[pos + 2..].find("*/") {
                Some(close) => pos = pos + 2 + close + 2,
                None => return input.len(),
            },
            _ => pos += 1,
        }
    }
    input.len()
}

// ── pest-error conversion ──

fn convert_pest_error(e: pest::error::Error<Rule>, input: &str, base: usize) -> ParseError {
    let slice_offset = match e.location {
        pest::error::InputLocation::Pos(p) => p,
        pest::error::InputLocation::Span((s, _)) => s,
    };
    let e = e.renamed_rules(|rule| {
        match rule {
            Rule::args => "an argument list `( … )`",
            Rule::arg => "an argument",
            Rule::term => "a term",
            Rule::claim
            | Rule::prenex
            | Rule::det_block
            | Rule::block_det
            | Rule::impl_chain
            | Rule::iff_chain
            | Rule::xor_chain
            | Rule::or_chain
            | Rule::and_chain
            | Rule::unary
            | Rule::atom => "a claim",
            Rule::predication => "a predication",
            Rule::equality => "an equality `a = b`",
            Rule::ident | Rule::pred_seq | Rule::pred_unit | Rule::pred_name => "a predicate word",
            Rule::label => "an argument label",
            Rule::statement => "a statement",
            Rule::det | Rule::det_phrase => "a determiner phrase",
            Rule::restr => "a restrictor predicate",
            Rule::selected => "a place selector",
            Rule::rel_cl | Rule::clause_body => "a relative clause",
            Rule::abstraction | Rule::abs_kind => "an abstraction `kind { … }`",
            Rule::rigid | Rule::name => "a Name",
            Rule::tag => "a `via` tag",
            Rule::number => "a number",
            Rule::string => "a string",
            Rule::var => "a `$variable`",
            Rule::keyterm => "a pro-term",
            Rule::paren => "`( claim )`",
            Rule::modifier | Rule::tilde => "a prefix",
            Rule::EOI => "end of input",
            other => return format!("{other:?}"),
        }
        .to_owned()
    });
    let offset = base + slice_offset;
    let (line, column) = line_col(input, offset);
    ParseError {
        message: e.variant.message().into_owned(),
        line,
        column,
    }
}

// ── the walker ──

fn build_statement(pair: Pair<Rule>, input: &str, base: usize) -> Result<Statement, ParseError> {
    let span = pair.as_span();
    let claim_pair = pair
        .into_inner()
        .find(|p| p.as_rule() == Rule::claim)
        .expect("statement contains a claim");
    Ok(Statement {
        claim: build_claim(claim_pair, input, base)?,
        span: base + span.start()..base + span.end(),
    })
}

/// claim = prenex | det_block | impl_chain
fn build_claim(pair: Pair<Rule>, input: &str, base: usize) -> Result<Claim, ParseError> {
    let inner = pair.into_inner().next().expect("claim inner");
    match inner.as_rule() {
        Rule::prenex => build_prenex(inner, input, base),
        Rule::det_block => build_det_block(inner, input, base),
        Rule::impl_chain => build_impl_chain(inner, input, base),
        other => unreachable!("claim inner: {other:?}"),
    }
}

fn build_prenex(pair: Pair<Rule>, input: &str, base: usize) -> Result<Claim, ParseError> {
    let mut vars = Vec::new();
    let mut body = None;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::kw_all => {}
            Rule::var => vars.push(child.as_str()[1..].to_owned()),
            Rule::claim => body = Some(build_claim(child, input, base)?),
            other => unreachable!("prenex child: {other:?}"),
        }
    }
    Ok(Claim::Prenex {
        vars,
        body: Box::new(body.expect("prenex has a body")),
    })
}

fn build_det_block(pair: Pair<Rule>, input: &str, base: usize) -> Result<Claim, ParseError> {
    let mut inner = pair.into_inner();
    let det = build_det(inner.next().expect("block_det"), input, base)?;
    let restr = build_restr(inner.next().expect("det_block restr"), input, base)?;
    let var_pair = inner.next().expect("det_block var");
    let var = var_pair.as_str()[1..].to_owned();
    let body_pair = inner
        .find(|p| p.as_rule() == Rule::claim)
        .expect("det_block body");
    Ok(Claim::DetBlock {
        det,
        restr,
        var,
        body: Box::new(build_claim(body_pair, input, base)?),
    })
}

/// impl_chain = iff_chain ~ (op_impl ~ impl_chain)?   (right-assoc)
fn build_impl_chain(pair: Pair<Rule>, input: &str, base: usize) -> Result<Claim, ParseError> {
    let mut inner = pair.into_inner();
    let lhs = build_chain(inner.next().expect("iff_chain"), input, base)?;
    match inner.find(|p| p.as_rule() == Rule::impl_chain) {
        Some(rhs) => Ok(Claim::Impl(
            Box::new(lhs),
            Box::new(build_impl_chain(rhs, input, base)?),
        )),
        None => Ok(lhs),
    }
}

/// Left-fold the `<->` / `^` / `|` / `&` chains.
fn build_chain(pair: Pair<Rule>, input: &str, base: usize) -> Result<Claim, ParseError> {
    let rule = pair.as_rule();
    if rule == Rule::unary {
        return build_unary(pair, input, base);
    }
    let mut acc: Option<Claim> = None;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::op_iff | Rule::op_xor | Rule::op_or | Rule::op_and => {}
            _ => {
                let operand = build_chain(child, input, base)?;
                acc = Some(match acc {
                    None => operand,
                    Some(lhs) => match rule {
                        Rule::iff_chain => Claim::Iff(Box::new(lhs), Box::new(operand)),
                        Rule::xor_chain => Claim::Xor(Box::new(lhs), Box::new(operand)),
                        Rule::or_chain => Claim::Or(Box::new(lhs), Box::new(operand)),
                        Rule::and_chain => Claim::And(Box::new(lhs), Box::new(operand)),
                        other => unreachable!("not a chain rule: {other:?}"),
                    },
                });
            }
        }
    }
    Ok(acc.expect("chain has at least one operand"))
}

/// unary = modifier* ~ atom — the walker enforces the §6 errata shape.
fn build_unary(pair: Pair<Rule>, input: &str, base: usize) -> Result<Claim, ParseError> {
    const NOT_OVER_PREFIX: &str = "`~` over a tense/deontic prefix is rejected — Not(Past(P)) has no encoding in the \
         compat profile; `past ~P` (= Past(Not(P))) is the supported spelling \
         (NIBLI_KR §6 errata)";

    let mut deontic: Option<Deontic> = None;
    let mut tense: Option<Tense> = None;
    let mut negated = false;
    let mut atom_pair: Option<Pair<Rule>> = None;

    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::modifier => {
                let m = child.into_inner().next().expect("modifier inner");
                let at = base + m.as_span().start();
                match m.as_rule() {
                    Rule::kw_must | Rule::kw_may => {
                        if negated {
                            return Err(err_at(input, at, NOT_OVER_PREFIX));
                        }
                        if tense.is_some() {
                            return Err(err_at(
                                input,
                                at,
                                "deontic comes before tense: write `must past P`, never \
                                 `past must P` (nesting is Obligatory(Past(…)), \
                                 NIBLI_KR §6)",
                            ));
                        }
                        if deontic.is_some() {
                            return Err(err_at(input, at, "duplicate deontic prefix"));
                        }
                        deontic = Some(if m.as_rule() == Rule::kw_must {
                            Deontic::Must
                        } else {
                            Deontic::May
                        });
                    }
                    Rule::kw_past | Rule::kw_now | Rule::kw_future => {
                        if negated {
                            return Err(err_at(input, at, NOT_OVER_PREFIX));
                        }
                        if tense.is_some() {
                            return Err(err_at(input, at, "duplicate tense prefix"));
                        }
                        tense = Some(match m.as_rule() {
                            Rule::kw_past => Tense::Past,
                            Rule::kw_now => Tense::Now,
                            _ => Tense::Future,
                        });
                    }
                    Rule::tilde => {
                        if negated {
                            return Err(err_at(
                                input,
                                at,
                                "double negation `~~` has no encoding (bridi-level negation \
                                 is a single flag) — drop both, or restate the claim",
                            ));
                        }
                        negated = true;
                    }
                    other => unreachable!("modifier inner: {other:?}"),
                }
            }
            Rule::atom => atom_pair = Some(child),
            other => unreachable!("unary child: {other:?}"),
        }
    }

    let atom_pair = atom_pair.expect("unary has an atom");
    let restricted = deontic.is_some() || tense.is_some() || negated;
    let atom = build_atom(atom_pair, input, base, restricted)?;

    let body = if negated {
        Claim::Not(Box::new(atom))
    } else {
        atom
    };
    if deontic.is_some() || tense.is_some() {
        Ok(Claim::Prefixed {
            deontic,
            tense,
            atom: Box::new(body),
        })
    } else {
        Ok(body)
    }
}

fn build_atom(
    pair: Pair<Rule>,
    input: &str,
    base: usize,
    restricted: bool,
) -> Result<Claim, ParseError> {
    let inner = pair.into_inner().next().expect("atom inner");
    match inner.as_rule() {
        Rule::paren => {
            let paren_at = base + inner.as_span().start();
            let claim_pair = inner
                .into_inner()
                .find(|p| p.as_rule() == Rule::claim)
                .expect("paren contains a claim");
            let built = build_claim(claim_pair, input, base)?;
            if restricted && !matches!(built, Claim::Predication(_) | Claim::Equality(..)) {
                return Err(err_at(
                    input,
                    paren_at,
                    "tense/deontic prefixes and `~` attach to a single predication or \
                     equality — not to a compound claim; distribute explicitly \
                     (NIBLI_KR §6 errata)",
                ));
            }
            Ok(built)
        }
        Rule::predication => Ok(Claim::Predication(build_predication(inner, input, base)?)),
        Rule::equality => {
            let mut terms = inner.into_inner();
            let lhs = build_term(terms.next().expect("lhs term"), input, base)?;
            let rhs = build_term(terms.next().expect("rhs term"), input, base)?;
            Ok(Claim::Equality(lhs, rhs))
        }
        other => unreachable!("atom inner: {other:?}"),
    }
}

fn build_predication(
    pair: Pair<Rule>,
    input: &str,
    base: usize,
) -> Result<Predication, ParseError> {
    let span = pair.as_span();
    let mut seq = None;
    let mut args = Vec::new();
    let mut tags = Vec::new();
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::pred_seq => seq = Some(build_pred_seq(child)),
            Rule::args => args = build_args(child, input, base)?,
            Rule::tag => tags.push(build_tag(child, input, base)?),
            other => unreachable!("predication child: {other:?}"),
        }
    }
    Ok(Predication {
        seq: seq.expect("predication has a pred_seq"),
        args,
        tags,
        span: base + span.start()..base + span.end(),
    })
}

fn build_pred_seq(pair: Pair<Rule>) -> PredSeq {
    let units = pair
        .into_inner()
        .map(|unit| {
            let inner = unit.into_inner().next().expect("pred_unit inner");
            match inner.as_rule() {
                Rule::pred_seq => PredUnit::Group(build_pred_seq(inner)),
                Rule::pred_name => PredUnit::Word(pred_name_parts(inner)),
                other => unreachable!("pred_unit inner: {other:?}"),
            }
        })
        .collect();
    PredSeq(units)
}

fn pred_name_parts(pair: Pair<Rule>) -> Vec<String> {
    pair.into_inner().map(|p| p.as_str().to_owned()).collect()
}

fn build_tag(pair: Pair<Rule>, input: &str, base: usize) -> Result<Tag, ParseError> {
    let span = pair.as_span();
    let mut pred = Vec::new();
    let mut term = None;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::kw_via => {}
            Rule::pred_name => pred = pred_name_parts(child),
            Rule::term => term = Some(build_term(child, input, base)?),
            other => unreachable!("tag child: {other:?}"),
        }
    }
    Ok(Tag {
        pred,
        term: term.expect("tag has a term"),
        span: base + span.start()..base + span.end(),
    })
}

/// Shared by predication args and restr linked args: positionals must precede
/// named args (NIBLI_KR §5).
fn build_args(pair: Pair<Rule>, input: &str, base: usize) -> Result<Vec<Arg>, ParseError> {
    let mut args: Vec<Arg> = Vec::new();
    let mut seen_named = false;
    for arg_pair in pair.into_inner() {
        debug_assert_eq!(arg_pair.as_rule(), Rule::arg);
        let arg_span = arg_pair.as_span();
        let arg_at = base + arg_span.start();
        let mut label: Option<String> = None;
        let mut term: Option<Term> = None;
        for part in arg_pair.into_inner() {
            match part.as_rule() {
                Rule::label => label = Some(part.as_str().to_owned()),
                Rule::term => term = Some(build_term(part, input, base)?),
                other => unreachable!("arg part: {other:?}"),
            }
        }
        if label.is_some() {
            seen_named = true;
        } else if seen_named {
            return Err(err_at(
                input,
                arg_at,
                "positional arguments must come before named arguments (NIBLI_KR §5)",
            ));
        }
        args.push(Arg {
            label,
            term: term.expect("arg has a term"),
            span: base + arg_span.start()..base + arg_span.end(),
        });
    }
    Ok(args)
}

fn build_term(pair: Pair<Rule>, input: &str, base: usize) -> Result<Term, ParseError> {
    let inner = pair.into_inner().next().expect("term inner");
    let at = base + inner.as_span().start();
    match inner.as_rule() {
        Rule::underscore => Ok(Term::Unspecified),
        Rule::question => Ok(Term::Witness),
        Rule::number => {
            let value: f64 = inner
                .as_str()
                .parse()
                .map_err(|_| err_at(input, at, "number literal does not parse as a float"))?;
            if !value.is_finite() {
                return Err(err_at(
                    input,
                    at,
                    "number literal overflows the representable range (non-finite) — \
                     fail closed per NIBLI_KR §3",
                ));
            }
            Ok(Term::Number(value))
        }
        Rule::string => Ok(Term::Str(unescape(inner.as_str()))),
        Rule::var => Ok(Term::Var(inner.as_str()[1..].to_owned())),
        Rule::rigid => {
            let mut kids = inner.into_inner();
            let name = kids.next().expect("rigid name").as_str().to_owned();
            let mut rel_clauses = Vec::new();
            for rel in kids {
                rel_clauses.push(build_rel_cl(rel, input, base)?);
            }
            Ok(Term::Name { name, rel_clauses })
        }
        Rule::abstraction => {
            let mut kids = inner.into_inner();
            let kind_pair = kids.next().expect("abs_kind");
            let kind = match kind_pair.into_inner().next().expect("abs kw").as_rule() {
                Rule::kw_event => AbsKind::Event,
                Rule::kw_fact => AbsKind::Fact,
                Rule::kw_property => AbsKind::Property,
                Rule::kw_amount => AbsKind::Amount,
                Rule::kw_concept => AbsKind::Concept,
                other => unreachable!("abs_kind inner: {other:?}"),
            };
            let body_pair = kids
                .find(|p| p.as_rule() == Rule::claim)
                .expect("abstraction body");
            Ok(Term::Abstraction {
                kind,
                body: Box::new(build_claim(body_pair, input, base)?),
            })
        }
        Rule::keyterm => {
            let kw = inner.into_inner().next().expect("keyterm inner");
            Ok(Term::Key(match kw.as_rule() {
                Rule::kw_me => KeyTerm::Me,
                Rule::kw_you => KeyTerm::You,
                Rule::kw_we => KeyTerm::We,
                Rule::kw_we_all => KeyTerm::WeAll,
                Rule::kw_we_others => KeyTerm::WeOthers,
                Rule::kw_you_all => KeyTerm::YouAll,
                Rule::kw_this => KeyTerm::This,
                Rule::kw_that => KeyTerm::That,
                Rule::kw_yonder => KeyTerm::Yonder,
                Rule::kw_it_a => KeyTerm::ItA,
                Rule::kw_it_e => KeyTerm::ItE,
                Rule::kw_it_i => KeyTerm::ItI,
                Rule::kw_it_o => KeyTerm::ItO,
                Rule::kw_it_u => KeyTerm::ItU,
                Rule::kw_it => KeyTerm::It,
                Rule::kw_slot => KeyTerm::Slot,
                other => unreachable!("keyterm inner: {other:?}"),
            }))
        }
        Rule::det_phrase => build_det_phrase(inner, input, base),
        other => unreachable!("term inner: {other:?}"),
    }
}

fn build_det_phrase(pair: Pair<Rule>, input: &str, base: usize) -> Result<Term, ParseError> {
    let mut inner = pair.into_inner();
    let det = build_det(inner.next().expect("det"), input, base)?;
    let restr = build_restr(inner.next().expect("restr"), input, base)?;
    Ok(Term::Det { det, restr })
}

/// Shared by `det` (term position) and `block_det` (statement position) —
/// identical child shapes. `no X` folds to `exactly 0 X` here (spec §4 sugar).
fn build_det(pair: Pair<Rule>, input: &str, base: usize) -> Result<Det, ParseError> {
    let mut kids = pair.into_inner().peekable();
    let head = kids.next().expect("det head");
    Ok(match head.as_rule() {
        Rule::kw_some => Det::Some,
        Rule::kw_the => Det::The,
        Rule::kw_no => Det::Exactly(0),
        Rule::kw_every => {
            if kids.peek().is_some() {
                Det::EveryThe
            } else {
                Det::Every
            }
        }
        Rule::kw_exactly => {
            let number = kids.next().expect("exactly count");
            let at = base + number.as_span().start();
            let slice = number.as_str();
            if slice.contains('.') {
                return Err(err_at(
                    input,
                    at,
                    format!("`exactly` needs a whole number of things, found `{slice}`"),
                ));
            }
            let n: u32 = slice.parse().map_err(|_| {
                err_at(
                    input,
                    at,
                    format!(
                        "exact count `{slice}` exceeds the supported range (0..={})",
                        u32::MAX
                    ),
                )
            })?;
            if kids.peek().is_some() {
                Det::ExactlyThe(n)
            } else {
                Det::Exactly(n)
            }
        }
        other => unreachable!("det head: {other:?}"),
    })
}

fn build_restr(pair: Pair<Rule>, input: &str, base: usize) -> Result<Restr, ParseError> {
    let span = pair.as_span();
    let mut negated = false;
    let mut kind: Option<RestrKind> = None;
    let mut linked_args = Vec::new();
    let mut rel_clauses = Vec::new();
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::tilde => negated = true,
            Rule::selected => {
                let mut idents = child.into_inner();
                let pred = idents.next().expect("selected pred").as_str().to_owned();
                let label = idents.next().expect("selected label").as_str().to_owned();
                kind = Some(RestrKind::Selected { pred, label });
            }
            Rule::pred_seq => {
                kind = Some(RestrKind::Seq {
                    seq: build_pred_seq(child),
                    linked_args: Vec::new(),
                });
            }
            Rule::args => linked_args = build_args(child, input, base)?,
            Rule::rel_cl => rel_clauses.push(build_rel_cl(child, input, base)?),
            other => unreachable!("restr child: {other:?}"),
        }
    }
    let kind = match kind.expect("restr has a kind") {
        RestrKind::Seq { seq, .. } => RestrKind::Seq { seq, linked_args },
        selected => selected, // grammar guarantees no args on the selected branch
    };
    Ok(Restr {
        negated,
        kind,
        rel_clauses,
        span: base + span.start()..base + span.end(),
    })
}

fn build_rel_cl(pair: Pair<Rule>, input: &str, base: usize) -> Result<RelClause, ParseError> {
    let span = pair.as_span();
    let clause_at = base + span.start();
    let mut kind = RelKind::Where;
    let mut body: Option<ClauseBody> = None;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::kw_where => kind = RelKind::Where,
            Rule::kw_also => kind = RelKind::Also,
            Rule::clause_body => body = Some(build_clause_body(child, input, base, clause_at)?),
            other => unreachable!("rel_cl child: {other:?}"),
        }
    }
    Ok(RelClause {
        kind,
        body: body.expect("rel_cl has a body"),
        span: base + span.start()..base + span.end(),
    })
}

fn build_clause_body(
    pair: Pair<Rule>,
    input: &str,
    base: usize,
    clause_at: usize,
) -> Result<ClauseBody, ParseError> {
    let mut negated = false;
    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::claim => {
                let claim = build_claim(child, input, base)?;
                // Mandatory-`it` (NIBLI_KR §7): a full-claim body that
                // never mentions the relativized entity is the implicit-ke'a
                // ambiguity the firewall exists to prevent.
                if !claim_contains_it(&claim) {
                    return Err(err_at(
                        input,
                        clause_at,
                        "a full relative-clause body must mention `it` (the relativized \
                         entity) at least once — bare `where pred` is the sugar for \
                         pred(it) (NIBLI_KR §7 mandatory-it)",
                    ));
                }
                return Ok(ClauseBody::Full(Box::new(claim)));
            }
            Rule::tilde => negated = true,
            Rule::pred_seq => {
                return Ok(ClauseBody::Bare {
                    negated,
                    seq: build_pred_seq(child),
                });
            }
            other => unreachable!("clause_body child: {other:?}"),
        }
    }
    unreachable!("clause_body has a body")
}

/// Does the claim mention `it`, NOT counting nested relative-clause bodies
/// (those own their `it`s — innermost binding, like ke'a)? Abstraction and
/// nested block/prenex bodies DO count; `it` inside a restr's linked args also
/// counts (documented over-acceptance — it is a bound-place marker there).
fn claim_contains_it(claim: &Claim) -> bool {
    match claim {
        Claim::Prenex { body, .. } => claim_contains_it(body),
        Claim::DetBlock { restr, body, .. } => {
            restr_linked_args_contain_it(restr) || claim_contains_it(body)
        }
        Claim::Impl(a, b)
        | Claim::Iff(a, b)
        | Claim::Xor(a, b)
        | Claim::Or(a, b)
        | Claim::And(a, b) => claim_contains_it(a) || claim_contains_it(b),
        Claim::Not(a) => claim_contains_it(a),
        Claim::Prefixed { atom, .. } => claim_contains_it(atom),
        Claim::Equality(a, b) => term_contains_it(a) || term_contains_it(b),
        Claim::Predication(p) => {
            p.args.iter().any(|arg| term_contains_it(&arg.term))
                || p.tags.iter().any(|tag| term_contains_it(&tag.term))
        }
    }
}

fn term_contains_it(term: &Term) -> bool {
    match term {
        Term::Key(KeyTerm::It) => true,
        Term::Abstraction { body, .. } => claim_contains_it(body),
        Term::Det { restr, .. } => restr_linked_args_contain_it(restr),
        _ => false,
    }
}

fn restr_linked_args_contain_it(restr: &Restr) -> bool {
    match &restr.kind {
        RestrKind::Seq { linked_args, .. } => {
            linked_args.iter().any(|arg| term_contains_it(&arg.term))
        }
        RestrKind::Selected { .. } => false,
    }
}

/// Unescape a string literal (the grammar guarantees only `\"` and `\\`
/// escapes reach here).
fn unescape(slice: &str) -> String {
    let inner = &slice[1..slice.len() - 1];
    let mut out = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('"') => out.push('"'),
                Some('\\') => out.push('\\'),
                other => unreachable!("grammar admits only \\\" and \\\\ escapes: {other:?}"),
            }
        } else {
            out.push(c);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;

    /// Parse exactly one statement, fail-closed.
    fn one(input: &str) -> Claim {
        let statements =
            parse_statements(input).unwrap_or_else(|e| panic!("parse failed for {input:?}: {e}"));
        assert_eq!(statements.len(), 1, "expected one statement in {input:?}");
        statements.into_iter().next().unwrap().claim
    }

    fn err(input: &str) -> ParseError {
        match parse_statements(input) {
            Ok(ast) => panic!("expected error for {input:?}, parsed {ast:?}"),
            Err(e) => e,
        }
    }

    fn word(name: &str) -> PredUnit {
        PredUnit::Word(vec![name.into()])
    }

    fn seq1(name: &str) -> PredSeq {
        PredSeq(vec![word(name)])
    }

    fn pred(name: &str, args: Vec<Arg>) -> Claim {
        Claim::Predication(Predication {
            seq: seq1(name),
            args,
            tags: vec![],
            span: 0..0, // spans not asserted through this helper
        })
    }

    fn pos(term: Term) -> Arg {
        Arg {
            label: None,
            term,
            span: 0..0,
        }
    }

    fn named(label: &str, term: Term) -> Arg {
        Arg {
            label: Some(label.into()),
            term,
            span: 0..0,
        }
    }

    fn name(n: &str) -> Term {
        Term::Name {
            name: n.into(),
            rel_clauses: vec![],
        }
    }

    fn restr(word_: &str) -> Restr {
        Restr {
            negated: false,
            kind: RestrKind::Seq {
                seq: seq1(word_),
                linked_args: vec![],
            },
            rel_clauses: vec![],
            span: 0..0,
        }
    }

    fn det_term(det: Det, word_: &str) -> Term {
        Term::Det {
            det,
            restr: restr(word_),
        }
    }

    /// Compare claims ignoring spans (helper-built nodes carry 0..0).
    fn assert_claim(input: &str, expected: Claim) {
        let mut actual = one(input);
        zero_spans(&mut actual);
        assert_eq!(actual, expected, "for input {input:?}");
    }

    fn zero_spans(claim: &mut Claim) {
        match claim {
            Claim::Prenex { body, .. } => zero_spans(body),
            Claim::DetBlock { restr, body, .. } => {
                zero_restr(restr);
                zero_spans(body);
            }
            Claim::Impl(a, b)
            | Claim::Iff(a, b)
            | Claim::Xor(a, b)
            | Claim::Or(a, b)
            | Claim::And(a, b) => {
                zero_spans(a);
                zero_spans(b);
            }
            Claim::Not(a) => zero_spans(a),
            Claim::Prefixed { atom, .. } => zero_spans(atom),
            Claim::Predication(p) => {
                p.span = 0..0;
                for arg in &mut p.args {
                    arg.span = 0..0;
                    zero_term(&mut arg.term);
                }
                for tag in &mut p.tags {
                    tag.span = 0..0;
                    zero_term(&mut tag.term);
                }
            }
            Claim::Equality(a, b) => {
                zero_term(a);
                zero_term(b);
            }
        }
    }

    fn zero_term(term: &mut Term) {
        match term {
            Term::Det { restr, .. } => zero_restr(restr),
            Term::Name { rel_clauses, .. } => {
                for rc in rel_clauses {
                    zero_rel(rc);
                }
            }
            Term::Abstraction { body, .. } => zero_spans(body),
            _ => {}
        }
    }

    fn zero_restr(restr: &mut Restr) {
        restr.span = 0..0;
        if let RestrKind::Seq { linked_args, .. } = &mut restr.kind {
            for arg in linked_args {
                arg.span = 0..0;
                zero_term(&mut arg.term);
            }
        }
        for rc in &mut restr.rel_clauses {
            zero_rel(rc);
        }
    }

    fn zero_rel(rc: &mut RelClause) {
        rc.span = 0..0;
        if let ClauseBody::Full(claim) = &mut rc.body {
            zero_spans(claim);
        }
    }

    // ── grammar ↔ reserved-word conformance (the executable-spec pin) ──

    #[test]
    fn grammar_keywords_match_reserved_words() {
        let grammar = include_str!("nibli_kr.pest");
        let mut spellings: Vec<&str> = Vec::new();
        for line in grammar.lines() {
            let Some((lhs, rhs)) = line.split_once('=') else {
                continue;
            };
            if !lhs.trim().starts_with("kw_") {
                continue;
            }
            let quoted = rhs.split('"').nth(1).expect("kw_ rule quotes its spelling");
            spellings.push(quoted);
        }
        spellings.sort_unstable();
        let reserved = nibli_kr_dictionary::reserved::RESERVED_WORDS;
        assert_eq!(
            spellings, reserved,
            "nibli_kr.pest kw_* rules and RESERVED_WORDS diverge"
        );
        for word in reserved {
            assert!(
                parse_statements(&format!("{word}(Adam).")).is_err(),
                "keyword {word:?} must not parse as a predicate name"
            );
        }
        assert!(parse_statements("person(Adam).").is_ok());
    }

    // ── the keyword-boundary defect class, behavioral ──

    #[test]
    fn keywords_never_split_identifiers() {
        for w in [
            "everyday", "theory", "nowhere", "someone", "itchy", "wealth",
        ] {
            let claim = one(&format!("{w}(Adam)."));
            assert!(
                matches!(&claim, Claim::Predication(p) if p.seq == seq1(w)),
                "{w:?} did not survive as one identifier: {claim:?}"
            );
        }
    }

    #[test]
    fn underscored_keyterms_lex_whole() {
        assert_claim(
            "goes(you_all).",
            pred("goes", vec![pos(Term::Key(KeyTerm::YouAll))]),
        );
        assert!(parse_statements("goes(you_all_x).").is_err());
        assert!(parse_statements("goes(it_ab).").is_err());
    }

    // ── core happy paths (unchanged behavior) ──

    #[test]
    fn ground_facts_and_terms() {
        assert_claim("person(Adam).", pred("person", vec![pos(name("Adam"))]));
        assert_claim("rains().", pred("rains", vec![]));
        assert_claim(
            "goes(me, to: some market).",
            pred(
                "goes",
                vec![
                    pos(Term::Key(KeyTerm::Me)),
                    named("to", det_term(Det::Some, "market")),
                ],
            ),
        );
        assert_claim(
            "loves(me, _).",
            pred(
                "loves",
                vec![pos(Term::Key(KeyTerm::Me)), pos(Term::Unspecified)],
            ),
        );
        assert_claim(
            "product(50, 5, 10).",
            pred(
                "product",
                vec![
                    pos(Term::Number(50.0)),
                    pos(Term::Number(5.0)),
                    pos(Term::Number(10.0)),
                ],
            ),
        );
        assert_claim("dog($x).", pred("dog", vec![pos(Term::Var("x".into()))]));
        assert_claim(
            "word(\"λ café\").",
            pred("word", vec![pos(Term::Str("λ café".into()))]),
        );
        assert!(parse_statements(r#"word("bad \q escape")."#).is_err());
    }

    #[test]
    fn determiner_taxonomy() {
        assert_claim(
            "animal(every dog).",
            pred("animal", vec![pos(det_term(Det::Every, "dog"))]),
        );
        assert_claim(
            "goes(every the dog).",
            pred("goes", vec![pos(det_term(Det::EveryThe, "dog"))]),
        );
        assert_claim(
            "red(exactly 2 red).",
            pred("red", vec![pos(det_term(Det::Exactly(2), "red"))]),
        );
        assert_claim(
            "goes(no dog).",
            pred("goes", vec![pos(det_term(Det::Exactly(0), "dog"))]),
        );
        let e = err("red(exactly 2.5 red).");
        assert!(e.message.contains("whole number"), "{e}");
        let e = err("red(exactly 4294967296 red).");
        assert!(e.message.contains("exceeds the supported range"), "{e}");
    }

    #[test]
    fn equality_prefixes_negation() {
        assert_claim("Kim = Adam.", Claim::Equality(name("Kim"), name("Adam")));
        assert_claim(
            "must past ~goes(me).",
            Claim::Prefixed {
                deontic: Some(Deontic::Must),
                tense: Some(Tense::Past),
                atom: Box::new(Claim::Not(Box::new(pred(
                    "goes",
                    vec![pos(Term::Key(KeyTerm::Me))],
                )))),
            },
        );
        let e = err("~past goes(me).");
        assert!(e.message.contains("past ~P"), "{e}");
        let e = err("~~goes(me).");
        assert!(e.message.contains("double negation"), "{e}");
        let e = err("past (a(A) & b(A)).");
        assert!(e.message.contains("single predication"), "{e}");
        let e = err("past must goes(me).");
        assert!(e.message.contains("deontic comes before tense"), "{e}");
        let e = err("goes(to: some market, me).");
        assert!(
            e.message.contains("positional arguments must come before"),
            "{e}"
        );
    }

    #[test]
    fn operator_ladder() {
        assert_claim(
            "a(X) & b(X) -> c(X).",
            Claim::Impl(
                Box::new(Claim::And(
                    Box::new(pred("a", vec![pos(name("X"))])),
                    Box::new(pred("b", vec![pos(name("X"))])),
                )),
                Box::new(pred("c", vec![pos(name("X"))])),
            ),
        );
        assert_claim(
            "p(A) -> q(A) -> r(A).",
            Claim::Impl(
                Box::new(pred("p", vec![pos(name("A"))])),
                Box::new(Claim::Impl(
                    Box::new(pred("q", vec![pos(name("A"))])),
                    Box::new(pred("r", vec![pos(name("A"))])),
                )),
            ),
        );
    }

    // ── tanru / brackets / zei ──

    #[test]
    fn tanru_heads_and_groups() {
        assert_claim(
            "health data(Kanrek).",
            Claim::Predication(Predication {
                seq: PredSeq(vec![word("health"), word("data")]),
                args: vec![pos(name("Kanrek"))],
                tags: vec![],
                span: 0..0,
            }),
        );
        assert_claim(
            "[big fast] dog(Rex).",
            Claim::Predication(Predication {
                seq: PredSeq(vec![
                    PredUnit::Group(PredSeq(vec![word("big"), word("fast")])),
                    word("dog"),
                ]),
                args: vec![pos(name("Rex"))],
                tags: vec![],
                span: 0..0,
            }),
        );
        assert_eq!(
            PredSeq(vec![word("health"), word("data")]).head_word(),
            "data"
        );
    }

    #[test]
    fn zei_compounds_are_word_identity() {
        assert_claim(
            "computer+user(me).",
            Claim::Predication(Predication {
                seq: PredSeq(vec![PredUnit::Word(vec!["computer".into(), "user".into()])]),
                args: vec![pos(Term::Key(KeyTerm::Me))],
                tags: vec![],
                span: 0..0,
            }),
        );
        // Compound identity may not contain whitespace or comments.
        assert!(parse_statements("computer + user(me).").is_err());
        assert!(parse_statements("computer/*x*/+user(me).").is_err());
    }

    #[test]
    fn tanru_fencing_regressions() {
        // Review near-misses: predication-then-`=` fails closed (n-ary du
        // inexpressible), bare ident is not a term.
        assert!(parse_statements("dog cat = Adam.").is_err());
        assert!(parse_statements("goes(every big, dog).").is_err());
    }

    // ── prenex + block determiners ──

    #[test]
    fn prenex_forms() {
        assert_claim(
            "all $x: dog($x) -> animal($x).",
            Claim::Prenex {
                vars: vec!["x".into()],
                body: Box::new(Claim::Impl(
                    Box::new(pred("dog", vec![pos(Term::Var("x".into()))])),
                    Box::new(pred("animal", vec![pos(Term::Var("x".into()))])),
                )),
            },
        );
        assert_claim(
            "all $x, $y: loves($x, $y).",
            Claim::Prenex {
                vars: vec!["x".into(), "y".into()],
                body: Box::new(pred(
                    "loves",
                    vec![pos(Term::Var("x".into())), pos(Term::Var("y".into()))],
                )),
            },
        );
        // Prenex as a bare RHS of -> needs parens (fails closed, §15).
        assert!(parse_statements("dog($x) -> all $y: dog($y).").is_err());
    }

    #[test]
    fn det_block_forms() {
        assert_claim(
            "every dog $d: animal($d) & alive($d).",
            Claim::DetBlock {
                det: Det::Every,
                restr: restr("dog"),
                var: "d".into(),
                body: Box::new(Claim::And(
                    Box::new(pred("animal", vec![pos(Term::Var("d".into()))])),
                    Box::new(pred("alive", vec![pos(Term::Var("d".into()))])),
                )),
            },
        );
        assert_claim(
            "no dog $d: goes($d).",
            Claim::DetBlock {
                det: Det::Exactly(0),
                restr: restr("dog"),
                var: "d".into(),
                body: Box::new(pred("goes", vec![pos(Term::Var("d".into()))])),
            },
        );
        // Backtracks cleanly into an equality when the binder is absent.
        assert_claim(
            "every dog = Adam.",
            Claim::Equality(det_term(Det::Every, "dog"), name("Adam")),
        );
        // …but a half-written block fails closed.
        assert!(parse_statements("some dog $d = it_a.").is_err());
    }

    // ── relative clauses ──

    #[test]
    fn rel_clause_forms() {
        // Bare-predicate sugar.
        assert_claim(
            "goes(every person where approves).",
            pred(
                "goes",
                vec![pos(Term::Det {
                    det: Det::Every,
                    restr: Restr {
                        negated: false,
                        kind: RestrKind::Seq {
                            seq: seq1("person"),
                            linked_args: vec![],
                        },
                        rel_clauses: vec![RelClause {
                            kind: RelKind::Where,
                            body: ClauseBody::Bare {
                                negated: false,
                                seq: seq1("approves"),
                            },
                            span: 0..0,
                        }],
                        span: 0..0,
                    },
                })],
            ),
        );
        // Negated bare body; stacking; also-clauses; bare tanru body.
        let claim = one("goes(every drug where ~thin also big fast).");
        let Claim::Predication(p) = claim else {
            panic!()
        };
        let Term::Det { restr: r, .. } = &p.args[0].term else {
            panic!()
        };
        assert_eq!(r.rel_clauses.len(), 2);
        assert!(matches!(
            &r.rel_clauses[0].body,
            ClauseBody::Bare { negated: true, seq } if *seq == seq1("thin")
        ));
        assert!(matches!(&r.rel_clauses[1].kind, RelKind::Also));
        assert!(matches!(
            &r.rel_clauses[1].body,
            ClauseBody::Bare { negated: false, seq } if seq.0.len() == 2
        ));
        // Full body with `it`; rigid-term clause; comma fencing.
        assert!(parse_statements("goes(some dog where big(it)).").is_ok());
        assert!(parse_statements("goes(some dog where it = Adam).").is_ok());
        let claim = one("goes(Adam where dog, you).");
        let Claim::Predication(p) = claim else {
            panic!()
        };
        assert_eq!(p.args.len(), 2, "rel clause must not eat the comma");
        // det_block inside a clause body (with `it`).
        assert!(parse_statements("goes(some dog where some cat $c: loves(it, $c)).").is_ok());
    }

    #[test]
    fn mandatory_it_in_full_bodies() {
        let e = err("goes(some dog where goes(me)).");
        assert!(e.message.contains("must mention `it`"), "{e}");
        // Recurses through nested binder bodies (review Finding 4).
        let e = err("goes(some dog where some cat $c: loves($c, $c)).");
        assert!(e.message.contains("must mention `it`"), "{e}");
        // `it` inside an abstraction body counts.
        assert!(parse_statements("goes(some dog where desires(me, event { eats(it) })).").is_ok());
    }

    // ── place selectors (O8) ──

    #[test]
    fn selectors_and_the_statement_dot() {
        let claim = one("permitted(every loves.loved).");
        let Claim::Predication(p) = claim else {
            panic!()
        };
        let Term::Det { restr: r, .. } = &p.args[0].term else {
            panic!()
        };
        assert!(matches!(
            &r.kind,
            RestrKind::Selected { pred, label } if pred == "loves" && label == "loved"
        ));
        // O8 battery: spaced = two statements; compact-with-args = parse error
        // (never a silent merge); spaces around the dot never select.
        let statements = parse_statements("Kim = every dog. eats(me).").unwrap();
        assert_eq!(statements.len(), 2);
        assert!(parse_statements("Kim = every dog.eats(me).").is_err());
        assert!(parse_statements("permitted(every loves .loved).").is_err());
        assert!(parse_statements("permitted(every loves. loved).").is_err());
    }

    // ── linked args ──

    #[test]
    fn linked_args_on_restrictors() {
        let claim = one("permitted(every tends(charge: some data)).");
        let Claim::Predication(p) = claim else {
            panic!()
        };
        let Term::Det { restr: r, .. } = &p.args[0].term else {
            panic!()
        };
        let RestrKind::Seq { linked_args, .. } = &r.kind else {
            panic!()
        };
        assert_eq!(linked_args.len(), 1);
        assert_eq!(linked_args[0].label.as_deref(), Some("charge"));
        // Bound-place marker parses (position legality is resolve's job).
        assert!(parse_statements("goes(every loves(x2: it)).").is_ok());
    }

    // ── abstractions ──

    #[test]
    fn abstraction_forms() {
        assert_claim(
            "desires(me, event { goes(you) }).",
            pred(
                "desires",
                vec![
                    pos(Term::Key(KeyTerm::Me)),
                    pos(Term::Abstraction {
                        kind: AbsKind::Event,
                        body: Box::new(pred("goes", vec![pos(Term::Key(KeyTerm::You))])),
                    }),
                ],
            ),
        );
        assert!(parse_statements("thinks(me, fact { dog(Adam) }).").is_ok());
        assert!(parse_statements("able(me, property { fast(slot) }).").is_ok());
        assert!(parse_statements("measures(me, amount { fast(you) }).").is_ok());
        assert!(parse_statements("likes(me, concept { flies(some dog) }).").is_ok());
    }

    // ── via tags ──

    #[test]
    fn via_tags() {
        let claim = one("goes(me) via uses(this) via reason(this).");
        let Claim::Predication(p) = claim else {
            panic!()
        };
        assert_eq!(p.tags.len(), 2);
        assert_eq!(p.tags[0].pred, vec!["uses".to_owned()]);
        assert_eq!(p.tags[1].pred, vec!["reason".to_owned()]);
        // Tag terms are full terms (det phrase with a rel clause).
        assert!(parse_statements("goes(me) via uses(some tool where big).").is_ok());
        // Equalities take no tags (spec: tags are predication-only).
        assert!(parse_statements("Kim = Adam via uses(this).").is_err());
    }

    // ── files, comments, recovery (unchanged behavior) ──

    #[test]
    fn multi_statement_files_with_comments() {
        let input = "# corpus header\nperson(Adam). /* mid */ dog(Rex).\nKim = Adam.";
        let statements = parse_statements(input).unwrap();
        assert_eq!(statements.len(), 3);
        assert_eq!(&input[statements[0].span.clone()], "person(Adam).");
        assert_eq!(&input[statements[2].span.clone()], "Kim = Adam.");
    }

    #[test]
    fn recovery_continues_after_broken_statement() {
        let (statements, errors) = parse_text_with_errors("dog(. person(Adam).");
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert_eq!(statements.len(), 1);
        let (statements, errors) = parse_text_with_errors("~~a(). person(Adam).");
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert_eq!(statements.len(), 1);
    }

    #[test]
    fn structural_and_lex_errors_positioned() {
        let e = err("goes(λ).");
        assert_eq!((e.line, e.column), (1, 6), "{e}");
        assert!(parse_statements("goes(me").is_err());
        assert!(parse_statements("every dog.").is_err());
        let (statements, errors) = parse_text_with_errors("/* /* */ goes(). */");
        assert_eq!(statements.len(), 1);
        assert!(!errors.is_empty(), "the orphaned */ must not parse");
    }
}
