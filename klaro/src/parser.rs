//! Klaro parser: pest-generated from `src/klaro.pest` (THE executable grammar
//! — SURFACE_SYNTAX §15), plus the walker that builds the tree AST
//! ([`crate::ast`]) and enforces the §6 errata as targeted, positioned errors.
//!
//! Division of labor:
//! - `klaro.pest` owns SYNTAX. It parses modifiers (`must/may/past/now/future/~`)
//!   permissively and knows nothing about the errata, argument ordering, or
//!   count integrality — encoding those as grammar would bury the spec
//!   guidance under generic "expected …" messages.
//! - The walker owns the FAIL-CLOSED SEMANTIC SHAPE: ≤1 deontic, ≤1 tense,
//!   deontic-before-tense, `~` innermost and single, prefixes/`~` only over a
//!   single predication/equality, positionals-before-named, `exactly N`
//!   integrality and u32 range, number finiteness, string unescaping.
//!
//! Error recovery is per-statement, like gerna: `parse_text_with_errors`
//! parses statement-by-statement, and on an error skips (string/comment-aware)
//! past the next `.` so later statements still parse.

use std::fmt;

use pest::Parser as _;
use pest::iterators::Pair;

use crate::ast::{Arg, Claim, Deontic, Det, KeyTerm, Predication, Restr, Statement, Tense, Term};

#[derive(pest_derive::Parser)]
#[grammar = "klaro.pest"]
struct KlaroPest;

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
        match KlaroPest::parse(Rule::statement, &input[pos..]) {
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
            | Rule::iff_chain
            | Rule::xor_chain
            | Rule::or_chain
            | Rule::and_chain
            | Rule::unary
            | Rule::atom => "a claim",
            Rule::predication => "a predication",
            Rule::equality => "an equality `a = b`",
            Rule::ident => "a predicate word",
            Rule::label => "an argument label",
            Rule::statement => "a statement",
            Rule::det | Rule::det_phrase => "a determiner phrase",
            Rule::restr => "a restrictor predicate",
            Rule::number => "a number",
            Rule::string => "a string",
            Rule::name => "a Name",
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

fn err_at(input: &str, offset: usize, message: impl Into<String>) -> ParseError {
    let (line, column) = line_col(input, offset);
    ParseError {
        message: message.into(),
        line,
        column,
    }
}

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

fn build_claim(pair: Pair<Rule>, input: &str, base: usize) -> Result<Claim, ParseError> {
    // claim = iff_chain ~ (op_impl ~ claim)?   (right-assoc)
    let mut inner = pair.into_inner();
    let lhs = build_chain(inner.next().expect("iff_chain"), input, base)?;
    match inner.find(|p| p.as_rule() == Rule::claim) {
        Some(rhs) => Ok(Claim::Impl(
            Box::new(lhs),
            Box::new(build_claim(rhs, input, base)?),
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
         (SURFACE_SYNTAX §6 errata)";

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
                                 SURFACE_SYNTAX §6)",
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
                     (SURFACE_SYNTAX §6 errata)",
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
    let mut inner = pair.into_inner();
    let pred = inner.next().expect("predication ident").as_str().to_owned();
    let args_pair = inner.next().expect("predication args");

    let mut args: Vec<Arg> = Vec::new();
    let mut seen_named = false;
    for arg_pair in args_pair.into_inner() {
        debug_assert_eq!(arg_pair.as_rule(), Rule::arg);
        let arg_at = base + arg_pair.as_span().start();
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
                "positional arguments must come before named arguments (SURFACE_SYNTAX §5)",
            ));
        }
        args.push(Arg {
            label,
            term: term.expect("arg has a term"),
        });
    }
    Ok(Predication {
        pred,
        args,
        span: base + span.start()..base + span.end(),
    })
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
                     fail closed per SURFACE_SYNTAX §3",
                ));
            }
            Ok(Term::Number(value))
        }
        Rule::string => Ok(Term::Str(unescape(inner.as_str()))),
        Rule::var => Ok(Term::Var(inner.as_str()[1..].to_owned())),
        Rule::name => Ok(Term::Name(inner.as_str().to_owned())),
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
    let det_pair = inner.next().expect("det");
    let restr_pair = inner.next().expect("restr");

    let mut kids = det_pair.into_inner().peekable();
    let head = kids.next().expect("det head");
    let det = match head.as_rule() {
        Rule::kw_some => Det::Some,
        Rule::kw_the => Det::The,
        Rule::kw_no => Det::Exactly(0), // `no X` = exactly-0 sugar (spec §4)
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
    };

    let restr_span = restr_pair.as_span();
    let ident = restr_pair.into_inner().next().expect("restr ident");
    Ok(Term::Det {
        det,
        restr: Restr {
            pred: ident.as_str().to_owned(),
            span: base + restr_span.start()..base + restr_span.end(),
        },
    })
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

    fn pred(name: &str, args: Vec<Arg>) -> Claim {
        Claim::Predication(Predication {
            pred: name.into(),
            args,
            span: 0..0, // spans not asserted through this helper
        })
    }

    fn pos(term: Term) -> Arg {
        Arg { label: None, term }
    }

    fn named(label: &str, term: Term) -> Arg {
        Arg {
            label: Some(label.into()),
            term,
        }
    }

    /// Compare claims ignoring spans (helper-built predications carry 0..0).
    fn assert_claim(input: &str, expected: Claim) {
        let mut actual = one(input);
        zero_spans(&mut actual);
        assert_eq!(actual, expected, "for input {input:?}");
    }

    fn zero_spans(claim: &mut Claim) {
        match claim {
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
                    zero_span_term(&mut arg.term);
                }
            }
            Claim::Equality(a, b) => {
                zero_span_term(a);
                zero_span_term(b);
            }
        }
    }

    fn zero_span_term(term: &mut Term) {
        if let Term::Det { restr, .. } = term {
            restr.span = 0..0;
        }
    }

    fn restr(word: &str) -> Restr {
        Restr {
            pred: word.into(),
            span: 0..0,
        }
    }

    // ── grammar ↔ reserved-word conformance (the executable-spec pin) ──

    #[test]
    fn grammar_keywords_match_reserved_words() {
        // Extract every kw_* spelling from the grammar TEXT and pin the set,
        // both directions, against klaro-dictionary's single source.
        let grammar = include_str!("klaro.pest");
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
        let reserved = klaro_dictionary::reserved::RESERVED_WORDS;
        assert_eq!(
            spellings, reserved,
            "klaro.pest kw_* rules and RESERVED_WORDS diverge"
        );
        // Behaviorally: no keyword is usable as a predicate name…
        for word in reserved {
            assert!(
                parse_statements(&format!("{word}(Adam).")).is_err(),
                "keyword {word:?} must not parse as a predicate name"
            );
        }
        // …while ordinary idents are.
        assert!(parse_statements("person(Adam).").is_ok());
    }

    // ── the keyword-boundary defect class, now behavioral ──

    #[test]
    fn keywords_never_split_identifiers() {
        // `everyday` is ONE predicate word, never `every` + `day` (which would
        // be a determiner phrase and fail to take an argument list).
        for word in [
            "everyday", "theory", "nowhere", "someone", "itchy", "wealth",
        ] {
            let claim = one(&format!("{word}(Adam)."));
            assert!(
                matches!(&claim, Claim::Predication(p) if p.pred == word),
                "{word:?} did not survive as one identifier: {claim:?}"
            );
        }
    }

    #[test]
    fn underscored_keyterms_lex_whole() {
        assert_claim(
            "goes(you_all).",
            pred("goes", vec![pos(Term::Key(KeyTerm::YouAll))]),
        );
        assert_claim(
            "goes(we_others, it_a).",
            pred(
                "goes",
                vec![
                    pos(Term::Key(KeyTerm::WeOthers)),
                    pos(Term::Key(KeyTerm::ItA)),
                ],
            ),
        );
        // One char longer -> a plain ident again, which is NOT a term.
        assert!(parse_statements("goes(you_all_x).").is_err());
        assert!(parse_statements("goes(it_ab).").is_err());
    }

    // ── happy paths ──

    #[test]
    fn ground_facts() {
        assert_claim(
            "person(Adam).",
            pred("person", vec![pos(Term::Name("Adam".into()))]),
        );
        assert_claim(
            "inhibits(Flukonazol, Siptucin).",
            pred(
                "inhibits",
                vec![
                    pos(Term::Name("Flukonazol".into())),
                    pos(Term::Name("Siptucin".into())),
                ],
            ),
        );
        assert_claim("rains().", pred("rains", vec![]));
    }

    #[test]
    fn named_and_mixed_args() {
        assert_claim(
            "goes(me, to: some market).",
            pred(
                "goes",
                vec![
                    pos(Term::Key(KeyTerm::Me)),
                    named(
                        "to",
                        Term::Det {
                            det: Det::Some,
                            restr: restr("market"),
                        },
                    ),
                ],
            ),
        );
        assert_claim(
            "goes(x2: some market, x3: some home).",
            pred(
                "goes",
                vec![
                    named(
                        "x2",
                        Term::Det {
                            det: Det::Some,
                            restr: restr("market"),
                        },
                    ),
                    named(
                        "x3",
                        Term::Det {
                            det: Det::Some,
                            restr: restr("home"),
                        },
                    ),
                ],
            ),
        );
    }

    #[test]
    fn term_zoo() {
        assert_claim(
            "loves(me, _).",
            pred(
                "loves",
                vec![pos(Term::Key(KeyTerm::Me)), pos(Term::Unspecified)],
            ),
        );
        assert_claim(
            "goes(?, to: the market).",
            pred(
                "goes",
                vec![
                    pos(Term::Witness),
                    named(
                        "to",
                        Term::Det {
                            det: Det::The,
                            restr: restr("market"),
                        },
                    ),
                ],
            ),
        );
        assert_claim(
            "word(\"any text\").",
            pred("word", vec![pos(Term::Str("any text".into()))]),
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
    }

    #[test]
    fn strings_escapes_and_utf8_payloads() {
        assert_claim(
            r#"word("he said \"hi\" \\ done")."#,
            pred(
                "word",
                vec![pos(Term::Str(r#"he said "hi" \ done"#.into()))],
            ),
        );
        // Non-ASCII is legal INSIDE strings (payloads are data, not syntax).
        assert_claim(
            "word(\"λ café\").",
            pred("word", vec![pos(Term::Str("λ café".into()))]),
        );
        // Unknown escape / unterminated / raw newline all fail closed.
        assert!(parse_statements(r#"word("bad \q escape")."#).is_err());
        assert!(parse_statements("word(\"unterminated).").is_err());
        assert!(parse_statements("word(\"no\nnewlines\").").is_err());
    }

    #[test]
    fn determiner_taxonomy() {
        assert_claim(
            "animal(every dog).",
            pred(
                "animal",
                vec![pos(Term::Det {
                    det: Det::Every,
                    restr: restr("dog"),
                })],
            ),
        );
        assert_claim(
            "goes(every the dog).",
            pred(
                "goes",
                vec![pos(Term::Det {
                    det: Det::EveryThe,
                    restr: restr("dog"),
                })],
            ),
        );
        assert_claim(
            "red(exactly 2 red).",
            pred(
                "red",
                vec![pos(Term::Det {
                    det: Det::Exactly(2),
                    restr: restr("red"),
                })],
            ),
        );
        assert_claim(
            "eats(exactly 0 the cat).",
            pred(
                "eats",
                vec![pos(Term::Det {
                    det: Det::ExactlyThe(0),
                    restr: restr("cat"),
                })],
            ),
        );
        // `no X` is exactly-0 sugar, resolved at parse.
        assert_claim(
            "goes(no dog).",
            pred(
                "goes",
                vec![pos(Term::Det {
                    det: Det::Exactly(0),
                    restr: restr("dog"),
                })],
            ),
        );
    }

    #[test]
    fn equality_is_binary_du() {
        assert_claim(
            "Kim = Adam.",
            Claim::Equality(Term::Name("Kim".into()), Term::Name("Adam".into())),
        );
        assert_claim(
            "2 = 2.",
            Claim::Equality(Term::Number(2.0), Term::Number(2.0)),
        );
    }

    #[test]
    fn prefixes_nest_deontic_outermost() {
        assert_claim(
            "past dog(Dan).",
            Claim::Prefixed {
                deontic: None,
                tense: Some(Tense::Past),
                atom: Box::new(pred("dog", vec![pos(Term::Name("Dan".into()))])),
            },
        );
        assert_claim(
            "must goes(me).",
            Claim::Prefixed {
                deontic: Some(Deontic::Must),
                tense: None,
                atom: Box::new(pred("goes", vec![pos(Term::Key(KeyTerm::Me))])),
            },
        );
        assert_claim(
            "must past goes(me).",
            Claim::Prefixed {
                deontic: Some(Deontic::Must),
                tense: Some(Tense::Past),
                atom: Box::new(pred("goes", vec![pos(Term::Key(KeyTerm::Me))])),
            },
        );
        // Negation innermost: past ~P = Past(Not(P)) — the ONLY legal ~×tense
        // composition (SURFACE_SYNTAX §6).
        assert_claim(
            "past ~goes(me).",
            Claim::Prefixed {
                deontic: None,
                tense: Some(Tense::Past),
                atom: Box::new(Claim::Not(Box::new(pred(
                    "goes",
                    vec![pos(Term::Key(KeyTerm::Me))],
                )))),
            },
        );
    }

    #[test]
    fn negation_and_paren_collapse() {
        assert_claim(
            "~goes(me).",
            Claim::Not(Box::new(pred("goes", vec![pos(Term::Key(KeyTerm::Me))]))),
        );
        // A parenthesized SIMPLE claim collapses and may be negated.
        assert_claim(
            "~(goes(me)).",
            Claim::Not(Box::new(pred("goes", vec![pos(Term::Key(KeyTerm::Me))]))),
        );
    }

    #[test]
    fn operator_precedence_and_associativity() {
        // & binds tighter than ->
        assert_claim(
            "a(X) & b(X) -> c(X).",
            Claim::Impl(
                Box::new(Claim::And(
                    Box::new(pred("a", vec![pos(Term::Name("X".into()))])),
                    Box::new(pred("b", vec![pos(Term::Name("X".into()))])),
                )),
                Box::new(pred("c", vec![pos(Term::Name("X".into()))])),
            ),
        );
        // -> is right-assoc
        assert_claim(
            "p(A) -> q(A) -> r(A).",
            Claim::Impl(
                Box::new(pred("p", vec![pos(Term::Name("A".into()))])),
                Box::new(Claim::Impl(
                    Box::new(pred("q", vec![pos(Term::Name("A".into()))])),
                    Box::new(pred("r", vec![pos(Term::Name("A".into()))])),
                )),
            ),
        );
        // parens regroup
        assert_claim(
            "(p(A) | q(A)) -> r(A).",
            Claim::Impl(
                Box::new(Claim::Or(
                    Box::new(pred("p", vec![pos(Term::Name("A".into()))])),
                    Box::new(pred("q", vec![pos(Term::Name("A".into()))])),
                )),
                Box::new(pred("r", vec![pos(Term::Name("A".into()))])),
            ),
        );
        // ladder: & < | < ^ < <->
        assert_claim(
            "a() | b() ^ c() <-> d().",
            Claim::Iff(
                Box::new(Claim::Xor(
                    Box::new(Claim::Or(
                        Box::new(pred("a", vec![])),
                        Box::new(pred("b", vec![])),
                    )),
                    Box::new(pred("c", vec![])),
                )),
                Box::new(pred("d", vec![])),
            ),
        );
    }

    #[test]
    fn multi_statement_files_with_comments() {
        let input = "# corpus header\nperson(Adam). /* mid */ dog(Rex).\nKim = Adam.";
        let statements = parse_statements(input).unwrap();
        assert_eq!(statements.len(), 3);
        // Statement spans are ABSOLUTE (offset-corrected across statements).
        assert_eq!(&input[statements[0].span.clone()], "person(Adam).");
        assert_eq!(&input[statements[1].span.clone()], "dog(Rex).");
        assert_eq!(&input[statements[2].span.clone()], "Kim = Adam.");
    }

    #[test]
    fn block_comments_do_not_nest() {
        // `/* /* */` closes at the FIRST `*/`; the orphaned `*/` then fails to
        // parse (never silently swallowed).
        let (statements, errors) = parse_text_with_errors("/* /* */ goes(). */");
        assert_eq!(statements.len(), 1);
        assert!(!errors.is_empty(), "the orphaned */ must not parse");
        // Unterminated block comments fail closed too.
        let (statements, errors) = parse_text_with_errors("goes(). /* never closed");
        assert_eq!(statements.len(), 1);
        assert!(!errors.is_empty());
    }

    // ── errata + fail-closed errors ──

    #[test]
    fn errata_prefix_over_compound_rejected() {
        let e = err("past (a(A) & b(A)).");
        assert!(e.message.contains("single predication"), "{e}");
        assert_eq!((e.line, e.column), (1, 6));
    }

    #[test]
    fn errata_not_over_prefix_rejected() {
        let e = err("~past goes(me).");
        assert!(e.message.contains("past ~P"), "{e}");
    }

    #[test]
    fn errata_double_negation_rejected() {
        let e = err("~~goes(me).");
        assert!(e.message.contains("double negation"), "{e}");
    }

    #[test]
    fn errata_not_over_compound_rejected() {
        let e = err("~(a(A) & b(A)).");
        assert!(e.message.contains("single predication"), "{e}");
    }

    #[test]
    fn wrong_prefix_order_rejected() {
        let e = err("past must goes(me).");
        assert!(e.message.contains("deontic comes before tense"), "{e}");
        let e = err("must must goes(me).");
        assert!(e.message.contains("duplicate deontic"), "{e}");
        let e = err("past now goes(me).");
        assert!(e.message.contains("duplicate tense"), "{e}");
    }

    #[test]
    fn positional_after_named_rejected() {
        let e = err("goes(to: some market, me).");
        assert!(
            e.message.contains("positional arguments must come before"),
            "{e}"
        );
    }

    #[test]
    fn exact_count_validation() {
        let e = err("red(exactly 2.5 red).");
        assert!(e.message.contains("whole number"), "{e}");
        let e = err("red(exactly 4294967296 red).");
        assert!(e.message.contains("exceeds the supported range"), "{e}");
        // Boundary: u32::MAX itself is fine.
        assert!(parse_statements("red(exactly 4294967295 red).").is_ok());
    }

    #[test]
    fn number_overflow_fails_closed() {
        let big = format!("f({}).", "9".repeat(400));
        let e = err(&big);
        assert!(e.message.contains("overflows"), "{e}");
    }

    #[test]
    fn structural_errors_are_positioned() {
        // Missing terminating dot.
        let e = err("goes(me)");
        assert_eq!(e.line, 1, "{e}");
        // A bare word is not a claim (predications need an argument list).
        assert!(parse_statements("dog.").is_err());
        // A determiner phrase alone is a term, not a claim (block form is a
        // later bullet).
        assert!(parse_statements("every dog.").is_err());
        // Unterminated argument list.
        assert!(parse_statements("goes(me").is_err());
    }

    #[test]
    fn non_ascii_syntax_fails_positioned() {
        let e = err("goes(λ).");
        assert_eq!((e.line, e.column), (1, 6), "{e}");
        // Stray operator fragments fail closed too.
        assert!(parse_statements("a(X) <- b(X).").is_err());
    }

    #[test]
    fn recovery_continues_after_broken_statement() {
        let (statements, errors) = parse_text_with_errors("dog(. person(Adam).");
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert_eq!(statements.len(), 1);
        assert!(matches!(&statements[0].claim, Claim::Predication(p) if p.pred == "person"));
        // Walker-level rejects recover to the NEXT statement too (the broken
        // one parsed syntactically, so we resume after its dot).
        let (statements, errors) = parse_text_with_errors("~~a(). person(Adam).");
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert_eq!(statements.len(), 1);
    }
}
