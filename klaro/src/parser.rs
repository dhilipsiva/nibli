//! Klaro recursive-descent parser: token stream → tree AST ([`crate::ast`]).
//!
//! Grammar authority: SURFACE_SYNTAX.md §15 plus the §6 errata (2026-07-12).
//! CORE PROFILE for now — terms, determiner phrases, predications with
//! positional+named args, the operator chain, tense/deontic prefixes, binary
//! `=`, `.`-terminated statements. Not yet parsed (subsequent KLARO_TODO
//! bullets): `all` prenex, block determiners, tanru/`[ ]`/`+` compounds,
//! `.label` place selectors, linked args, `via` tags, `where`/`also` clauses,
//! abstractions; those spellings currently fail with ordinary "expected …"
//! errors.
//!
//! Determinism: every choice point is keyword/sigil-led or one-token
//! lookahead. After an `Ident`, `(` commits a predication; otherwise an atom
//! is an equality (no term starts with a lowercase ident — the grammar has no
//! bare-ident term). No backtracking.
//!
//! The §6 errata are enforced HERE, as grammar (each with a targeted,
//! positioned error): prefixes and `~` attach to a single predication/equality
//! (a parenthesized SIMPLE claim collapses and is accepted; a compound one is
//! rejected); `~` under a prefix is legal (`past ~P` = `Past(Not(P))`,
//! smuni's verified nesting) but `~` OVER a prefix (`~past P` =
//! `Not(Past(P))`) has no encoding and is rejected; `~~P` likewise; deontic
//! precedes tense (`must past P`, never `past must P`).

use std::fmt;
use std::ops::Range;

use crate::ast::{Arg, Claim, Deontic, Det, KeyTerm, Predication, Restr, Statement, Tense, Term};
use crate::lexer::{self, line_col};
use crate::token::Token;

/// A positioned parse (or lex) error. 1-based line/column; columns count
/// characters.
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

/// Parse a whole input with PER-STATEMENT error recovery: on an error the
/// parser records it and skips past the next `.`, so later statements still
/// parse. Lex errors are folded in as [`ParseError`]s. Errors come back in
/// source order.
pub fn parse_text_with_errors(input: &str) -> (Vec<Statement>, Vec<ParseError>) {
    let (tokens, lex_errors) = lexer::tokenize_with_errors(input);
    let mut errors: Vec<ParseError> = lex_errors
        .iter()
        .map(|e| {
            let (line, column) = line_col(input, e.start);
            ParseError {
                message: e.message(input),
                line,
                column,
            }
        })
        .collect();

    let mut parser = Parser {
        input,
        tokens,
        pos: 0,
    };
    let mut statements = Vec::new();
    while !parser.at_eof() {
        match parser.parse_statement() {
            Ok(statement) => statements.push(statement),
            Err(e) => {
                errors.push(e);
                parser.skip_past_statement_end();
            }
        }
    }
    errors.sort_by_key(|e| (e.line, e.column));
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

struct Parser<'a> {
    input: &'a str,
    tokens: Vec<(Token, Range<usize>)>,
    pos: usize,
}

impl<'a> Parser<'a> {
    // ── stream helpers ──

    fn at_eof(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos).map(|(t, _)| t)
    }

    fn peek_second(&self) -> Option<&Token> {
        self.tokens.get(self.pos + 1).map(|(t, _)| t)
    }

    fn advance(&mut self) -> Option<(Token, Range<usize>)> {
        let item = self.tokens.get(self.pos).cloned();
        if item.is_some() {
            self.pos += 1;
        }
        item
    }

    fn eat(&mut self, token: &Token) -> bool {
        if self.peek() == Some(token) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    /// Byte offset of the current token (or end of input at EOF).
    fn offset(&self) -> usize {
        self.tokens
            .get(self.pos)
            .map(|(_, s)| s.start)
            .unwrap_or(self.input.len())
    }

    fn error_at(&self, offset: usize, message: impl Into<String>) -> ParseError {
        let (line, column) = line_col(self.input, offset);
        ParseError {
            message: message.into(),
            line,
            column,
        }
    }

    fn error_here(&self, message: impl Into<String>) -> ParseError {
        self.error_at(self.offset(), message)
    }

    fn expect(&mut self, token: &Token, what: &str) -> Result<Range<usize>, ParseError> {
        match self.peek() {
            Some(t) if t == token => Ok(self.advance().unwrap().1),
            Some(t) => Err(self.error_here(format!("expected {what}, found {t:?}"))),
            None => Err(self.error_here(format!("expected {what}, found end of input"))),
        }
    }

    /// Error recovery: consume through the next `.` (or EOF).
    fn skip_past_statement_end(&mut self) {
        while let Some((token, _)) = self.advance() {
            if token == Token::Dot {
                break;
            }
        }
    }

    // ── statements ──

    fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        let start = self.offset();
        let claim = self.parse_claim()?;
        let dot = self.expect(&Token::Dot, "`.` to end the statement")?;
        Ok(Statement {
            claim,
            span: start..dot.end,
        })
    }

    // ── the operator ladder (tightest first: ~/prefixes · & · | · ^ · <-> · ->) ──

    fn parse_claim(&mut self) -> Result<Claim, ParseError> {
        self.parse_impl()
    }

    fn parse_impl(&mut self) -> Result<Claim, ParseError> {
        let lhs = self.parse_iff()?;
        if self.eat(&Token::Arrow) {
            let rhs = self.parse_impl()?; // right-assoc
            Ok(Claim::Impl(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    fn parse_iff(&mut self) -> Result<Claim, ParseError> {
        let mut lhs = self.parse_xor()?;
        while self.eat(&Token::Iff) {
            let rhs = self.parse_xor()?;
            lhs = Claim::Iff(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_xor(&mut self) -> Result<Claim, ParseError> {
        let mut lhs = self.parse_or()?;
        while self.eat(&Token::Xor) {
            let rhs = self.parse_or()?;
            lhs = Claim::Xor(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_or(&mut self) -> Result<Claim, ParseError> {
        let mut lhs = self.parse_and()?;
        while self.eat(&Token::Or) {
            let rhs = self.parse_and()?;
            lhs = Claim::Or(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_and(&mut self) -> Result<Claim, ParseError> {
        let mut lhs = self.parse_prefixed()?;
        while self.eat(&Token::And) {
            let rhs = self.parse_prefixed()?;
            lhs = Claim::And(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    // ── prefixes + negation + atoms ──

    fn parse_prefixed(&mut self) -> Result<Claim, ParseError> {
        let deontic = match self.peek() {
            Some(Token::Must) => {
                self.pos += 1;
                Some(Deontic::Must)
            }
            Some(Token::May) => {
                self.pos += 1;
                Some(Deontic::May)
            }
            _ => None,
        };
        let tense = match self.peek() {
            Some(Token::Past) => {
                self.pos += 1;
                Some(Tense::Past)
            }
            Some(Token::Now) => {
                self.pos += 1;
                Some(Tense::Now)
            }
            Some(Token::Future) => {
                self.pos += 1;
                Some(Tense::Future)
            }
            _ => None,
        };
        // Wrong prefix order: nesting is fixed (deontic outermost, O3).
        if tense.is_some()
            && let Some(Token::Must | Token::May) = self.peek()
        {
            return Err(self.error_here(
                "deontic comes before tense: write `must past P`, never `past must P` \
                 (nesting is Obligatory(Past(…)), SURFACE_SYNTAX §6)",
            ));
        }

        let negated = if self.peek() == Some(&Token::Tilde) {
            let tilde_at = self.offset();
            self.pos += 1;
            match self.peek() {
                Some(Token::Tilde) => {
                    return Err(self.error_here(
                        "double negation `~~` has no encoding (bridi-level negation is a \
                         single flag) — drop both, or restate the claim",
                    ));
                }
                Some(Token::Must | Token::May | Token::Past | Token::Now | Token::Future) => {
                    return Err(self.error_at(
                        tilde_at,
                        "`~` over a tense/deontic prefix is rejected — Not(Past(P)) has no \
                         encoding in the compat profile; `past ~P` (= Past(Not(P))) is the \
                         supported spelling (SURFACE_SYNTAX §6 errata)",
                    ));
                }
                _ => {}
            }
            true
        } else {
            false
        };

        let restricted = deontic.is_some() || tense.is_some() || negated;
        let atom = self.parse_atom(restricted)?;

        let base = if negated {
            Claim::Not(Box::new(atom))
        } else {
            atom
        };
        if deontic.is_some() || tense.is_some() {
            Ok(Claim::Prefixed {
                deontic,
                tense,
                atom: Box::new(base),
            })
        } else {
            Ok(base)
        }
    }

    /// Atom ← `(` Claim `)` / Equality / Predication.
    ///
    /// `restricted` = under a prefix or `~`: the atom must collapse to a
    /// single predication/equality (§6 errata — `past (A & B)` and `~(A & B)`
    /// are rejected; a parenthesized SIMPLE claim is accepted and collapses).
    fn parse_atom(&mut self, restricted: bool) -> Result<Claim, ParseError> {
        match self.peek() {
            Some(Token::LParen) => {
                let paren_at = self.offset();
                self.pos += 1;
                let inner = self.parse_claim()?;
                self.expect(&Token::RParen, "`)`")?;
                if restricted && !matches!(inner, Claim::Predication(_) | Claim::Equality(..)) {
                    return Err(self.error_at(
                        paren_at,
                        "tense/deontic prefixes and `~` attach to a single predication or \
                         equality — not to a compound claim; distribute explicitly \
                         (SURFACE_SYNTAX §6 errata)",
                    ));
                }
                Ok(inner)
            }
            Some(Token::Ident(_)) => Ok(Claim::Predication(self.parse_predication()?)),
            _ => {
                // Equality is the only remaining atom form: Term `=` Term.
                let lhs_at = self.offset();
                let lhs = self.parse_term().map_err(|_| {
                    self.error_at(
                        lhs_at,
                        "expected a claim: a predication `pred(…)`, an equality `a = b`, \
                         or a parenthesized claim",
                    )
                })?;
                if self.peek() != Some(&Token::Eq) {
                    return Err(self.error_here(
                        "expected `=` — a term by itself is not a claim (claims are \
                         predications, equalities, or combinations of them)",
                    ));
                }
                self.pos += 1;
                let rhs = self.parse_term()?;
                Ok(Claim::Equality(lhs, rhs))
            }
        }
    }

    // ── predications ──

    fn parse_predication(&mut self) -> Result<Predication, ParseError> {
        let (pred, pred_span) = match self.advance() {
            Some((Token::Ident(name), span)) => (name, span),
            other => unreachable!("parse_predication called off an ident: {other:?}"),
        };
        if self.peek() != Some(&Token::LParen) {
            return Err(self.error_at(
                pred_span.start,
                format!(
                    "a bare word is not a claim — predications need an argument list: \
                     `{pred}(…)` (use `()` for the observative)"
                ),
            ));
        }
        self.pos += 1; // (

        let mut args: Vec<Arg> = Vec::new();
        let mut seen_named = false;
        if self.peek() != Some(&Token::RParen) {
            loop {
                let arg_at = self.offset();
                let label = if let (Some(Token::Ident(_)), Some(Token::Colon)) =
                    (self.peek(), self.peek_second())
                {
                    let Some((Token::Ident(label), _)) = self.advance() else {
                        unreachable!()
                    };
                    self.pos += 1; // :
                    Some(label)
                } else {
                    None
                };
                if label.is_some() {
                    seen_named = true;
                } else if seen_named {
                    return Err(self.error_at(
                        arg_at,
                        "positional arguments must come before named arguments \
                         (SURFACE_SYNTAX §5)",
                    ));
                }
                let term = self.parse_term()?;
                args.push(Arg { label, term });
                if !self.eat(&Token::Comma) {
                    break;
                }
            }
        }
        let rparen = self.expect(&Token::RParen, "`)` to close the argument list")?;
        Ok(Predication {
            pred,
            args,
            span: pred_span.start..rparen.end,
        })
    }

    // ── terms ──

    fn parse_term(&mut self) -> Result<Term, ParseError> {
        let key = |k: KeyTerm| Term::Key(k);
        let term = match self.peek() {
            Some(Token::Underscore) => Term::Unspecified,
            Some(Token::Question) => Term::Witness,
            Some(Token::Number(n)) => Term::Number(*n),
            Some(Token::Str(s)) => Term::Str(s.clone()),
            Some(Token::Var(v)) => Term::Var(v.clone()),
            Some(Token::Name(n)) => Term::Name(n.clone()),
            Some(Token::Me) => key(KeyTerm::Me),
            Some(Token::You) => key(KeyTerm::You),
            Some(Token::We) => key(KeyTerm::We),
            Some(Token::WeAll) => key(KeyTerm::WeAll),
            Some(Token::WeOthers) => key(KeyTerm::WeOthers),
            Some(Token::YouAll) => key(KeyTerm::YouAll),
            Some(Token::This) => key(KeyTerm::This),
            Some(Token::That) => key(KeyTerm::That),
            Some(Token::Yonder) => key(KeyTerm::Yonder),
            Some(Token::ItA) => key(KeyTerm::ItA),
            Some(Token::ItE) => key(KeyTerm::ItE),
            Some(Token::ItI) => key(KeyTerm::ItI),
            Some(Token::ItO) => key(KeyTerm::ItO),
            Some(Token::ItU) => key(KeyTerm::ItU),
            Some(Token::It) => key(KeyTerm::It),
            Some(Token::Slot) => key(KeyTerm::Slot),
            Some(Token::Some | Token::The | Token::Every | Token::Exactly | Token::No) => {
                return self.parse_det_phrase();
            }
            _ => return Err(self.error_here("expected a term")),
        };
        self.pos += 1;
        Ok(term)
    }

    /// Determiner phrase (`no X` folds to `exactly 0 X` here — the spec
    /// defines it as pure sugar).
    fn parse_det_phrase(&mut self) -> Result<Term, ParseError> {
        let det = match self.advance() {
            Some((Token::Some, _)) => Det::Some,
            Some((Token::The, _)) => Det::The,
            Some((Token::Every, _)) => {
                if self.eat(&Token::The) {
                    Det::EveryThe
                } else {
                    Det::Every
                }
            }
            Some((Token::No, _)) => Det::Exactly(0),
            Some((Token::Exactly, _)) => {
                let n = self.parse_exact_count()?;
                if self.eat(&Token::The) {
                    Det::ExactlyThe(n)
                } else {
                    Det::Exactly(n)
                }
            }
            other => unreachable!("parse_det_phrase called off a determiner: {other:?}"),
        };
        let restr = self.parse_restr()?;
        Ok(Term::Det { det, restr })
    }

    /// The `N` of `exactly N`: an integer literal, digits only (spec `Nat` —
    /// the SOURCE must not contain `.`), within u32.
    fn parse_exact_count(&mut self) -> Result<u32, ParseError> {
        match self.peek() {
            Some(Token::Number(_)) => {
                let (_, span) = self.advance().unwrap();
                let slice = &self.input[span.clone()];
                if slice.contains('.') {
                    return Err(self.error_at(
                        span.start,
                        format!("`exactly` needs a whole number of things, found `{slice}`"),
                    ));
                }
                slice.parse::<u32>().map_err(|_| {
                    self.error_at(
                        span.start,
                        format!(
                            "exact count `{slice}` exceeds the supported range (0..={})",
                            u32::MAX
                        ),
                    )
                })
            }
            _ => Err(self.error_here("expected a count after `exactly`")),
        }
    }

    /// Restrictor — CORE PROFILE: a single predicate word. (Tanru, `.label`
    /// selectors, linked args, and `where`/`also` clauses extend this in the
    /// parser-completion bullet.)
    fn parse_restr(&mut self) -> Result<Restr, ParseError> {
        match self.peek() {
            Some(Token::Ident(_)) => {
                let Some((Token::Ident(pred), span)) = self.advance() else {
                    unreachable!()
                };
                Ok(Restr {
                    pred,
                    span: span.clone(),
                })
            }
            _ => Err(self.error_here(
                "expected a restrictor predicate after the determiner (e.g. `some dog`)",
            )),
        }
    }
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
        // Statement spans cover source text through the terminating dot.
        assert_eq!(&input[statements[0].span.clone()], "person(Adam).");
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
        assert_eq!((e.line, e.column), (1, 1));
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
    fn structural_errors_are_positioned() {
        // Missing terminating dot.
        let e = err("goes(me)");
        assert!(e.message.contains('.'), "{e}");
        // A bare word is not a claim.
        let e = err("dog.");
        assert!(e.message.contains("argument list"), "{e}");
        // A determiner phrase alone is a term, not a claim (block form is a
        // later bullet).
        let e = err("every dog.");
        assert!(e.message.contains("not a claim"), "{e}");
        // Unterminated argument list.
        let e = err("goes(me");
        assert!(e.message.contains(")"), "{e}");
    }

    #[test]
    fn lex_errors_surface_positioned() {
        let e = err("goes(λ).");
        assert!(e.message.contains("unlexable"), "{e}");
        assert_eq!((e.line, e.column), (1, 6));
    }

    #[test]
    fn recovery_continues_after_broken_statement() {
        let (statements, errors) = parse_text_with_errors("dog(. person(Adam).");
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert_eq!(statements.len(), 1);
        assert!(matches!(&statements[0].claim, Claim::Predication(p) if p.pred == "person"));
    }
}
