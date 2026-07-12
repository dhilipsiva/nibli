//! Klaro token types (SURFACE_SYNTAX.md §2), produced by the Logos DFA engine.
//!
//! Lexing is MAXIMAL-MUNCH with exact-match keyword reservation: Logos always
//! prefers the longest match (`everyday` is one [`Token::Ident`], never
//! `every` + `day`), and on equal length a `#[token]` keyword outranks the
//! ident regex (`every` alone is [`Token::Every`]). The keyword set is
//! single-sourced in `klaro-dictionary/src/reserved.rs`; the [`KEYWORDS`]
//! table here is pinned to it, both directions, by an exhaustive unit test in
//! `lexer.rs` — adding a keyword in either place without the other fails the
//! suite.

use logos::Logos;

/// One Klaro token. Whitespace, `#` line comments, and non-nesting `/* */`
/// block comments are skipped. Anything unlexable (including any non-ASCII
/// character outside a string literal) is a positioned lex error — fail
/// closed, never guessed.
#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+")]
// `[^\n]*` is the dot-class logos warns about; it is newline-bounded here, so
// the greedy scan is one comment line at worst — opt in explicitly.
#[logos(skip(r"#[^\n]*", allow_greedy = true))]
// Non-nesting block comment (classic DFA form; `/* /* */` ends at the first `*/`).
#[logos(skip r"/\*[^*]*\*+([^/*][^*]*\*+)*/")]
pub enum Token {
    // ── Keywords (SURFACE_SYNTAX §2; single source: klaro-dictionary reserved.rs) ──
    #[token("all")]
    All,
    #[token("also")]
    Also,
    #[token("amount")]
    Amount,
    #[token("concept")]
    Concept,
    #[token("event")]
    Event,
    #[token("every")]
    Every,
    #[token("exactly")]
    Exactly,
    #[token("fact")]
    Fact,
    #[token("future")]
    Future,
    #[token("it")]
    It,
    #[token("it_a")]
    ItA,
    #[token("it_e")]
    ItE,
    #[token("it_i")]
    ItI,
    #[token("it_o")]
    ItO,
    #[token("it_u")]
    ItU,
    #[token("may")]
    May,
    #[token("me")]
    Me,
    #[token("must")]
    Must,
    #[token("no")]
    No,
    #[token("now")]
    Now,
    #[token("past")]
    Past,
    #[token("property")]
    Property,
    #[token("seeming")]
    Seeming,
    #[token("slot")]
    Slot,
    #[token("some")]
    Some,
    #[token("that")]
    That,
    #[token("the")]
    The,
    #[token("this")]
    This,
    #[token("via")]
    Via,
    #[token("we")]
    We,
    #[token("we_all")]
    WeAll,
    #[token("we_others")]
    WeOthers,
    #[token("where")]
    Where,
    #[token("yonder")]
    Yonder,
    #[token("you")]
    You,
    #[token("you_all")]
    YouAll,

    // ── Identifier classes ──
    /// Predicate / label word: `[a-z][a-z0-9_]*` (keywords excluded by priority).
    #[regex(r"[a-z][a-z0-9_]*", |lex| lex.slice().to_owned())]
    Ident(String),

    /// Rigid name (la): `[A-Z][A-Za-z0-9_]*` — case is the sigil.
    #[regex(r"[A-Z][A-Za-z0-9_]*", |lex| lex.slice().to_owned())]
    Name(String),

    /// Logic variable `$x` — payload excludes the sigil.
    #[regex(r"\$[a-z][a-z0-9_]*", |lex| lex.slice()[1..].to_owned())]
    Var(String),

    // ── Literals ──
    /// Unsigned decimal literal; maximal munch keeps `2.5` one token while
    /// `f(2).` still ends with the statement dot. Non-finite (overflowing)
    /// values are a lex error — fail closed, matching the spec's
    /// "overflow = parse error".
    #[regex(r"[0-9]+(\.[0-9]+)?", |lex| lex.slice().parse::<f64>().ok().filter(|f| f.is_finite()))]
    Number(f64),

    /// String literal with `\"` and `\\` escapes (any other escape is a lex
    /// error). May carry arbitrary UTF-8 — the ASCII-only rule applies to
    /// syntax, not string payloads (SURFACE_SYNTAX §9). Payload is unescaped.
    #[regex(r#""([^"\\\n]|\\.)*""#, unescape)]
    Str(String),

    // ── Sigil terms ──
    /// `?` — anonymous witness (ma).
    #[token("?")]
    Question,
    /// `_` — explicit unspecified place (zo'e).
    #[token("_")]
    Underscore,

    // ── Punctuation / operators ──
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    /// Statement terminator AND the place-selector separator (`loves.loved`);
    /// the parser disambiguates by position. Never part of a `Number` thanks
    /// to maximal munch.
    #[token(".")]
    Dot,
    /// `=` — du identity (binary only, enforced by the parser).
    #[token("=")]
    Eq,
    /// `->` — implication (right-assoc).
    #[token("->")]
    Arrow,
    /// `<->` — biconditional.
    #[token("<->")]
    Iff,
    #[token("&")]
    And,
    #[token("|")]
    Or,
    #[token("^")]
    Xor,
    #[token("~")]
    Tilde,
    /// `+` — zei compound glue (`a+b`).
    #[token("+")]
    Plus,
}

/// Every keyword spelling and its token — the lexer-side mirror of
/// `klaro_dictionary::reserved::RESERVED_WORDS`, pinned to it (both
/// directions, exact count) by `lexer::tests::keyword_set_matches_reserved_words`.
pub const KEYWORDS: &[(&str, Token)] = &[
    ("all", Token::All),
    ("also", Token::Also),
    ("amount", Token::Amount),
    ("concept", Token::Concept),
    ("event", Token::Event),
    ("every", Token::Every),
    ("exactly", Token::Exactly),
    ("fact", Token::Fact),
    ("future", Token::Future),
    ("it", Token::It),
    ("it_a", Token::ItA),
    ("it_e", Token::ItE),
    ("it_i", Token::ItI),
    ("it_o", Token::ItO),
    ("it_u", Token::ItU),
    ("may", Token::May),
    ("me", Token::Me),
    ("must", Token::Must),
    ("no", Token::No),
    ("now", Token::Now),
    ("past", Token::Past),
    ("property", Token::Property),
    ("seeming", Token::Seeming),
    ("slot", Token::Slot),
    ("some", Token::Some),
    ("that", Token::That),
    ("the", Token::The),
    ("this", Token::This),
    ("via", Token::Via),
    ("we", Token::We),
    ("we_all", Token::WeAll),
    ("we_others", Token::WeOthers),
    ("where", Token::Where),
    ("yonder", Token::Yonder),
    ("you", Token::You),
    ("you_all", Token::YouAll),
];

/// Unescape a string literal body; `None` (= lex error) on any escape other
/// than `\"` or `\\`.
fn unescape(lex: &mut logos::Lexer<Token>) -> Option<String> {
    let slice = lex.slice();
    let inner = &slice[1..slice.len() - 1];
    let mut out = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('"') => out.push('"'),
                Some('\\') => out.push('\\'),
                _ => return None,
            }
        } else {
            out.push(c);
        }
    }
    Some(out)
}
