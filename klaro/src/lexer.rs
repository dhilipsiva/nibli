//! Klaro lexer driver: token stream + positioned, fail-closed errors.
//!
//! Mirrors gerna's `tokenize_with_errors` contract: the full input is always
//! scanned (errors don't stop the stream — the parser layer decides to fail
//! closed), adjacent unlexable characters coalesce into one error run (Logos
//! reports them char by char), and byte spans convert to 1-based line/column
//! via [`line_col`].

use std::ops::Range;

use logos::Logos;

use crate::token::Token;

/// One unlexable run, as byte offsets into the input. This covers every
/// fail-closed lexical class: non-ASCII outside strings, unterminated strings
/// and block comments, unknown escapes, non-finite numbers, stray operators
/// (`<-`, lone `-`), and `$`-vars without a lowercase head.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexError {
    pub start: usize,
    pub end: usize,
}

impl LexError {
    /// Human-readable message with a 1-based line:column position.
    pub fn message(&self, input: &str) -> String {
        let (line, column) = line_col(input, self.start);
        let run = input.get(self.start..self.end).unwrap_or("");
        format!("unlexable input {run:?} at line {line}, column {column}")
    }
}

/// 1-based (line, column) of a byte offset. Columns count CHARACTERS, not
/// bytes (string literals may carry multibyte UTF-8).
pub fn line_col(input: &str, offset: usize) -> (u32, u32) {
    let prefix = &input[..offset.min(input.len())];
    let line = prefix.bytes().filter(|&b| b == b'\n').count() as u32 + 1;
    let column = match prefix.rfind('\n') {
        Some(nl) => prefix[nl + 1..].chars().count() as u32 + 1,
        None => prefix.chars().count() as u32 + 1,
    };
    (line, column)
}

/// Lex the whole input. Every token carries its byte span; unlexable runs are
/// collected (coalesced) rather than aborting the scan.
pub fn tokenize_with_errors(input: &str) -> (Vec<(Token, Range<usize>)>, Vec<LexError>) {
    let mut lex = Token::lexer(input);
    let mut tokens = Vec::new();
    let mut errors: Vec<LexError> = Vec::new();

    while let Some(result) = lex.next() {
        match result {
            Ok(token) => tokens.push((token, lex.span())),
            Err(()) => {
                let span = lex.span();
                match errors.last_mut() {
                    Some(last) if last.end == span.start => last.end = span.end,
                    _ => errors.push(LexError {
                        start: span.start,
                        end: span.end,
                    }),
                }
            }
        }
    }
    (tokens, errors)
}

/// FAIL CLOSED: tokens, or the FIRST lex error. The drop-in analog of the
/// checked entry the parser will build on.
pub fn tokenize(input: &str) -> Result<Vec<(Token, Range<usize>)>, LexError> {
    let (tokens, errors) = tokenize_with_errors(input);
    match errors.into_iter().next() {
        None => Ok(tokens),
        Some(e) => Err(e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::KEYWORDS;

    /// Tokens only, asserting a clean lex.
    fn toks(input: &str) -> Vec<Token> {
        let (tokens, errors) = tokenize_with_errors(input);
        assert!(
            errors.is_empty(),
            "unexpected lex errors for {input:?}: {errors:?}"
        );
        tokens.into_iter().map(|(t, _)| t).collect()
    }

    fn ident(s: &str) -> Token {
        Token::Ident(s.to_owned())
    }

    // ── The keyword-boundary defect class from the design review ──

    #[test]
    fn maximal_munch_never_splits_identifiers() {
        // `everyday` is ONE ident, never `every` + `day`; same for the other
        // review counterexamples.
        assert_eq!(toks("everyday"), vec![ident("everyday")]);
        assert_eq!(toks("theory"), vec![ident("theory")]);
        assert_eq!(toks("nowhere"), vec![ident("nowhere")]);
        assert_eq!(toks("someone"), vec![ident("someone")]);
        assert_eq!(toks("itchy"), vec![ident("itchy")]);
        assert_eq!(toks("mean"), vec![ident("mean")]);
        assert_eq!(toks("wealth"), vec![ident("wealth")]);
    }

    #[test]
    fn exact_keywords_win_equal_length_ties() {
        assert_eq!(toks("every"), vec![Token::Every]);
        assert_eq!(toks("the"), vec![Token::The]);
        assert_eq!(toks("now"), vec![Token::Now]);
        assert_eq!(toks("it"), vec![Token::It]);
        assert_eq!(toks("every dog"), vec![Token::Every, ident("dog")]);
    }

    #[test]
    fn underscored_keywords_lex_whole() {
        // The `you`/`you_all` ordered-choice bug from the review is impossible
        // under maximal munch — pin it anyway.
        assert_eq!(toks("you_all"), vec![Token::YouAll]);
        assert_eq!(toks("you"), vec![Token::You]);
        assert_eq!(toks("we_all"), vec![Token::WeAll]);
        assert_eq!(toks("we_others"), vec![Token::WeOthers]);
        assert_eq!(toks("we"), vec![Token::We]);
        assert_eq!(toks("it_a"), vec![Token::ItA]);
        // One char longer -> plain idents again.
        assert_eq!(toks("you_all_x"), vec![ident("you_all_x")]);
        assert_eq!(toks("it_ab"), vec![ident("it_ab")]);
        assert_eq!(toks("we_all2"), vec![ident("we_all2")]);
    }

    #[test]
    fn keyword_set_matches_reserved_words() {
        // BOTH DIRECTIONS against the single source. Adding a keyword to
        // reserved.rs without a token (or vice versa) fails here.
        let reserved = klaro_dictionary::reserved::RESERVED_WORDS;
        assert_eq!(
            KEYWORDS.len(),
            reserved.len(),
            "KEYWORDS and RESERVED_WORDS diverge in size"
        );
        for (spelling, token) in KEYWORDS {
            assert!(
                reserved.contains(spelling),
                "lexer keyword {spelling:?} is not in RESERVED_WORDS"
            );
            assert_eq!(
                toks(spelling),
                vec![token.clone()],
                "keyword {spelling:?} does not lex to its token"
            );
        }
        for word in reserved {
            assert!(
                !matches!(toks(word).as_slice(), [Token::Ident(_)]),
                "reserved word {word:?} lexes as a plain ident — missing keyword token"
            );
        }
    }

    // ── Numbers, dots, operators ──

    #[test]
    fn number_maximal_munch_vs_statement_dot() {
        assert_eq!(
            toks("f(2.5)."),
            vec![
                ident("f"),
                Token::LParen,
                Token::Number(2.5),
                Token::RParen,
                Token::Dot
            ]
        );
        assert_eq!(
            toks("f(2)."),
            vec![
                ident("f"),
                Token::LParen,
                Token::Number(2.0),
                Token::RParen,
                Token::Dot
            ]
        );
        // No digit after the dot -> the dot is a separate token.
        assert_eq!(
            toks("2.x"),
            vec![Token::Number(2.0), Token::Dot, ident("x")]
        );
    }

    #[test]
    fn place_selector_dots_and_zei_plus() {
        assert_eq!(
            toks("loves.loved"),
            vec![ident("loves"), Token::Dot, ident("loved")]
        );
        assert_eq!(
            toks("computer+user"),
            vec![ident("computer"), Token::Plus, ident("user")]
        );
    }

    #[test]
    fn arrows_and_operators() {
        assert_eq!(
            toks("a -> b <-> c"),
            vec![ident("a"), Token::Arrow, ident("b"), Token::Iff, ident("c")]
        );
        // Idents cannot contain `-`, so `a->b` needs no whitespace.
        assert_eq!(toks("a->b"), vec![ident("a"), Token::Arrow, ident("b")]);
        assert_eq!(
            toks("(){}[],:=~^&|+?_"),
            vec![
                Token::LParen,
                Token::RParen,
                Token::LBrace,
                Token::RBrace,
                Token::LBracket,
                Token::RBracket,
                Token::Comma,
                Token::Colon,
                Token::Eq,
                Token::Tilde,
                Token::Xor,
                Token::And,
                Token::Or,
                Token::Plus,
                Token::Question,
                Token::Underscore
            ]
        );
    }

    #[test]
    fn stray_operator_fragments_fail_closed() {
        let (_, errors) = tokenize_with_errors("a <- b");
        assert!(!errors.is_empty(), "`<-` must not lex");
        let (_, errors) = tokenize_with_errors("a - b");
        assert!(!errors.is_empty(), "lone `-` must not lex");
    }

    // ── Names and variables ──

    #[test]
    fn names_and_vars() {
        assert_eq!(
            toks("Adam Djan_Smit R2"),
            vec![
                Token::Name("Adam".into()),
                Token::Name("Djan_Smit".into()),
                Token::Name("R2".into())
            ]
        );
        assert_eq!(
            toks("$x $abc1"),
            vec![Token::Var("x".into()), Token::Var("abc1".into())]
        );
        // `$` must head a lowercase ident.
        let (_, errors) = tokenize_with_errors("$X");
        assert!(!errors.is_empty());
    }

    // ── Strings ──

    #[test]
    fn strings_escapes_and_utf8_payloads() {
        assert_eq!(
            toks(r#""any text here""#),
            vec![Token::Str("any text here".into())]
        );
        assert_eq!(
            toks(r#""he said \"hi\" \\ done""#),
            vec![Token::Str(r#"he said "hi" \ done"#.into())]
        );
        // Non-ASCII is legal INSIDE strings (payloads are data, not syntax).
        assert_eq!(toks("\"λ café\""), vec![Token::Str("λ café".into())]);
    }

    #[test]
    fn bad_strings_fail_closed() {
        let (_, errors) = tokenize_with_errors(r#""unknown \q escape""#);
        assert!(!errors.is_empty(), "unknown escape must be a lex error");
        let (_, errors) = tokenize_with_errors("\"unterminated");
        assert!(
            !errors.is_empty(),
            "unterminated string must be a lex error"
        );
        let (_, errors) = tokenize_with_errors("\"no\nnewlines\"");
        assert!(
            !errors.is_empty(),
            "raw newline inside a string must be a lex error"
        );
    }

    // ── ASCII-only syntax ──

    #[test]
    fn non_ascii_outside_strings_is_a_positioned_error() {
        let input = "goes(λµ).";
        let (tokens, errors) = tokenize_with_errors(input);
        assert_eq!(errors.len(), 1, "adjacent bad chars coalesce into one run");
        let e = &errors[0];
        assert_eq!(&input[e.start..e.end], "λµ");
        let (line, col) = line_col(input, e.start);
        assert_eq!((line, col), (1, 6));
        assert!(e.message(input).contains("line 1, column 6"));
        // The rest of the stream still lexed (errors never truncate the scan).
        assert!(tokens.iter().any(|(t, _)| *t == Token::Dot));
    }

    #[test]
    fn line_col_counts_chars_after_newlines() {
        let input = "goes().\n eats(\"é\") λ";
        let (_, errors) = tokenize_with_errors(input);
        assert_eq!(errors.len(), 1);
        let (line, col) = line_col(input, errors[0].start);
        assert_eq!(line, 2);
        assert_eq!(col, 12, "column counts characters, not bytes");
    }

    // ── Comments ──

    #[test]
    fn comments_are_skipped() {
        assert_eq!(
            toks("# header\ngoes(). # trailing"),
            vec![ident("goes"), Token::LParen, Token::RParen, Token::Dot]
        );
        assert_eq!(
            toks("/* block\n comment */ goes()."),
            vec![ident("goes"), Token::LParen, Token::RParen, Token::Dot]
        );
    }

    #[test]
    fn block_comments_do_not_nest() {
        // `/* /* */` closes at the FIRST `*/`; the trailing `*/` is then a
        // stray-operator lex error (fail closed, never silently swallowed).
        let (tokens, errors) = tokenize_with_errors("/* /* */ goes(). */");
        assert!(
            tokens
                .iter()
                .any(|(t, _)| matches!(t, Token::Ident(i) if i == "goes"))
        );
        assert!(!errors.is_empty(), "the orphaned */ must not lex");
    }

    #[test]
    fn unterminated_block_comment_fails_closed() {
        let (_, errors) = tokenize_with_errors("goes(). /* never closed");
        assert!(!errors.is_empty());
    }

    // ── Numbers: overflow fails closed ──

    #[test]
    fn non_finite_numbers_fail_closed() {
        // ~400 digits overflows f64 to infinity -> lex error, not Number(inf).
        let big = "9".repeat(400);
        let (_, errors) = tokenize_with_errors(&big);
        assert!(!errors.is_empty(), "non-finite number must be a lex error");
    }

    // ── A realistic statement end-to-end ──

    #[test]
    fn full_statement_shapes() {
        assert_eq!(
            toks("obligated(every person where ~approves, duty: event { removes() })."),
            vec![
                ident("obligated"),
                Token::LParen,
                Token::Every,
                ident("person"),
                Token::Where,
                Token::Tilde,
                ident("approves"),
                Token::Comma,
                ident("duty"),
                Token::Colon,
                Token::Event,
                Token::LBrace,
                ident("removes"),
                Token::LParen,
                Token::RParen,
                Token::RBrace,
                Token::RParen,
                Token::Dot
            ]
        );
        assert_eq!(
            toks("all $x: dog($x) -> animal($x)."),
            vec![
                Token::All,
                Token::Var("x".into()),
                Token::Colon,
                ident("dog"),
                Token::LParen,
                Token::Var("x".into()),
                Token::RParen,
                Token::Arrow,
                ident("animal"),
                Token::LParen,
                Token::Var("x".into()),
                Token::RParen,
                Token::Dot
            ]
        );
    }
}
