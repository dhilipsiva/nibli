//! Lightweight nibli KR lexer for syntax highlighting.
//!
//! Not a full parse — a best-effort token stream for editors and the REPL.
//! Keywords come from [`nibli_lexicon::reserved`] (single source). Used by
//! nibli-host / nibli (reedline) and nibli-ui (CSS spans).

use nibli_lexicon::reserved::is_reserved;

/// Highlight token class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    /// Spaces, tabs, newlines.
    Whitespace,
    /// `#` to end of line (corpus comments).
    Comment,
    /// Reserved word (`every`, `some`, `must`, …).
    Keyword,
    /// Lowercase predicate / label / relation piece (`dog`, `owns`, …).
    Predicate,
    /// Capitalized constant name (`Ara`, `Adam`, `Paris`).
    Name,
    /// `$var` logic variable.
    Variable,
    /// Numeric literal.
    Number,
    /// Logical / syntactic operators (`&`, `|`, `~`, `=`, `->`, `+`, …).
    Operator,
    /// Brackets and separators (`( ) { } [ ] , . :`).
    Punctuation,
    /// Unclassified remainder (kept visible, neutral style).
    Other,
}

impl TokenKind {
    /// CSS class suffix for the UI: `tok-{name}` (e.g. `tok-keyword`).
    pub fn css_class(self) -> &'static str {
        match self {
            TokenKind::Whitespace => "tok-ws",
            TokenKind::Comment => "tok-comment",
            TokenKind::Keyword => "tok-keyword",
            TokenKind::Predicate => "tok-predicate",
            TokenKind::Name => "tok-name",
            TokenKind::Variable => "tok-variable",
            TokenKind::Number => "tok-number",
            TokenKind::Operator => "tok-operator",
            TokenKind::Punctuation => "tok-punct",
            TokenKind::Other => "tok-other",
        }
    }
}

/// One token: kind + borrowed slice of the source.
pub type Token<'a> = (TokenKind, &'a str);

/// Lex `src` into a contiguous cover of tokens (no gaps, no overlap).
pub fn lex(src: &str) -> Vec<Token<'_>> {
    let bytes = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let start = i;
        let b = bytes[i];

        // Whitespace
        if b.is_ascii_whitespace() {
            i += 1;
            while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                i += 1;
            }
            out.push((TokenKind::Whitespace, &src[start..i]));
            continue;
        }

        // Line comment
        if b == b'#' {
            i += 1;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            out.push((TokenKind::Comment, &src[start..i]));
            continue;
        }

        // Variable: $ident
        if b == b'$' {
            i += 1;
            while i < bytes.len() && is_ident_continue(bytes[i]) {
                i += 1;
            }
            out.push((TokenKind::Variable, &src[start..i]));
            continue;
        }

        // Number (integer / float, optional leading sign only if followed by digit)
        if b.is_ascii_digit()
            || ((b == b'-' || b == b'+')
                && i + 1 < bytes.len()
                && bytes[i + 1].is_ascii_digit()
                && !is_ident_continue_prev(bytes, i))
        {
            if b == b'-' || b == b'+' {
                i += 1;
            }
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            if i < bytes.len()
                && bytes[i] == b'.'
                && i + 1 < bytes.len()
                && bytes[i + 1].is_ascii_digit()
            {
                i += 1;
                while i < bytes.len() && bytes[i].is_ascii_digit() {
                    i += 1;
                }
            }
            out.push((TokenKind::Number, &src[start..i]));
            continue;
        }

        // Multi-char operators first
        if b == b'-' && i + 1 < bytes.len() && bytes[i + 1] == b'>' {
            i += 2;
            out.push((TokenKind::Operator, &src[start..i]));
            continue;
        }
        if b == b'=' && i + 1 < bytes.len() && bytes[i + 1] == b'=' {
            // not a KR operator, but style as operator if typed
            i += 2;
            out.push((TokenKind::Operator, &src[start..i]));
            continue;
        }

        // Single-char operators
        if matches!(
            b,
            b'&' | b'|' | b'~' | b'=' | b'+' | b'!' | b'^' | b'*' | b'/' | b'%' | b'<' | b'>'
        ) {
            i += 1;
            out.push((TokenKind::Operator, &src[start..i]));
            continue;
        }

        // Punctuation
        if matches!(
            b,
            b'(' | b')' | b'{' | b'}' | b'[' | b']' | b',' | b'.' | b':' | b';' | b'@'
        ) {
            i += 1;
            out.push((TokenKind::Punctuation, &src[start..i]));
            continue;
        }

        // Identifiers: Name (A…) or predicate (a…)
        if b.is_ascii_alphabetic() || b == b'_' {
            i += 1;
            while i < bytes.len() && is_ident_continue(bytes[i]) {
                i += 1;
            }
            let word = &src[start..i];
            let kind = if word.starts_with(|c: char| c.is_ascii_uppercase()) {
                TokenKind::Name
            } else if is_reserved(word) {
                TokenKind::Keyword
            } else {
                TokenKind::Predicate
            };
            out.push((kind, word));
            continue;
        }

        // Fallback: one char
        i += 1;
        out.push((TokenKind::Other, &src[start..i]));
    }
    out
}

fn is_ident_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// True when byte before `i` is an identifier continue (so `-` is binary minus, not number sign).
fn is_ident_continue_prev(bytes: &[u8], i: usize) -> bool {
    i > 0 && is_ident_continue(bytes[i - 1])
}

/// Classify a full REPL input line for highlighting: optional `??` / `?` /
/// `:`-command prefix, then KR body.
pub fn lex_repl_line(line: &str) -> Vec<Token<'_>> {
    if line.is_empty() {
        return Vec::new();
    }
    if let Some(rest) = line.strip_prefix("??") {
        let mut v = vec![(TokenKind::Operator, &line[..2])];
        v.extend(lex(rest));
        return v;
    }
    if let Some(rest) = line.strip_prefix('?') {
        let mut v = vec![(TokenKind::Operator, &line[..1])];
        v.extend(lex(rest));
        return v;
    }
    if line.starts_with(':') {
        // :command [args…] — highlight the colon-command as keyword, rest as KR/args
        let bytes = line.as_bytes();
        let mut i = 1;
        while i < bytes.len() && is_ident_continue(bytes[i]) {
            i += 1;
        }
        let mut v = vec![(TokenKind::Keyword, &line[..i])];
        if i < line.len() {
            v.extend(lex(&line[i..]));
        }
        return v;
    }
    lex(line)
}

/// Split into `(css_class, text)` spans for UI rendering (whitespace kept).
pub fn css_spans(src: &str) -> Vec<(&'static str, String)> {
    lex(src)
        .into_iter()
        .map(|(k, t)| (k.css_class(), t.to_string()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> Vec<TokenKind> {
        lex(src).into_iter().map(|(k, _)| k).collect()
    }

    fn joined(src: &str) -> String {
        lex(src).into_iter().map(|(_, t)| t).collect()
    }

    #[test]
    fn cover_is_lossless() {
        let samples = [
            "",
            "dog(Adam).\n",
            "animal(every dog).\n# comment\n",
            "owns(Ara, some data).",
            "? free(Ara).",
            "exactly 0 person.",
            "past goes(me, some market).",
            "computer+user(Ara, this, some purpose).",
            "all $x, $y: dog($x) & likes($x, $y).",
            "obligated(every person where owns(it, some data), event { permits() }).",
        ];
        for s in samples {
            assert_eq!(joined(s), s, "lossless cover failed for {s:?}");
        }
    }

    #[test]
    fn keywords_and_names() {
        let toks = lex("animal(every dog).");
        assert!(
            toks.iter()
                .any(|(k, t)| *k == TokenKind::Keyword && *t == "every")
        );
        assert!(
            toks.iter()
                .any(|(k, t)| *k == TokenKind::Predicate && *t == "animal")
        );
        assert!(
            toks.iter()
                .any(|(k, t)| *k == TokenKind::Predicate && *t == "dog")
        );
        let toks = lex("dog(Ara).");
        assert!(
            toks.iter()
                .any(|(k, t)| *k == TokenKind::Name && *t == "Ara")
        );
    }

    #[test]
    fn variable_and_comment() {
        assert!(lex("$x").iter().any(|(k, _)| *k == TokenKind::Variable));
        assert!(lex("# hi\n").iter().any(|(k, _)| *k == TokenKind::Comment));
        assert_eq!(kinds("12.5")[0], TokenKind::Number);
    }

    #[test]
    fn repl_prefixes() {
        let t = lex_repl_line("? dog(Adam).");
        assert_eq!(t[0], (TokenKind::Operator, "?"));
        let t = lex_repl_line("?? free(?).");
        assert_eq!(t[0], (TokenKind::Operator, "??"));
        let t = lex_repl_line(":load foo.nibli");
        assert_eq!(t[0].0, TokenKind::Keyword);
        assert!(t[0].1.starts_with(":load"));
    }

    #[test]
    fn css_class_names_stable() {
        assert_eq!(TokenKind::Keyword.css_class(), "tok-keyword");
        assert_eq!(TokenKind::Name.css_class(), "tok-name");
    }
}
