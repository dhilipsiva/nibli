//! Reedline syntax highlighter for nibli KR (+ REPL prefixes).
//!
//! Shared token classes from [`nibli_kr::highlight`]; colors match nibli-host.

use nibli_kr::highlight::{TokenKind, lex_repl_line};
use nu_ansi_term::{Color, Style};
use reedline::{Highlighter, StyledText};

/// Live-buffer highlighter for the native `nibli` debug REPL.
pub struct KrHighlighter;

impl Highlighter for KrHighlighter {
    fn highlight(&self, line: &str, _cursor: usize) -> StyledText {
        let mut styled = StyledText::new();
        if line.is_empty() {
            styled.push((Style::new(), String::new()));
            return styled;
        }
        for (kind, text) in lex_repl_line(line) {
            styled.push((style_for(kind), text.to_string()));
        }
        styled
    }
}

fn style_for(kind: TokenKind) -> Style {
    match kind {
        TokenKind::Whitespace => Style::new(),
        TokenKind::Comment => Style::new().fg(Color::DarkGray).italic(),
        TokenKind::Keyword => Style::new().fg(Color::LightRed).bold(),
        TokenKind::Predicate => Style::new().fg(Color::LightPurple),
        TokenKind::Name => Style::new().fg(Color::LightGreen),
        TokenKind::Variable => Style::new().fg(Color::LightCyan),
        TokenKind::Number => Style::new().fg(Color::Yellow),
        TokenKind::Operator => Style::new().fg(Color::LightYellow),
        TokenKind::Punctuation => Style::new().fg(Color::DarkGray),
        TokenKind::Other => Style::new().fg(Color::White),
    }
}
