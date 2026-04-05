//! Recursive descent parser for Lojban.
//!
//! Operates on the preprocessed [`NormalizedToken`] stream (after lexing and
//! metalinguistic resolution). Produces an arena-allocated AST with per-sentence
//! error recovery (on failure, skips to next `.i` boundary and continues parsing).
//!
//! # Grammar (subset of CLL, expanded incrementally)
//!
//! ```text
//! text        → sentence (.i sentence)*
//! sentence    → tense? terms? cu? tense? selbri tail? vau?
//! tail        → terms
//! terms       → term+
//! term        → place_tag sumti | modal_tag sumti | sumti
//! modal_tag   → bai_tag | fi'o selbri fe'u?
//! bai_tag     → ri'a | ni'i | mu'i | ki'u | pi'o | ba'i
//! sumti       → la_name | description | pro_sumti | quoted
//!              | sumti rel_clause
//! la_name     → la cmevla+
//! quantified_desc → su'o? PA* (lo|le) selbri ku?
//! description → ro? (lo|le) selbri ku?
//! rel_clause  → (poi|noi) sentence ku'o?
//! selbri      → na? selbri_conn
//! selbri_conn → selbri_2 ((je|ja|jo|ju) selbri_2)*
//! selbri_2    → conversion? tanru
//! tanru       → tanru_unit+   (right-grouping)
//! tanru_unit  → brivla | ke selbri ke'e? | tanru_unit be_clause
//! be_clause   → be sumti (bei sumti)* be'o?
//! brivla      → gismu | lujvo | compound
//! conversion  → se | te | ve | xe
//! place_tag   → fa | fe | fi | fo | fu
//! ```

use crate::ast::*;
use crate::lexer::LojbanToken;
use crate::preprocessor::NormalizedToken;
use bumpalo::Bump;

mod selbri;
mod sentence;
mod sumti;

/// Maximum recursion depth to prevent stack overflow on pathological input.
const MAX_DEPTH: usize = 64;

/// Parse error with line:column context.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub position: usize,
    pub line: u32,
    pub column: u32,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.column, self.message)
    }
}

/// Result of parsing: successfully parsed sentences + any per-sentence errors.
pub struct ParseResult<'arena> {
    pub parsed: ParsedText<'arena>,
    pub errors: Vec<ParseError>,
}

/// Recursive descent parser over the preprocessed token stream.
pub struct Parser<'a, 'arena> {
    tokens: &'a [NormalizedToken<'a>],
    pos: usize,
    depth: usize,
    original_input: &'a str,
    arena: &'arena Bump,
}

#[allow(dead_code)]
impl<'a, 'arena> Parser<'a, 'arena> {
    pub fn new(
        tokens: &'a [NormalizedToken<'a>],
        original_input: &'a str,
        arena: &'arena Bump,
    ) -> Self {
        Self {
            tokens,
            pos: 0,
            depth: 0,
            original_input,
            arena,
        }
    }

    // ─── Position helpers ────────────────────────────────────

    /// Derive the byte offset into original_input for the token at `idx`.
    fn byte_offset_of_token(&self, idx: usize) -> usize {
        if idx >= self.tokens.len() || self.original_input.is_empty() {
            return self.original_input.len();
        }
        let slice = match &self.tokens[idx] {
            NormalizedToken::Standard(_, s) => *s,
            NormalizedToken::Quoted(s) => *s,
            NormalizedToken::Glued(parts) => {
                if let Some(first) = parts.first() {
                    *first
                } else {
                    return self.original_input.len();
                }
            }
        };
        let base = self.original_input.as_ptr() as usize;
        let ptr = slice.as_ptr() as usize;
        if ptr >= base && ptr <= base + self.original_input.len() {
            ptr - base
        } else {
            // Token slice doesn't point into original_input (test constructors)
            0
        }
    }

    /// Compute 1-indexed (line, column) from a byte offset into original_input.
    fn line_col_at(&self, byte_offset: usize) -> (u32, u32) {
        let text = if byte_offset <= self.original_input.len() {
            &self.original_input[..byte_offset]
        } else {
            self.original_input
        };
        let line = text.bytes().filter(|&b| b == b'\n').count() as u32 + 1;
        let col = match text.rfind('\n') {
            Some(nl_pos) => (byte_offset - nl_pos - 1) as u32 + 1,
            None => byte_offset as u32 + 1,
        };
        (line, col)
    }

    // ─── Depth guard ──────────────────────────────────────────

    fn enter(&mut self) -> Result<(), ParseError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            Err(self.error("maximum nesting depth exceeded"))
        } else {
            Ok(())
        }
    }

    fn leave(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }

    // ─── Token inspection ─────────────────────────────────────

    fn at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn peek(&self) -> Option<&NormalizedToken<'a>> {
        self.tokens.get(self.pos)
    }

    fn peek_cmavo(&self) -> Option<&'a str> {
        match self.peek()? {
            NormalizedToken::Standard(LojbanToken::Cmavo, s) => Some(s),
            _ => None,
        }
    }

    fn peek_is_cmavo(&self, target: &str) -> bool {
        self.peek_cmavo().map_or(false, |s| s == target)
    }

    fn peek_is_any_cmavo(&self, targets: &[&str]) -> bool {
        self.peek_cmavo().map_or(false, |s| targets.contains(&s))
    }

    fn peek_is_gismu(&self) -> bool {
        matches!(
            self.peek(),
            Some(NormalizedToken::Standard(LojbanToken::Gismu, _))
                | Some(NormalizedToken::Standard(LojbanToken::Lujvo, _))
        )
    }

    fn peek_is_cmevla(&self) -> bool {
        matches!(
            self.peek(),
            Some(NormalizedToken::Standard(LojbanToken::Cmevla, _))
        )
    }

    fn advance(&mut self) -> Option<&NormalizedToken<'a>> {
        let t = self.tokens.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    /// Consume a specific cmavo if present. Returns true if consumed.
    fn eat_cmavo(&mut self, target: &str) -> bool {
        if self.peek_is_cmavo(target) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    /// Consume any of the given cmavo. Returns the matched one, or None.
    fn eat_any_cmavo(&mut self, targets: &[&str]) -> Option<String> {
        if let Some(s) = self.peek_cmavo() {
            if targets.contains(&s) {
                let owned = s.to_string();
                self.pos += 1;
                return Some(owned);
            }
        }
        None
    }

    /// Consume a Pause token if present.
    fn eat_pause(&mut self) -> bool {
        if matches!(
            self.peek(),
            Some(NormalizedToken::Standard(LojbanToken::Pause, _))
        ) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    /// Save position for backtracking.
    fn save(&self) -> usize {
        self.pos
    }

    /// Restore position for backtracking.
    fn restore(&mut self, pos: usize) {
        self.pos = pos;
    }

    /// Check if the current position is at a `.i` sentence separator.
    fn at_dot_i(&self) -> bool {
        if self.pos + 1 >= self.tokens.len() {
            return false;
        }
        matches!(
            (&self.tokens[self.pos], &self.tokens[self.pos + 1]),
            (
                NormalizedToken::Standard(LojbanToken::Pause, _),
                NormalizedToken::Standard(LojbanToken::Cmavo, "i")
            )
        )
    }

    /// Consume a `.i` sentence separator if present.
    fn eat_dot_i(&mut self) -> bool {
        if self.at_dot_i() {
            self.pos += 2;
            true
        } else {
            false
        }
    }

    /// Try to parse an afterthought sentence connective: [na] (je|ja|jo|ju) [nai]
    /// Called right after `.i` has been consumed. Returns the SentenceConnective
    /// or None (restoring position) if no connective follows.
    fn try_parse_afterthought_sentence_connective(&mut self) -> Option<SentenceConnective> {
        let saved = self.save();

        // Optional left negation: na
        let left_negated = self.eat_cmavo("na");

        // Try compound forms first (jenai, janai, jonai, junai)
        let (conn, right_negated) = if self.eat_cmavo("jenai") {
            (Connective::Je, true)
        } else if self.eat_cmavo("janai") {
            (Connective::Ja, true)
        } else if self.eat_cmavo("jonai") {
            (Connective::Jo, true)
        } else if self.eat_cmavo("junai") {
            (Connective::Ju, true)
        } else if self.eat_cmavo("je") {
            (Connective::Je, self.eat_cmavo("nai"))
        } else if self.eat_cmavo("ja") {
            (Connective::Ja, self.eat_cmavo("nai"))
        } else if self.eat_cmavo("jo") {
            (Connective::Jo, self.eat_cmavo("nai"))
        } else if self.eat_cmavo("ju") {
            (Connective::Ju, self.eat_cmavo("nai"))
        } else {
            // No connective found; backtrack (may have consumed "na")
            self.restore(saved);
            return None;
        };

        Some(SentenceConnective::Afterthought {
            left_negated,
            connective: conn,
            right_negated,
        })
    }

    /// Check if current token is a sentence boundary.
    fn at_sentence_boundary(&self) -> bool {
        if self.at_end() {
            return true;
        }
        if self.at_dot_i() {
            return true;
        }
        self.peek_is_any_cmavo(&["ku'o", "kei", "vau"])
    }

    /// Advance to the next `.i` boundary or end of tokens (error recovery).
    fn skip_to_next_dot_i(&mut self) {
        while !self.at_end() {
            if self.at_dot_i() {
                return; // Don't consume — the main loop will eat it
            }
            self.pos += 1;
        }
    }

    /// Parse all sentences with per-sentence error recovery.
    /// Successfully parsed sentences go into `parsed.sentences`;
    /// per-sentence errors go into `errors`.
    pub fn parse_text(&mut self) -> ParseResult<'arena> {
        let mut sentences = Vec::new();
        let mut errors = Vec::new();

        while self.eat_dot_i() || self.eat_pause() {}

        if self.at_end() {
            errors.push(self.error("empty input"));
            return ParseResult {
                parsed: ParsedText { sentences },
                errors,
            };
        }

        // First sentence
        match self.parse_sentence() {
            Ok(s) => sentences.push(s),
            Err(e) => {
                errors.push(e);
                self.skip_to_next_dot_i();
            }
        }

        loop {
            if !self.eat_dot_i() {
                while self.eat_pause() {}
                if !self.eat_dot_i() {
                    break;
                }
            }

            // Try afterthought sentence connective: .i [na] (je|ja|jo|ju) [nai]
            if let Some(conn) = self.try_parse_afterthought_sentence_connective() {
                while self.eat_pause() {}
                if self.at_end() {
                    errors.push(self.error("expected sentence after afterthought connective"));
                    break;
                }
                match self.parse_sentence() {
                    Ok(right) => {
                        if let Some(left) = sentences.pop() {
                            sentences.push(Sentence::Connected {
                                connective: conn,
                                left: self.arena.alloc(left),
                                right: self.arena.alloc(right),
                            });
                        } else {
                            // Left sentence had an error; push right as standalone
                            sentences.push(right);
                        }
                    }
                    Err(e) => {
                        errors.push(e);
                        self.skip_to_next_dot_i();
                    }
                }
                continue;
            }

            while self.eat_pause() {}
            if self.at_end() {
                break;
            }
            if self.at_dot_i() {
                continue;
            }

            match self.parse_sentence() {
                Ok(s) => sentences.push(s),
                Err(e) => {
                    errors.push(e);
                    self.skip_to_next_dot_i();
                }
            }
        }

        while self.eat_pause() {}

        if !self.at_end() {
            errors.push(self.error("unconsumed tokens remaining"));
        }

        ParseResult {
            parsed: ParsedText { sentences },
            errors,
        }
    }

    // ─── Error helpers ────────────────────────────────────────

    fn error(&self, message: &str) -> ParseError {
        let byte_off = if self.pos < self.tokens.len() {
            self.byte_offset_of_token(self.pos)
        } else if !self.tokens.is_empty() {
            let last = self.tokens.len() - 1;
            let off = self.byte_offset_of_token(last);
            let len = match &self.tokens[last] {
                NormalizedToken::Standard(_, s) => s.len(),
                NormalizedToken::Quoted(s) => s.len(),
                NormalizedToken::Glued(parts) => parts.iter().map(|p| p.len()).sum(),
            };
            off + len
        } else {
            0
        };
        let (line, column) = self.line_col_at(byte_off);
        ParseError {
            message: message.to_string(),
            position: self.pos,
            line,
            column,
        }
    }

}

// ─── Public entry point ───────────────────────────────────────────

pub fn parse_tokens_to_ast<'a, 'arena>(
    tokens: &[NormalizedToken<'a>],
    original_input: &'a str,
    arena: &'arena Bump,
) -> ParseResult<'arena> {
    let mut parser = Parser::new(tokens, original_input, arena);
    parser.parse_text()
}

// ─── Tests ────────────────────────────────────────────────────────


#[cfg(test)]
#[path = "grammar_tests.rs"]
mod tests;
