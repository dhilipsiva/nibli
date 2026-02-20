// parser/src/preprocessor.rs
//
// Consumes the raw lexical stream and resolves metalinguistic operations:
//   si  — erase preceding word
//   sa  — erase backward to matching class (degraded: no-op with warning)
//   su  — erase entire discourse
//   zo  — quote next word
//   zoi — quote delimited text
//   zei — glue adjacent words into compound

use crate::lexer::LojbanToken;

#[derive(Debug, PartialEq)]
pub enum NormalizedToken<'a> {
    /// A standard Lojban word (Gismu, Cmavo, Cmevla, etc.)
    Standard(LojbanToken, &'a str),
    /// Text explicitly quoted by `zo` or `zoi`. Opaque to the structural parser.
    Quoted(&'a str),
    /// A compound word glued together by `zei`.
    Glued(Vec<&'a str>),
}

/// Consumes the raw lexical stream and resolves metalinguistic operations in O(n) time.
pub fn preprocess<'a>(
    raw_tokens: impl Iterator<Item = (LojbanToken, &'a str)>,
    original_input: &'a str,
) -> Vec<NormalizedToken<'a>> {
    let mut output: Vec<NormalizedToken<'a>> = Vec::with_capacity(128);
    let mut iter = raw_tokens.peekable();

    while let Some((token, text)) = iter.next() {
        match token {
            // ── Erasure Operations ────────────────────────────────
            LojbanToken::EraseWord => {
                // `si` erases the immediately preceding metalinguistically resolved token.
                output.pop();
            }

            LojbanToken::EraseStream => {
                // `su` clears the entire current discourse buffer.
                output.clear();
            }

            LojbanToken::EraseClass => {
                // `sa` erases backward until a token of the same grammatical class
                // is found. Full implementation requires selma'o classification.
                //
                // B4 FIX: was `unimplemented!()` which caused WASM trap.
                // Degraded behavior: erase preceding word (same as si).
                // This is safe and handles the most common use case.
                eprintln!(
                    "[parser] warning: 'sa' erasure degraded to single-word erase (si behavior)"
                );
                output.pop();
            }

            // ── Quotation Operations ─────────────────────────────
            LojbanToken::QuoteNext => {
                // `zo` treats the immediately following token as a literal string.
                if let Some((_, quoted_text)) = iter.next() {
                    output.push(NormalizedToken::Quoted(quoted_text));
                }
            }

            LojbanToken::QuoteDelimited => {
                // `zoi` requires a delimiter, arbitrary text, and the same delimiter.
                if let Some((_, delimiter)) = iter.next() {
                    let start_ptr = delimiter.as_ptr() as usize - original_input.as_ptr() as usize
                        + delimiter.len();
                    let mut end_ptr = start_ptr;

                    // Consume until we hit the exact same delimiter token
                    while let Some((_, next_text)) = iter.next() {
                        if next_text == delimiter {
                            break;
                        }
                        end_ptr = next_text.as_ptr() as usize - original_input.as_ptr() as usize
                            + next_text.len();
                    }

                    // Extract the zero-copy payload slice from the original input
                    if end_ptr > start_ptr && end_ptr <= original_input.len() {
                        let payload = &original_input[start_ptr..end_ptr].trim();
                        output.push(NormalizedToken::Quoted(payload));
                    }
                }
            }

            // ── Word Gluing ──────────────────────────────────────
            LojbanToken::GlueWords => {
                // `zei` joins the previous token and the next token into a single
                // lujvo-like unit.
                if let Some(prev) = output.pop() {
                    if let Some((_, next_text)) = iter.next() {
                        let mut parts = match prev {
                            NormalizedToken::Glued(existing) => existing,
                            NormalizedToken::Standard(_, t) | NormalizedToken::Quoted(t) => vec![t],
                        };
                        parts.push(next_text);
                        output.push(NormalizedToken::Glued(parts));
                    }
                }
            }

            // ── Standard Tokens ──────────────────────────────────
            _ => {
                output.push(NormalizedToken::Standard(token, text));
            }
        }
    }

    output
}
