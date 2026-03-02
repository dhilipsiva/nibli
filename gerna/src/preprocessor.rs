//! Metalinguistic preprocessor for the Lojban token stream.
//!
//! Sits between the lexer and parser, resolving metalinguistic operations
//! in a single O(n) pass over the token stream:
//!
//! - **`si`** — erase preceding word
//! - **`sa`** — erase backward to matching selma'o (grammatical class)
//! - **`su`** — erase entire discourse
//! - **`zo`** — quote next word (produces opaque `Quoted` token)
//! - **`zoi`** — quote delimited text (zero-copy slice from original input)
//! - **`zei`** — glue adjacent words into a compound (`Glued` token)
//!
//! The `sa` erasure uses a 28-class selma'o classification table to find the
//! backward erasure boundary. Unclassified tokens fall back to single-word erase.

use crate::lexer::LojbanToken;

// ─── Selma'o (grammatical class) classification ───────────────────
//
// Lojban cmavo belong to grammatical classes called selma'o. The `sa`
// erasure operator needs to classify tokens by selma'o to find the
// backward erasure boundary. This enum covers all classes currently
// recognized by the parser.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Selmaho {
    LE,     // Gadri: lo, le, la
    FA,     // Place tags: fa, fe, fi, fo, fu
    JA,     // Selbri connectives: je, ja, jo, ju (+ nai compounds)
    A,      // Sumti connectives: e, a, o, u (+ nai compounds)
    GA,     // Forethought: ge, ga, go, gu, ganai, gonai, etc.
    GI,     // Forethought separator: gi
    PU,     // Tense: pu, ca, ba (+ nai compounds)
    NU,     // Abstractions: nu, du'u, ka, ni, si'o
    BAI,    // Modal tags: ri'a, ni'i, mu'i, ki'u, pi'o, ba'i
    SE,     // Conversion: se, te, ve, xe
    NA,     // Negation: na, nai
    KU,     // Terminators: ku, kei, vau, ku'o, ke'e, be'o, fe'u, li'u, lo'o
    KE,     // Grouping: ke
    BE,     // Sumti raising: be, bei
    NOI,    // Relative clauses: poi, noi, voi
    CU,     // Selbri separator: cu
    I,      // Sentence separator: .i
    LI,     // Number sumti: li
    LU,     // Quote: lu
    GOhI,   // Pro-bridi: go'i
    COI,    // Pro-sumti: mi, do, ko, ti, ta, tu, etc.
    PA,     // Numbers: pa, re, ci, vo, mu, xa, ze, bi, so, no, ro, su'o
    FIhO,   // Custom modal: fi'o
    DA,     // Logic variables: da, de, di
    CEhU,   // Lambda variable: ce'u
    KEhA,   // Relative variable: ke'a
    Brivla, // Content words: gismu, lujvo
    Cmevla, // Names
}

/// Classify a NormalizedToken into its selma'o (grammatical class).
/// Returns None for quoted tokens and unrecognized cmavo.
fn classify_selmaho(token: &NormalizedToken) -> Option<Selmaho> {
    match token {
        NormalizedToken::Standard(LojbanToken::Gismu, _) => Some(Selmaho::Brivla),
        NormalizedToken::Standard(LojbanToken::Lujvo, _) => Some(Selmaho::Brivla),
        NormalizedToken::Standard(LojbanToken::Cmevla, _) => Some(Selmaho::Cmevla),
        NormalizedToken::Standard(LojbanToken::Cmavo, text) => classify_cmavo(text),
        NormalizedToken::Glued(_) => Some(Selmaho::Brivla), // zei compounds are brivla
        NormalizedToken::Quoted(_) => None,
        _ => None,
    }
}

/// Classify a cmavo text into its selma'o class.
fn classify_cmavo(text: &str) -> Option<Selmaho> {
    match text {
        // LE — Gadri
        "lo" | "le" | "la" => Some(Selmaho::LE),
        // FA — Place tags
        "fa" | "fe" | "fi" | "fo" | "fu" => Some(Selmaho::FA),
        // JA — Selbri connectives (+ nai compounds)
        "je" | "ja" | "jo" | "ju"
        | "jenai" | "janai" | "jonai" | "junai" => Some(Selmaho::JA),
        // A — Sumti connectives (+ nai)
        "e" | "a" | "o" | "u" => Some(Selmaho::A),
        // GA — Forethought connectives (+ nai compounds)
        "ge" | "ga" | "go" | "gu"
        | "ganai" | "genai" | "ginai" | "gonai" | "gunai" => Some(Selmaho::GA),
        // GI — Forethought separator
        "gi" => Some(Selmaho::GI),
        // PU — Tense (+ nai compounds)
        "pu" | "ca" | "ba"
        | "punai" | "canai" | "banai" => Some(Selmaho::PU),
        // NU — Abstractions
        "nu" | "du'u" | "ka" | "ni" | "si'o" => Some(Selmaho::NU),
        // BAI — Modal tags
        "ri'a" | "ni'i" | "mu'i" | "ki'u" | "pi'o" | "ba'i" => Some(Selmaho::BAI),
        // SE — Conversion
        "se" | "te" | "ve" | "xe" => Some(Selmaho::SE),
        // NA — Negation
        "na" | "nai" => Some(Selmaho::NA),
        // KU — Terminators (grouped as one class)
        "ku" | "kei" | "vau" | "ku'o" | "ke'e" | "be'o" | "fe'u" | "li'u" | "lo'o"
            => Some(Selmaho::KU),
        // KE — Grouping
        "ke" => Some(Selmaho::KE),
        // BE — Sumti raising
        "be" | "bei" => Some(Selmaho::BE),
        // NOI — Relative clauses
        "poi" | "noi" | "voi" => Some(Selmaho::NOI),
        // CU — Selbri separator
        "cu" => Some(Selmaho::CU),
        // I — Sentence separator
        "i" => Some(Selmaho::I),
        // LI — Number sumti marker
        "li" => Some(Selmaho::LI),
        // LU — Quote opener
        "lu" => Some(Selmaho::LU),
        // GOhI — Pro-bridi
        "go'i" => Some(Selmaho::GOhI),
        // PA — Numbers and quantifiers
        "pa" | "re" | "ci" | "vo" | "mu" | "xa" | "ze" | "bi" | "so" | "no"
        | "ro" | "su'o" => Some(Selmaho::PA),
        // FIhO — Custom modal
        "fi'o" => Some(Selmaho::FIhO),
        // DA — Logic variables
        "da" | "de" | "di" => Some(Selmaho::DA),
        // CEhU — Lambda variable
        "ce'u" => Some(Selmaho::CEhU),
        // KEhA — Relative variable
        "ke'a" => Some(Selmaho::KEhA),
        // Pro-sumti
        "mi" | "do" | "ko" | "ti" | "ta" | "tu"
        | "ri" | "ra" | "ru" | "zo'e" => Some(Selmaho::COI),
        // Attitudinals — treat as NA-class for erasure purposes
        "ei" | "e'e" => Some(Selmaho::NA),
        // Unrecognized cmavo — no classification
        _ => None,
    }
}

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
                // (selma'o) as the token immediately following `sa` is found.
                //
                // Algorithm:
                // 1. Peek at the next token to determine the target selma'o class
                // 2. If classifiable, walk backward through output to find a match
                // 3. Truncate output at the match point (erasing match + everything after)
                // 4. If no match found or unclassifiable, fall back to single-word erase
                //
                // The token after `sa` is NOT consumed — it stays in the stream as the
                // "restart" point for parsing.
                if let Some((next_tok, next_text)) = iter.peek() {
                    let target_class = classify_selmaho(
                        &NormalizedToken::Standard(next_tok.clone(), next_text),
                    );
                    if let Some(target) = target_class {
                        // Walk backward to find the first token of the same class
                        let mut found = None;
                        for j in (0..output.len()).rev() {
                            if classify_selmaho(&output[j]) == Some(target) {
                                found = Some(j);
                                break;
                            }
                        }
                        if let Some(idx) = found {
                            output.truncate(idx);
                        } else {
                            // No matching class found — fall back to single-word erase
                            output.pop();
                        }
                    } else {
                        // Next token has no known selma'o — fall back to single-word erase
                        output.pop();
                    }
                }
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

// ─── Tests ───

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classify_selmaho_gadri() {
        assert_eq!(classify_cmavo("lo"), Some(Selmaho::LE));
        assert_eq!(classify_cmavo("le"), Some(Selmaho::LE));
        assert_eq!(classify_cmavo("la"), Some(Selmaho::LE));
    }

    #[test]
    fn test_classify_selmaho_gismu() {
        let tok = NormalizedToken::Standard(LojbanToken::Gismu, "klama");
        assert_eq!(classify_selmaho(&tok), Some(Selmaho::Brivla));
    }

    #[test]
    fn test_classify_selmaho_lujvo() {
        let tok = NormalizedToken::Standard(LojbanToken::Lujvo, "brivla");
        assert_eq!(classify_selmaho(&tok), Some(Selmaho::Brivla));
    }

    #[test]
    fn test_classify_selmaho_unknown_cmavo() {
        assert_eq!(classify_cmavo("xyz"), None);
    }

    #[test]
    fn test_classify_selmaho_all_classes() {
        // Spot-check one representative from each class
        assert_eq!(classify_cmavo("fa"), Some(Selmaho::FA));
        assert_eq!(classify_cmavo("je"), Some(Selmaho::JA));
        assert_eq!(classify_cmavo("e"), Some(Selmaho::A));
        assert_eq!(classify_cmavo("ge"), Some(Selmaho::GA));
        assert_eq!(classify_cmavo("gi"), Some(Selmaho::GI));
        assert_eq!(classify_cmavo("pu"), Some(Selmaho::PU));
        assert_eq!(classify_cmavo("nu"), Some(Selmaho::NU));
        assert_eq!(classify_cmavo("ri'a"), Some(Selmaho::BAI));
        assert_eq!(classify_cmavo("se"), Some(Selmaho::SE));
        assert_eq!(classify_cmavo("na"), Some(Selmaho::NA));
        assert_eq!(classify_cmavo("ku"), Some(Selmaho::KU));
        assert_eq!(classify_cmavo("ke"), Some(Selmaho::KE));
        assert_eq!(classify_cmavo("be"), Some(Selmaho::BE));
        assert_eq!(classify_cmavo("poi"), Some(Selmaho::NOI));
        assert_eq!(classify_cmavo("cu"), Some(Selmaho::CU));
        assert_eq!(classify_cmavo("i"), Some(Selmaho::I));
        assert_eq!(classify_cmavo("li"), Some(Selmaho::LI));
        assert_eq!(classify_cmavo("lu"), Some(Selmaho::LU));
        assert_eq!(classify_cmavo("go'i"), Some(Selmaho::GOhI));
        assert_eq!(classify_cmavo("mi"), Some(Selmaho::COI));
        assert_eq!(classify_cmavo("pa"), Some(Selmaho::PA));
        assert_eq!(classify_cmavo("fi'o"), Some(Selmaho::FIhO));
        assert_eq!(classify_cmavo("da"), Some(Selmaho::DA));
        assert_eq!(classify_cmavo("ce'u"), Some(Selmaho::CEhU));
        assert_eq!(classify_cmavo("ke'a"), Some(Selmaho::KEhA));
    }

    #[test]
    fn test_sa_erase_to_matching_gadri_class() {
        // "lo gerku cu klama sa lo mlatu cu sutra"
        //  ↑ erases back to here (lo is LE class, matching the lo after sa)
        // Result: "lo mlatu cu sutra"
        let tokens = vec![
            (LojbanToken::Cmavo, "lo"),
            (LojbanToken::Gismu, "gerku"),
            (LojbanToken::Cmavo, "cu"),
            (LojbanToken::Gismu, "klama"),
            (LojbanToken::EraseClass, "sa"),
            (LojbanToken::Cmavo, "lo"),
            (LojbanToken::Gismu, "mlatu"),
            (LojbanToken::Cmavo, "cu"),
            (LojbanToken::Gismu, "sutra"),
        ];
        let input = "lo gerku cu klama sa lo mlatu cu sutra";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 4);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Cmavo, "lo"));
        assert_eq!(result[1], NormalizedToken::Standard(LojbanToken::Gismu, "mlatu"));
        assert_eq!(result[2], NormalizedToken::Standard(LojbanToken::Cmavo, "cu"));
        assert_eq!(result[3], NormalizedToken::Standard(LojbanToken::Gismu, "sutra"));
    }

    #[test]
    fn test_sa_erase_brivla_class() {
        // "mi klama sa prami do"
        //     ↑ erases back to here (klama is Brivla, matching prami after sa)
        // Result: "mi prami do"
        let tokens = vec![
            (LojbanToken::Cmavo, "mi"),
            (LojbanToken::Gismu, "klama"),
            (LojbanToken::EraseClass, "sa"),
            (LojbanToken::Gismu, "prami"),
            (LojbanToken::Cmavo, "do"),
        ];
        let input = "mi klama sa prami do";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 3);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Cmavo, "mi"));
        assert_eq!(result[1], NormalizedToken::Standard(LojbanToken::Gismu, "prami"));
        assert_eq!(result[2], NormalizedToken::Standard(LojbanToken::Cmavo, "do"));
    }

    #[test]
    fn test_sa_no_match_fallback() {
        // "mi klama sa lo gerku"
        // No LE-class token exists in output before sa → falls back to single-word erase
        // Result: "mi lo gerku" (only "klama" removed)
        let tokens = vec![
            (LojbanToken::Cmavo, "mi"),
            (LojbanToken::Gismu, "klama"),
            (LojbanToken::EraseClass, "sa"),
            (LojbanToken::Cmavo, "lo"),
            (LojbanToken::Gismu, "gerku"),
        ];
        let input = "mi klama sa lo gerku";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 3);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Cmavo, "mi"));
        assert_eq!(result[1], NormalizedToken::Standard(LojbanToken::Cmavo, "lo"));
        assert_eq!(result[2], NormalizedToken::Standard(LojbanToken::Gismu, "gerku"));
    }

    #[test]
    fn test_sa_erases_multiple_tokens() {
        // "lo gerku cu barda .e lo mlatu cu klama sa lo prenu cu sutra"
        //                       ↑ erases back to second "lo" (LE class)
        // Result: "lo gerku cu barda .e lo prenu cu sutra"
        let tokens = vec![
            (LojbanToken::Cmavo, "lo"),
            (LojbanToken::Gismu, "gerku"),
            (LojbanToken::Cmavo, "cu"),
            (LojbanToken::Gismu, "barda"),
            (LojbanToken::Pause, "."),
            (LojbanToken::Cmavo, "e"),
            (LojbanToken::Cmavo, "lo"),
            (LojbanToken::Gismu, "mlatu"),
            (LojbanToken::Cmavo, "cu"),
            (LojbanToken::Gismu, "klama"),
            (LojbanToken::EraseClass, "sa"),
            (LojbanToken::Cmavo, "lo"),
            (LojbanToken::Gismu, "prenu"),
            (LojbanToken::Cmavo, "cu"),
            (LojbanToken::Gismu, "sutra"),
        ];
        let input = "lo gerku cu barda .e lo mlatu cu klama sa lo prenu cu sutra";
        let result = preprocess(tokens.into_iter(), input);
        // After sa: erases back to second "lo" (index 6), truncating [lo, mlatu, cu, klama]
        // Then continues with: lo, prenu, cu, sutra
        assert_eq!(result.len(), 10);
        // First part preserved: lo gerku cu barda . e
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Cmavo, "lo"));
        assert_eq!(result[1], NormalizedToken::Standard(LojbanToken::Gismu, "gerku"));
        assert_eq!(result[2], NormalizedToken::Standard(LojbanToken::Cmavo, "cu"));
        assert_eq!(result[3], NormalizedToken::Standard(LojbanToken::Gismu, "barda"));
        assert_eq!(result[4], NormalizedToken::Standard(LojbanToken::Pause, "."));
        assert_eq!(result[5], NormalizedToken::Standard(LojbanToken::Cmavo, "e"));
        // Replacement: lo prenu cu sutra
        assert_eq!(result[6], NormalizedToken::Standard(LojbanToken::Cmavo, "lo"));
        assert_eq!(result[7], NormalizedToken::Standard(LojbanToken::Gismu, "prenu"));
        assert_eq!(result[8], NormalizedToken::Standard(LojbanToken::Cmavo, "cu"));
        assert_eq!(result[9], NormalizedToken::Standard(LojbanToken::Gismu, "sutra"));
    }

    // ─── si (erase word) tests ─────────────────────────────────

    #[test]
    fn test_si_erases_preceding_word() {
        // "mi klama si prami do" → "mi prami do"
        let tokens = vec![
            (LojbanToken::Cmavo, "mi"),
            (LojbanToken::Gismu, "klama"),
            (LojbanToken::EraseWord, "si"),
            (LojbanToken::Gismu, "prami"),
            (LojbanToken::Cmavo, "do"),
        ];
        let input = "mi klama si prami do";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 3);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Cmavo, "mi"));
        assert_eq!(result[1], NormalizedToken::Standard(LojbanToken::Gismu, "prami"));
        assert_eq!(result[2], NormalizedToken::Standard(LojbanToken::Cmavo, "do"));
    }

    #[test]
    fn test_si_at_beginning_does_nothing() {
        // "si klama" → "klama" (si with empty output just has no effect)
        let tokens = vec![
            (LojbanToken::EraseWord, "si"),
            (LojbanToken::Gismu, "klama"),
        ];
        let input = "si klama";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Gismu, "klama"));
    }

    #[test]
    fn test_double_si_erases_two_words() {
        // "mi do si si klama" → "mi klama" (two si erases two words)
        let tokens = vec![
            (LojbanToken::Cmavo, "mi"),
            (LojbanToken::Cmavo, "do"),
            (LojbanToken::EraseWord, "si"),
            (LojbanToken::EraseWord, "si"),
            (LojbanToken::Gismu, "klama"),
        ];
        let input = "mi do si si klama";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Gismu, "klama"));
    }

    // ─── su (erase stream) tests ──────────────────────────────

    #[test]
    fn test_su_erases_entire_discourse() {
        // "mi klama do su lo gerku cu sutra" → "lo gerku cu sutra"
        let tokens = vec![
            (LojbanToken::Cmavo, "mi"),
            (LojbanToken::Gismu, "klama"),
            (LojbanToken::Cmavo, "do"),
            (LojbanToken::EraseStream, "su"),
            (LojbanToken::Cmavo, "lo"),
            (LojbanToken::Gismu, "gerku"),
            (LojbanToken::Cmavo, "cu"),
            (LojbanToken::Gismu, "sutra"),
        ];
        let input = "mi klama do su lo gerku cu sutra";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 4);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Cmavo, "lo"));
        assert_eq!(result[1], NormalizedToken::Standard(LojbanToken::Gismu, "gerku"));
        assert_eq!(result[2], NormalizedToken::Standard(LojbanToken::Cmavo, "cu"));
        assert_eq!(result[3], NormalizedToken::Standard(LojbanToken::Gismu, "sutra"));
    }

    #[test]
    fn test_su_on_empty_output() {
        // "su klama" → "klama" (su clears empty buffer, no effect)
        let tokens = vec![
            (LojbanToken::EraseStream, "su"),
            (LojbanToken::Gismu, "klama"),
        ];
        let input = "su klama";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Gismu, "klama"));
    }

    // ─── zo (quote next) tests ────────────────────────────────

    #[test]
    fn test_zo_quotes_next_word() {
        // "zo klama cu selbri" → Quoted("klama"), cu, selbri
        let tokens = vec![
            (LojbanToken::QuoteNext, "zo"),
            (LojbanToken::Gismu, "klama"),
            (LojbanToken::Cmavo, "cu"),
            (LojbanToken::Gismu, "selbri"),
        ];
        let input = "zo klama cu selbri";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 3);
        assert_eq!(result[0], NormalizedToken::Quoted("klama"));
        assert_eq!(result[1], NormalizedToken::Standard(LojbanToken::Cmavo, "cu"));
    }

    #[test]
    fn test_zo_at_end_of_stream() {
        // "mi zo" → just "mi" (zo at end has no next token to quote)
        let tokens = vec![
            (LojbanToken::Cmavo, "mi"),
            (LojbanToken::QuoteNext, "zo"),
        ];
        let input = "mi zo";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Cmavo, "mi"));
    }

    // ─── zei (glue words) tests ───────────────────────────────

    #[test]
    fn test_zei_glues_two_words() {
        // "skami zei pilno" → Glued(["skami", "pilno"])
        let tokens = vec![
            (LojbanToken::Gismu, "skami"),
            (LojbanToken::GlueWords, "zei"),
            (LojbanToken::Gismu, "pilno"),
        ];
        let input = "skami zei pilno";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], NormalizedToken::Glued(vec!["skami", "pilno"]));
    }

    #[test]
    fn test_zei_chains_three_words() {
        // "skami zei pilno zei tadni" → Glued(["skami", "pilno", "tadni"])
        let tokens = vec![
            (LojbanToken::Gismu, "skami"),
            (LojbanToken::GlueWords, "zei"),
            (LojbanToken::Gismu, "pilno"),
            (LojbanToken::GlueWords, "zei"),
            (LojbanToken::Gismu, "tadni"),
        ];
        let input = "skami zei pilno zei tadni";
        let result = preprocess(tokens.into_iter(), input);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], NormalizedToken::Glued(vec!["skami", "pilno", "tadni"]));
    }

    #[test]
    fn test_zei_at_beginning_no_previous() {
        // "zei klama" → no previous token, zei is no-op; klama remains in stream
        let tokens = vec![
            (LojbanToken::GlueWords, "zei"),
            (LojbanToken::Gismu, "klama"),
        ];
        let input = "zei klama";
        let result = preprocess(tokens.into_iter(), input);
        // zei pops nothing (output is empty), if-let fails, klama stays in stream
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Gismu, "klama"));
    }

    // ─── sa edge cases ────────────────────────────────────────

    #[test]
    fn test_sa_at_end_of_stream() {
        // "mi klama sa" → sa peeks but nothing follows
        let tokens = vec![
            (LojbanToken::Cmavo, "mi"),
            (LojbanToken::Gismu, "klama"),
            (LojbanToken::EraseClass, "sa"),
        ];
        let input = "mi klama sa";
        let result = preprocess(tokens.into_iter(), input);
        // sa at end: peek returns None, nothing happens
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Cmavo, "mi"));
        assert_eq!(result[1], NormalizedToken::Standard(LojbanToken::Gismu, "klama"));
    }

    #[test]
    fn test_sa_with_unclassifiable_next_token() {
        // "mi klama sa .djan." → pause/cmevla after sa; cmevla has Cmevla class
        // but test with a pause token which gets classified as None
        let tokens = vec![
            (LojbanToken::Cmavo, "mi"),
            (LojbanToken::Gismu, "klama"),
            (LojbanToken::EraseClass, "sa"),
            (LojbanToken::Pause, "."),
            (LojbanToken::Gismu, "sutra"),
        ];
        let input = "mi klama sa . sutra";
        let result = preprocess(tokens.into_iter(), input);
        // Pause has no selmaho classification → fallback to single-word erase
        // Removes "klama", then ". sutra" continues
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Cmavo, "mi"));
        assert_eq!(result[1], NormalizedToken::Standard(LojbanToken::Pause, "."));
        assert_eq!(result[2], NormalizedToken::Standard(LojbanToken::Gismu, "sutra"));
    }

    // ─── classify_selmaho edge cases ──────────────────────────

    #[test]
    fn test_classify_selmaho_glued_is_brivla() {
        let tok = NormalizedToken::Glued(vec!["skami", "pilno"]);
        assert_eq!(classify_selmaho(&tok), Some(Selmaho::Brivla));
    }

    #[test]
    fn test_classify_selmaho_quoted_is_none() {
        let tok = NormalizedToken::Quoted("anything");
        assert_eq!(classify_selmaho(&tok), None);
    }

    #[test]
    fn test_classify_selmaho_cmevla() {
        let tok = NormalizedToken::Standard(LojbanToken::Cmevla, "djan");
        assert_eq!(classify_selmaho(&tok), Some(Selmaho::Cmevla));
    }

    #[test]
    fn test_classify_cmavo_attitudinals_as_na() {
        // ei and e'e are treated as NA-class for erasure purposes
        assert_eq!(classify_cmavo("ei"), Some(Selmaho::NA));
        assert_eq!(classify_cmavo("e'e"), Some(Selmaho::NA));
    }

    #[test]
    fn test_classify_cmavo_pro_sumti() {
        assert_eq!(classify_cmavo("mi"), Some(Selmaho::COI));
        assert_eq!(classify_cmavo("do"), Some(Selmaho::COI));
        assert_eq!(classify_cmavo("ko"), Some(Selmaho::COI));
        assert_eq!(classify_cmavo("ti"), Some(Selmaho::COI));
        assert_eq!(classify_cmavo("ta"), Some(Selmaho::COI));
        assert_eq!(classify_cmavo("tu"), Some(Selmaho::COI));
        assert_eq!(classify_cmavo("ri"), Some(Selmaho::COI));
        assert_eq!(classify_cmavo("zo'e"), Some(Selmaho::COI));
    }

    // ─── Empty input ──────────────────────────────────────────

    #[test]
    fn test_preprocess_empty_input() {
        let tokens: Vec<(LojbanToken, &str)> = vec![];
        let result = preprocess(tokens.into_iter(), "");
        assert!(result.is_empty());
    }

    // ─── Combined operations ──────────────────────────────────

    #[test]
    fn test_si_followed_by_sa() {
        // "mi do si klama sa gerku" → "mi" then si removes "do", then "klama",
        // then sa looks for Brivla class (gerku), finds "klama" at position 1, truncates
        let tokens = vec![
            (LojbanToken::Cmavo, "mi"),
            (LojbanToken::Cmavo, "do"),
            (LojbanToken::EraseWord, "si"),
            (LojbanToken::Gismu, "klama"),
            (LojbanToken::EraseClass, "sa"),
            (LojbanToken::Gismu, "gerku"),
        ];
        let input = "mi do si klama sa gerku";
        let result = preprocess(tokens.into_iter(), input);
        // After si: [mi]
        // After "klama": [mi, klama]
        // sa peeks "gerku" (Brivla), walks back, finds "klama" (Brivla) at idx 1
        // Truncates to idx 1: [mi]
        // Then gerku is added: [mi, gerku]
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], NormalizedToken::Standard(LojbanToken::Cmavo, "mi"));
        assert_eq!(result[1], NormalizedToken::Standard(LojbanToken::Gismu, "gerku"));
    }
}
