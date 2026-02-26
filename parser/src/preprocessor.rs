// parser/src/preprocessor.rs
//
// Consumes the raw lexical stream and resolves metalinguistic operations:
//   si  — erase preceding word
//   sa  — erase backward to matching selma'o class
//   su  — erase entire discourse
//   zo  — quote next word
//   zoi — quote delimited text
//   zei — glue adjacent words into compound

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
}
