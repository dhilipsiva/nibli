//! Lojban lexer built on the Logos DFA engine.
//!
//! Produces a stream of [`LojbanToken`] variants from raw Lojban text.
//! Morphological classes (gismu, lujvo, cmevla, cmavo) are distinguished by
//! regex patterns. Two post-lex correction passes handle edge cases:
//!
//! 1. **Compound cmavo reclassification** — Logos greedily matches CVC prefixes
//!    of compound cmavo (e.g., "ganai") as Cmevla. A post-lex pass merges them
//!    back into single Cmavo tokens when not preceded by a pause.
//!
//! 2. **Sumti connective `nai` fix** — Fused forms like ".enai" are split into
//!    separate Cmavo("e") + Cmavo("nai") tokens for the parser.

use logos::Logos;

/// Lojban token types produced by the Logos-based lexer.
///
/// The lexer recognizes five morphological classes plus metalinguistic operators.
/// Whitespace is skipped; explicit pauses (`.`) are preserved as tokens.
#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(skip r"[ \t\n\f]+")] // Whitespace is ignored, but explicit pauses (.) are not
pub enum LojbanToken {
    // --------------------------------------------------
    // Metalinguistic Operators (Must be intercepted)
    // --------------------------------------------------
    /// `si`: erase the preceding word.
    #[token("si")]
    EraseWord,

    /// `sa`: erase backward to matching grammatical class.
    #[token("sa")]
    EraseClass,

    /// `su`: erase the entire discourse.
    #[token("su")]
    EraseStream,

    /// `zo`: quote the next word as a literal.
    #[token("zo")]
    QuoteNext,

    /// `zoi`: delimited quotation.
    #[token("zoi")]
    QuoteDelimited,

    /// `zei`: glue adjacent words into a compound lujvo.
    #[token("zei")]
    GlueWords,

    // --------------------------------------------------
    // Morphological Classes
    // --------------------------------------------------

    // Gismu: CVCCV or CCVCV structure. This regex enforces only the 5-letter
    // SHAPE; the `validate_gismu_clusters` post-lex pass then enforces Lojban's
    // phonotactic consonant-cluster rules (the 48 valid initial pairs / the
    // medial-pair rules), rejecting shape-valid but cluster-invalid roots like
    // `bkalu` as a lex error (fail-closed) rather than a misclassified gismu.
    #[regex(r"([bcdfghjklmnprstvxz][aeiou][bcdfghjklmnprstvxz][bcdfghjklmnprstvxz][aeiou])|([bcdfghjklmnprstvxz][bcdfghjklmnprstvxz][aeiou][bcdfghjklmnprstvxz][aeiou])")]
    /// Root predicate word (CVCCV or CCVCV, 5 letters).
    Gismu,

    // Lujvo (compound brivla): 6+ letter words ending in vowel.
    // Longest-match prevents cmavo from stealing prefixes (e.g., "nunprami" ≠ "nu" + ...).
    // Semantics dictionary lookup handles arity for known lujvo.
    #[regex(r"[a-z']{5}[a-z']*[aeiou]")]
    /// Compound predicate word (6+ letters ending in vowel).
    Lujvo,

    // Cmevla (Names): Must end in a consonant.
    // No dots in body — dots are pause tokens and must not be consumed as part of a word.
    // Final character is explicitly a Lojban consonant, not a negated vowel class.
    #[regex(r"[a-zA-Z']+[bcdfghjklmnprstvxzBCDFGHJKLMNPRSTVXZ]")]
    /// Name word (ends in a consonant, preceded by a pause).
    Cmevla,

    // Cmavo (Structure words): one-to-many of the five Lojban vowels (a/e/i/o/u),
    // optionally preceded by one consonant (apostrophe allowed between vowels, e.g.
    // `du'u`/`go'i`/`ri'a`). `y` is deliberately excluded — it is not a structural
    // cmavo vowel (it appears only in the hesitation cmavo `.y.`, the BY letterals
    // like `by`/`cy`, and as a lujvo hyphen, none of which are supported here), so a
    // `y`-containing token fails closed as an unlexable run instead of a misclassified
    // cmavo. Lujvo internal `y` is matched by the Lujvo regex's `[a-z']` body. This
    // vowel class matches the Gismu/Lujvo regexes above.
    // This acts as a fallback for structural words not explicitly tokenized above.
    #[regex(r"[bcdfghjklmnprstvxz]?[aeiou']+")]
    /// Structure word (vowel-based, optionally one leading consonant).
    Cmavo,

    // Explicit Pauses
    #[token(".")]
    Pause,
}

// ─── Compound cmavo lookup table ──────────────────────────────
//
// Logos's Cmevla regex `[a-zA-Z']+[consonant]` greedily matches CVC
// prefixes of compound cmavo. Example: "ganai" → Cmevla("gan") + Cmavo("ai").
//
// In standard Lojban, cmevla must be preceded by a pause (period).
// Unpaused CVC tokens are misclassified cmavo prefixes. This table
// drives a post-lex merge pass that reconstitutes the intended compound.
//
// Pattern: every entry is a CV-cmavo + "nai" suffix, where the fusion
// creates a CVC prefix that the Cmevla regex grabs. Extend this table
// when adding new selma'o compounds that hit the same pattern.

const COMPOUND_CMAVO: &[&str] = &[
    // GA selma'o + nai — the only parser-handled forethought conditional
    "ganai", // JA selma'o + nai — afterthought logical connectives
    "janai", "jenai", "jonai", "junai", // PU selma'o + nai — tense negation
    "punai", "canai", "banai",
];

/// Check whether a string matches a known compound cmavo.
fn is_compound_cmavo(s: &str) -> bool {
    COMPOUND_CMAVO.iter().any(|&c| c == s)
}

/// Post-lex pass: merge misclassified Cmevla + Cmavo into compound Cmavo.
///
/// Scans for any Cmevla NOT preceded by a Pause. When the Cmevla's text
/// is contiguous with the next token's text (no whitespace gap) and their
/// concatenation is a known compound cmavo, the two tokens are merged into
/// a single Cmavo token whose slice spans both originals.
fn reclassify_compounds<'a>(tokens: &mut Vec<(LojbanToken, &'a str)>, input: &'a str) {
    let base = input.as_ptr() as usize;
    let mut i = 0;

    while i < tokens.len() {
        let is_cmevla = tokens[i].0 == LojbanToken::Cmevla;
        let preceded_by_pause = i > 0 && tokens[i - 1].0 == LojbanToken::Pause;

        if is_cmevla && !preceded_by_pause {
            if i + 1 < tokens.len() {
                let s1 = tokens[i].1;
                let s2 = tokens[i + 1].1;
                let off1 = s1.as_ptr() as usize - base;
                let off2 = s2.as_ptr() as usize - base;

                // Only merge if slices are contiguous in the source text
                if off1 + s1.len() == off2 {
                    let compound = &input[off1..off2 + s2.len()];
                    if is_compound_cmavo(compound) {
                        tokens[i] = (LojbanToken::Cmavo, compound);
                        tokens.remove(i + 1);
                        continue; // re-examine position i (in case of triple merge)
                    }
                }
            }
        }

        i += 1;
    }
}

/// Post-lex pass: fix sumti connective `nai` compounds after a pause.
///
/// Logos greedily lexes `.enai` as Pause(".") + Cmevla("en") + Cmavo("ai")
/// because "en" ends in consonant 'n'. The correct tokenization for sumti
/// connectives is Pause + Cmavo("e") + Cmavo("nai").
///
/// This pass detects `Pause + Cmevla(Vn) + Cmavo("ai")` when contiguous
/// in the source, and splits the Cmevla into Cmavo(V) + Cmavo("nai").
fn fix_sumti_connective_nai<'a>(tokens: &mut Vec<(LojbanToken, &'a str)>, input: &'a str) {
    let base = input.as_ptr() as usize;
    let mut i = 1; // start at 1 since we need i-1

    while i + 1 < tokens.len() {
        let preceded_by_pause = tokens[i - 1].0 == LojbanToken::Pause;
        let is_cmevla = tokens[i].0 == LojbanToken::Cmevla;
        let followed_by_ai = tokens[i + 1].0 == LojbanToken::Cmavo && tokens[i + 1].1 == "ai";

        if preceded_by_pause && is_cmevla && followed_by_ai {
            let cmevla_text = tokens[i].1;
            // Check if the cmevla is exactly a vowel + "n" (e.g., "en", "an", "on", "un")
            if cmevla_text.len() == 2 {
                let bytes = cmevla_text.as_bytes();
                let is_vowel_n = matches!(bytes[0], b'e' | b'a' | b'o' | b'u') && bytes[1] == b'n';

                if is_vowel_n {
                    // Verify contiguity: cmevla + "ai" must be contiguous
                    let off_cmevla = cmevla_text.as_ptr() as usize - base;
                    let off_ai = tokens[i + 1].1.as_ptr() as usize - base;

                    if off_cmevla + cmevla_text.len() == off_ai {
                        // Split: Cmevla("en") + Cmavo("ai") → Cmavo("e") + Cmavo("nai")
                        let vowel_slice = &input[off_cmevla..off_cmevla + 1];
                        let nai_slice = &input[off_cmevla + 1..off_ai + 2];

                        tokens[i] = (LojbanToken::Cmavo, vowel_slice);
                        tokens[i + 1] = (LojbanToken::Cmavo, nai_slice);
                    }
                }
            }
        }

        i += 1;
    }
}

/// Voiced obstruent consonants (for the gismu medial voicing-agreement check).
fn is_voiced_obstruent(c: u8) -> bool {
    matches!(c, b'b' | b'd' | b'g' | b'v' | b'z' | b'j')
}

/// Unvoiced obstruent consonants.
fn is_unvoiced_obstruent(c: u8) -> bool {
    matches!(c, b'p' | b't' | b'k' | b'f' | b's' | b'c' | b'x')
}

/// Any Lojban consonant: an obstruent or a sonorant (`l m n r`). Excludes `h`,
/// which is not a Lojban consonant, so any pair containing it is invalid.
fn is_lojban_consonant(c: u8) -> bool {
    is_voiced_obstruent(c) || is_unvoiced_obstruent(c) || matches!(c, b'l' | b'm' | b'n' | b'r')
}

/// The 48 permissible Lojban initial consonant pairs (the onset of a CCVCV gismu).
const VALID_INITIAL_PAIRS: &[[u8; 2]] = &[
    *b"bl", *b"br", *b"cf", *b"ck", *b"cl", *b"cm", *b"cn", *b"cp", *b"cr", *b"ct", *b"dj", *b"dr",
    *b"dz", *b"fl", *b"fr", *b"gl", *b"gr", *b"jb", *b"jd", *b"jg", *b"jm", *b"jv", *b"kl", *b"kr",
    *b"ml", *b"mr", *b"pl", *b"pr", *b"sf", *b"sk", *b"sl", *b"sm", *b"sn", *b"sp", *b"sr", *b"st",
    *b"tc", *b"tr", *b"ts", *b"vl", *b"vr", *b"xl", *b"xr", *b"zb", *b"zd", *b"zg", *b"zm", *b"zv",
];

/// CCVCV onset rule: the initial pair must be one of the 48 permissible pairs.
fn is_valid_initial_pair(c1: u8, c2: u8) -> bool {
    VALID_INITIAL_PAIRS.contains(&[c1, c2])
}

/// CVCCV medial rule (CLL): not a doubled consonant, not a forbidden pair, and
/// not a voiced/unvoiced obstruent clash (sonorants `l m n r` pair with anything).
fn is_valid_medial_pair(c1: u8, c2: u8) -> bool {
    if c1 == c2 || !is_lojban_consonant(c1) || !is_lojban_consonant(c2) {
        return false;
    }
    const FORBIDDEN: &[[u8; 2]] = &[*b"cx", *b"kx", *b"xc", *b"xk", *b"mz"];
    if FORBIDDEN.contains(&[c1, c2]) {
        return false;
    }
    let clash = (is_voiced_obstruent(c1) && is_unvoiced_obstruent(c2))
        || (is_unvoiced_obstruent(c1) && is_voiced_obstruent(c2));
    !clash
}

/// Whether a shape-matched gismu has a valid consonant cluster. `char[1]` being a
/// vowel marks the CVCCV shape (check the medial pair); otherwise CCVCV (initial).
fn is_valid_gismu(word: &str) -> bool {
    let b = word.as_bytes();
    if b.len() != 5 {
        return false;
    }
    if matches!(b[1], b'a' | b'e' | b'i' | b'o' | b'u') {
        is_valid_medial_pair(b[2], b[3])
    } else {
        is_valid_initial_pair(b[0], b[1])
    }
}

/// Post-lex pass: reject gismu tokens whose consonant cluster is invalid.
///
/// The Gismu regex enforces only the CVCCV/CCVCV shape, not Lojban's phonotactic
/// cluster rules — so `bkalu` (invalid initial `bk`) or a voiced/unvoiced medial
/// clash lexed as a Gismu and then silently became an arity-2 unknown predicate.
/// This pass removes such tokens and records each as a [`LexError`] span
/// (fail-closed), so a malformed root surfaces as a positioned error instead.
fn validate_gismu_clusters<'a>(
    tokens: &mut Vec<(LojbanToken, &'a str)>,
    input: &'a str,
    errors: &mut Vec<LexError>,
) {
    let base = input.as_ptr() as usize;
    let mut rejected = false;
    let mut i = 0;
    while i < tokens.len() {
        if tokens[i].0 == LojbanToken::Gismu && !is_valid_gismu(tokens[i].1) {
            let off = tokens[i].1.as_ptr() as usize - base;
            errors.push(LexError {
                start: off,
                end: off + tokens[i].1.len(),
            });
            tokens.remove(i);
            rejected = true;
            continue;
        }
        i += 1;
    }
    // A rejected gismu may sit before an earlier main-loop error in source order;
    // restore the start-ordered invariant the error consumers rely on.
    if rejected {
        errors.sort_by_key(|e| e.start);
    }
}

/// A lexical error: a maximal run of unlexable characters in the input.
///
/// `start..end` is the byte span of the run in the original input string.
/// Callers convert the span to line:column for diagnostics (the parser
/// already does pointer-arithmetic positioning from token slices; lex
/// errors carry explicit offsets because the offending text never becomes
/// a token).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexError {
    /// Byte offset of the first unlexable character.
    pub start: usize,
    /// Byte offset one past the last unlexable character of the run.
    pub end: usize,
}

/// Tokenizer with an explicit error channel: Logos DFA + post-lex compound
/// cmavo reclassification.
///
/// Unlexable characters (digits, most punctuation, capitalized vowel-final
/// words) do NOT stop lexing: each maximal run is skipped, recorded as a
/// [`LexError`] span, and lexing continues — so later sentences still parse
/// and input is never silently dropped. Callers that must fail closed
/// (e.g. assertion paths) reject the input when any error is present.
pub fn tokenize_with_errors(input: &str) -> (Vec<(LojbanToken, &str)>, Vec<LexError>) {
    let mut lex = LojbanToken::lexer(input);
    let mut tokens = Vec::new();
    let mut errors: Vec<LexError> = Vec::new();

    while let Some(result) = lex.next() {
        match result {
            Ok(token) => tokens.push((token, lex.slice())),
            Err(()) => {
                let span = lex.span();
                // Coalesce adjacent unlexable characters into one run
                // (logos reports errors char by char).
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

    reclassify_compounds(&mut tokens, input);
    fix_sumti_connective_nai(&mut tokens, input);
    validate_gismu_clusters(&mut tokens, input, &mut errors);
    (tokens, errors)
}

/// Tokenizer returning only the token stream.
///
/// Unlexable characters are skipped (lexing continues past them) but their
/// positions are discarded — use [`tokenize_with_errors`] to observe them.
/// The full pipeline ([`crate::parse_text_native`]) uses the error-carrying
/// variant so unlexable input surfaces as a positioned parse error.
pub fn tokenize(input: &str) -> Vec<(LojbanToken, &str)> {
    tokenize_with_errors(input).0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ganai_lexes_as_cmavo() {
        let tokens = tokenize("ganai mi klama gi do sutra");
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "ganai"));
    }

    #[test]
    fn gonai_is_not_a_recognized_forethought_compound() {
        // gu/genai/ginai/gonai/gunai are not parser-handled forethought
        // connectives (only ge/ga/go/ganai are), so the lexer no longer fuses
        // `gonai` into one GA cmavo — it falls back to the greedy Cmevla split
        // (fail-closed: a later parse rejects it).
        let tokens = tokenize("gonai mi klama gi do ciska");
        assert_ne!(tokens[0], (LojbanToken::Cmavo, "gonai"));
    }

    #[test]
    fn ganai_with_space_stays_separate() {
        // "ga nai" with whitespace → two separate cmavo, no merge
        let tokens = tokenize("ga nai mi klama gi do sutra");
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "ga"));
        assert_eq!(tokens[1], (LojbanToken::Cmavo, "nai"));
    }

    #[test]
    fn cmevla_after_pause_stays_cmevla() {
        // ".djan." is a real cmevla — preceded by pause, must NOT be reclassified
        let tokens = tokenize(".djan.");
        assert_eq!(tokens[0], (LojbanToken::Pause, "."));
        assert_eq!(tokens[1], (LojbanToken::Cmevla, "djan"));
        assert_eq!(tokens[2], (LojbanToken::Pause, "."));
    }

    #[test]
    fn ganai_inside_nu_abstraction() {
        let tokens = tokenize("mi djica lo nu ganai do klama gi mi ciska kei");
        let ganai_tok = tokens.iter().find(|(_, s)| *s == "ganai");
        assert_eq!(ganai_tok, Some(&(LojbanToken::Cmavo, "ganai")));
    }

    #[test]
    fn all_compound_cmavo_recognized() {
        for &compound in COMPOUND_CMAVO {
            let input = format!("{} mi klama", compound);
            let tokens = tokenize(&input);
            assert_eq!(
                tokens[0].0,
                LojbanToken::Cmavo,
                "{} should lex as Cmavo, got {:?}",
                compound,
                tokens[0].0
            );
            assert_eq!(tokens[0].1, compound);
        }
    }

    #[test]
    fn janai_in_sentence() {
        let tokens = tokenize("lo mlatu janai gerku cu klama");
        let janai_tok = tokens.iter().find(|(_, s)| *s == "janai");
        assert_eq!(janai_tok, Some(&(LojbanToken::Cmavo, "janai")));
    }

    #[test]
    fn normal_gismu_unaffected() {
        let tokens = tokenize("klama sutra bajra");
        assert_eq!(tokens[0], (LojbanToken::Gismu, "klama"));
        assert_eq!(tokens[1], (LojbanToken::Gismu, "sutra"));
        assert_eq!(tokens[2], (LojbanToken::Gismu, "bajra"));
    }

    #[test]
    fn enai_fused_tokenization() {
        // .enai → Pause + Cmavo("e") + Cmavo("nai") after fix_sumti_connective_nai
        let tokens = tokenize("mi .enai do klama");
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "mi"));
        assert_eq!(tokens[1], (LojbanToken::Pause, "."));
        assert_eq!(tokens[2], (LojbanToken::Cmavo, "e"));
        assert_eq!(tokens[3], (LojbanToken::Cmavo, "nai"));
        assert_eq!(tokens[4], (LojbanToken::Cmavo, "do"));
        assert_eq!(tokens[5], (LojbanToken::Gismu, "klama"));
    }

    #[test]
    fn enai_spaced_tokenization() {
        // .e nai → Pause + Cmavo("e") + Cmavo("nai") (already correct)
        let tokens = tokenize("mi .e nai do klama");
        assert_eq!(tokens[1], (LojbanToken::Pause, "."));
        assert_eq!(tokens[2], (LojbanToken::Cmavo, "e"));
        assert_eq!(tokens[3], (LojbanToken::Cmavo, "nai"));
    }

    #[test]
    fn all_sumti_connective_nai_fused() {
        for (input, vowel) in [
            ("mi .enai do klama", "e"),
            ("mi .anai do klama", "a"),
            ("mi .onai do klama", "o"),
            ("mi .unai do klama", "u"),
        ] {
            let tokens = tokenize(input);
            assert_eq!(
                tokens[2],
                (LojbanToken::Cmavo, vowel),
                "fused {} should produce Cmavo(\"{}\")",
                input,
                vowel
            );
            assert_eq!(
                tokens[3],
                (LojbanToken::Cmavo, "nai"),
                "fused {} should produce Cmavo(\"nai\")",
                input
            );
        }
    }

    #[test]
    fn cmevla_after_pause_not_affected_by_nai_fix() {
        // ".djan." is a real cmevla — should NOT be reclassified
        let tokens = tokenize(".djan. klama");
        assert_eq!(tokens[0], (LojbanToken::Pause, "."));
        assert_eq!(tokens[1], (LojbanToken::Cmevla, "djan"));
        assert_eq!(tokens[2], (LojbanToken::Pause, "."));
    }

    // ─── Lujvo recognition (Tier 3.2) ────────────────────────────

    #[test]
    fn test_lujvo_brivla() {
        // "brivla" (6 chars, CCVCCV ending in vowel) → Lujvo
        let tokens = tokenize("brivla cu klama");
        assert_eq!(tokens[0], (LojbanToken::Lujvo, "brivla"));
    }

    #[test]
    fn test_lujvo_nunprami() {
        // "nunprami" (8 chars) → Lujvo
        let tokens = tokenize("nunprami cu klama");
        assert_eq!(tokens[0], (LojbanToken::Lujvo, "nunprami"));
    }

    #[test]
    fn test_lujvo_selkla() {
        // "selkla" (6 chars) → Lujvo
        let tokens = tokenize("selkla");
        assert_eq!(tokens[0], (LojbanToken::Lujvo, "selkla"));
    }

    #[test]
    fn test_lujvo_does_not_steal_gismu() {
        // "klama" (5 chars, valid CVCCV) → still Gismu, not Lujvo
        let tokens = tokenize("klama");
        assert_eq!(tokens[0], (LojbanToken::Gismu, "klama"));
    }

    #[test]
    fn test_lujvo_in_sentence() {
        // "jbobau" in a sentence → Lujvo
        let tokens = tokenize("mi jbobau tavla");
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "mi"));
        assert_eq!(tokens[1], (LojbanToken::Lujvo, "jbobau"));
        assert_eq!(tokens[2], (LojbanToken::Gismu, "tavla"));
    }

    // ─── Empty / whitespace input ─────────────────────────────

    #[test]
    fn test_empty_input() {
        let tokens = tokenize("");
        assert!(tokens.is_empty());
    }

    #[test]
    fn test_whitespace_only() {
        let tokens = tokenize("   \t  \n  ");
        assert!(tokens.is_empty());
    }

    // ─── Single token types ───────────────────────────────────

    #[test]
    fn test_single_cmavo() {
        let tokens = tokenize("mi");
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "mi"));
    }

    #[test]
    fn test_single_gismu() {
        let tokens = tokenize("klama");
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0], (LojbanToken::Gismu, "klama"));
    }

    #[test]
    fn test_single_pause() {
        let tokens = tokenize(".");
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0], (LojbanToken::Pause, "."));
    }

    // ─── Metalinguistic operator tokens ───────────────────────

    #[test]
    fn test_metalinguistic_tokens() {
        let tokens = tokenize("si sa su zo zoi zei");
        assert_eq!(tokens[0], (LojbanToken::EraseWord, "si"));
        assert_eq!(tokens[1], (LojbanToken::EraseClass, "sa"));
        assert_eq!(tokens[2], (LojbanToken::EraseStream, "su"));
        assert_eq!(tokens[3], (LojbanToken::QuoteNext, "zo"));
        assert_eq!(tokens[4], (LojbanToken::QuoteDelimited, "zoi"));
        assert_eq!(tokens[5], (LojbanToken::GlueWords, "zei"));
    }

    // ─── Cmevla recognition ──────────────────────────────────

    #[test]
    fn test_cmevla_standalone() {
        // ".alis." is a name: pause + consonant-ending + pause
        let tokens = tokenize(".alis.");
        assert_eq!(tokens[0], (LojbanToken::Pause, "."));
        assert_eq!(tokens[1], (LojbanToken::Cmevla, "alis"));
        assert_eq!(tokens[2], (LojbanToken::Pause, "."));
    }

    #[test]
    fn test_cmevla_in_sentence() {
        let tokens = tokenize("la .alis. cu klama");
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "la"));
        assert_eq!(tokens[1], (LojbanToken::Pause, "."));
        assert_eq!(tokens[2], (LojbanToken::Cmevla, "alis"));
        assert_eq!(tokens[3], (LojbanToken::Pause, "."));
        assert_eq!(tokens[4], (LojbanToken::Cmavo, "cu"));
        assert_eq!(tokens[5], (LojbanToken::Gismu, "klama"));
    }

    // ─── Compound cmavo: contiguity edge cases ────────────────

    #[test]
    fn test_compound_cmavo_with_space_not_merged() {
        // "ga nai" spaced → two separate tokens, NOT "ganai"
        let tokens = tokenize("ga nai");
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "ga"));
        assert_eq!(tokens[1], (LojbanToken::Cmavo, "nai"));
    }

    #[test]
    fn test_real_cmevla_after_pause_not_reclassified() {
        // ".djan." preceded by pause → stays as Cmevla
        let tokens = tokenize("la .djan. cu klama");
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "la"));
        assert_eq!(tokens[1], (LojbanToken::Pause, "."));
        assert_eq!(tokens[2], (LojbanToken::Cmevla, "djan"));
        assert_eq!(tokens[3], (LojbanToken::Pause, "."));
    }

    // ─── Multiple compound cmavo in sequence ──────────────────

    #[test]
    fn test_multiple_compounds_in_sentence() {
        // The reclassify pass fuses multiple compound cmavo in one sentence
        // (ganai = forethought conditional, janai = afterthought connective; both kept).
        let tokens = tokenize("ganai mi klama gi janai do sutra");
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "ganai"));
        let janai_tok = tokens.iter().find(|(_, s)| *s == "janai");
        assert_eq!(janai_tok, Some(&(LojbanToken::Cmavo, "janai")));
    }

    // ─── Gismu morphology edge cases ──────────────────────────

    #[test]
    fn test_ccvcv_gismu() {
        // "blanu" is CCVCV pattern
        let tokens = tokenize("blanu");
        assert_eq!(tokens[0], (LojbanToken::Gismu, "blanu"));
    }

    #[test]
    fn test_cvccv_gismu() {
        // "klama" is CVCCV pattern
        let tokens = tokenize("klama");
        assert_eq!(tokens[0], (LojbanToken::Gismu, "klama"));
    }

    // ─── Multi-vowel cmavo ────────────────────────────────────

    #[test]
    fn test_multi_vowel_cmavo() {
        // "iu" and "ai" are multi-vowel cmavo
        let tokens = tokenize("ui iu ai");
        assert_eq!(tokens[0].0, LojbanToken::Cmavo);
        assert_eq!(tokens[1].0, LojbanToken::Cmavo);
        assert_eq!(tokens[2].0, LojbanToken::Cmavo);
    }

    // ─── Full sentence tokenization ───────────────────────────

    #[test]
    fn test_full_sentence_token_types() {
        let tokens = tokenize("mi klama lo zarci");
        assert_eq!(tokens.len(), 4);
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "mi"));
        assert_eq!(tokens[1], (LojbanToken::Gismu, "klama"));
        assert_eq!(tokens[2], (LojbanToken::Cmavo, "lo"));
        assert_eq!(tokens[3], (LojbanToken::Gismu, "zarci"));
    }

    #[test]
    fn test_sentence_with_cu_separator() {
        let tokens = tokenize("lo gerku cu klama lo zarci");
        assert_eq!(tokens.len(), 6);
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "lo"));
        assert_eq!(tokens[1], (LojbanToken::Gismu, "gerku"));
        assert_eq!(tokens[2], (LojbanToken::Cmavo, "cu"));
        assert_eq!(tokens[3], (LojbanToken::Gismu, "klama"));
    }

    #[test]
    fn test_sentence_separator_i() {
        let tokens = tokenize("mi klama .i do sutra");
        // .i is tokenized as Pause(".") + Cmavo("i")
        let i_tok = tokens
            .iter()
            .find(|(t, s)| *t == LojbanToken::Cmavo && *s == "i");
        assert!(i_tok.is_some());
    }

    // ─── Apostrophe in cmavo ──────────────────────────────────

    #[test]
    fn test_apostrophe_cmavo() {
        let tokens = tokenize("du'u si'o e'e");
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "du'u"));
        assert_eq!(tokens[1], (LojbanToken::Cmavo, "si'o"));
        assert_eq!(tokens[2], (LojbanToken::Cmavo, "e'e"));
    }

    // ─── Lex error channel (2026-06-10 panel regression) ──────────
    //
    // tokenize() used to stop at the first logos Err and DISCARD the rest
    // of the input with zero errors: `mi klama 7 do prami .i lo gerku cu
    // danlu` silently asserted just `mi klama`. The error channel records
    // each unlexable run's byte span and lexing continues.

    #[test]
    fn test_unlexable_char_mid_input_reported_and_rest_lexed() {
        let input = "mi klama 7 do prami .i lo gerku cu danlu";
        let (tokens, errors) = tokenize_with_errors(input);

        // The `7` must surface as exactly one error at its byte span.
        assert_eq!(errors.len(), 1, "expected one lex error, got {errors:?}");
        assert_eq!(&input[errors[0].start..errors[0].end], "7");
        assert_eq!(errors[0].start, 9); // "mi klama " is 9 bytes

        // Lexing must CONTINUE past the bad char: the trailing sentence's
        // tokens must all be present.
        for expected in ["do", "prami", "i", "lo", "gerku", "cu", "danlu"] {
            assert!(
                tokens.iter().any(|(_, s)| *s == expected),
                "token `{expected}` missing after the unlexable char — input truncated"
            );
        }
    }

    #[test]
    fn test_unlexable_run_coalesced_into_one_error() {
        let input = "mi 123 klama";
        let (tokens, errors) = tokenize_with_errors(input);

        // Adjacent unlexable chars coalesce into one maximal run.
        assert_eq!(
            errors.len(),
            1,
            "expected one coalesced run, got {errors:?}"
        );
        assert_eq!(&input[errors[0].start..errors[0].end], "123");

        // Both surrounding words still lex.
        assert!(tokens.iter().any(|(_, s)| *s == "mi"));
        assert!(tokens.iter().any(|(_, s)| *s == "klama"));
    }

    #[test]
    fn cmavo_regex_excludes_y() {
        // `y` is not a structural-cmavo vowel (a/e/i/o/u). A bare `y` and the
        // BY-letteral forms `by`/`cy` are unsupported: they lex as unlexable
        // runs (fail-closed), not as Cmavo tokens.
        let input = "y by cy";
        let (tokens, errors) = tokenize_with_errors(input);
        assert!(
            tokens.is_empty(),
            "y/by/cy must not lex as cmavo, got {tokens:?}"
        );
        assert_eq!(errors.len(), 3, "expected 3 unlexable runs, got {errors:?}");
        assert_eq!(&input[errors[0].start..errors[0].end], "y");
        assert_eq!(&input[errors[1].start..errors[1].end], "by");
        assert_eq!(&input[errors[2].start..errors[2].end], "cy");
    }

    #[test]
    fn valid_gismu_clusters_lex() {
        // Real gismu (both shapes) plus the GDPR/DDI proxy vocab must still lex
        // as a single Gismu with no errors — the cluster check rejects nothing valid.
        for w in [
            "klama", "prami", "gerku", "bridi", "mlatu", "ckape", "xukmi", "kajde", "zenba",
            "fanta", "cfila", "djacu",
        ] {
            let (tokens, errors) = tokenize_with_errors(w);
            assert!(
                errors.is_empty(),
                "`{w}` is a valid gismu, got errors {errors:?}"
            );
            assert_eq!(
                tokens,
                vec![(LojbanToken::Gismu, w)],
                "`{w}` should lex as one Gismu"
            );
        }
    }

    #[test]
    fn invalid_gismu_clusters_rejected() {
        // Invalid initial pairs (bk/pd), a voiced/unvoiced medial clash (t-b),
        // forbidden medials (mz/cx), and a doubled medial (t-t) all fail closed:
        // no Gismu token, one LexError spanning the whole word.
        for w in ["bkalu", "pdaca", "katba", "samza", "bacxa", "katta"] {
            let (tokens, errors) = tokenize_with_errors(w);
            assert!(
                !tokens.iter().any(|(t, _)| *t == LojbanToken::Gismu),
                "`{w}` must not lex as a Gismu, got {tokens:?}"
            );
            assert_eq!(
                errors.len(),
                1,
                "`{w}` should be one lex error, got {errors:?}"
            );
            assert_eq!(&w[errors[0].start..errors[0].end], w);
        }
    }

    #[test]
    fn invalid_gismu_in_sentence_rejected_rest_lexes() {
        // A malformed root mid-sentence is a positioned error; the rest still lexes.
        let input = "mi bkalu lo gerku";
        let (tokens, errors) = tokenize_with_errors(input);
        assert_eq!(errors.len(), 1, "expected one lex error, got {errors:?}");
        assert_eq!(&input[errors[0].start..errors[0].end], "bkalu");
        for expected in ["mi", "lo", "gerku"] {
            assert!(
                tokens.iter().any(|(_, s)| *s == expected),
                "token `{expected}` missing — input truncated"
            );
        }
    }

    #[test]
    fn test_separated_unlexable_runs_reported_individually() {
        let input = "mi 7 klama 9 do";
        let (tokens, errors) = tokenize_with_errors(input);

        assert_eq!(
            errors.len(),
            2,
            "expected two separate runs, got {errors:?}"
        );
        assert_eq!(&input[errors[0].start..errors[0].end], "7");
        assert_eq!(&input[errors[1].start..errors[1].end], "9");
        assert!(tokens.iter().any(|(_, s)| *s == "do"));
    }

    #[test]
    fn test_clean_input_has_no_lex_errors() {
        let (tokens, errors) = tokenize_with_errors("lo gerku cu klama lo zarci");
        assert!(errors.is_empty(), "clean input produced {errors:?}");
        assert_eq!(tokens.len(), 6);
    }

    #[test]
    fn test_tokenize_wrapper_skips_unlexable_and_continues() {
        // The error-discarding wrapper must not truncate either.
        let tokens = tokenize("mi klama 7 do prami");
        assert!(tokens.iter().any(|(_, s)| *s == "prami"));
    }
}
