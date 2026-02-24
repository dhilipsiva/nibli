use logos::Logos;

#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(skip r"[ \t\n\f]+")] // Whitespace is ignored, but explicit pauses (.) are not
pub enum LojbanToken {
    // --------------------------------------------------
    // Metalinguistic Operators (Must be intercepted)
    // --------------------------------------------------
    #[token("si")]
    EraseWord,

    #[token("sa")]
    EraseClass,

    #[token("su")]
    EraseStream,

    #[token("zo")]
    QuoteNext,

    #[token("zoi")]
    QuoteDelimited,

    #[token("zei")]
    GlueWords,

    // --------------------------------------------------
    // Morphological Classes
    // --------------------------------------------------

    // Gismu: CVCCV or CCVCV structure (simplified for demonstration,
    // real phonotactics check for specific valid consonant clusters)
    #[regex(r"([bcdfghjklmnprstvxz][aeiou][bcdfghjklmnprstvxz][bcdfghjklmnprstvxz][aeiou])|([bcdfghjklmnprstvxz][bcdfghjklmnprstvxz][aeiou][bcdfghjklmnprstvxz][aeiou])")]
    Gismu,

    // Cmevla (Names): Must end in a consonant.
    // No dots in body — dots are pause tokens and must not be consumed as part of a word.
    // Final character is explicitly a Lojban consonant, not a negated vowel class.
    #[regex(r"[a-zA-Z']+[bcdfghjklmnprstvxzBCDFGHJKLMNPRSTVXZ]")]
    Cmevla,

    // Cmavo (Structure words): 1-to-many vowels, optionally preceded by one consonant
    // This acts as a fallback for structural words not explicitly tokenized above.
    #[regex(r"[bcdfghjklmnprstvxz]?[aeiouy']+")]
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
    // GA selma'o + nai — forethought connectives
    "ganai", "genai", "ginai", "gonai", "gunai",
    // JA selma'o + nai — afterthought logical connectives
    "janai", "jenai", "jonai", "junai",
    // PU selma'o + nai — tense negation
    "punai", "canai", "banai",
];

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

/// Tokenizer: Logos DFA + post-lex compound cmavo reclassification.
pub fn tokenize(input: &str) -> Vec<(LojbanToken, &str)> {
    let mut lex = LojbanToken::lexer(input);
    let mut tokens = Vec::new();

    while let Some(Ok(token)) = lex.next() {
        tokens.push((token, lex.slice()));
    }

    reclassify_compounds(&mut tokens, input);
    tokens
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
    fn gonai_lexes_as_cmavo() {
        let tokens = tokenize("gonai mi klama gi do ciska");
        assert_eq!(tokens[0], (LojbanToken::Cmavo, "gonai"));
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
}
