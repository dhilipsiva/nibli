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

    // Cmevla (Names): Must end in a consonant
    #[regex(r"[a-zA-Z'\.]+[^aeiouy \t\n\f\.]")]
    Cmevla,

    // Cmavo (Structure words): 1-to-many vowels, optionally preceded by one consonant
    // This acts as a fallback for structural words not explicitly tokenized above.
    #[regex(r"[bcdfghjklmnprstvxz]?[aeiouy']+")]
    Cmavo,

    // Explicit Pauses
    #[token(".")]
    Pause,
}

/// Tokenizer wrapper that yields zero-copy string slices paired with their classification.
pub fn tokenize(input: &str) -> Vec<(LojbanToken, &str)> {
    let mut lex = LojbanToken::lexer(input);
    let mut tokens = Vec::new();
    
    while let Some(Ok(token)) = lex.next() {
        tokens.push((token, lex.slice()));
    }
    
    tokens
}
