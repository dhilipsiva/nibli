//! Structured error types shared across the pipeline.

/// Detailed syntax error with source location.
#[derive(Clone, Debug)]
pub struct SyntaxDetail {
    pub message: String,
    pub line: u32,
    pub column: u32,
}

/// Unified error type for the gerna → smuni → logji pipeline.
#[derive(Clone, Debug)]
pub enum NibliError {
    /// Syntax error from the parser (gerna).
    Syntax(SyntaxDetail),
    /// Semantic error from the compiler (smuni).
    Semantic(String),
    /// Reasoning error from the inference engine (logji).
    Reasoning(String),
    /// Backend error from external compute dispatch. Fields: (predicate, message).
    Backend((String, String)),
}

// FORMAL CONTRACT: the `[Syntax Error]` / `[Semantic Error]` / `[Reasoning Error]`
// / `[Backend Error]` prefixes below are a stable cross-consumer interface — they
// are the de-facto error CLASS encoding wherever the typed `NibliError` has been
// flattened to a `String` (tavla's public API → nibli-server's `error_class`
// classifier; gasnu's `[Xxx Error]` REPL output; the nibli-ui `strip_prefix`
// renderer). Do NOT change a prefix without updating those classifiers.
impl std::fmt::Display for NibliError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NibliError::Syntax(d) => {
                write!(
                    f,
                    "[Syntax Error] line {}:{}: {}",
                    d.line, d.column, d.message
                )
            }
            NibliError::Semantic(m) => write!(f, "[Semantic Error] {}", m),
            NibliError::Reasoning(m) => write!(f, "[Reasoning Error] {}", m),
            NibliError::Backend((k, m)) => write!(f, "[Backend Error] {} — {}", k, m),
        }
    }
}
