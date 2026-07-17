//! The nibli KR reserved-word list — SINGLE SOURCE (NIBLI_KR.md §2).
//!
//! Consumed by the corpus const-validator (a shipped name must never collide
//! with a keyword), by the nibli-kr grammar's self-guarded `kw_*` rules (pinned
//! equal to this list by a conformance test), and by `tools/lexigen`'s
//! sanitization. Keep sorted (unit-tested); every entry must be a valid
//! nibli KR identifier shape (`[a-z][a-z0-9_]*`).

/// Every nibli KR keyword, sorted ascending. A predicate alias or place label may
/// never equal one of these.
pub const RESERVED_WORDS: &[&str] = &[
    "all",
    "also",
    "amount",
    "concept",
    "event",
    "every",
    "exactly",
    "fact",
    "future",
    "it",
    "it_a",
    "it_e",
    "it_i",
    "it_o",
    "it_u",
    "may",
    "me",
    "must",
    "no",
    "now",
    "past",
    "property",
    "seeming",
    "slot",
    "some",
    "that",
    "the",
    "this",
    "via",
    "we",
    "we_all",
    "we_others",
    "where",
    "yonder",
    "you",
    "you_all",
];

/// True when `word` is a nibli KR keyword.
pub fn is_reserved(word: &str) -> bool {
    RESERVED_WORDS.binary_search(&word).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sorted_and_deduped() {
        for pair in RESERVED_WORDS.windows(2) {
            assert!(
                pair[0] < pair[1],
                "RESERVED_WORDS must stay sorted+deduped: {:?} !< {:?}",
                pair[0],
                pair[1]
            );
        }
    }

    #[test]
    fn expected_membership() {
        // The NIBLI_KR §2 list — 36 keywords.
        assert_eq!(RESERVED_WORDS.len(), 36);
        for kw in ["must", "it_a", "seeming", "some", "the", "every", "slot"] {
            assert!(is_reserved(kw), "{kw} must be reserved");
        }
        assert!(!is_reserved("goes"));
        assert!(!is_reserved("dog"));
    }

    #[test]
    fn keywords_are_ident_shaped() {
        for kw in RESERVED_WORDS {
            let mut chars = kw.chars();
            assert!(
                matches!(chars.next(), Some('a'..='z'))
                    && chars.all(|c| matches!(c, 'a'..='z' | '0'..='9' | '_')),
                "keyword {kw:?} is not ident-shaped"
            );
        }
    }
}
