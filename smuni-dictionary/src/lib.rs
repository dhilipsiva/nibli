/// Dictionary entry with optional arity and English gloss.
#[derive(Clone, Copy, Debug)]
pub struct DictEntry {
    pub arity: Option<usize>,
    pub gloss: &'static str,
}

include!(concat!(env!("OUT_DIR"), "/generated_dictionary.rs"));

/// Look up the arity of a Lojban word (gismu/lujvo only; cmavo returns None).
pub fn get_arity(word: &str) -> Option<usize> {
    DICTIONARY.get(word).and_then(|e| e.arity)
}

/// Look up the primary English gloss of a Lojban word.
pub fn get_gloss(word: &str) -> Option<&'static str> {
    DICTIONARY.get(word).map(|e| e.gloss)
}

/// Word-by-word robotic back-translation of Lojban text to English glosses.
pub fn back_translate(lojban: &str) -> String {
    lojban
        .split_whitespace()
        .map(|token| {
            // cmevla: starts and ends with '.'
            if token.starts_with('.') && token.ends_with('.') && token.len() > 2 {
                let inner = &token[1..token.len() - 1];
                // Could be a cmavo like ".i" — check dictionary first
                if let Some(entry) = DICTIONARY.get(inner) {
                    return entry.gloss.to_string();
                }
                return inner.to_string();
            }
            // Regular token: look up in dictionary
            if let Some(entry) = DICTIONARY.get(token) {
                return entry.gloss.to_string();
            }
            // Unknown: pass through
            token.to_string()
        })
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gismu_arity() {
        assert_eq!(get_arity("klama"), Some(5));
        assert_eq!(get_arity("gerku"), Some(2));
        assert_eq!(get_arity("prami"), Some(2));
    }

    #[test]
    fn test_cmavo_no_arity() {
        assert_eq!(get_arity("lo"), None);
        assert_eq!(get_arity("cu"), None);
    }

    #[test]
    fn test_gismu_gloss() {
        // jbovlaste first glossword for gerku is "bitch" (female dog)
        assert!(get_gloss("gerku").is_some());
        assert!(get_gloss("klama").is_some());
        assert_eq!(get_gloss("prami"), Some("love"));
    }

    #[test]
    fn test_cmavo_gloss_overrides() {
        assert_eq!(get_gloss("lo"), Some("the"));
        assert_eq!(get_gloss("na"), Some("not"));
        assert_eq!(get_gloss("pu"), Some("[past]"));
    }

    #[test]
    fn test_back_translate_basic() {
        let result = back_translate("lo gerku cu klama lo zarci");
        // Should contain glosses for gerku and klama (whatever jbovlaste provides)
        assert!(result.contains("the"), "Expected 'the' in: {}", result);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_back_translate_cmevla() {
        let result = back_translate(".adam. prami .evas.");
        assert!(result.contains("adam"), "Expected 'adam' in: {}", result);
        assert!(result.contains("evas"), "Expected 'evas' in: {}", result);
    }

    #[test]
    fn test_back_translate_empty() {
        assert_eq!(back_translate(""), "");
    }

    #[test]
    fn test_structural_suppressed() {
        // "cu" and "ku" should be suppressed (empty gloss)
        let result = back_translate("cu ku");
        assert_eq!(result, "");
    }
}
