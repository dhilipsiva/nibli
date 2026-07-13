/// Dictionary entry with optional arity, English gloss, and place-frame template.
///
/// `template` is a curated English place-frame for the predicate using `{x1}`..`{x5}`
/// placeholders (e.g. `gerku` -> `"{x1} is a dog"`, `klama` -> `"{x1} goes to {x2}
/// from {x3} via {x4} using {x5}"`). An empty `template` means no curated frame
/// exists; the IR renderer falls back to a generic gloss-based frame.
#[derive(Clone, Copy, Debug)]
pub struct DictEntry {
    pub arity: Option<usize>,
    pub gloss: &'static str,
    pub template: &'static str,
}

include!(concat!(env!("OUT_DIR"), "/generated_dictionary.rs"));

/// Canonical place-count extraction from a lensisku definition. Used by `build.rs`
/// (via `#[path]`) to derive arity; exposed here so it is unit-tested by
/// `cargo test -p nibli-lexicon` (CI runs the no-data build, which never calls it,
/// so the pure-function tests are the coverage).
pub mod arity;

/// Look up the arity of a Lojban word (gismu/lujvo only; cmavo returns None).
pub fn get_arity(word: &str) -> Option<usize> {
    DICTIONARY.get(word).and_then(|e| e.arity)
}

/// Look up the primary English gloss of a Lojban word.
pub fn get_gloss(word: &str) -> Option<&'static str> {
    DICTIONARY.get(word).map(|e| e.gloss)
}

/// Look up the curated English place-frame template of a Lojban word.
///
/// Returns `None` when no curated template exists (the entry's `template` is
/// empty) — callers should then build a generic frame from [`get_gloss`] and
/// [`get_arity`]. e.g. `get_template("gerku")` -> `Some("{x1} is a dog")`.
pub fn get_template(word: &str) -> Option<&'static str> {
    DICTIONARY
        .get(word)
        .map(|e| e.template)
        .filter(|t| !t.is_empty())
}

/// Word-by-word robotic back-translation of Lojban text to English glosses.
pub fn back_translate(lojban: &str) -> String {
    lojban
        .split_whitespace()
        .map(|token| {
            // cmevla (a dot-delimited proper name like `.adam.`): the
            // back-translation of a name is the name itself — return the inner
            // form verbatim, never a dictionary gloss. Consulting the dictionary
            // would DROP a name whose inner collides with a suppressed-gloss cmavo
            // (`.cu.`/`.la.` -> "" -> filtered out) and MISTRANSLATE one colliding
            // with a real gloss (`.lo.` -> "the").
            if token.starts_with('.') && token.ends_with('.') && token.len() > 2 {
                return token[1..token.len() - 1].to_string();
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
        // Curated glosses win over the alphabetically-first jbovlaste
        // glossword (gerku's glosswords are bitch/canine/dog)
        assert_eq!(get_gloss("gerku"), Some("dog"));
        assert_eq!(get_gloss("prenu"), Some("person"));
        assert_eq!(get_gloss("curmi"), Some("permit"));
        assert_eq!(get_gloss("bilga"), Some("must"));
        assert_eq!(get_gloss("prami"), Some("love"));
        assert!(get_gloss("klama").is_some());
    }

    #[test]
    fn test_cmavo_gloss_overrides() {
        assert_eq!(get_gloss("lo"), Some("the"));
        assert_eq!(get_gloss("na"), Some("not"));
        assert_eq!(get_gloss("pu"), Some("[past]"));
    }

    #[test]
    fn test_corpus_proxy_templates() {
        // Curated place-frames for the GDPR / drug-interaction proxy vocabulary
        // (identical in the data and no-data build modes — single-sourced).
        assert_eq!(get_template("zanru"), Some("{x1} approves of {x2}"));
        assert_eq!(get_template("pilno"), Some("{x1} uses {x2}"));
        assert_eq!(get_template("katna"), Some("{x1} cuts {x2}"));
        assert_eq!(get_template("zenba"), Some("{x1} increases"));
        assert_eq!(get_template("cinla"), Some("{x1} is thin"));
        assert_eq!(get_template("ckape"), Some("{x1} is in danger"));
        assert_eq!(get_template("vimcu"), Some("{x1} is removed"));
        // Already-curated regulatory words stay curated.
        assert_eq!(get_template("curmi"), Some("{x1} permits {x2}"));
        assert_eq!(get_template("javni"), Some("{x1} is a rule about {x2}"));
    }

    #[test]
    fn test_back_translate_basic() {
        let result = back_translate("lo gerku cu klama lo zarci");
        // Should contain glosses for gerku and klama (whatever jbovlaste provides)
        assert!(result.contains("the"), "Expected 'the' in: {}", result);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_back_translate_default_syllogism() {
        // The Transparency Triad UI's default example (book Ch 19)
        assert_eq!(back_translate("ro lo gerku cu danlu"), "all the dog animal");
    }

    #[test]
    fn test_back_translate_cmevla() {
        let result = back_translate(".adam. prami .evas.");
        assert!(result.contains("adam"), "Expected 'adam' in: {}", result);
        assert!(result.contains("evas"), "Expected 'evas' in: {}", result);
    }

    #[test]
    fn test_back_translate_cmevla_collides_with_dictionary_entry() {
        // A dot-delimited name is a proper name: return the inner form verbatim,
        // never the dictionary gloss. Regression for two collision cases:
        //   - inner is a SUPPRESSED-gloss cmavo (`cu` -> "") — the name must NOT
        //     vanish through the empty-gloss filter.
        assert_eq!(back_translate(".cu."), "cu");
        assert_eq!(back_translate(".cu. prami"), "cu love");
        //   - inner has a REAL gloss (`lo` -> "the") — the name must stay the
        //     name, not become the content word.
        assert_eq!(back_translate(".lo."), "lo");
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
