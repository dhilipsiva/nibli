//! The front-end language selector shared by every runtime surface.
//!
//! Two input languages compile to the same `ast::AstBuffer` (and from there
//! through the same smuni→logji pipeline): **Klaro** (the klaro crate;
//! SURFACE_SYNTAX.md) and **Lojban** (gerna). Klaro is the DEFAULT since THE
//! FLIP (2026-07-12, KLARO_TODO); Lojban remains fully supported during the
//! dual-front-end phase (`--lang lojban` / `NIBLI_LANG=lojban` / `:lojban`).
//! `FromStr` is the parser for `NIBLI_LANG`-style configuration
//! (`"klaro"` / `"lojban"`, lowercase).

/// Which surface language a text entry point parses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Language {
    /// The default since THE FLIP (2026-07-12).
    #[default]
    Klaro,
    Lojban,
}

impl std::fmt::Display for Language {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Language::Klaro => write!(f, "klaro"),
            Language::Lojban => write!(f, "lojban"),
        }
    }
}

impl std::str::FromStr for Language {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "klaro" => Ok(Language::Klaro),
            "lojban" => Ok(Language::Lojban),
            other => Err(format!(
                "unknown language {other:?} — expected \"klaro\" or \"lojban\""
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_is_klaro_since_the_flip() {
        assert_eq!(Language::default(), Language::Klaro);
    }

    #[test]
    fn display_from_str_round_trip() {
        for lang in [Language::Klaro, Language::Lojban] {
            assert_eq!(lang.to_string().parse::<Language>(), Ok(lang));
        }
    }

    #[test]
    fn from_str_rejects_unknown_names() {
        let err = "english".parse::<Language>().unwrap_err();
        assert!(err.contains("unknown language"), "{err}");
        assert!("Lojban".parse::<Language>().is_err(), "case-sensitive");
    }
}
