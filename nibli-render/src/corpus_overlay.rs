//! Domain-gloss overlays for the shipped curated corpora.
//!
//! These are the documented "reader's overlay" for each case-study corpus (the
//! mapping disclosed in the corpus comments and the book's Ch 20/21 tables): the
//! proxy gismu (`fanta`, `se curmi`, …) and the opaque transliterated constants
//! (`varfarin`, `siptucin`, …) rendered in real domain language. They are applied
//! ONLY when the matching read-only example is loaded in the UI; Custom KBs and
//! every other surface fall through to the engine's literal glosses.
//!
//! Honesty note: nothing here is engine-derived knowledge. The overlay is a
//! display layer that makes the proof read consistently with the example's
//! already-domain-English Source tab. It never touches the back-translation
//! (the firewall's verification surface).

use crate::overlay::DomainGloss;

/// Drug-interaction case study (`drug-interactions.lojban`, book Ch 21).
///
/// `katna` is keyed `se`-converted: the corpus uses `se katna` ("is metabolized
/// by"), whose IR stores the enzyme in x1 and the substrate in x2, so the
/// template reorders to read substrate-first.
pub static DRUG_INTERACTIONS_OVERLAY: DomainGloss = DomainGloss {
    templates: &[
        ("fanta", "{x1} inhibits {x2}"),
        ("katna", "{x2} is metabolized by {x1}"),
        ("cinla", "{x1} has a narrow therapeutic index"),
        ("zenba", "{x1} has a raised concentration"),
        ("ckape", "{x1} is at toxicity risk"),
        ("kajde", "{x1} warrants a safety alert"),
        ("xukmi", "{x1} is a drug"),
        ("pilno", "{x1} takes {x2}"),
    ],
    glosses: &[("xukmi", "drug")],
    names: &[
        ("varfarin", "warfarin"),
        ("flukonazol", "fluconazole"),
        ("apiksaban", "apixaban"),
        ("fenitoin", "phenytoin"),
        ("siptucin", "CYP2C9"),
        ("sipcivon", "CYP3A4"),
        ("adam", "Adam"),
    ],
};

/// GDPR compliance case study (`gdpr.lojban`, book Ch 20).
///
/// `curmi` is keyed `se`-converted: `se curmi` ("has a lawful basis for
/// processing") stores the data subject in x2, so the template reads off x2.
pub static GDPR_OVERLAY: DomainGloss = DomainGloss {
    templates: &[
        ("curmi", "{x2} has a lawful basis for processing"),
        ("datni", "{x1} is personal data"),
        ("zanru", "{x1} consents"),
        ("nupre", "{x1} is bound by a contract"),
        ("bilga", "{x1} is under a legal obligation"),
        ("cfila", "{x1} has suffered a breach"),
        // Embedded `lo nu <event>` obligation/right contents.
        ("drani", "{x1} is accurate"),
        ("marbi", "{x1} is kept secure"),
        ("sarcu", "{x1} is necessary"),
        ("satci", "{x1} has a specific basis"),
        ("notci", "{x1} notifies"),
        ("vimcu", "{x1} is erased"),
        ("facki", "{x1} accesses {x2}"),
    ],
    glosses: &[("datni", "personal data")],
    names: &[
        ("adam", "Adam"),
        ("akmes", "AkmeCorp"),
        ("gugli", "Google"),
        ("kanrek", "Adam's health record"),
        ("ordrek", "Adam's ordinary record"),
    ],
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ddi_overlay_key_mappings() {
        assert_eq!(
            DRUG_INTERACTIONS_OVERLAY.template("fanta"),
            Some("{x1} inhibits {x2}")
        );
        // `se katna` reorders so the substrate (x2) heads the clause.
        assert_eq!(
            DRUG_INTERACTIONS_OVERLAY.template("katna"),
            Some("{x2} is metabolized by {x1}")
        );
        assert_eq!(
            DRUG_INTERACTIONS_OVERLAY.template("ckape"),
            Some("{x1} is at toxicity risk")
        );
        assert_eq!(DRUG_INTERACTIONS_OVERLAY.name("varfarin"), Some("warfarin"));
        assert_eq!(DRUG_INTERACTIONS_OVERLAY.name("siptucin"), Some("CYP2C9"));
    }

    #[test]
    fn gdpr_overlay_key_mappings() {
        assert_eq!(
            GDPR_OVERLAY.template("curmi"),
            Some("{x2} has a lawful basis for processing")
        );
        assert_eq!(
            GDPR_OVERLAY.template("datni"),
            Some("{x1} is personal data")
        );
        assert_eq!(GDPR_OVERLAY.name("akmes"), Some("AkmeCorp"));
    }
}
