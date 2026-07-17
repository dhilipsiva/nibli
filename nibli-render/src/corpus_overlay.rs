//! Domain-gloss overlays for the shipped curated corpora.
//!
//! These are the documented "reader's overlay" for each case-study corpus (the
//! mapping disclosed in the corpus comments and the book's Ch 20/21 tables): the
//! proxy gismu (`prevents`, `se permits`, …) and the opaque transliterated constants
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
/// `cuts` is keyed `se`-converted: the corpus uses `se cuts` ("is metabolized
/// by"), whose IR stores the enzyme in x1 and the substrate in x2, so the
/// template reorders to read substrate-first.
pub static DRUG_INTERACTIONS_OVERLAY: DomainGloss = DomainGloss {
    templates: &[
        ("prevents", "{x1} inhibits {x2}"),
        ("cuts", "{x2} is metabolized by {x1}"),
        ("thin", "{x1} has a narrow therapeutic index"),
        ("increases", "{x1} has a raised concentration"),
        ("dangerous", "{x1} is at toxicity risk"),
        ("warns", "{x1} warrants a safety alert"),
        ("chemical", "{x1} is a drug"),
        ("uses", "{x1} takes {x2}"),
    ],
    glosses: &[("chemical", "drug")],
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
/// `permits` is keyed `se`-converted: `se permits` ("has a lawful basis for
/// processing") stores the data subject in x2, so the template reads off x2.
pub static GDPR_OVERLAY: DomainGloss = DomainGloss {
    templates: &[
        ("permits", "{x2} has a lawful basis for processing"),
        ("data", "{x1} is personal data"),
        ("approves", "{x1} consents"),
        ("promise", "{x1} is bound by a contract"),
        ("obliged", "{x1} is under a legal obligation"),
        ("flaw", "{x1} has suffered a breach"),
        // Embedded `lo nu <event>` obligation/right contents.
        ("correct", "{x1} is accurate"),
        ("shelter", "{x1} is kept secure"),
        ("necessary", "{x1} is necessary"),
        ("exact", "{x1} has a specific basis"),
        ("message", "{x1} notifies"),
        ("removes", "{x1} is erased"),
        ("discovers", "{x1} accesses {x2}"),
    ],
    glosses: &[("data", "personal data")],
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
            DRUG_INTERACTIONS_OVERLAY.template("prevents"),
            Some("{x1} inhibits {x2}")
        );
        // `se cuts` reorders so the substrate (x2) heads the clause.
        assert_eq!(
            DRUG_INTERACTIONS_OVERLAY.template("cuts"),
            Some("{x2} is metabolized by {x1}")
        );
        assert_eq!(
            DRUG_INTERACTIONS_OVERLAY.template("dangerous"),
            Some("{x1} is at toxicity risk")
        );
        assert_eq!(DRUG_INTERACTIONS_OVERLAY.name("varfarin"), Some("warfarin"));
        assert_eq!(DRUG_INTERACTIONS_OVERLAY.name("siptucin"), Some("CYP2C9"));
    }

    #[test]
    fn gdpr_overlay_key_mappings() {
        assert_eq!(
            GDPR_OVERLAY.template("permits"),
            Some("{x2} has a lawful basis for processing")
        );
        assert_eq!(GDPR_OVERLAY.template("data"), Some("{x1} is personal data"));
        assert_eq!(GDPR_OVERLAY.name("akmes"), Some("AkmeCorp"));
    }
}
