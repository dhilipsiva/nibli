//! Per-example domain-gloss overlay: an OPTIONAL display layer that renders a
//! curated corpus's proxy predicates and opaque constants in real domain terms
//! (`prevents` -> "inhibits", `flukonazol` -> "fluconazole"), scoped to a loaded
//! example.
//!
//! The engine dictionary (`nibli_lexicon`) is always the FALLBACK: an example
//! with no entry for a relation, and every Custom (user-authored) KB, render with
//! the literal glosses. The overlay is installed only for the duration of one
//! render call via [`with_overlay`] and read back through [`active`], so it never
//! leaks into the back-translation ("What Nibli Understood") tab — that surface
//! calls the renderer WITHOUT an overlay and stays deliberately literal as the
//! firewall's verification view.

use std::cell::Cell;

/// A domain-term overlay for one curated example. The tables are tiny (a handful
/// of entries each), so a linear scan is fine.
#[derive(Clone, Copy, Debug)]
pub struct DomainGloss {
    /// Place-frame template overrides keyed by bare gismu. Placeholders `{x1}`..
    /// may reorder, e.g. `se cuts` -> "{x2} is metabolized by {x1}" (the IR has
    /// already swapped the `se` args, so the template keys on the bare gismu).
    pub templates: &'static [(&'static str, &'static str)],
    /// Single-word noun-gloss overrides keyed by gismu (e.g. the "a <noun>" of an
    /// existence clause).
    pub glosses: &'static [(&'static str, &'static str)],
    /// Display-name overrides keyed by constant (cmevla), e.g. `varfarin` ->
    /// "warfarin", `siptucin` -> "CYP2C9".
    pub names: &'static [(&'static str, &'static str)],
}

impl DomainGloss {
    /// Overlay place-frame template for `relation`, if any.
    pub fn template(&self, relation: &str) -> Option<&'static str> {
        lookup(self.templates, relation)
    }

    /// Overlay noun gloss for `relation`, if any.
    pub fn gloss(&self, relation: &str) -> Option<&'static str> {
        lookup(self.glosses, relation)
    }

    /// Overlay display name for a constant, if any.
    pub fn name(&self, constant: &str) -> Option<&'static str> {
        lookup(self.names, constant)
    }
}

fn lookup(table: &[(&'static str, &'static str)], key: &str) -> Option<&'static str> {
    table.iter().find(|(k, _)| *k == key).map(|(_, v)| *v)
}

thread_local! {
    /// The overlay active for the current render call (`None` = dictionary
    /// fallback). A `&'static` reference, so the cell is `Copy`.
    static OVERLAY: Cell<Option<&'static DomainGloss>> = const { Cell::new(None) };
}

/// Run `f` with `overlay` installed as the active render overlay, restoring the
/// previous value afterward (panic-safe via the drop guard). Intended for the
/// single-threaded UI render path; other threads see `None`.
pub(crate) fn with_overlay<T>(overlay: Option<&'static DomainGloss>, f: impl FnOnce() -> T) -> T {
    struct Guard(Option<&'static DomainGloss>);
    impl Drop for Guard {
        fn drop(&mut self) {
            OVERLAY.with(|o| o.set(self.0));
        }
    }
    let _guard = OVERLAY.with(|o| Guard(o.replace(overlay)));
    f()
}

/// The overlay active for this render call, if any.
pub(crate) fn active() -> Option<&'static DomainGloss> {
    OVERLAY.with(Cell::get)
}

#[cfg(test)]
mod tests {
    use super::*;

    static SAMPLE: DomainGloss = DomainGloss {
        templates: &[("dangerous", "{x1} is at toxicity risk")],
        glosses: &[("chemical", "drug")],
        names: &[("varfarin", "warfarin")],
    };

    #[test]
    fn lookups_resolve() {
        assert_eq!(
            SAMPLE.template("dangerous"),
            Some("{x1} is at toxicity risk")
        );
        assert_eq!(SAMPLE.template("increases"), None);
        assert_eq!(SAMPLE.gloss("chemical"), Some("drug"));
        assert_eq!(SAMPLE.name("varfarin"), Some("warfarin"));
        assert_eq!(SAMPLE.name("adam"), None);
    }

    #[test]
    fn overlay_is_scoped_and_restored() {
        assert!(active().is_none());
        with_overlay(Some(&SAMPLE), || {
            assert!(std::ptr::eq(active().unwrap(), &SAMPLE));
            // Nested override + restore.
            with_overlay(None, || assert!(active().is_none()));
            assert!(std::ptr::eq(active().unwrap(), &SAMPLE));
        });
        assert!(active().is_none());
    }
}
