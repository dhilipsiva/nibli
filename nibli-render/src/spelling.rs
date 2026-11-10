//! Constants keep the spelling they were typed with. The reasoner lowercases every constant
//! (`StrawHatCrew` reasons as `strawhatcrew`), so the proof trace and the logic buffer only know
//! the lowercase form. The KR the author wrote is still at hand: the trace cites the asserted
//! lines and the rules, and a caller can pass the query text. A spelling table built from those
//! restores the author's spelling at render time; a constant typed in lowercase stays as it was.

use std::cell::RefCell;
use std::collections::BTreeMap;

use nibli_types::logic::{ProofRule, ProofTrace};

thread_local! {
    static TABLE: RefCell<Option<BTreeMap<String, String>>> = const { RefCell::new(None) };
}

/// Every capitalised identifier of a KR text, keyed by its lowercase form (first spelling wins).
pub(crate) fn learn(table: &mut BTreeMap<String, String>, kr: &str) {
    let bytes = kr.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b.is_ascii_alphanumeric() || b == b'_' {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            let word = &kr[start..i];
            let preceded_by_sigil = start > 0 && bytes[start - 1] == b'$';
            if word.as_bytes()[0].is_ascii_uppercase() && !preceded_by_sigil {
                let lower = word.to_ascii_lowercase();
                if lower != word {
                    table.entry(lower).or_insert_with(|| word.to_string());
                }
            }
        } else {
            i += 1;
        }
    }
}

/// The spelling table of a trace (its citations) and, when given, of the query text.
pub(crate) fn table_from(
    trace: Option<&ProofTrace>,
    source: Option<&str>,
) -> BTreeMap<String, String> {
    let mut table = BTreeMap::new();
    if let Some(kr) = source {
        learn(&mut table, kr);
    }
    if let Some(trace) = trace {
        for step in &trace.steps {
            match &step.rule {
                ProofRule::Asserted { sources, .. } => {
                    for c in sources {
                        learn(&mut table, &c.label);
                    }
                }
                ProofRule::Derived { sources, .. } | ProofRule::Presupposed { sources, .. } => {
                    for c in sources {
                        learn(&mut table, &c.assertion_label);
                    }
                }
                _ => {}
            }
        }
    }
    table
}

/// Run `f` with `table` as the active spelling; the previous table is restored after.
pub(crate) fn with_spelling<R>(table: BTreeMap<String, String>, f: impl FnOnce() -> R) -> R {
    let prev = TABLE.with(|t| t.borrow_mut().replace(table));
    let out = f();
    TABLE.with(|t| *t.borrow_mut() = prev);
    out
}

/// The author's spelling of a lowercase constant, when the active table knows it.
pub(crate) fn restore(word: &str) -> Option<String> {
    TABLE.with(|t| t.borrow().as_ref().and_then(|m| m.get(word).cloned()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capitalised_identifiers_are_learned_by_their_lowercase_form() {
        let mut t = BTreeMap::new();
        learn(&mut t, "captain(Luffy, StrawHatCrew). # about: luffy");
        learn(&mut t, "all $e: exist($e, Memory, Loaded) -> person($e).");
        learn(&mut t, "owns(Dhilipsiva, NixOS).");
        assert_eq!(
            t.get("strawhatcrew").map(String::as_str),
            Some("StrawHatCrew")
        );
        assert_eq!(t.get("nixos").map(String::as_str), Some("NixOS"));
        assert_eq!(t.get("loaded").map(String::as_str), Some("Loaded"));
        assert!(!t.contains_key("captain") && !t.contains_key("e"));
    }

    #[test]
    fn restore_is_scoped_to_the_active_table() {
        let mut t = BTreeMap::new();
        learn(&mut t, "dog(Bucchi).");
        assert_eq!(restore("bucchi"), None);
        with_spelling(t, || {
            assert_eq!(restore("bucchi").as_deref(), Some("Bucchi"))
        });
        assert_eq!(restore("bucchi"), None);
    }
}
