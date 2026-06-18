//! Per-predicate English place-frame templates and filling.
//!
//! A *frame* is an English clause schema for a predicate using `{x1}`..`{x5}`
//! placeholders. The curated table in `smuni-dictionary` supplies frames for the
//! predicates the corpora use (`gerku` -> `"{x1} is a dog"`); everything else
//! falls back to a generic gloss-based frame here.

use smuni_dictionary::{get_arity, get_gloss, get_template};

/// Resolve a fill-template (a string with `{x1}`..`{xN}` placeholders) for a
/// relation: the curated template if present, else a generic gloss+arity frame.
pub(crate) fn frame_template(relation: &str) -> String {
    if let Some(t) = get_template(relation) {
        return t.to_string();
    }
    let gloss = get_gloss(relation).unwrap_or(relation);
    let arity = get_arity(relation).unwrap_or(1).max(1);
    generic_template(gloss, arity)
}

/// Generic frame when no curated template exists. Imperfect but honest: a 1-place
/// predicate reads "X is <gloss>", an n-place reads "X <gloss> Y Z …".
fn generic_template(gloss: &str, arity: usize) -> String {
    let mut t = if arity <= 1 {
        format!("{{x1}} is {gloss}")
    } else {
        format!("{{x1}} {gloss}")
    };
    for i in 2..=arity {
        t.push_str(&format!(" {{x{i}}}"));
    }
    t
}

/// Fill a template with rendered place fillers. `places[i]` is the filler for
/// place `x(i+1)`; `None` means the place was unspecified (`zo'e`) or absent.
///
/// Unfilled places are dropped by truncating the template at the first unfilled
/// placeholder (Lojban leaves trailing places implicit, so this reads cleanly:
/// `klama` with only x1,x2 filled renders "X goes to the market", not
/// "X goes to the market from  via  using ").
pub(crate) fn fill_template(template: &str, places: &[Option<String>]) -> String {
    let mut out = String::new();
    let mut rest = template;
    while let Some(pos) = rest.find("{x") {
        let before = &rest[..pos];
        let Some(close_rel) = rest[pos..].find('}') else {
            break;
        };
        let close = pos + close_rel;
        let ph = &rest[pos + 2..close]; // the "N" in "{xN}"
        let n: usize = ph.parse().unwrap_or(0);
        match places.get(n.wrapping_sub(1)).and_then(|f| f.as_ref()) {
            Some(filler) => {
                out.push_str(before);
                out.push_str(filler);
                rest = &rest[close + 1..];
            }
            None => {
                // Unfilled place: drop this placeholder AND the connective text
                // leading into it ("… the market" not "… the market from").
                rest = "";
                break;
            }
        }
    }
    out.push_str(rest);
    out.trim().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn curated_template_used() {
        // gerku is curated as "{x1} is a dog" (via the smuni-dictionary build).
        assert_eq!(frame_template("gerku"), "{x1} is a dog");
        assert_eq!(frame_template("danlu"), "{x1} is an animal");
    }

    #[test]
    fn generic_fallback_for_uncurated() {
        // An invented predicate falls back to a generic frame.
        let t = frame_template("frobnicatezzzz");
        assert!(t.starts_with("{x1}"), "got: {t}");
    }

    #[test]
    fn fill_basic() {
        assert_eq!(
            fill_template("{x1} is a dog", &[Some("adam".into())]),
            "adam is a dog"
        );
    }

    #[test]
    fn fill_drops_trailing_unfilled() {
        let t = "{x1} goes to {x2} from {x3} via {x4} using {x5}";
        assert_eq!(
            fill_template(
                t,
                &[
                    Some("adam".into()),
                    Some("the market".into()),
                    None,
                    None,
                    None
                ]
            ),
            "adam goes to the market"
        );
    }

    #[test]
    fn fill_two_place() {
        assert_eq!(
            fill_template(
                "{x1} loves {x2}",
                &[Some("adam".into()), Some("eve".into())]
            ),
            "adam loves eve"
        );
    }
}
