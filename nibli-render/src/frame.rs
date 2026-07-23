//! Per-predicate English place-frame templates and filling.
//!
//! A *frame* is an English clause schema for a predicate using `{x1}`..`{x5}`
//! placeholders. The curated table in `nibli-lexicon` supplies frames for the
//! predicates the corpora use (`dog` -> `"{x1} is a dog"`); everything else
//! falls back to a generic gloss-based frame here.

use nibli_lexicon::{get_arity, get_gloss, get_template};

use crate::overlay;

/// Template overrides where the lexicon English is inverted, truncated, or
/// systematically misleading for the IR's place-filling patterns. Applied
/// before corpus templates so the back-translation stays readable without
/// waiting on a full corpus prose pass.
const TEMPLATE_OVERRIDES: &[(&str, &str)] = &[
    // bilga/curmi: IR x1 = duty/content, x2 = obligated party — not "duty is obligated to person".
    ("obligated", "{x2} is obligated that {x1}"),
    ("obliged", "{x2} is obligated that {x1}"),
    // cirko: x1 = loss, x2 = person who loses.
    ("lose", "{x2} loses {x1}"),
    // dinju used as facility placement: x1 = facility, x2 = resident.
    ("building", "{x2} is placed at {x1}"),
    // zdani as confinement status (constitutional corpora), not "X is a house".
    ("home", "{x1} is under home confinement"),
    // Status / boolean-ish 1-place readings.
    ("false", "{x1} is voided"),
    ("prisoner", "{x1} is a prisoner"),
    ("family", "{x1} has a domestic offense"),
    ("severe", "{x1}'s offense is severe"),
    ("reward", "{x1} is rewarded"),
    ("travel", "{x1} may travel"),
    ("dwell", "{x1} has shelter"),
    ("expresses", "{x1} may express"),
    ("work", "{x1} works on {x2}"),
    ("judge", "{x1} judges {x2}"),
    ("capture", "{x1} captures fraud by {x2}"),
    ("parent", "{x1} is a parent of {x2}"),
    ("injure", "{x1} injures {x2}"),
    ("deceive", "{x1} falsely accuses {x2}"),
    ("teaches", "{x1} teaches {x2}"),
    ("permits", "{x1} permits {x2}"),
    ("secure", "{x1} is secure"),
    ("healthy", "{x1} is healthy"),
    ("learn", "{x1} learns"),
    ("eats", "{x1} eats"),
];

/// Resolve a fill-template (a string with `{x1}`..`{xN}` placeholders) for a
/// relation — everything is ENGLISH-keyed since the committed corpus (the old
/// English→gismu `frame_key` un-mapping died with gismu input). DRY resolution
/// chain: the active domain overlay (if any) wins, then a small set of
/// place-order / readability overrides, then the corpus template, then a
/// generic gloss+arity frame. The overlay is just the first tier —
/// Custom KBs and non-UI surfaces fall straight through past it.
pub(crate) fn frame_template(relation: &str) -> String {
    if let Some(t) = overlay::active().and_then(|o| o.template(relation)) {
        return t.to_string();
    }
    if let Some((_, t)) = TEMPLATE_OVERRIDES.iter().find(|(r, _)| *r == relation) {
        return (*t).to_string();
    }
    if let Some(t) = get_template(relation) {
        return t.to_string();
    }
    let gloss = gloss_for(relation);
    let arity = get_arity(relation).unwrap_or(1).max(1);
    generic_template(&gloss, arity)
}

/// Single-word gloss for a relation via the same overlay -> corpus -> bare
/// chain. Used for the generic frame fallback and the "a &lt;noun&gt;" rendering.
pub(crate) fn gloss_for(relation: &str) -> String {
    overlay::active()
        .and_then(|o| o.gloss(relation))
        .or_else(|| get_gloss(relation))
        .unwrap_or(relation)
        .to_string()
}

/// The highest place index `N` appearing in a `{xN}` placeholder (0 if none).
/// Used to size the filler vector when rendering a RULE clause, so the trailing
/// places of a multi-place frame render a generic "something" rather than being
/// truncated to the bare subject (the proof-trace rule-justification path; facts,
/// which have concrete args, keep truncating trailing places).
pub(crate) fn template_max_place(template: &str) -> usize {
    let mut max = 0;
    let mut rest = template;
    while let Some(pos) = rest.find("{x") {
        let Some(close_rel) = rest[pos..].find('}') else {
            break;
        };
        let close = pos + close_rel;
        if let Ok(n) = rest[pos + 2..close].parse::<usize>() {
            max = max.max(n);
        }
        rest = &rest[close + 1..];
    }
    max
}

/// Adjectival / status glosses that take "is {gloss}" rather than "is a {gloss}".
fn is_adjectival_gloss(gloss: &str) -> bool {
    matches!(
        gloss,
        "false"
            | "true"
            | "severe"
            | "secure"
            | "healthy"
            | "correct"
            | "necessary"
            | "exact"
            | "thin"
            | "dangerous"
            | "big"
            | "small"
            | "good"
            | "bad"
            | "alive"
            | "dead"
            | "free"
    ) || gloss.ends_with("ous")
        || gloss.ends_with("ful")
        || gloss.ends_with("less")
        || gloss.ends_with("ive")
        || gloss.ends_with("able")
        || gloss.ends_with("ible")
}

fn indefinite_article(gloss: &str) -> &'static str {
    let first = gloss.chars().next().map(|c| c.to_ascii_lowercase());
    match first {
        Some('a' | 'e' | 'i' | 'o' | 'u') => "an ",
        _ => "a ",
    }
}

/// Third-person singular present for bare gloss verbs used in multi-place frames.
fn third_person_s(gloss: &str) -> String {
    if gloss.is_empty() {
        return gloss.to_string();
    }
    // Already looks conjugated or is multi-word — leave alone.
    if gloss.contains(' ') || gloss.ends_with('s') {
        return gloss.to_string();
    }
    let lower = gloss.to_ascii_lowercase();
    if lower.ends_with("ss")
        || lower.ends_with("sh")
        || lower.ends_with("ch")
        || lower.ends_with('x')
        || lower.ends_with('z')
        || lower.ends_with('o')
    {
        format!("{gloss}es")
    } else if lower.ends_with('y')
        && !matches!(
            lower.chars().rev().nth(1),
            Some('a' | 'e' | 'i' | 'o' | 'u')
        )
    {
        format!("{}ies", &gloss[..gloss.len() - 1])
    } else {
        format!("{gloss}s")
    }
}

/// Generic frame when no curated template exists. Imperfect but honest:
/// - 1-place adjective → "X is false"
/// - 1-place noun → "X is a dog"
/// - n-place → "X judges Y" (3sg verb)
fn generic_template(gloss: &str, arity: usize) -> String {
    if arity <= 1 {
        if is_adjectival_gloss(gloss) {
            format!("{{x1}} is {gloss}")
        } else {
            format!("{{x1}} is {}{gloss}", indefinite_article(gloss))
        }
    } else {
        let verb = third_person_s(gloss);
        let mut t = format!("{{x1}} {verb}");
        for i in 2..=arity {
            t.push_str(&format!(" {{x{i}}}"));
        }
        t
    }
}

/// English particles that, in a frame template, exist only to introduce a place
/// (`goes to {x2}`, `from {x3}`). When that place is elided we keep the verb but
/// strip such a now-dangling particle (`goes to` → `goes`).
const TRAILING_PARTICLES: &[&str] = &[
    "to", "from", "of", "with", "by", "at", "in", "on", "for", "via", "using", "into", "onto",
    "about", "as", "than", "that",
];

/// Trim trailing whitespace and any dangling particle words from a kept
/// connective, preserving leading whitespace so the join keeps its separator
/// (`" eats "` → `" eats"`, `" goes to "` → `" goes"`, `" from "` → `""`).
pub(crate) fn strip_trailing_particle(before: &str) -> &str {
    let mut s = before.trim_end();
    loop {
        let start = s.rfind(char::is_whitespace).map_or(0, |i| i + 1);
        let last = &s[start..];
        if start > 0 && TRAILING_PARTICLES.contains(&last) {
            s = s[..start].trim_end();
        } else {
            return s;
        }
    }
}

/// Fill a template with rendered place fillers. `places[i]` is the filler for
/// place `x(i+1)`; `None` means the place was unspecified (`zo'e`) or absent.
///
/// Placeholders BEYOND the last filled place are a TRAILING run and are truncated
/// (Lojban leaves trailing places implicit, so `goes` with only x1,x2 filled
/// reads "X goes to the market", not "X goes to the market from  via  using ").
/// The verb connective leading into the first dropped place is KEPT, minus any
/// dangling particle — so `citka` with only x1 reads "X eats" (not "X"), and
/// `goes` with only x1 reads "X goes" (not "X" or a dangling "X goes to").
/// An INTERIOR or LEADING unspecified place — one where a LATER place IS filled —
/// renders a generic "something" so the clause is not collapsed to nothing
/// (`goes fi le market do` → "something goes to something from the market via do",
/// not an empty string). No sort info is available, so the filler is uniformly
/// "something" (animacy-aware "someone" would need type info threaded through).
pub(crate) fn fill_template(template: &str, places: &[Option<String>]) -> String {
    let last_filled = places
        .iter()
        .rposition(|f| f.is_some())
        .map_or(0, |i| i + 1);
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
        if n > last_filled {
            // Trailing unfilled place(s): Lojban elides them. Keep the connective
            // that introduced the FIRST dropped place — it carries the verb
            // ("eats" in "{x1} eats {x2}", so `la .adam. cu citka` reads "Adam
            // eats", not "Adam") — but strip any dangling particle that only
            // existed to introduce the now-elided place ("goes to" → "goes").
            out.push_str(strip_trailing_particle(before));
            rest = "";
            break;
        }
        out.push_str(before);
        match places.get(n.wrapping_sub(1)).and_then(|f| f.as_ref()) {
            Some(filler) => out.push_str(filler),
            None => out.push_str("something"), // interior/leading unspecified place
        }
        rest = &rest[close + 1..];
    }
    out.push_str(rest);
    out.trim().to_string()
}

/// Infinitive content phrase for a deontic duty's embedded event predicate.
pub(crate) fn deontic_content_phrase(relation: &str) -> String {
    let gloss = gloss_for(relation);
    if is_adjectival_gloss(&gloss) || matches!(relation, "secure" | "healthy" | "correct" | "exact")
    {
        format!("be {gloss}")
    } else if matches!(relation, "eats" | "eat") {
        "eat".into()
    } else if matches!(relation, "dwell") {
        "have shelter".into()
    } else if matches!(relation, "learn") {
        "learn".into()
    } else if matches!(relation, "expresses" | "express") {
        "express".into()
    } else if matches!(relation, "removes" | "remove") {
        "be erased".into()
    } else if matches!(relation, "message") {
        "notify".into()
    } else if matches!(relation, "shelter") {
        "be kept secure".into()
    } else if matches!(relation, "necessary") {
        "be necessary".into()
    } else {
        // Strip trailing -s from 3sg glosses for a rough infinitive.
        let g = gloss_for(relation);
        if g.ends_with('s') && g.len() > 1 {
            format!("{}", &g[..g.len() - 1])
        } else {
            g
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn curated_template_used() {
        // dog is curated as "{x1} is a dog" (via the nibli-lexicon build).
        assert_eq!(frame_template("dog"), "{x1} is a dog");
        assert_eq!(frame_template("animal"), "{x1} is an animal");
    }

    #[test]
    fn overrides_beat_corpus_for_inverted_places() {
        assert_eq!(frame_template("obligated"), "{x2} is obligated that {x1}");
        assert_eq!(frame_template("lose"), "{x2} loses {x1}");
        assert_eq!(frame_template("building"), "{x2} is placed at {x1}");
        assert_eq!(frame_template("prisoner"), "{x1} is a prisoner");
    }

    #[test]
    fn generic_fallback_for_uncurated() {
        // An invented predicate falls back to a generic frame.
        let t = frame_template("frobnicatezzzz");
        assert!(t.starts_with("{x1}"), "got: {t}");
        assert!(t.contains("is a ") || t.contains("is an "), "got: {t}");
    }

    #[test]
    fn generic_multi_place_uses_3sg_verb() {
        let t = generic_template("judge", 2);
        assert_eq!(t, "{x1} judges {x2}");
    }

    #[test]
    fn overlay_template_wins_then_restores() {
        use crate::corpus_overlay::DRUG_INTERACTIONS_OVERLAY;
        use crate::overlay::with_overlay;
        // Fallback tier: the engine dictionary's literal proxy gloss.
        assert_eq!(frame_template("dangerous"), "{x1} is in danger");
        // Overlay tier: the domain term wins, and `se cuts` reorders its places.
        with_overlay(Some(&DRUG_INTERACTIONS_OVERLAY), || {
            assert_eq!(frame_template("dangerous"), "{x1} is at toxicity risk");
            assert_eq!(frame_template("cuts"), "{x2} is metabolized by {x1}");
            // A relation the overlay does not cover still falls through.
            assert_eq!(frame_template("dog"), "{x1} is a dog");
        });
        // Restored after the scope.
        assert_eq!(frame_template("dangerous"), "{x1} is in danger");
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
    fn trailing_object_keeps_verb() {
        // The reported bug: "{x1} eats {x2}" with x2 elided (zo'e) must read
        // "adam eats", NOT "adam" (the verb was being dropped with the place).
        assert_eq!(
            fill_template("{x1} eats {x2}", &[Some("adam".into())]),
            "adam eats"
        );
        // Rule consequent path: "X eats" for the elided object.
        assert_eq!(
            fill_template("{x1} eats {x2}", &[Some("X".into()), None]),
            "X eats"
        );
    }

    #[test]
    fn trailing_strips_dangling_particle() {
        // Only x1 filled → "x goes" (the "to {x2}" run is dropped, and the now-
        // dangling preposition "to" goes with it — not "x goes to").
        let t = "{x1} goes to {x2} from {x3} via {x4} using {x5}";
        assert_eq!(fill_template(t, &[Some("x".into())]), "x goes");
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

    #[test]
    fn fill_renders_interior_unspecified() {
        // x1/x2 unspecified but x3/x4 filled: render "something" for the interior
        // places (a later place is filled) rather than collapsing the whole clause.
        // x5 is a TRAILING unfilled place and is still truncated.
        let t = "{x1} goes to {x2} from {x3} via {x4} using {x5}";
        assert_eq!(
            fill_template(
                t,
                &[
                    None,
                    None,
                    Some("the market".into()),
                    Some("do".into()),
                    None
                ]
            ),
            "something goes to something from the market via do"
        );
    }

    #[test]
    fn fill_renders_leading_unspecified() {
        // x1 unspecified, x2 filled → leading "something", clause not collapsed.
        assert_eq!(
            fill_template("{x1} loves {x2}", &[None, Some("eve".into())]),
            "something loves eve"
        );
    }

    #[test]
    fn template_max_place_counts_placeholders() {
        assert_eq!(template_max_place("{x1} permits {x2}"), 2);
        assert_eq!(template_max_place("{x1} is a dog"), 1);
        assert_eq!(
            template_max_place("{x1} goes to {x2} from {x3} via {x4} using {x5}"),
            5
        );
        assert_eq!(template_max_place("no placeholders here"), 0);
        // Out-of-order placeholders return the max, not the count.
        assert_eq!(template_max_place("{x2} loves {x1}"), 2);
    }

    #[test]
    fn lose_template_person_first() {
        assert_eq!(
            fill_template(
                &frame_template("lose"),
                &[Some("Points".into()), Some("Bela".into())]
            ),
            "Bela loses Points"
        );
    }
}
