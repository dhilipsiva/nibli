//! The single fact humanizer.
//!
//! Parses the flat display string produced by logji's `StoredFact::to_display_string()`
//! — `relation(arg, arg)`, optionally wrapped in `Past(…)`/`Present(…)`/`Future(…)`/
//! `Obligatory(…)`/`Permitted(…)`, with args that may be `sk_N(dep)` Skolem
//! functions, `(a, b)` DepPairs, `le foo` descriptions, `_` (zo'e), numbers, or
//! plain constants — and renders it readably: role predicates collapse
//! (`gerku_x1` -> `dog.dog`), event Skolems are hidden, witness Skolems become
//! `#N`.
//!
//! This replaces nibli-protocol's S-expr `humanize_fact`, which expected the
//! `(Pred …)` representation and silently dropped arguments when fed the flat
//! form that the proof trace actually carries.

use crate::term::{collapse_role_name, humanize_skolem, is_event_skolem};

/// Humanize a single flat fact-display string into readable notation.
///
/// Pure and total: any input that does not parse as the flat form (e.g. a stray
/// S-expr starting with `(`) is returned unchanged.
pub fn humanize_fact(input: &str) -> String {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return String::new();
    }
    // Defensive passthrough: a leading '(' is not our `relation(...)` shape
    // (e.g. a legacy S-expr `(Pred …)` or a bare DepPair) — leave it alone
    // rather than mangle it.
    if trimmed.starts_with('(') {
        return trimmed.to_string();
    }
    let tokens = tokenize(trimmed);
    let mut pos = 0;
    match parse_fact(&tokens, &mut pos) {
        Some(rendered) if pos == tokens.len() => rendered,
        _ => trimmed.to_string(),
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    LParen,
    RParen,
    Comma,
}

fn tokenize(s: &str) -> Vec<Tok> {
    let mut toks = Vec::new();
    let mut buf = String::new();
    for c in s.chars() {
        match c {
            '(' | ')' | ',' => {
                let t = buf.trim();
                if !t.is_empty() {
                    toks.push(Tok::Ident(t.to_string()));
                }
                buf.clear();
                toks.push(match c {
                    '(' => Tok::LParen,
                    ')' => Tok::RParen,
                    _ => Tok::Comma,
                });
            }
            _ => buf.push(c),
        }
    }
    let t = buf.trim();
    if !t.is_empty() {
        toks.push(Tok::Ident(t.to_string()));
    }
    toks
}

fn is_wrapper(name: &str) -> Option<&'static str> {
    match name {
        "Past" => Some("past"),
        "Present" => Some("present"),
        "Future" => Some("future"),
        "Obligatory" => Some("obligatory"),
        "Permitted" => Some("permitted"),
        _ => None,
    }
}

/// fact := WRAPPER '(' fact ')' | predicate
fn parse_fact(tokens: &[Tok], pos: &mut usize) -> Option<String> {
    if let Some(Tok::Ident(name)) = tokens.get(*pos)
        && let Some(label) = is_wrapper(name)
        && tokens.get(*pos + 1) == Some(&Tok::LParen)
    {
        *pos += 2; // consume WRAPPER and '('
        let inner = parse_fact(tokens, pos)?;
        if tokens.get(*pos) != Some(&Tok::RParen) {
            return None;
        }
        *pos += 1;
        return Some(format!("[{label}] {inner}"));
    }
    parse_predicate(tokens, pos)
}

/// predicate := IDENT [ '(' termlist ')' ]
fn parse_predicate(tokens: &[Tok], pos: &mut usize) -> Option<String> {
    let Some(Tok::Ident(name)) = tokens.get(*pos) else {
        return None;
    };
    let name = name.clone();
    *pos += 1;
    let args = if tokens.get(*pos) == Some(&Tok::LParen) {
        *pos += 1;
        let items = parse_term_list(tokens, pos)?;
        if tokens.get(*pos) != Some(&Tok::RParen) {
            return None;
        }
        *pos += 1;
        items
    } else {
        Vec::new()
    };
    Some(render_predicate(&name, &args))
}

/// termlist := [ term (',' term)* ]
fn parse_term_list(tokens: &[Tok], pos: &mut usize) -> Option<Vec<String>> {
    let mut items = Vec::new();
    if tokens.get(*pos) == Some(&Tok::RParen) {
        return Some(items);
    }
    loop {
        items.push(parse_term(tokens, pos)?);
        match tokens.get(*pos) {
            Some(Tok::Comma) => {
                *pos += 1;
            }
            Some(Tok::RParen) => break,
            _ => return None,
        }
    }
    Some(items)
}

/// term := '(' termlist ')'            (DepPair)
///       | IDENT '(' termlist ')'      (SkolemFn, e.g. sk_1(adam))
///       | IDENT                       (constant / sk_N / "le foo" / "_" / number / "?x")
///
/// Returns the RAW reconstructed term string (Skolem humanization is applied
/// later in `render_predicate`, after event-Skolem filtering on the raw form).
fn parse_term(tokens: &[Tok], pos: &mut usize) -> Option<String> {
    match tokens.get(*pos) {
        Some(Tok::LParen) => {
            *pos += 1;
            let items = parse_term_list(tokens, pos)?;
            if tokens.get(*pos) != Some(&Tok::RParen) {
                return None;
            }
            *pos += 1;
            Some(format!("({})", items.join(", ")))
        }
        Some(Tok::Ident(name)) => {
            let name = name.clone();
            *pos += 1;
            if tokens.get(*pos) == Some(&Tok::LParen) {
                *pos += 1;
                let items = parse_term_list(tokens, pos)?;
                if tokens.get(*pos) != Some(&Tok::RParen) {
                    return None;
                }
                *pos += 1;
                Some(format!("{}({})", name, items.join(", ")))
            } else {
                Some(name)
            }
        }
        _ => None,
    }
}

/// Render one predication: collapse a role-predicate name, hide event-Skolem
/// arguments, humanize the surviving terms.
fn render_predicate(name: &str, raw_args: &[String]) -> String {
    let display_name = collapse_role_name(name).unwrap_or_else(|| name.to_string());
    let kept: Vec<String> = raw_args
        .iter()
        .filter(|a| !is_event_skolem(a))
        .map(|a| humanize_skolem(a))
        .collect();
    if kept.is_empty() {
        display_name
    } else {
        format!("{}({})", display_name, kept.join(", "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_flat_predicate() {
        assert_eq!(humanize_fact("animal(adam)"), "animal(adam)");
    }

    #[test]
    fn type_predicate_hides_event_skolem() {
        // dog(sk_2): the lone arg is the event Skolem -> hidden -> bare "dog".
        assert_eq!(humanize_fact("dog(sk_2)"), "dog");
    }

    #[test]
    fn role_predicate_collapses_and_keeps_filler() {
        // gerku_x1(sk_2, adam): collapse to dog.dog, hide the event Skolem.
        assert_eq!(humanize_fact("dog_x1(sk_2, adam)"), "dog.dog(adam)");
    }

    #[test]
    fn witness_skolem_becomes_hash() {
        assert_eq!(humanize_fact("animal(sk_1(adam))"), "animal(#1(adam))");
    }

    #[test]
    fn dep_pair_skolem() {
        assert_eq!(
            humanize_fact("nelci_x2(sk_5, sk_2(adam, bob))"),
            "nelci.x2(#2(adam, bob))"
        );
    }

    #[test]
    fn tense_wrapper() {
        assert_eq!(
            humanize_fact("Past(goes(adam, paris))"),
            "[past] goes(adam, paris)"
        );
    }

    #[test]
    fn deontic_wrapper() {
        assert_eq!(
            humanize_fact("Obligatory(permits(adam))"),
            "[obligatory] permits(adam)"
        );
    }

    #[test]
    fn zoe_and_description_args() {
        assert_eq!(humanize_fact("goes(adam, _)"), "goes(adam, _)");
        assert_eq!(humanize_fact("goes(le dog)"), "goes(le dog)");
    }

    #[test]
    fn zero_arg_predicate() {
        assert_eq!(humanize_fact("dog"), "dog");
    }

    #[test]
    fn stray_s_expr_passes_through() {
        let s = r#"(Pred "dog" (Cons (Const "adam") (Nil)))"#;
        assert_eq!(humanize_fact(s), s);
    }

    #[test]
    fn empty_is_empty() {
        assert_eq!(humanize_fact(""), "");
    }
}
