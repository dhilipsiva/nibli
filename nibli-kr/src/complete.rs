//! Shared nibli KR autocomplete — one engine for console and UI.
//!
//! Completes against:
//! - reserved keywords ([`nibli_lexicon::reserved`])
//! - committed corpus predicate names (+ gloss)
//! - committed compound spellings (`a+b`)
//! - place labels of the open call (when the cursor is inside `pred(…`)
//! - optional REPL `:`-commands (host / native REPL only)
//!
//! Surfaces map [`CompleteResult`] into reedline suggestions or a web dropdown;
//! they do not re-implement ranking or corpus lookup.

use nibli_lexicon::corpus::{corpus_compounds, corpus_entries};
use nibli_lexicon::reserved::RESERVED_WORDS;
use nibli_lexicon::{alias, compound, compound_by_relation};
use std::sync::LazyLock;

/// What kind of completion this is (for UI chrome / menu labels).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionKind {
    Keyword,
    Predicate,
    Compound,
    Place,
    ReplCommand,
    /// Caller-supplied session extra (names, recent predicates, …).
    Extra,
}

impl CompletionKind {
    pub fn label(self) -> &'static str {
        match self {
            CompletionKind::Keyword => "keyword",
            CompletionKind::Predicate => "predicate",
            CompletionKind::Compound => "compound",
            CompletionKind::Place => "place",
            CompletionKind::ReplCommand => "command",
            CompletionKind::Extra => "session",
        }
    }
}

/// One completion item. `value` replaces the prefix span in the line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Completion {
    pub value: String,
    pub description: Option<String>,
    pub kind: CompletionKind,
}

/// Result of a completion query: items + the byte span they replace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompleteResult {
    /// Inclusive start of the token prefix (bytes).
    pub span_start: usize,
    /// Exclusive end of the token prefix (usually the cursor).
    pub span_end: usize,
    pub items: Vec<Completion>,
}

impl CompleteResult {
    pub fn empty(span_start: usize, span_end: usize) -> Self {
        Self {
            span_start,
            span_end,
            items: Vec::new(),
        }
    }

    /// Apply the item at `index` to `line`; returns `(new_line, new_cursor)`.
    pub fn apply(&self, line: &str, index: usize) -> Option<(String, usize)> {
        let item = self.items.get(index)?;
        apply_replacement(line, self.span_start, self.span_end, &item.value)
    }
}

/// Options for a completion request.
#[derive(Debug, Clone, Copy)]
pub struct CompleteOpts<'a> {
    /// Include `:load`, `:help`, … (REPL surfaces only).
    pub include_repl_commands: bool,
    /// Max items returned (after ranking).
    pub limit: usize,
    /// Minimum prefix length to open a free (non-command) completion.
    /// `0` allows Tab-on-empty inside `pred(` place lists.
    pub min_prefix: usize,
    /// Extra session candidates (e.g. names seen in the KB).
    pub extra: &'a [Completion],
}

impl Default for CompleteOpts<'static> {
    fn default() -> Self {
        Self {
            include_repl_commands: false,
            limit: 40,
            min_prefix: 1,
            extra: &[],
        }
    }
}

/// REPL colon-commands shared by nibli-host and the native `nibli` REPL.
/// Surfaces may not implement every command; completion still lists the
/// common set so the two consoles stay aligned.
pub const REPL_COMMANDS: &[(&str, &str)] = &[
    (":help", "show commands"),
    (":quit", "exit the REPL"),
    (":reset", "clear the knowledge base"),
    (":load", "load a .nibli file"),
    (":facts", "list active facts"),
    (":retract", "retract a fact by id"),
    (":debug", "compile to logic without asserting"),
    (":compute", "register a compute predicate"),
    (":assert", "assert a ground fact directly"),
    (":backend", "show/set compute backend address"),
    (":fuel", "show/set WASM fuel budget"),
    (":memory", "show/set WASM memory limit"),
    (":strict", "strict mode on|off"),
    (":existential-import", "xorlo witnesses on|off"),
    (":db", "open/close durable store"),
    (":q", "quit (short)"),
    (":r", "reset (short)"),
    (":h", "help (short)"),
];

/// Complete at `cursor` (byte offset) in `line`.
pub fn complete(line: &str, cursor: usize, opts: CompleteOpts<'_>) -> CompleteResult {
    let cursor = cursor.min(line.len());
    // Prefer char boundary
    let cursor = floor_char_boundary(line, cursor);

    let (span_start, span_end, prefix) = token_prefix(line, cursor);

    // Colon-command mode: line (or current token) starts with `:`
    if opts.include_repl_commands && (prefix.starts_with(':') || line[..span_start].trim().is_empty() && line[span_start..].starts_with(':'))
    {
        return complete_repl(prefix, span_start, span_end, opts.limit);
    }
    // Whole-line REPL when the only token is `:…`
    if opts.include_repl_commands && line.trim_start().starts_with(':') {
        let trim_start = line.len() - line.trim_start().len();
        if span_start >= trim_start {
            let cmd_prefix = &line[trim_start..cursor];
            if cmd_prefix.starts_with(':') && !cmd_prefix.contains(char::is_whitespace) {
                return complete_repl(cmd_prefix, trim_start, cursor, opts.limit);
            }
        }
    }

    if prefix.len() < opts.min_prefix && !in_call_args(line, span_start) {
        return CompleteResult::empty(span_start, span_end);
    }

    let prefix_lower = prefix.to_ascii_lowercase();
    let mut items: Vec<Completion> = Vec::new();

    // Place labels of the open call take priority when the cursor is in args.
    if let Some(rel) = open_call_relation(line, span_start) {
        if let Some(places) = places_for_relation(rel) {
            for p in places {
                if prefix.is_empty() || p.starts_with(&prefix_lower) || starts_with_ci(p, prefix) {
                    items.push(Completion {
                        value: (*p).to_string(),
                        description: Some(format!("place of {rel}")),
                        kind: CompletionKind::Place,
                    });
                }
            }
        }
    }

    // Keywords
    for kw in RESERVED_WORDS {
        if prefix.is_empty() || kw.starts_with(&prefix_lower) || starts_with_ci(kw, prefix) {
            items.push(Completion {
                value: (*kw).to_string(),
                description: Some("keyword".into()),
                kind: CompletionKind::Keyword,
            });
        }
    }

    // Predicates (binary-range scan over sorted corpus)
    for e in predicates_with_prefix(&prefix_lower) {
        items.push(Completion {
            value: e.name.to_string(),
            description: Some(format!("{} · arity {}", e.gloss, e.arity())),
            kind: CompletionKind::Predicate,
        });
    }

    // Compounds
    for c in corpus_compounds() {
        if prefix.is_empty()
            || c.name.starts_with(&prefix_lower)
            || starts_with_ci(c.name, prefix)
            || c.relation.starts_with(&prefix_lower)
        {
            items.push(Completion {
                value: c.name.to_string(),
                description: Some(format!("{} · compound", c.gloss)),
                kind: CompletionKind::Compound,
            });
        }
    }

    // Session extras
    for ex in opts.extra {
        if prefix.is_empty()
            || ex.value.to_ascii_lowercase().starts_with(&prefix_lower)
            || starts_with_ci(&ex.value, prefix)
        {
            items.push(ex.clone());
        }
    }

    // De-dupe by value (first wins — places/keywords beat later predicates)
    dedupe_by_value(&mut items);

    // Rank: exact prefix match length, then kind priority, then name
    let kind_rank = |k: CompletionKind| match k {
        CompletionKind::Place => 0,
        CompletionKind::Keyword => 1,
        CompletionKind::ReplCommand => 2,
        CompletionKind::Compound => 3,
        CompletionKind::Predicate => 4,
        CompletionKind::Extra => 5,
    };
    items.sort_by(|a, b| {
        let a_exact = a.value.eq_ignore_ascii_case(prefix) as i8;
        let b_exact = b.value.eq_ignore_ascii_case(prefix) as i8;
        b_exact
            .cmp(&a_exact)
            .then_with(|| kind_rank(a.kind).cmp(&kind_rank(b.kind)))
            .then_with(|| a.value.len().cmp(&b.value.len()))
            .then_with(|| a.value.cmp(&b.value))
    });

    items.truncate(opts.limit);

    CompleteResult {
        span_start,
        span_end,
        items,
    }
}

/// Replace `line[span_start..span_end]` with `replacement`.
pub fn apply_replacement(
    line: &str,
    span_start: usize,
    span_end: usize,
    replacement: &str,
) -> Option<(String, usize)> {
    if span_start > span_end || span_end > line.len() {
        return None;
    }
    let mut out = String::with_capacity(line.len() - (span_end - span_start) + replacement.len());
    out.push_str(&line[..span_start]);
    out.push_str(replacement);
    let new_cursor = out.len();
    out.push_str(&line[span_end..]);
    Some((out, new_cursor))
}

// ── internals ──────────────────────────────────────────────────────────────

static PREDICATE_NAMES: LazyLock<Vec<&'static nibli_lexicon::PredicateEntry>> = LazyLock::new(|| {
    corpus_entries().collect()
});

fn predicates_with_prefix(prefix_lower: &str) -> impl Iterator<Item = &'static nibli_lexicon::PredicateEntry> + '_ {
    let slice = PREDICATE_NAMES.as_slice();
    // Sorted by name — find lower bound
    let start = slice.partition_point(|e| e.name < prefix_lower);
    slice[start..]
        .iter()
        .copied()
        .take_while(move |e| e.name.starts_with(prefix_lower))
}

fn complete_repl(prefix: &str, span_start: usize, span_end: usize, limit: usize) -> CompleteResult {
    let prefix_lower = prefix.to_ascii_lowercase();
    let mut items: Vec<Completion> = REPL_COMMANDS
        .iter()
        .filter(|(cmd, _)| cmd.starts_with(&prefix_lower) || starts_with_ci(cmd, prefix))
        .map(|(cmd, desc)| Completion {
            value: (*cmd).to_string(),
            description: Some((*desc).into()),
            kind: CompletionKind::ReplCommand,
        })
        .collect();
    items.truncate(limit);
    CompleteResult {
        span_start,
        span_end,
        items,
    }
}

fn places_for_relation(rel: &str) -> Option<&'static [&'static str]> {
    alias(rel)
        .map(|e| e.places)
        .or_else(|| compound(rel).map(|c| c.places))
        .or_else(|| compound_by_relation(rel).map(|c| c.places))
}

/// Relation name of the innermost unclosed `name(` to the left of `pos`.
fn open_call_relation<'a>(line: &'a str, pos: usize) -> Option<&'a str> {
    let head = &line[..pos];
    let mut depth = 0i32;
    let bytes = head.as_bytes();
    let mut i = bytes.len();
    while i > 0 {
        i -= 1;
        match bytes[i] {
            b')' => depth += 1,
            b'(' => {
                if depth == 0 {
                    // walk back over whitespace then ident
                    let mut j = i;
                    while j > 0 && bytes[j - 1].is_ascii_whitespace() {
                        j -= 1;
                    }
                    let end = j;
                    while j > 0 && is_ident_byte(bytes[j - 1]) {
                        j -= 1;
                    }
                    if j < end {
                        let name = &head[j..end];
                        if !name.is_empty() {
                            return Some(name);
                        }
                    }
                    return None;
                }
                depth -= 1;
            }
            _ => {}
        }
    }
    None
}

fn in_call_args(line: &str, pos: usize) -> bool {
    open_call_relation(line, pos).is_some()
}

/// Token under/before cursor: `[A-Za-z0-9_+$:]` run ending at cursor.
fn token_prefix(line: &str, cursor: usize) -> (usize, usize, &str) {
    let bytes = line.as_bytes();
    let mut start = cursor;
    while start > 0 {
        let b = bytes[start - 1];
        if is_ident_byte(b) || b == b'$' || b == b'+' || b == b':' {
            start -= 1;
        } else {
            break;
        }
    }
    // Don't let `:` mid-token from `label:` swallow the preceding word incorrectly:
    // if we have `foo:bar` that's rare; `destination:` means place complete after `:`.
    // When prefix contains `:` not at start, take only the part after the last `:`.
    let raw = &line[start..cursor];
    if let Some(idx) = raw.rfind(':') {
        if idx > 0 {
            // `place:` — completing after colon with empty prefix for place labels
            // or continuing a typed place. Prefer segment after colon.
            let after = idx + 1;
            return (start + after, cursor, &raw[after..]);
        }
    }
    (start, cursor, raw)
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn starts_with_ci(s: &str, prefix: &str) -> bool {
    s.len() >= prefix.len()
        && s.as_bytes()
            .iter()
            .zip(prefix.as_bytes())
            .all(|(a, b)| a.to_ascii_lowercase() == b.to_ascii_lowercase())
}

fn floor_char_boundary(s: &str, i: usize) -> usize {
    if i >= s.len() {
        return s.len();
    }
    let mut i = i;
    while i > 0 && !s.is_char_boundary(i) {
        i -= 1;
    }
    i
}

fn dedupe_by_value(items: &mut Vec<Completion>) {
    let mut seen = std::collections::HashSet::new();
    items.retain(|c| seen.insert(c.value.clone()));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn vals(r: &CompleteResult) -> Vec<&str> {
        r.items.iter().map(|c| c.value.as_str()).collect()
    }

    #[test]
    fn completes_keyword_every() {
        let r = complete("ev", 2, CompleteOpts::default());
        assert!(vals(&r).contains(&"every"), "{:?}", vals(&r));
        assert_eq!(&"ev"[r.span_start..r.span_end], "ev");
    }

    #[test]
    fn completes_predicate_dog() {
        let r = complete("do", 2, CompleteOpts::default());
        assert!(vals(&r).iter().any(|v| *v == "dog"), "{:?}", vals(&r));
    }

    #[test]
    fn completes_inside_call_places() {
        let line = "goes(des";
        let r = complete(line, line.len(), CompleteOpts {
            min_prefix: 0,
            ..CompleteOpts::default()
        });
        assert!(
            vals(&r).iter().any(|v| v.starts_with("des") || *v == "destination"),
            "places for goes: {:?}",
            vals(&r)
        );
    }

    #[test]
    fn completes_repl_commands() {
        let line = ":lo";
        let r = complete(
            line,
            line.len(),
            CompleteOpts {
                include_repl_commands: true,
                min_prefix: 1,
                ..CompleteOpts::default()
            },
        );
        assert!(vals(&r).contains(&":load"), "{:?}", vals(&r));
    }

    #[test]
    fn apply_replaces_prefix() {
        let r = complete("animal(ev", 9, CompleteOpts::default());
        let every = r.items.iter().position(|c| c.value == "every").expect("every");
        let (new, cur) = r.apply("animal(ev", every).unwrap();
        assert_eq!(new, "animal(every");
        assert_eq!(cur, "animal(every".len());
    }

    #[test]
    fn lossless_span_for_query_prefix() {
        let line = "? do";
        let r = complete(line, line.len(), CompleteOpts::default());
        assert_eq!(&line[r.span_start..r.span_end], "do");
    }

    #[test]
    fn empty_prefix_without_call_is_empty_at_min_1() {
        let r = complete("", 0, CompleteOpts::default());
        assert!(r.items.is_empty());
    }
}
