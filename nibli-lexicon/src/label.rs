//! Prose place-label heuristic — the third tier of the place-label chain
//! (curated → lensisku `place_keywords` → THIS → positional).
//!
//! Extracts a candidate label per place from a lensisku definition string by
//! taking the content word immediately before each `$x_{N}$` / `$x_N$` marker
//! (e.g. klama's "… goes to destination $x_{2}$ from origin $x_{3}$ …" yields
//! `destination`/`origin`). Pure functions, unit-tested here; consumed by
//! `tools/lexigen` (the corpus regeneration tool), which applies the
//! reserved-word/dup/x-tag sanitization on top. Measured on the lensisku
//! dump this fully labels only ~56% of gismu — that is fine: a place
//! this heuristic can't label stays positional (`""`), which is always honest.
//!
//! Place 1 is never labeled from prose: definitions START with `$x_1$`, so there
//! is no preceding content word (and x1 is the positional subject anyway).

/// Words that precede a marker but describe the relation, not the place.
const STOPWORDS: &[&str] = &[
    "a", "an", "and", "are", "as", "at", "be", "being", "by", "for", "from", "in", "into", "is",
    "it", "of", "on", "or", "over", "per", "than", "that", "the", "to", "under", "via", "with",
];

/// Candidate labels for places 1..=5 derived from `definition` prose.
/// Slot 0 (x1) is always empty; slots at or beyond `arity` are always empty.
/// Candidates are lowercase and shaped like idents when extraction succeeds,
/// but the caller still owns reserved-word / duplicate / x-tag sanitization.
pub fn prose_labels(definition: &str, arity: u8) -> [String; 5] {
    let mut labels: [String; 5] = Default::default();
    let bytes = definition.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if let Some((place, marker_len)) = marker_at(&bytes[i..]) {
            let idx = (place - 1) as usize;
            if place >= 2
                && (place as u8) <= arity
                && idx < 5
                && labels[idx].is_empty()
                && let Some(word) = content_word_before(definition, i)
            {
                labels[idx] = word;
            }
            i += marker_len;
        } else {
            i += 1;
        }
    }
    labels
}

/// Parse a `$x_{N}$` or `$x_N$` marker at the start of `bytes`; returns
/// `(N, byte_len)`.
fn marker_at(bytes: &[u8]) -> Option<(u32, usize)> {
    if !bytes.starts_with(b"$x_") {
        return None;
    }
    let rest = &bytes[3..];
    if let Some(inner) = rest.strip_prefix(b"{") {
        // $x_{N}$ — N may be multi-digit; only 1..=5 is a place marker.
        let close = inner.iter().position(|&b| b == b'}')?;
        let digits = std::str::from_utf8(&inner[..close]).ok()?;
        let n: u32 = digits.parse().ok()?;
        if inner.get(close + 1) == Some(&b'$') {
            return Some((n, 3 + 1 + close + 2));
        }
        None
    } else {
        let digit = *rest.first()?;
        if digit.is_ascii_digit() && rest.get(1) == Some(&b'$') {
            return Some(((digit - b'0') as u32, 5));
        }
        None
    }
}

/// The content word immediately before byte offset `marker_start`, normalized:
/// trailing run of `[A-Za-z/-]`, first `/`-alternative, lowercased, `-` → `_`;
/// rejected when a stopword or not ident-shaped.
fn content_word_before(definition: &str, marker_start: usize) -> Option<String> {
    let before = definition[..marker_start].trim_end();
    // Char-wise backward scan (no byte arithmetic — dump prose contains
    // multibyte chars): collect the trailing [A-Za-z/-] run.
    let tail: Vec<char> = before
        .chars()
        .rev()
        .take_while(|c| c.is_ascii_alphabetic() || *c == '/' || *c == '-')
        .collect();
    if tail.is_empty() {
        return None;
    }
    let raw: String = tail.into_iter().rev().collect();
    // Slashed alternatives ("means/vehicle"): the first alternative is the label.
    let first = raw.split('/').next().unwrap();
    let candidate = first.to_ascii_lowercase().replace('-', "_");
    if STOPWORDS.contains(&candidate.as_str()) {
        return None;
    }
    let mut chars = candidate.chars();
    let ident_ok = matches!(chars.next(), Some('a'..='z'))
        && chars.all(|c| matches!(c, 'a'..='z' | '0'..='9' | '_'));
    if ident_ok { Some(candidate) } else { None }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn klama_definition_yields_curated_labels() {
        // The real lensisku definition shape for klama.
        let def = "$x_{1}$ comes/goes to destination $x_{2}$ from origin $x_{3}$ \
                   via route $x_{4}$ using means/vehicle $x_{5}$.";
        let labels = prose_labels(def, 5);
        assert_eq!(labels[0], "");
        assert_eq!(labels[1], "destination");
        assert_eq!(labels[2], "origin");
        assert_eq!(labels[3], "route");
        assert_eq!(labels[4], "means"); // first slash-alternative of means/vehicle
    }

    #[test]
    fn unbraced_markers_parse_too() {
        let labels = prose_labels("$x_1$ loves beloved $x_2$.", 2);
        assert_eq!(labels[1], "beloved");
    }

    #[test]
    fn stopwords_and_bare_markers_stay_positional() {
        // Word before $x_2$ is the stopword "to"; no label.
        let labels = prose_labels("$x_1$ gives to $x_2$.", 2);
        assert_eq!(labels[1], "");
        // Marker directly after the leading marker: nothing usable before it.
        let labels = prose_labels("$x_1$ $x_2$ something.", 2);
        assert_eq!(labels[1], "");
    }

    #[test]
    fn arity_bounds_and_first_occurrence_win() {
        // x3 beyond arity 2 stays empty even though prose offers a word.
        let labels = prose_labels("$x_1$ sees thing $x_2$ at place $x_3$.", 2);
        assert_eq!(labels[1], "thing");
        assert_eq!(labels[2], "");
        // First occurrence of a marker wins.
        let labels = prose_labels("$x_1$ hits target $x_2$; also strikes $x_2$.", 2);
        assert_eq!(labels[1], "target");
    }

    #[test]
    fn multidigit_and_malformed_markers_are_ignored() {
        // $x_{12}$ is not a place marker; malformed $x_{2 has no close.
        let labels = prose_labels("$x_1$ uses widget $x_{12}$ and gadget $x_{2}$.", 3);
        assert_eq!(labels[1], "gadget");
        let labels = prose_labels("$x_1$ broken marker $x_{2 oops.", 3);
        assert_eq!(labels, ["", "", "", "", ""].map(String::from));
    }

    #[test]
    fn place_one_never_labeled() {
        let labels = prose_labels("agent $x_1$ acts.", 3);
        assert_eq!(labels[0], "");
    }
}
