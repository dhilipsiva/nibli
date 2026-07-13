//! Canonical gismu/lujvo arity (place count) from a lensisku `definition` field.
//!
//! lensisku/jbovlaste marks each REAL place with a structured, `$`-delimited token.
//! Gismu label their places with `x`: `$x_{N}$` (and the brace-less `$x_N$`). Lujvo
//! instead label each place with the COMPONENT letter it came from — e.g. flubisli is
//! `$b_1=f_1$ is an iceberg floating on $f_2$` (arity 2), where `$b_1=f_1$` is a single
//! place formed by MERGING two component places (`=`) at subscript 1. [`definition_arity`]
//! takes the MAX subscript N over EVERY such marker (any ASCII-letter component, not just
//! `x`), so a lujvo whose places are all labelled by component letters is no longer
//! silently read as arity 1 (measured against the current dump, 3,252 gismu/lujvo carry
//! only component-letter markers and were all mis-read as monovalent).
//!
//! The `$…$` delimiting is load-bearing and is NOT relaxed here. A marker must open on
//! `$`, be built only from `<letters><subscript>` atoms (optionally `=`-merged), and
//! close on `$`. Consequently bare prose `xN` (e.g. "x 4 times", "(cf. x4)"), a `{x4}`
//! without `$`, and `$`-delimited math (money `$5`, an exponent `$10^9$`, `$m^3$`) are
//! NOT markers and never fabricate a place — this is exactly the discipline that fixed
//! the old prose byte-scan's over-arity bug. Shared by `build.rs` (via `#[path]`) and
//! the crate's tests.

/// Highest place index N over the canonical `$…$` place markers in a lensisku
/// definition. A marker is a `$`-delimited run of `<letters>[_/{]*<digits>[}]?` atoms
/// joined by `=` (ASCII whitespace around `=` and before the closing `$` is tolerated —
/// jbovlaste writes both `$b_1=f_1$` and `$x_1 = t_1$`). N is kept within `1..=5` (the
/// gismu place range — preserves the historical cap). An `=`-merge counts as ONE place
/// at its shared subscript (both sides carry the same N, so the MAX is unaffected). Bare
/// prose `xN` and non-marker `$…$` spans are ignored. Defaults to 1 when no marker is
/// present.
pub fn definition_arity(definition: &str) -> usize {
    let bytes = definition.as_bytes();
    let len = bytes.len();
    let mut max_place = 0usize;
    let mut i = 0;
    while i < len {
        // Anchor on `$` and try to parse a well-formed marker span. Anything that is
        // not a marker span (bare prose `xN`, `{x4}`, money `$5`, exponent `$10^9$`)
        // fails the parse and we simply advance past this `$`.
        if bytes[i] == b'$'
            && let Some((span_max, end)) = scan_marker_span(bytes, i + 1)
        {
            max_place = max_place.max(span_max);
            i = end;
            continue;
        }
        i += 1;
    }
    max_place.max(1)
}

/// Parse a `$…$` marker span whose opening `$` sat at `start - 1`. Returns the max
/// in-range (`1..=5`) subscript over the span's atoms and the index just past the
/// closing `$`, or `None` if the bytes from `start` are not a well-formed marker span
/// (`<letters><subscript>` atoms, `=`-joined, closed by `$`).
fn scan_marker_span(bytes: &[u8], start: usize) -> Option<(usize, usize)> {
    let len = bytes.len();
    let mut j = start;
    let mut span_max = 0usize;
    loop {
        // Optional whitespace, then one-or-more ASCII letters (the component prefix:
        // `x`, `b`, `bi`, `ba`, …). No letter ⇒ not an atom ⇒ not a marker span.
        while j < len && matches!(bytes[j], b' ' | b'\t') {
            j += 1;
        }
        let letters_start = j;
        while j < len && bytes[j].is_ascii_alphabetic() {
            j += 1;
        }
        if j == letters_start {
            return None;
        }
        // Optional `_` / `{` run, then the subscript digit run.
        while j < len && matches!(bytes[j], b'_' | b'{') {
            j += 1;
        }
        let digits_start = j;
        while j < len && bytes[j].is_ascii_digit() {
            j += 1;
        }
        if j == digits_start {
            return None; // a letter with no subscript is not a place marker
        }
        // Fold the digit run (saturating — place indices are tiny, but the input is
        // untrusted dictionary text).
        let mut n = 0usize;
        for &d in &bytes[digits_start..j] {
            n = n.saturating_mul(10).saturating_add((d - b'0') as usize);
        }
        // Optional closing brace of a `$x_{N}$`-style marker.
        if j < len && bytes[j] == b'}' {
            j += 1;
        }
        if (1..=5).contains(&n) {
            span_max = span_max.max(n);
        }
        // Optional whitespace, then either `=` (another merged atom follows) or the
        // closing `$` (span complete). Anything else means this was not a marker span.
        while j < len && matches!(bytes[j], b' ' | b'\t') {
            j += 1;
        }
        if j < len && bytes[j] == b'=' {
            j += 1;
            continue;
        } else if j < len && bytes[j] == b'$' {
            return Some((span_max, j + 1));
        } else {
            return None;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_markers_counted() {
        assert_eq!(
            definition_arity(
                "$x_{1}$ comes/goes to destination $x_{2}$ from origin $x_{3}$ \
                 via route $x_{4}$ using means/vehicle $x_{5}$."
            ),
            5
        );
        assert_eq!(
            definition_arity("$x_{1}$ is a dog/canine/cur of breed/species $x_{2}$."),
            2
        );
        assert_eq!(definition_arity("$x_{1}$ is dead/has died."), 1);
    }

    #[test]
    fn braceless_form_counted() {
        assert_eq!(
            definition_arity("$x_1$ loves/feels romantic affection for $x_2$."),
            2
        );
    }

    #[test]
    fn letter_component_markers_counted() {
        // flubisli: a lujvo whose places are labelled by component letters, not `x`.
        // `$b_1=f_1$` is a single (merged) place at subscript 1; `$f_2$` is place 2.
        // The old x-only scanner found no `$x_N$` and mis-read this as arity 1.
        assert_eq!(
            definition_arity("$b_1=f_1$ is an iceberg floating on $f_2$ (water, sea etc.)."),
            2
        );
        // Multi-letter component prefixes (`bi`, `ba`) and a higher merged subscript.
        assert_eq!(
            definition_arity("$bi_1=ba_1$ is a rampart protecting $bi_4=ba_2$ from attack."),
            4
        );
    }

    #[test]
    fn merged_place_counts_once() {
        // An `=`-merge is ONE place at the shared subscript — both sides carry the same
        // N, so counting it once vs twice cannot change the MAX. A 3-way merge still
        // reports its subscript, never a fabricated higher place.
        assert_eq!(
            definition_arity("$x_1=l_1=b_1$ is a quantity of antibody."),
            1
        );
        assert_eq!(
            definition_arity("$d_1=k_1$ acts so that $d_2=k_2$ becomes $k_3$."),
            3
        );
    }

    #[test]
    fn spaced_merge_tolerated() {
        // jbovlaste writes the merge both tight (`$x_1=t_1$`) and spaced (`$x_1 = t_1$`);
        // ASCII whitespace around `=` and before the closing `$` is tolerated.
        assert_eq!(
            definition_arity("$x_1 = t_1$ is the elapsed time reducing $x_2$ to $x_3$."),
            3
        );
        assert_eq!(definition_arity("$c_2 $ is the endpoint."), 2);
    }

    #[test]
    fn mixed_x_and_letter_markers() {
        // A definition mixing an `$x_N$` place with component-letter places takes the
        // overall max over all markers.
        assert_eq!(
            definition_arity("$x_1=g_1$ (agent) marks $b_3$ with material $b_2$."),
            3
        );
    }

    #[test]
    fn prose_mentions_not_counted() {
        // The real places are 1..3 ($x_{N}$). A bare prose `x4` / `(cf. x4)` must NOT
        // bump the arity to 4 — this is the over-arity bug the `$…$` discipline closes.
        assert_eq!(
            definition_arity("$x_{1}$ gives $x_{2}$ to $x_{3}$ (cf. x4 for the reverse)."),
            3
        );
        // A space between `x` and the digit, and a brace-without-dollar, are not markers.
        assert_eq!(
            definition_arity("$x_{1}$ repeats roughly x 5 times near {x4} for $x_{2}$."),
            2
        );
    }

    #[test]
    fn dollar_math_is_not_a_marker() {
        // `$`-delimited math (money, exponents) is not a place marker: the atom grammar
        // rejects a leading digit and the `^` in an exponent, so no place is fabricated.
        assert_eq!(
            definition_arity("$x_1$ costs $5 and scales as $10^9$ for $x_2$."),
            2
        );
        assert_eq!(definition_arity("$x_1$ has volume $m^3$."), 1);
    }

    #[test]
    fn no_marker_defaults_to_one() {
        assert_eq!(
            definition_arity("a property with no place markup at all"),
            1
        );
        assert_eq!(definition_arity(""), 1);
    }

    #[test]
    fn out_of_range_marker_capped() {
        // A 6-place markup is outside the gismu place range; N>5 is dropped, so the
        // result caps at 5 (preserves the historical 1..=5 behavior).
        assert_eq!(
            definition_arity("$x_{1}$ a $x_{2}$ b $x_{3}$ c $x_{4}$ d $x_{5}$ e $x_{6}$ f."),
            5
        );
    }
}
