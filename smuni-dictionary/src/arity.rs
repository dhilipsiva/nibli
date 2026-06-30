//! Canonical gismu/lujvo arity (place count) from a lensisku `definition` field.
//!
//! lensisku/jbovlaste marks each REAL place with the structured token `$x_{N}$` (and the
//! brace-less `$x_N$`). [`definition_arity`] takes the MAX N over those markers
//! ONLY — distinct from loose prose mentions of `xN` — so a parenthetical / prose
//! `xN` (e.g. "x 4 times", "(cf. x4)") can no longer fabricate an extra place (the
//! over-arity bug the old prose byte-scan had). Shared by `build.rs` (via
//! `#[path]`) and the crate's tests.

/// Highest place index N over the canonical `$x_{N}$` / `$x_N$` place markers in a
/// lensisku definition. Bare prose `xN` (no `$…$` delimiters) is ignored. N is
/// kept within `1..=5` (the gismu place range — preserves the historical cap, so
/// no collateral change to lujvo arity). Defaults to 1 when no marker is present.
pub fn definition_arity(definition: &str) -> usize {
    let bytes = definition.as_bytes();
    let len = bytes.len();
    let mut max_place = 0usize;
    let mut i = 0;
    while i < len {
        // Canonical place marker: `$x` then optional `_`/`{`, a digit run, optional
        // `}`, then a closing `$`. Anything else (bare prose `xN`, a `{x4}` without
        // `$`, an `x 4` with a space) is NOT a place marker and is skipped.
        if bytes[i] == b'$' && i + 1 < len && bytes[i + 1] == b'x' {
            let mut j = i + 2;
            while j < len && matches!(bytes[j], b'_' | b'{') {
                j += 1;
            }
            let digits_start = j;
            while j < len && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j > digits_start {
                let mut k = j;
                if k < len && bytes[k] == b'}' {
                    k += 1;
                }
                if k < len && bytes[k] == b'$' {
                    if let Ok(n) = definition[digits_start..j].parse::<usize>() {
                        if (1..=5).contains(&n) {
                            max_place = max_place.max(n);
                        }
                    }
                    i = k + 1;
                    continue;
                }
            }
        }
        i += 1;
    }
    max_place.max(1)
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
    fn prose_mentions_not_counted() {
        // The real places are 1..3 ($x_{N}$). A bare prose `x4` / `(cf. x4)` must NOT
        // bump the arity to 4 — this is the over-arity bug the fix closes.
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
        // result caps at 5 (preserves the historical 1..=5 behavior — no collateral
        // lujvo-arity change in this fix).
        assert_eq!(
            definition_arity("$x_{1}$ a $x_{2}$ b $x_{3}$ c $x_{4}$ d $x_{5}$ e $x_{6}$ f."),
            5
        );
    }
}
