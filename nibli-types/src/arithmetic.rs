//! Built-in arithmetic for the engine's three native compute predicates.
//!
//! `pilji` (multiply), `sumji` (add), and `dilcu` (divide) each assert the
//! relation `x1 = x2 op x3`. This is the SINGLE shared evaluation used by both
//! the logji engine fast path (compiled into the WASM guest) and the gasnu host
//! fast path — `nibli-types` is the one crate both depend on. The Python
//! reference backend (`python/nibli_backend.py`) mirrors the same semantics.

/// Evaluate a built-in arithmetic predicate `x1 = x2 op x3` over three numbers.
///
/// Returns `Some(true|false)` for `pilji`/`sumji`/`dilcu` given at least three
/// arguments, and `None` otherwise (unknown relation or too few args) so the
/// caller falls through to the external compute backend.
///
/// Equality is TOLERANT (`isclose`, rel_tol `1e-9`), so decimal queries such as
/// `0.3 = 0.1 + 0.2` answer TRUE despite IEEE-754 rounding — the engine, the
/// host, and the Python backend all agree. The `dilcu` divide-by-zero check is an
/// exact `== 0.0` guard (a guard, not a result comparison).
pub fn eval_arithmetic(relation: &str, args: &[f64]) -> Option<bool> {
    let (&x1, &x2, &x3) = (args.first()?, args.get(1)?, args.get(2)?);
    match relation {
        "pilji" => Some(isclose(x1, x2 * x3)),
        "sumji" => Some(isclose(x1, x2 + x3)),
        "dilcu" => Some(x3 != 0.0 && isclose(x1, x2 / x3)),
        _ => None,
    }
}

/// Tolerant float equality, mirroring Python `math.isclose(a, b, rel_tol=1e-9,
/// abs_tol=0.0)`: `|a - b| <= 1e-9 * max(|a|, |b|)`. (With `abs_tol = 0`, `0.0`
/// is close only to exactly `0.0`, matching the reference.)
fn isclose(a: f64, b: f64) -> bool {
    (a - b).abs() <= 1e-9 * a.abs().max(b.abs())
}

#[cfg(test)]
mod tests {
    use super::eval_arithmetic;

    #[test]
    fn integer_cases_exact() {
        assert_eq!(eval_arithmetic("pilji", &[6.0, 2.0, 3.0]), Some(true)); // 6 = 2*3
        assert_eq!(eval_arithmetic("pilji", &[7.0, 2.0, 3.0]), Some(false));
        assert_eq!(eval_arithmetic("sumji", &[5.0, 2.0, 3.0]), Some(true)); // 5 = 2+3
        assert_eq!(eval_arithmetic("sumji", &[4.0, 2.0, 3.0]), Some(false));
        assert_eq!(eval_arithmetic("dilcu", &[3.0, 6.0, 2.0]), Some(true)); // 3 = 6/2
    }

    #[test]
    fn float_tolerance_headline() {
        // 0.1 + 0.2 = 0.30000000000000004 in IEEE-754; exact `==` would say
        // FALSE, but the user means 0.3 — isclose makes it TRUE.
        assert_eq!(eval_arithmetic("sumji", &[0.3, 0.1, 0.2]), Some(true));
        // A genuinely-wrong claim is still FALSE (the tolerance is tiny).
        assert_eq!(eval_arithmetic("sumji", &[0.4, 0.1, 0.2]), Some(false));
        // Product with rounding: 0.1 * 0.1 = 0.010000000000000002.
        assert_eq!(eval_arithmetic("pilji", &[0.01, 0.1, 0.1]), Some(true));
    }

    #[test]
    fn dilcu_divide_by_zero_is_false_not_none() {
        assert_eq!(eval_arithmetic("dilcu", &[0.0, 5.0, 0.0]), Some(false));
    }

    #[test]
    fn unknown_relation_and_short_args_are_none() {
        assert_eq!(eval_arithmetic("tenfa", &[8.0, 2.0, 3.0]), None);
        assert_eq!(eval_arithmetic("sumji", &[5.0, 2.0]), None);
    }
}
