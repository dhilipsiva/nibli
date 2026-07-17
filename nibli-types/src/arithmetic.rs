//! Built-in arithmetic for the engine's three native compute predicates.
//!
//! `pilji` (multiply), `sumji` (add), and `dilcu` (divide) each assert the
//! relation `x1 = x2 op x3`. This is the SINGLE shared evaluation used by both
//! the nibli-reason engine fast path (compiled into the WASM guest) and the nibli-host host
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
    // A non-finite operand (a literal too large for an f64 overflows to ±inf) makes the
    // relation meaningless — DECLINE (None) rather than return a confident TRUE/FALSE.
    // nibli-reason turns this into `Unknown(NonFinite)`; the nibli-host host fast path declines too.
    let nonfinite_operand = !x1.is_finite() || !x2.is_finite() || !x3.is_finite();
    let result = match relation {
        "product" => x2 * x3,
        "sum" => x2 + x3,
        "quotient" => {
            if x3 == 0.0 {
                // Divide-by-zero (exact guard): never equal — but only DECIDE that for
                // finite operands; with a non-finite operand it is the undetermined case.
                return if nonfinite_operand { None } else { Some(false) };
            }
            x2 / x3
        }
        _ => return None,
    };
    // Even finite operands can overflow (e.g. `1e200 * 1e200 -> inf`); an out-of-range
    // result is equally undetermined.
    if nonfinite_operand || !result.is_finite() {
        return None;
    }
    Some(isclose(x1, result))
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
        // Conformance: the evaluator's domain is exactly relations::BUILTIN_ARITHMETIC
        // (the single-source name sets) — comparisons are NOT tolerant arithmetic.
        for r in crate::relations::BUILTIN_ARITHMETIC {
            assert!(
                eval_arithmetic(r, &[6.0, 2.0, 3.0]).is_some(),
                "{r} must be evaluable"
            );
        }
        for r in crate::relations::NUMERIC_COMPARISONS {
            assert!(
                eval_arithmetic(r, &[6.0, 2.0, 3.0]).is_none(),
                "{r} must not be tolerant arithmetic"
            );
        }
        assert_eq!(eval_arithmetic("product", &[6.0, 2.0, 3.0]), Some(true)); // 6 = 2*3
        assert_eq!(eval_arithmetic("product", &[7.0, 2.0, 3.0]), Some(false));
        assert_eq!(eval_arithmetic("sum", &[5.0, 2.0, 3.0]), Some(true)); // 5 = 2+3
        assert_eq!(eval_arithmetic("sum", &[4.0, 2.0, 3.0]), Some(false));
        assert_eq!(eval_arithmetic("quotient", &[3.0, 6.0, 2.0]), Some(true)); // 3 = 6/2
    }

    #[test]
    fn float_tolerance_headline() {
        // 0.1 + 0.2 = 0.30000000000000004 in IEEE-754; exact `==` would say
        // FALSE, but the user means 0.3 — isclose makes it TRUE.
        assert_eq!(eval_arithmetic("sum", &[0.3, 0.1, 0.2]), Some(true));
        // A genuinely-wrong claim is still FALSE (the tolerance is tiny).
        assert_eq!(eval_arithmetic("sum", &[0.4, 0.1, 0.2]), Some(false));
        // Product with rounding: 0.1 * 0.1 = 0.010000000000000002.
        assert_eq!(eval_arithmetic("product", &[0.01, 0.1, 0.1]), Some(true));
    }

    #[test]
    fn dilcu_divide_by_zero_is_false_not_none() {
        assert_eq!(eval_arithmetic("quotient", &[0.0, 5.0, 0.0]), Some(false));
    }

    #[test]
    fn non_finite_operand_or_result_declines() {
        let inf = f64::INFINITY;
        // A non-finite operand makes the relation undetermined → None (nibli-reason surfaces
        // Unknown(NonFinite)); never a confident TRUE/FALSE.
        assert_eq!(eval_arithmetic("sum", &[inf, inf, 1.0]), None);
        assert_eq!(eval_arithmetic("product", &[1.0, inf, 2.0]), None);
        assert_eq!(eval_arithmetic("quotient", &[1.0, inf, 2.0]), None);
        assert_eq!(eval_arithmetic("sum", &[f64::NAN, 1.0, 2.0]), None);
        // Finite operands whose product overflows to ±inf are equally undetermined.
        assert_eq!(eval_arithmetic("product", &[1.0, 1e200, 1e200]), None);
        // A divide-by-zero with FINITE operands is still a decided false (not None).
        assert_eq!(eval_arithmetic("quotient", &[0.0, 5.0, 0.0]), Some(false));
        // A non-finite operand on a divide-by-zero is undetermined, not a decided false.
        assert_eq!(eval_arithmetic("quotient", &[inf, 5.0, 0.0]), None);
    }

    #[test]
    fn unknown_relation_and_short_args_are_none() {
        assert_eq!(eval_arithmetic("exponential", &[8.0, 2.0, 3.0]), None);
        assert_eq!(eval_arithmetic("sum", &[5.0, 2.0]), None);
    }
}
