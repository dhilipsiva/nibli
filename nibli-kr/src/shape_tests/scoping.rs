//! Quantifier scope order: binder spines, ∃-over-∀ nesting, closedness.

use super::*;

#[test]
fn free_var_before_universal_outscopes_it() {
    // `eats($da, every dog).` — the surface-earlier `$da` binds OUTSIDE the
    // universal: spine `[Exists($da), ForAll]`, and $da's subtree holds the ∀.
    let b = lb("eats($da, every dog).");
    assert_eq!(
        binder_spine(&b),
        vec![Binder::Exists("$da".into()), Binder::ForAll]
    );
    assert!(exists_outscopes_forall(&b, "$da"));
    assert!(free_vars(&b).is_empty());
}

#[test]
fn free_var_after_universal_closes_inside_it() {
    // `eats(every dog, $da).` — the surface-later `$da` closes INSIDE the
    // universal's matrix (spine starts ForAll; $da does not outscope it).
    // Folds in the old regressions `da_after_universal_closes_inside_forall`.
    let b = lb("eats(every dog, $da).");
    assert_eq!(binder_spine(&b).first(), Some(&Binder::ForAll));
    assert!(!exists_outscopes_forall(&b, "$da"));
    assert_eq!(count_exists_binding(&b, "$da"), 1);
    assert!(free_vars(&b).is_empty());
}

#[test]
fn free_var_interleaved_between_count_and_universal() {
    // `goes(exactly 2 dog, $da, every cat).` — outermost is the Count; the
    // middle `$da` still outscopes the trailing ∀.
    let b = lb("goes(exactly 2 dog, $da, every cat).");
    assert_eq!(binder_spine(&b).first(), Some(&Binder::Count(2)));
    assert!(exists_outscopes_forall(&b, "$da"));
    assert_eq!(count_exists_binding(&b, "$da"), 1);
    assert!(free_vars(&b).is_empty());
}

#[test]
fn restrictor_internal_free_var_closes_innermost() {
    // `goes(every dog where loves(it, $da)).` — the `$da` inside the
    // restrictor closes innermost; the whole form is a closed universal.
    let b = lb("goes(every dog where loves(it, $da)).");
    assert_eq!(binder_spine(&b).first(), Some(&Binder::ForAll));
    assert_eq!(count_exists_binding(&b, "$da"), 1);
    assert!(free_vars(&b).is_empty());
}

#[test]
fn prenex_var_not_re_closed() {
    // `all $da: eats($da, some dog).` — a prenex `$da` is universally bound and
    // must NOT be re-closed existentially (count 0).
    let b = lb("all $da: eats($da, some dog).");
    assert_eq!(binder_spine(&b).first(), Some(&Binder::ForAll));
    assert_eq!(count_exists_binding(&b, "$da"), 0);
    assert!(free_vars(&b).is_empty());
}

#[test]
fn repeated_free_var_dedups_to_one_exists() {
    let b = lb("eats($da, $da).");
    assert_eq!(count_exists_binding(&b, "$da"), 1);
    assert!(free_vars(&b).is_empty());
}

#[test]
fn identity_with_free_var_closed() {
    // `$da = me.` — the flat identity predicate with a free var closes cleanly.
    let b = lb("$da = me.");
    assert_eq!(count_exists_binding(&b, "$da"), 1);
    assert!(has_pred(&b, "equals"));
    assert!(free_vars(&b).is_empty());
}
