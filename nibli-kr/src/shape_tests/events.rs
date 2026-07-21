//! Neo-Davidsonian event-decomposition shape.

use super::*;

#[test]
fn event_decompose_basic() {
    // `goes(me).` → ∃e. goes(e) ∧ goes_x1(e, me) ∧ … — the type predicate
    // carries the event var, the x1 role predicate carries (event, filler),
    // and the two share the event var.
    let b = lb("goes(me).");
    assert!(matches!(root(&b), LogicNode::ExistsNode(_)));
    let type_args = pred_args(&b, "goes").unwrap();
    let x1_args = pred_args(&b, "goes_x1").unwrap();
    assert!(matches!(x1_args.as_slice(), [_, LogicalTerm::Constant(c)] if c == "me"));
    assert_eq!(
        type_args[0], x1_args[0],
        "type-pred and role share the event var"
    );
    assert!(matches!(type_args[0], LogicalTerm::Variable(_)));
}

#[test]
fn all_five_roles_emitted_for_known_arity() {
    // `goes` is a known corpus predicate — all five role predicates emit,
    // and no sixth (the arity floor: known_gismu_gets_correct_arity).
    let b = lb("goes(me).");
    for r in ["goes_x1", "goes_x2", "goes_x3", "goes_x4", "goes_x5"] {
        assert!(has_pred(&b, r), "missing {r}");
    }
    assert!(
        !has_pred(&b, "goes_x6"),
        "arity-5 predicate must not emit x6"
    );
}

#[test]
fn pair_shares_event_var() {
    // `fast dog(me).` — the tanru head+modifier share one event; the modifier
    // contributes only its role predicate (`fast_x1`), bound to the same
    // entity `me`.
    let b = lb("fast dog(me).");
    assert!(has_pred(&b, "dog"));
    let dog_x1 = pred_args(&b, "dog_x1").unwrap();
    let fast_x1 = pred_args(&b, "fast_x1").unwrap();
    assert_eq!(
        dog_x1[0], fast_x1[0],
        "head and modifier share the event var"
    );
    assert!(role_is_const(&b, "dog_x1", "me"));
    assert!(role_is_const(&b, "fast_x1", "me"));
}

#[test]
fn pair_emits_no_intersective_type_predicate() {
    // `big dog(me).` — an event-bound modifier does NOT get a standalone `big`
    // type predicate (that would be the intersective fallacy); only the
    // role predicate `big_x1`.
    let b = lb("big dog(me).");
    assert!(
        !has_pred(&b, "big"),
        "modifier must not emit a standalone type pred"
    );
    assert!(has_pred(&b, "big_x1"));
}

#[test]
fn three_unit_stack_keeps_every_modifier() {
    // `big fast dog(me).` — a 3-unit stack: the head `dog` gets the type
    // predicate; BOTH modifiers contribute role predicates on the one shared
    // event, and neither gets a standalone type predicate. Before 2026-07-19
    // the nested pair side was collapsed to its single head name, so `fast`
    // was silently dropped from the compiled buffer.
    let b = lb("big fast dog(me).");
    assert!(has_pred(&b, "dog"));
    let dog_x1 = pred_args(&b, "dog_x1").unwrap();
    let big_x1 = pred_args(&b, "big_x1").unwrap();
    let fast_x1 = pred_args(&b, "fast_x1").unwrap();
    assert_eq!(
        dog_x1[0], big_x1[0],
        "head and first modifier share the event var"
    );
    assert_eq!(
        dog_x1[0], fast_x1[0],
        "head and second modifier share the event var"
    );
    assert!(role_is_const(&b, "big_x1", "me"));
    assert!(role_is_const(&b, "fast_x1", "me"));
    assert!(
        !has_pred(&b, "big"),
        "modifier must not emit a standalone type pred"
    );
    assert!(
        !has_pred(&b, "fast"),
        "modifier must not emit a standalone type pred"
    );
}

#[test]
fn bracketed_stack_compiles_like_unbracketed() {
    // `[big fast] dog(me).` — grouping is head-selection only in the
    // shared-event encoding: every unit's roles land on the one event, so the
    // bracketed and unbracketed spellings compile to the same buffer. Before
    // 2026-07-19 the bracketed modifier group was collapsed to `fast` and
    // `big` was silently dropped.
    let bracketed = lb("[big fast] dog(me).");
    let unbracketed = lb("big fast dog(me).");
    assert_eq!(
        bracketed, unbracketed,
        "grouping must not drop or reorder units"
    );
    for r in ["dog", "dog_x1", "big_x1", "fast_x1"] {
        assert!(has_pred(&bracketed, r), "missing {r}");
    }
    assert!(!has_pred(&bracketed, "big"));
    assert!(!has_pred(&bracketed, "fast"));
}

#[test]
fn observative_with_modifier_compiles() {
    // `big rain().` — an observative (zero arguments) with a modifier stack:
    // the head's and the modifier's role predicates all emit with Unspecified
    // fillers, sharing one event; the empty argument list must not be indexed.
    // KILLS predicate.rs `replace && with ||` on the pair-modifier
    // `!args.is_empty() && *mod_arity > 0` face (the mutant would read
    // args[0] from the empty list).
    let b = lb("big rain().");
    assert!(has_pred(&b, "rain"));
    assert!(has_pred(&b, "rain_x1"));
    assert!(
        has_pred(&b, "big_x1"),
        "modifier roles must emit on an observative"
    );
    assert!(
        !has_pred(&b, "big"),
        "modifier must not emit a standalone type pred"
    );
    assert_eq!(role_filler(&b, "big_x1"), Some(LogicalTerm::Unspecified));
    assert_eq!(role_filler(&b, "rain_x1"), Some(LogicalTerm::Unspecified));
}

#[test]
fn decompose_with_quantified_argument() {
    // `goes(some dog).` — the quantified argument still decomposes: both
    // relations and both x1 role predicates are present under the existential.
    let b = lb("goes(some dog).");
    assert!(matches!(root(&b), LogicNode::ExistsNode(_)));
    for r in ["dog", "goes", "dog_x1", "goes_x1"] {
        assert!(has_pred(&b, r), "missing {r}");
    }
}

#[test]
fn conversion_routes_places() {
    // `owned` is the converted alias of `owns` (SE swap): the surface
    // `owned(Rex, Adam)` routes Rex→x2, Adam→x1. Covers both the old
    // event_conversion_x2 and the wrappers x2_conversion test.
    let b = lb("owned(Rex, Adam).");
    assert!(role_is_const(&b, "owns_x1", "adam"));
    assert!(role_is_const(&b, "owns_x2", "rex"));
}
