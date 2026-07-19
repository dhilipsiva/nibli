//! Mutation-audit kill tests: each test pins the compiled-shape property a
//! specific surviving cargo-mutants mutant of the nibli-semantics compile
//! path would silently break (the mutant is named in each test's comment).
//! Same discipline as the rest of shape_tests: drive the REAL front-end via
//! `lb` and assert on the public `LogicBuffer`.

use super::*;

/// The (first) `__abs_<hash>` opacity-marker relation in the buffer — the
/// content identity of an abstraction (predicate.rs `abstraction_content_key`).
/// These single-abstraction compiles carry exactly one.
fn abs_marker(b: &LogicBuffer) -> String {
    b.nodes
        .iter()
        .find_map(|n| match n {
            LogicNode::Predicate((r, _)) if r.starts_with("__abs_") => Some(r.clone()),
            _ => None,
        })
        .expect("buffer has no __abs_ marker")
}

#[test]
fn mutation_audit_abs_marker_sees_constants() {
    // KILLS predicate.rs `replace SemanticCompiler::canon_term with ()`:
    // a constant-blind content key gives `fact { goes(Adam) }` and
    // `fact { goes(Bel) }` the SAME `__abs_` marker, so a believes-P assert
    // would satisfy a believes-Q query downstream.
    let adam = abs_marker(&lb("big(fact { goes(Adam) })."));
    let bel = abs_marker(&lb("big(fact { goes(Bel) })."));
    assert_ne!(
        adam, bel,
        "abstractions differing only in a constant must get distinct markers"
    );
    // Identity half (over-kill guard): the same content must keep the SAME
    // marker across independent compiles — assert/query matching depends on it.
    let adam_again = abs_marker(&lb("big(fact { goes(Adam) })."));
    assert_eq!(adam, adam_again, "same content must keep the same marker");
}

#[test]
fn mutation_audit_abs_marker_sees_tense_and_deontic_wrappers() {
    // KILLS predicate.rs `replace SemanticCompiler::canon_wrap with ()`:
    // a no-op canon_wrap drops the ENTIRE wrapped subtree (tag AND body) from
    // the content key, so any two wrapper-rooted bodies conflate. `past P` vs
    // `future P` (and `must P` vs `may P`) differ ONLY through canon_wrap.
    let past = abs_marker(&lb("big(fact { past goes(Adam) })."));
    let future = abs_marker(&lb("big(fact { future goes(Adam) })."));
    assert_ne!(past, future, "tense-differing abstractions must differ");
    let must = abs_marker(&lb("big(fact { must goes(Adam) })."));
    let may = abs_marker(&lb("big(fact { may goes(Adam) })."));
    assert_ne!(must, may, "deontic-differing abstractions must differ");
}

#[test]
fn mutation_audit_abs_marker_sees_variable_topology() {
    // KILLS predicate.rs `replace SemanticCompiler::canon_var -> usize with 0`
    // (and `with 1`). Both bodies close the same two `$vars` over the same
    // And-skeleton with the same binder COUNT (three: $x, $y, the event var),
    // so only the first-seen-index renaming distinguishes gives_x3 re-using
    // $x from gives_x3 re-using $y; a constant canon_var conflates them.
    let xyx = abs_marker(&lb("big(fact { gives($x, $y, $x) })."));
    let xyy = abs_marker(&lb("big(fact { gives($x, $y, $y) })."));
    assert_ne!(
        xyx, xyy,
        "variable-topology-differing abstractions must differ"
    );
    // Identity half: the canonical renaming stays deterministic across
    // independent compiles.
    let xyx_again = abs_marker(&lb("big(fact { gives($x, $y, $x) })."));
    assert_eq!(xyx, xyx_again);
}

#[test]
fn mutation_audit_selector_place3_mints_swap13() {
    // KILLS predicate.rs `replace match guard permuted.len() >= 3 with false
    // in SemanticCompiler::apply_predicate` (the Swap13 face): `some goes.x3`
    // (a place-3 selector over arity-5 `goes`) must bind the description var
    // in goes_x3 — a dropped swap silently rebinds it to goes_x1.
    let b = lb("big(some goes.x3).");
    let bound = role_filler(&b, "goes_x3").unwrap();
    assert!(matches!(bound, LogicalTerm::Variable(_)));
    assert_eq!(
        Some(bound),
        role_filler(&b, "big_x1"),
        "the domain var reaches the matrix"
    );
    assert_eq!(role_filler(&b, "goes_x1"), Some(LogicalTerm::Unspecified));
}

#[test]
fn mutation_audit_selector_place4_mints_swap14() {
    // KILLS the Swap14 guard-false face of the same apply_predicate mutant trio.
    let b = lb("big(some goes.x4).");
    let bound = role_filler(&b, "goes_x4").unwrap();
    assert!(matches!(bound, LogicalTerm::Variable(_)));
    assert_eq!(Some(bound), role_filler(&b, "big_x1"));
    assert_eq!(role_filler(&b, "goes_x1"), Some(LogicalTerm::Unspecified));
}

#[test]
fn mutation_audit_selector_place5_mints_swap15() {
    // KILLS the Swap15 guard-false face of the same apply_predicate mutant trio.
    let b = lb("big(some goes.x5).");
    let bound = role_filler(&b, "goes_x5").unwrap();
    assert!(matches!(bound, LogicalTerm::Variable(_)));
    assert_eq!(Some(bound), role_filler(&b, "big_x1"));
    assert_eq!(role_filler(&b, "goes_x1"), Some(LogicalTerm::Unspecified));
}

#[test]
fn mutation_audit_converted_description_domain_binds_swapped_place() {
    // KILLS helpers.rs `replace < with ==` / `with >` in
    // SemanticCompiler::close_quantifier (the restrictor-args padding loop):
    // unpadded args ([var] instead of [var, _, _]) sail past the Converted
    // swap guard (1 >= 2 is false), so `every owned` would bind the domain
    // var at owns_x1 (the OWNER) instead of owns_x2 (the owned thing).
    let b = lb("big(every owned).");
    assert!(matches!(root(&b), LogicNode::ForAllNode(_)));
    let bound = role_filler(&b, "owns_x2").unwrap();
    assert!(matches!(bound, LogicalTerm::Variable(_)));
    assert_eq!(Some(bound), role_filler(&b, "big_x1"));
    assert_eq!(role_filler(&b, "owns_x1"), Some(LogicalTerm::Unspecified));
}

#[test]
fn mutation_audit_block_exact_count_converted_domain_binds_swapped_place() {
    // KILLS compile.rs `replace < with ==` / `with >` in
    // SemanticCompiler::compile_sentence (the BlockQuant::ExactCount
    // restrictor padding loop — the block-form twin of close_quantifier's).
    let b = lb("exactly 1 owned $o: big($o).");
    assert!(matches!(root(&b), LogicNode::CountNode((_, 1, _))));
    assert_eq!(
        role_filler(&b, "owns_x2"),
        Some(LogicalTerm::Variable("$o".into()))
    );
    assert_eq!(role_filler(&b, "owns_x1"), Some(LogicalTerm::Unspecified));
    assert_eq!(
        role_filler(&b, "big_x1"),
        Some(LogicalTerm::Variable("$o".into()))
    );
}

#[test]
fn mutation_audit_pair_converted_modifier_keeps_swap() {
    // KILLS helpers.rs `delete match arm Predicate::Converted(...) in
    // SemanticCompiler::collect_stack_units` AND predicate.rs
    // `replace < with ==` / `with >` on the `idx < mod_args.len()`
    // pair-modifier swap face of apply_predicate: in `owned dog(Rex)` the
    // converted modifier unit must keep its swap — Rex is the OWNED thing
    // (owns_x2), never the owner (owns_x1).
    let b = lb("owned dog(Rex).");
    assert!(role_is_const(&b, "owns_x2", "rex"));
    assert!(role_is_const(&b, "dog_x1", "rex"));
    assert_eq!(role_filler(&b, "owns_x1"), Some(LogicalTerm::Unspecified));
    // One predication: the modifier's roles ride the head's event var.
    assert_eq!(
        pred_args(&b, "owns_x2").unwrap()[0],
        pred_args(&b, "dog_x1").unwrap()[0],
        "modifier and head share the event var"
    );
}

#[test]
fn mutation_audit_pair_converted_head_keeps_swap() {
    // KILLS the `idx < head_args.len()` pair-HEAD swap face of the same
    // apply_predicate `<` mutants (and backs up the unit-base arm deletion):
    // with the converted unit as the pair head, both positional args must
    // route through the swap — owned(Rex, Adam) puts Adam at owns_x1 (owner)
    // and Rex at owns_x2 (owned).
    let b = lb("dog owned(Rex, Adam).");
    assert!(role_is_const(&b, "owns_x1", "adam"));
    assert!(role_is_const(&b, "owns_x2", "rex"));
    assert!(role_is_const(&b, "dog_x1", "rex"));
}

#[test]
fn mutation_audit_grouped_converted_unit_keeps_swap() {
    // KILLS helpers.rs `delete match arm Predicate::Grouped(...) in
    // SemanticCompiler::collect_stack_units`: the unit walk must keep
    // collecting swaps THROUGH a `[...]` group, or `[owned] dog(Rex)` silently
    // loses the conversion the ungrouped spelling keeps.
    let b = lb("[owned] dog(Rex).");
    assert!(role_is_const(&b, "owns_x2", "rex"));
    assert_eq!(role_filler(&b, "owns_x1"), Some(LogicalTerm::Unspecified));
}

#[test]
fn mutation_audit_arity2_via_modal_compiles() {
    // KILLS compile.rs `replace < with <= in SemanticCompiler::compile_proposition`
    // (the `modal_arity < 2` fail-closed face): arity 2 is the MINIMUM legal
    // via-modal arity (x1 = the tag's own term, x2 = the main clause's x1
    // link), and the mutant spuriously rejects every arity-2 modal. `likes`
    // is arity 2 in the corpus; the modal stays a flat predicate.
    let b = lb("goes(me) via likes(you).");
    assert!(has_pred(&b, "goes"), "main clause decomposes");
    let likes = pred_args(&b, "likes").unwrap();
    assert_eq!(likes.len(), 2);
    assert_eq!(likes[0], LogicalTerm::Constant("you".into()));
    assert_eq!(likes[1], LogicalTerm::Constant("me".into()));
}

#[test]
fn mutation_audit_clause_prefill_routes_through_conversion() {
    // KILLS compile.rs `replace SemanticCompiler::terms_contain_explicit_kea
    // -> bool with true`: a spuriously-true scan disables the implicit-`it`
    // x1 PRE-fill (which runs BEFORE conversion). The spelling threads the
    // divergence deliberately: a via-tag `it` satisfies the parser's
    // mandatory-it rule, but a modal-carried `it` is NOT place-filling, so
    // the shallow scan must return false and keep the implicit-x1 default.
    // Under the mutant the prefill is skipped and — because the modal `it`
    // sets ref_used — the injection fallback never runs either, so the
    // clause body's owns_x2 slot silently stays Unspecified: the clause no
    // longer predicates ownership of the dog at all.
    let b = lb("big(some dog where owned() via likes(it)).");
    let bound = role_filler(&b, "owns_x2").unwrap();
    assert!(matches!(bound, LogicalTerm::Variable(_)));
    assert_eq!(
        Some(bound.clone()),
        role_filler(&b, "dog_x1"),
        "the clause binds the described entity in the swapped place"
    );
    assert_eq!(role_filler(&b, "owns_x1"), Some(LogicalTerm::Unspecified));
    // The via modal is flat: likes(<the it = the dog var>, <main x1 = the
    // same var, threaded through the prefill>).
    let likes = pred_args(&b, "likes").unwrap();
    assert_eq!(likes[0], bound);
    assert_eq!(likes[1], bound);
}
