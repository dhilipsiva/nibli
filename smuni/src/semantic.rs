//! Semantic compiler: flat AST buffer → First-Order Logic IR.
//!
//! Walks the WIT AST buffer (flat arrays of `Selbri`, `Sumti`, `Sentence`) and
//! compiles each sentence into a [`LogicalForm`] tree. Key transformations:
//!
//! - **Quantifier scoping**: gadri descriptions (`lo`/`le`/`la`/`ro lo`) introduce
//!   quantified variables; scopes are closed outward after the bridi body is compiled.
//! - **Quantifier closure**: bare logic variables (`da`/`de`/`di`) are wrapped in
//!   `Exists`; Skolemization itself happens downstream in logji at assertion time.
//! - **Connective expansion**: sumti/selbri/sentence connectives expand into FOL
//!   `And`/`Or`/`Not`/`Biconditional`/`Xor` combinations.
//! - **Conversion**: `se`/`te`/`ve`/`xe` permute argument places.
//! - **Abstraction**: `nu`/`du'u`/`ka`/`ni`/`si'o` reify inner bridi as 1-place predicates.
//! - **Relative clauses**: `poi`/`voi` (restrictive) conjoin a domain restrictor;
//!   `noi` (non-restrictive) conjoins its body at the MATRIX level (consequent for
//!   universals, body conjunct for existentials/counts) so it does not narrow the
//!   quantifier domain. Residual: under exact-count quantifiers `noi` is still
//!   treated restrictively (documented limitation).
//! - **Modal tags**: BAI cmavo and `fi'o` produce conjoined modal predications.
//! - **String interning**: all relation names and variable names use [`lasso::Rodeo`]
//!   for zero-copy comparison and deduplication.

use crate::dictionary::JbovlasteSchema;
use crate::ir::{LogicalForm, LogicalTerm};
use lasso::Rodeo;
use nibli_types::ast::{
    AbstractionKind, Attitudinal, BaiTag, Bridi, Connective, Conversion, Gadri, ModalTag, PlaceTag,
    RelClauseKind, Selbri, Sentence, SentenceConnective, Sumti, Tense,
};

mod compile;
mod helpers;
mod selbri;

/// The kind of quantifier introduced by a gadri description.
#[derive(Debug, Clone)]
pub(crate) enum QuantifierKind {
    /// lo → ∃x (veridical existential, restrictor = selbri predicate)
    Existential,
    /// ro lo → ∀x (veridical universal, restrictor = selbri predicate)
    Universal,
    /// ro le → ∀x (referential universal, restrictor = opaque le_domain predicate)
    UniversalLe,
    /// PA lo → exactly N (veridical, restrictor = selbri predicate)
    ExactCount(u32),
    /// PA le → exactly N (referential, restrictor = opaque le_domain predicate)
    ExactCountLe(u32),
}

/// Tracks a quantifier introduced by a description (lo/le/ro lo/ro le/PA lo),
/// with an optional relative clause restrictor.
pub(crate) struct QuantifierEntry {
    /// The fresh variable bound by this quantifier.
    var: lasso::Spur,
    /// Index into the selbri array for the description predicate (restrictor source).
    desc_id: u32,
    /// Optional restrictive (poi/voi) relative clause body, already compiled.
    /// Folded on the domain side: antecedent for ∀, conjunct for ∃/Count.
    restrictor: Option<LogicalForm>,
    /// Optional non-restrictive (noi) relative clause body, already compiled.
    /// Folded on the MATRIX side (consequent for ∀, body conjunct for ∃/Count) so
    /// it does not narrow the quantifier domain — see `close_quantifier`.
    noi_restrictor: Option<LogicalForm>,
    /// What kind of quantifier this description introduces.
    kind: QuantifierKind,
}

/// One scope introduction in a bridi, recorded in left-to-right SURFACE order so
/// quantifier nesting can follow Lojban scope (leftmost = outermost). Folding the
/// list in reverse interleaves bare-variable existentials among the description
/// quantifiers, so `da citka ro lo gerku` compiles `∃da.∀x` and `ro lo gerku cu
/// citka da` compiles `∀x.∃da`.
pub(crate) enum ScopeMarker {
    /// A gadri description (lo/le/ro lo/ro le/PA lo) → closed via `close_quantifier`.
    Desc(QuantifierEntry),
    /// A bare logic variable (da/de/di), first occurrence → closed via `Exists`.
    Bare(lasso::Spur),
}

/// Stateful compiler that transforms flat AST buffers into FOL logic forms.
///
/// Maintains a string interner, fresh variable counter, and context state for
/// relative clauses, ka-abstractions, and `ma` query variables. Accumulated
/// errors are checked after compilation.
pub struct SemanticCompiler {
    /// String interner for relation names and variable names.
    pub interner: Rodeo,
    /// Monotonically increasing counter for generating fresh variable names.
    pub var_counter: usize,
    /// When inside a relative clause, holds the bound variable from the
    /// enclosing description. ke'a resolves to this variable directly.
    rel_clause_var: Option<lasso::Spur>,
    /// Set to true when ke'a is encountered during rel clause compilation.
    /// When true, inject_variable is skipped (user placed the variable explicitly).
    kea_used: bool,
    /// When inside a ka abstraction, holds the variable that ce'u resolves to.
    /// This is the x1 arg from the enclosing description quantifier.
    ka_open_var: Option<lasso::Spur>,
    /// Fresh variables generated for `ma` query pro-sumti. Each `ma` gets
    /// an independent variable (unlike da/de/di which co-refer). These are
    /// wrapped in ∃ during quantifier closure.
    ma_vars: Vec<lasso::Spur>,
    /// Accumulated semantic errors (e.g., ambiguous inject_variable).
    /// Checked after compilation; if non-empty, compile_buffer returns error.
    pub errors: Vec<String>,
    /// Monotonically increasing counter for generating fresh event variable names.
    event_counter: usize,
    /// Relative clause bodies attached to sumti that introduce NO quantifier
    /// (la names, le descriptions, pro-sumti). The clause term is already
    /// substituted in; `compile_bridi` drains its frame's entries and conjoins
    /// them into the bridi matrix (previously these were silently dropped —
    /// panel finding 2026-06-10).
    pending_matrix_conjuncts: Vec<LogicalForm>,
    /// One-shot: the implicit `ke'a` subject of a relative clause, to be placed
    /// as the x1 ARGUMENT of the clause's main bridi BEFORE selbri conversion —
    /// the same position an explicit subject occupies. Consumed by the first
    /// `compile_bridi` of the clause body. This makes `poi se prami la .alis.`
    /// route `ke'a` through `se` conversion to the correct underlying role
    /// (prami_x2), instead of post-hoc `inject_variable` wrongly filling the
    /// conversion-vacated `prami_x1` slot.
    pending_clause_subject: Option<lasso::Spur>,
    /// Logic variables (`da`/`de`/`di`) bound by an enclosing prenex
    /// (`ro da ... zo'u`). These are universally quantified by the prenex
    /// lowering, so `compile_bridi` must NOT existentially close them the way it
    /// closes free `da`/`de`/`di`.
    prenex_vars: std::collections::HashSet<lasso::Spur>,
}

impl SemanticCompiler {
    /// Creates a new compiler with empty interner and zeroed counters.
    pub fn new() -> Self {
        Self {
            interner: Rodeo::new(),
            var_counter: 0,
            rel_clause_var: None,
            kea_used: false,
            ka_open_var: None,
            ma_vars: Vec::new(),
            errors: Vec::new(),
            event_counter: 0,
            pending_matrix_conjuncts: Vec::new(),
            pending_clause_subject: None,
            prenex_vars: std::collections::HashSet::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{LogicalForm, LogicalTerm};
    use nibli_types::ast::{
        Bridi, Connective, Gadri, PlaceTag, RelClause, RelClauseKind, Selbri, Sentence,
        SentenceConnective, Sumti,
    };

    /// Helper: build a minimal buffer and compile the first sentence.
    /// Returns the compiled LogicalForm.
    fn compile_one(
        selbris: Vec<Selbri>,
        sumtis: Vec<Sumti>,
        bridi: Bridi,
    ) -> (LogicalForm, SemanticCompiler) {
        let sentences = vec![Sentence::Simple(bridi)];
        let mut compiler = SemanticCompiler::new();
        let form = compiler.compile_bridi(
            match &sentences[0] {
                Sentence::Simple(b) => b,
                _ => unreachable!(),
            },
            &selbris,
            &sumtis,
            &sentences,
        );
        (form, compiler)
    }

    /// Helper: resolve a string from the compiler's interner
    fn resolve(compiler: &SemanticCompiler, spur: &lasso::Spur) -> String {
        compiler.interner.resolve(spur).to_string()
    }

    /// Helper: collect all (relation_name, args) pairs from a LogicalForm tree.
    fn collect_predicates(
        form: &LogicalForm,
        compiler: &SemanticCompiler,
    ) -> Vec<(String, Vec<LogicalTerm>)> {
        let mut result = Vec::new();
        collect_predicates_inner(form, compiler, &mut result);
        result
    }

    fn collect_predicates_inner(
        form: &LogicalForm,
        compiler: &SemanticCompiler,
        result: &mut Vec<(String, Vec<LogicalTerm>)>,
    ) {
        match form {
            LogicalForm::Predicate { relation, args } => {
                result.push((resolve(compiler, relation), args.clone()));
            }
            LogicalForm::And(l, r)
            | LogicalForm::Or(l, r)
            | LogicalForm::Biconditional(l, r)
            | LogicalForm::Xor(l, r) => {
                collect_predicates_inner(l, compiler, result);
                collect_predicates_inner(r, compiler, result);
            }
            LogicalForm::Not(inner)
            | LogicalForm::Exists(_, inner)
            | LogicalForm::ForAll(_, inner)
            | LogicalForm::Past(inner)
            | LogicalForm::Present(inner)
            | LogicalForm::Future(inner)
            | LogicalForm::Obligatory(inner)
            | LogicalForm::Permitted(inner) => {
                collect_predicates_inner(inner, compiler, result);
            }
            LogicalForm::Count { body, .. } => {
                collect_predicates_inner(body, compiler, result);
            }
        }
    }

    /// Helper: check if form contains a predicate with given name.
    fn has_pred(form: &LogicalForm, name: &str, compiler: &SemanticCompiler) -> bool {
        collect_predicates(form, compiler)
            .iter()
            .any(|(n, _)| n == name)
    }

    /// Helper: get the args of the first predicate with given name.
    fn get_pred_args(
        form: &LogicalForm,
        name: &str,
        compiler: &SemanticCompiler,
    ) -> Option<Vec<LogicalTerm>> {
        collect_predicates(form, compiler)
            .into_iter()
            .find(|(n, _)| n == name)
            .map(|(_, args)| args)
    }

    /// Helper: get the args of EVERY predicate with the given name (in tree order).
    /// Needed when a form distributes into multiple predications sharing a name
    /// (e.g. two `rinka` modals, or four `prami` leaves).
    fn get_all_pred_args(
        form: &LogicalForm,
        name: &str,
        compiler: &SemanticCompiler,
    ) -> Vec<Vec<LogicalTerm>> {
        collect_predicates(form, compiler)
            .into_iter()
            .filter(|(n, _)| n == name)
            .map(|(_, args)| args)
            .collect()
    }

    /// Helper: extract a `Constant` term's interned string (panics otherwise).
    fn const_str(compiler: &SemanticCompiler, term: &LogicalTerm) -> String {
        match term {
            LogicalTerm::Constant(c) => resolve(compiler, c),
            other => panic!("expected Constant, got {:?}", other),
        }
    }

    /// Helper: collect the names of all FREE `Variable` occurrences in a form
    /// (binder-tracking). A closed top-level form should have NONE — any free
    /// da/de/di/ma var is an under-quantification soundness bug.
    fn free_vars(form: &LogicalForm, compiler: &SemanticCompiler) -> Vec<String> {
        let mut bound: Vec<lasso::Spur> = Vec::new();
        let mut out: Vec<String> = Vec::new();
        free_vars_inner(form, compiler, &mut bound, &mut out);
        out
    }

    fn free_vars_inner(
        form: &LogicalForm,
        compiler: &SemanticCompiler,
        bound: &mut Vec<lasso::Spur>,
        out: &mut Vec<String>,
    ) {
        match form {
            LogicalForm::Predicate { args, .. } => {
                for arg in args {
                    if let LogicalTerm::Variable(spur) = arg {
                        if !bound.contains(spur) {
                            out.push(resolve(compiler, spur));
                        }
                    }
                }
            }
            LogicalForm::And(l, r)
            | LogicalForm::Or(l, r)
            | LogicalForm::Biconditional(l, r)
            | LogicalForm::Xor(l, r) => {
                free_vars_inner(l, compiler, bound, out);
                free_vars_inner(r, compiler, bound, out);
            }
            LogicalForm::Not(inner)
            | LogicalForm::Past(inner)
            | LogicalForm::Present(inner)
            | LogicalForm::Future(inner)
            | LogicalForm::Obligatory(inner)
            | LogicalForm::Permitted(inner) => {
                free_vars_inner(inner, compiler, bound, out);
            }
            LogicalForm::Exists(v, body) | LogicalForm::ForAll(v, body) => {
                bound.push(*v);
                free_vars_inner(body, compiler, bound, out);
                bound.pop();
            }
            LogicalForm::Count { var, body, .. } => {
                bound.push(*var);
                free_vars_inner(body, compiler, bound, out);
                bound.pop();
            }
        }
    }

    /// Helper: count `Exists` nodes binding a variable with the given name.
    /// (ForAll binders are NOT counted — a prenex-bound `da` is universal, not
    /// existential.)
    fn count_exists_binding(form: &LogicalForm, name: &str, compiler: &SemanticCompiler) -> usize {
        match form {
            LogicalForm::Exists(v, body) => {
                let here = usize::from(resolve(compiler, v) == name);
                here + count_exists_binding(body, name, compiler)
            }
            LogicalForm::ForAll(_, body) => count_exists_binding(body, name, compiler),
            LogicalForm::And(l, r)
            | LogicalForm::Or(l, r)
            | LogicalForm::Biconditional(l, r)
            | LogicalForm::Xor(l, r) => {
                count_exists_binding(l, name, compiler) + count_exists_binding(r, name, compiler)
            }
            LogicalForm::Not(inner)
            | LogicalForm::Past(inner)
            | LogicalForm::Present(inner)
            | LogicalForm::Future(inner)
            | LogicalForm::Obligatory(inner)
            | LogicalForm::Permitted(inner) => count_exists_binding(inner, name, compiler),
            LogicalForm::Count { body, .. } => count_exists_binding(body, name, compiler),
            LogicalForm::Predicate { .. } => 0,
        }
    }

    /// A quantifier binder, for asserting nesting ORDER (which `free_vars` /
    /// `count_exists_binding` do not capture). `ForAll`/`Count` carry no var name
    /// (description vars are fresh `_vN`); `Exists` carries the bound name so a
    /// test can assert it is exactly `da`/`de`/`di`.
    #[derive(Debug, PartialEq)]
    enum Binder {
        Exists(String),
        ForAll,
        Count(u32),
    }

    /// The quantifier-binder sequence from the ROOT inward, following the single
    /// body branch through transparent Not/tense/deontic wrappers and stopping at
    /// the first And/Or/Predicate. Lets a test distinguish `∃da.∀x`
    /// (`[Exists("da"), ForAll]`) from `∀x.∃da` (`[ForAll]`, the `da` hidden in
    /// the universal's matrix Or). Use `exists_outscopes_forall` for ∃-over-∀
    /// nesting that the Or/And hides from the spine.
    fn binder_spine(form: &LogicalForm, compiler: &SemanticCompiler) -> Vec<Binder> {
        let mut out = Vec::new();
        let mut cur = form;
        loop {
            match cur {
                LogicalForm::Exists(v, body) => {
                    out.push(Binder::Exists(resolve(compiler, v)));
                    cur = body;
                }
                LogicalForm::ForAll(_, body) => {
                    out.push(Binder::ForAll);
                    cur = body;
                }
                LogicalForm::Count { count, body, .. } => {
                    out.push(Binder::Count(*count));
                    cur = body;
                }
                LogicalForm::Not(inner)
                | LogicalForm::Past(inner)
                | LogicalForm::Present(inner)
                | LogicalForm::Future(inner)
                | LogicalForm::Obligatory(inner)
                | LogicalForm::Permitted(inner) => cur = inner,
                _ => break,
            }
        }
        out
    }

    /// True if a `ForAll` appears anywhere in `form`'s subtree.
    fn subtree_has_forall(form: &LogicalForm) -> bool {
        match form {
            LogicalForm::ForAll(_, _) => true,
            LogicalForm::Exists(_, b)
            | LogicalForm::Not(b)
            | LogicalForm::Past(b)
            | LogicalForm::Present(b)
            | LogicalForm::Future(b)
            | LogicalForm::Obligatory(b)
            | LogicalForm::Permitted(b) => subtree_has_forall(b),
            LogicalForm::Count { body, .. } => subtree_has_forall(body),
            LogicalForm::And(l, r)
            | LogicalForm::Or(l, r)
            | LogicalForm::Biconditional(l, r)
            | LogicalForm::Xor(l, r) => subtree_has_forall(l) || subtree_has_forall(r),
            LogicalForm::Predicate { .. } => false,
        }
    }

    /// True if some `Exists` binding `name` has a `ForAll` in its subtree — i.e.
    /// the existential OUTSCOPES a universal (∃-over-∀). Reaches through the
    /// matrix-side Or/And that `binder_spine` stops at.
    fn exists_outscopes_forall(
        form: &LogicalForm,
        name: &str,
        compiler: &SemanticCompiler,
    ) -> bool {
        match form {
            LogicalForm::Exists(v, body) => {
                (resolve(compiler, v) == name && subtree_has_forall(body))
                    || exists_outscopes_forall(body, name, compiler)
            }
            LogicalForm::ForAll(_, body) => exists_outscopes_forall(body, name, compiler),
            LogicalForm::Count { body, .. } => exists_outscopes_forall(body, name, compiler),
            LogicalForm::Not(b)
            | LogicalForm::Past(b)
            | LogicalForm::Present(b)
            | LogicalForm::Future(b)
            | LogicalForm::Obligatory(b)
            | LogicalForm::Permitted(b) => exists_outscopes_forall(b, name, compiler),
            LogicalForm::And(l, r)
            | LogicalForm::Or(l, r)
            | LogicalForm::Biconditional(l, r)
            | LogicalForm::Xor(l, r) => {
                exists_outscopes_forall(l, name, compiler)
                    || exists_outscopes_forall(r, name, compiler)
            }
            LogicalForm::Predicate { .. } => false,
        }
    }

    // ─── du (identity) selbri lowering ───────────────────────────

    #[test]
    fn test_du_lowers_flat_not_event_decomposed() {
        // `la .X. cu du la .Y.` (Root("du") + 2 sumti) must lower to a FLAT
        // 2-arg du(X,Y) predicate — NOT the Neo-Davidsonian event form
        // (∃e. du(e) ∧ du_x1(e,X) ∧ du_x2(e,Y)) — so logji's union-find
        // ingestion (which matches relation=="du" && args.len()==2) fires.
        let selbris = vec![Selbri::Root("du".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()), // 0
            Sumti::ProSumti("do".into()), // 1
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        let args =
            get_pred_args(&form, "du", &compiler).expect("flat du predicate must be present");
        assert_eq!(args.len(), 2, "du must be a flat 2-arg predicate");
        assert!(
            !has_pred(&form, "du_x1", &compiler),
            "du must NOT be event-decomposed (no role predicates)"
        );
    }

    #[test]
    fn test_du_with_more_than_two_sumti_is_rejected() {
        // Fail-closed: n-ary du is unsupported (logji handles only binary
        // identity). A 3-sumti du must push a semantic error rather than
        // silently dropping the third argument.
        let selbris = vec![Selbri::Root("du".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()), // 0
            Sumti::ProSumti("do".into()), // 1
            Sumti::ProSumti("ti".into()), // 2
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1, 2],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (_form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            !compiler.errors.is_empty(),
            ">2-place du must be rejected fail-closed"
        );
    }

    // ─── Sumti connective expansion tests ────────────────────────

    #[test]
    fn test_sumti_connective_e_expands_to_and() {
        // mi .e do klama → klama(mi, ...) ∧ klama(do, ...)
        // Buffer layout:
        //   sumtis: [0: mi, 1: do, 2: Connected(0, Je, false, 1)]
        //   selbris: [0: klama]
        //   bridi: { relation: 0, head_terms: [2], tail_terms: [] }
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                    // 0
            Sumti::ProSumti("do".into()),                    // 1
            Sumti::Connected((0, Connective::Je, false, 1)), // 2
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![2],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Should be And(klama_event(mi), klama_event(do))
        // Each side is an event-decomposed form (Exists wrapping type+role preds)
        match &form {
            LogicalForm::And(left, right) => {
                // Left: event-decomposed klama with mi in x1
                assert!(
                    has_pred(left, "klama", &compiler),
                    "left should have klama type pred"
                );
                let x1_args = get_pred_args(left, "klama_x1", &compiler).unwrap();
                match &x1_args[1] {
                    LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "mi"),
                    other => panic!("expected Constant(mi) in klama_x1, got {:?}", other),
                }
                // Right: event-decomposed klama with do in x1
                assert!(
                    has_pred(right, "klama", &compiler),
                    "right should have klama type pred"
                );
                let x1_args_r = get_pred_args(right, "klama_x1", &compiler).unwrap();
                match &x1_args_r[1] {
                    LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "do"),
                    other => panic!("expected Constant(do) in klama_x1, got {:?}", other),
                }
            }
            other => panic!("expected And, got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_a_expands_to_or() {
        // mi .a do klama → klama(mi, ...) ∨ klama(do, ...)
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),
            Sumti::ProSumti("do".into()),
            Sumti::Connected((0, Connective::Ja, false, 1)),
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![2],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, _) = compile_one(selbris, sumtis, bridi);
        assert!(matches!(&form, LogicalForm::Or(_, _)));
    }

    #[test]
    fn test_sumti_connective_o_expands_to_biconditional() {
        // mi .o do klama → (¬klama(mi) ∨ klama(do)) ∧ (¬klama(do) ∨ klama(mi))
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),
            Sumti::ProSumti("do".into()),
            Sumti::Connected((0, Connective::Jo, false, 1)),
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![2],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, _) = compile_one(selbris, sumtis, bridi);
        // Biconditional stored as first-class IR node (expanded at flattening)
        assert!(
            matches!(&form, LogicalForm::Biconditional(_, _)),
            "expected Biconditional, got {:?}",
            form
        );
    }

    #[test]
    fn test_sumti_connective_u_expands_to_xor() {
        // mi .u do klama → (klama(mi) ∨ klama(do)) ∧ ¬(klama(mi) ∧ klama(do))
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),
            Sumti::ProSumti("do".into()),
            Sumti::Connected((0, Connective::Ju, false, 1)),
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![2],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, _) = compile_one(selbris, sumtis, bridi);
        // XOR stored as first-class IR node (expanded at flattening)
        assert!(
            matches!(&form, LogicalForm::Xor(_, _)),
            "expected Xor, got {:?}",
            form
        );
    }

    #[test]
    fn test_sumti_connective_enai_negates_right() {
        // mi .e nai do klama → klama(mi, ...) ∧ ¬klama(do, ...)
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),
            Sumti::ProSumti("do".into()),
            Sumti::Connected((0, Connective::Je, true, 1)), // right_negated = true
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![2],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Should be And(klama_event(mi), Not(klama_event(do)))
        match &form {
            LogicalForm::And(left, right) => {
                // Left: event-decomposed klama with mi in x1
                assert!(
                    has_pred(left, "klama", &compiler),
                    "left should have klama type pred"
                );
                let x1_args = get_pred_args(left, "klama_x1", &compiler).unwrap();
                match &x1_args[1] {
                    LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "mi"),
                    other => panic!("expected Constant(mi) in klama_x1, got {:?}", other),
                }
                // Right: Not(klama_event(do))
                match right.as_ref() {
                    LogicalForm::Not(inner) => {
                        assert!(
                            has_pred(inner, "klama", &compiler),
                            "Not body should have klama type pred"
                        );
                        let x1_args_r = get_pred_args(inner, "klama_x1", &compiler).unwrap();
                        match &x1_args_r[1] {
                            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "do"),
                            other => panic!("expected Constant(do) in klama_x1, got {:?}", other),
                        }
                    }
                    other => panic!("expected Not, got {:?}", other),
                }
            }
            other => panic!("expected And, got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_in_tail_position() {
        // mi prami lo gerku .e lo mlatu
        // head: [mi], selbri: prami, tail: [Connected(lo gerku, Je, lo mlatu)]
        // → prami(mi, lo gerku) ∧ prami(mi, lo mlatu)
        // But with descriptions: ∃v0.(gerku(v0) ∧ prami(mi, v0)) ∧ ∃v1.(mlatu(v1) ∧ prami(mi, v1))
        let selbris = vec![
            Selbri::Root("prami".into()), // 0
            Selbri::Root("gerku".into()), // 1
            Selbri::Root("mlatu".into()), // 2
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                    // 0
            Sumti::Description((Gadri::Lo, 1)),              // 1: lo gerku
            Sumti::Description((Gadri::Lo, 2)),              // 2: lo mlatu
            Sumti::Connected((1, Connective::Je, false, 2)), // 3
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![3],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, _) = compile_one(selbris, sumtis, bridi);

        // The result should be And(Exists(...), Exists(...))
        match &form {
            LogicalForm::And(left, right) => {
                assert!(
                    matches!(left.as_ref(), LogicalForm::Exists(_, _)),
                    "expected Exists on left, got {:?}",
                    left
                );
                assert!(
                    matches!(right.as_ref(), LogicalForm::Exists(_, _)),
                    "expected Exists on right, got {:?}",
                    right
                );
            }
            other => panic!("expected And(Exists, Exists), got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_with_bridi_negation() {
        // mi .e do na klama → ¬(klama(mi) ∧ klama(do))
        // Actually: na applies at bridi level, and .e expansion happens first
        // → And(Not(klama(mi)), Not(klama(do)))? No...
        // .e splits first: bridi(head:[mi], negated:true) and bridi(head:[do], negated:true)
        // Each gets negated: Not(klama(mi)) ∧ Not(klama(do))
        // Wait, the whole bridi is negated, so both copies inherit negated:true
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),
            Sumti::ProSumti("do".into()),
            Sumti::Connected((0, Connective::Je, false, 1)),
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![2],
            tail_terms: vec![],
            negated: true,
            tense: None,
            attitudinal: None,
        };

        let (form, _) = compile_one(selbris, sumtis, bridi);

        // Both sub-bridis inherit negated:true → And(Not(klama(mi)), Not(klama(do)))
        match &form {
            LogicalForm::And(left, right) => {
                assert!(
                    matches!(left.as_ref(), LogicalForm::Not(_)),
                    "expected Not on left, got {:?}",
                    left
                );
                assert!(
                    matches!(right.as_ref(), LogicalForm::Not(_)),
                    "expected Not on right, got {:?}",
                    right
                );
            }
            other => panic!("expected And(Not, Not), got {:?}", other),
        }
    }

    // ─── Connected sumti under place tags / BAI modals + CLL place counter ───
    // Soundness fix: a connected sumti nested under a place tag or BAI modal
    // (`fa mi .e do`, `ri'a do .e ti`) previously dropped the right operand;
    // only the FIRST connected sumti in a bridi was split; and untagged sumti
    // after a tag filled the first free slot instead of the CLL place counter.

    #[test]
    fn test_fa_tagged_connected_distributes() {
        // `fa mi .e do klama` parses as Tagged(Fa, Connected(mi, Je, do)) — the
        // tag distributes over BOTH operands: klama(mi in x1) ∧ klama(do in x1).
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                    // 0
            Sumti::ProSumti("do".into()),                    // 1
            Sumti::Connected((0, Connective::Je, false, 1)), // 2: mi .e do
            Sumti::Tagged((PlaceTag::Fa, 2)),                // 3: fa (mi .e do)
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![3],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        match &form {
            LogicalForm::And(left, right) => {
                let l = get_pred_args(left, "klama_x1", &compiler).expect("left klama_x1");
                let r = get_pred_args(right, "klama_x1", &compiler).expect("right klama_x1");
                assert_eq!(const_str(&compiler, &l[1]), "mi");
                assert_eq!(const_str(&compiler, &r[1]), "do");
            }
            other => panic!("expected And(klama(mi), klama(do)), got {:?}", other),
        }
    }

    #[test]
    fn test_bai_modal_connected_distributes() {
        // `mi klama ri'a do .e ti` → ModalTagged(Ria, Connected(do, Je, ti)).
        // Must distribute into TWO rinka modals: rinka(do, mi) and rinka(ti, mi).
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                          // 0
            Sumti::ProSumti("do".into()),                          // 1
            Sumti::ProSumti("ti".into()),                          // 2
            Sumti::Connected((1, Connective::Je, false, 2)),       // 3: do .e ti
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Ria), 3)), // 4: ri'a (do .e ti)
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![4],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        let rinkas = get_all_pred_args(&form, "rinka", &compiler);
        assert_eq!(
            rinkas.len(),
            2,
            "expected two rinka modals (do .e ti), got {}: {:?}",
            rinkas.len(),
            rinkas
        );
        let tagged: Vec<String> = rinkas.iter().map(|a| const_str(&compiler, &a[0])).collect();
        assert!(tagged.contains(&"do".to_string()), "missing rinka(do, ..)");
        assert!(tagged.contains(&"ti".to_string()), "missing rinka(ti, ..)");
        for a in &rinkas {
            assert_eq!(const_str(&compiler, &a[1]), "mi", "rinka x2 = main x1 (mi)");
        }
    }

    #[test]
    fn test_two_connected_sumti_both_split() {
        // `mi .e do prami ti .e ta` — TWO connected sumti must both distribute
        // into four prami leaves: (mi,ti), (mi,ta), (do,ti), (do,ta).
        let selbris = vec![Selbri::Root("prami".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                    // 0
            Sumti::ProSumti("do".into()),                    // 1
            Sumti::ProSumti("ti".into()),                    // 2
            Sumti::ProSumti("ta".into()),                    // 3
            Sumti::Connected((0, Connective::Je, false, 1)), // 4: mi .e do
            Sumti::Connected((2, Connective::Je, false, 3)), // 5: ti .e ta
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![4],
            tail_terms: vec![5],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        let x1 = get_all_pred_args(&form, "prami_x1", &compiler);
        let x2 = get_all_pred_args(&form, "prami_x2", &compiler);
        assert_eq!(x1.len(), 4, "expected 4 prami leaves, got {}", x1.len());
        let pairs: Vec<(String, String)> = x1
            .iter()
            .zip(x2.iter())
            .map(|(a, b)| (const_str(&compiler, &a[1]), const_str(&compiler, &b[1])))
            .collect();
        for expected in [("mi", "ti"), ("mi", "ta"), ("do", "ti"), ("do", "ta")] {
            assert!(
                pairs
                    .iter()
                    .any(|(l, r)| l == expected.0 && r == expected.1),
                "missing prami{:?} in {:?}",
                expected,
                pairs
            );
        }
    }

    #[test]
    fn test_cll_place_counter_resumes_after_fi() {
        // `klama fi le zarci do` — CLL: `fi` sets the place counter to x3, so
        // `le zarci` is x3 and the following UNTAGGED `do` resumes at x4
        // (NOT x1, which is the pre-fix "first free slot" bug).
        let selbris = vec![
            Selbri::Root("klama".into()), // 0
            Selbri::Root("zarci".into()), // 1
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Le, 1)), // 0: le zarci
            Sumti::Tagged((PlaceTag::Fi, 0)),   // 1: fi le zarci
            Sumti::ProSumti("do".into()),       // 2: do (untagged)
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![],
            tail_terms: vec![1, 2],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        let x4 = get_pred_args(&form, "klama_x4", &compiler).expect("klama_x4 present");
        assert_eq!(
            const_str(&compiler, &x4[1]),
            "do",
            "untagged `do` must fill x4 after fi"
        );
        let x1 = get_pred_args(&form, "klama_x1", &compiler).expect("klama_x1 present");
        assert!(
            !matches!(&x1[1], LogicalTerm::Constant(c) if resolve(&compiler, c) == "do"),
            "do must NOT land in x1 (pre-fix bug), got {:?}",
            x1[1]
        );
        let x3 = get_pred_args(&form, "klama_x3", &compiler).expect("klama_x3 present");
        assert!(
            matches!(&x3[1], LogicalTerm::Description(_)),
            "fi `le zarci` must fill x3, got {:?}",
            x3[1]
        );
    }

    #[test]
    fn test_untagged_before_tag_still_fills_x1() {
        // Regression: `mi klama fe do` — untagged `mi` fills x1, `fe do` fills x2.
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),     // 0
            Sumti::ProSumti("do".into()),     // 1
            Sumti::Tagged((PlaceTag::Fe, 1)), // 2: fe do
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![2],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        let x1 = get_pred_args(&form, "klama_x1", &compiler).expect("klama_x1");
        let x2 = get_pred_args(&form, "klama_x2", &compiler).expect("klama_x2");
        assert_eq!(const_str(&compiler, &x1[1]), "mi");
        assert_eq!(const_str(&compiler, &x2[1]), "do");
    }

    // ─── Abstraction type tests ──────────────────────────────────

    /// Helper: build a buffer with abstraction and compile.
    fn compile_abstraction(
        kind: AbstractionKind,
        inner_selbri: &str,
        inner_sumtis: Vec<Sumti>,
    ) -> (LogicalForm, SemanticCompiler) {
        // Build: lo <kind> <inner_sumtis> <inner_selbri> kei cu barda
        // Buffer layout:
        //   selbris: [0: inner_selbri, 1: Abstraction(kind, sentence_idx=1), 2: barda]
        //   sumtis: [0..N: inner sumtis, N: Description(Lo, 1)]
        //   sentences: [0: top-level bridi, 1: inner bridi]
        let inner_sumti_ids: Vec<u32> = (0..inner_sumtis.len() as u32).collect();
        let desc_sumti_idx = inner_sumtis.len() as u32;

        let mut all_sumtis = inner_sumtis;
        all_sumtis.push(Sumti::Description((Gadri::Lo, 1))); // desc_sumti_idx

        let selbris = vec![
            Selbri::Root(inner_selbri.into()), // 0
            Selbri::Abstraction((kind, 1)),    // 1 → sentences[1]
            Selbri::Root("barda".into()),      // 2
        ];

        let inner_bridi = Bridi {
            relation: 0,
            head_terms: inner_sumti_ids,
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let outer_bridi = Bridi {
            relation: 2,
            head_terms: vec![desc_sumti_idx],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let sentences = vec![Sentence::Simple(outer_bridi), Sentence::Simple(inner_bridi)];

        let mut compiler = SemanticCompiler::new();
        let form = compiler.compile_bridi(
            match &sentences[0] {
                Sentence::Simple(b) => b,
                _ => unreachable!(),
            },
            &selbris,
            &all_sumtis,
            &sentences,
        );
        (form, compiler)
    }

    #[test]
    fn test_duhu_abstraction_produces_duhu_predicate() {
        // lo du'u mi klama kei cu barda
        // → Exists(_v0, And(duhu(_v0), And(klama(mi, ...), barda(_v0, ...))))
        let (form, compiler) = compile_abstraction(
            AbstractionKind::Duhu,
            "klama",
            vec![Sumti::ProSumti("mi".into())],
        );

        // Should be Exists(_v0, And(duhu(_v0), And(klama_event, barda_event)))
        // With event decomposition, klama and barda are wrapped in Exists
        match &form {
            LogicalForm::Exists(var, _body) => {
                assert!(resolve(&compiler, var).starts_with("_v"));
                // Use the recursive helpers that descend into Exists
                assert!(
                    has_pred(&form, "duhu", &compiler),
                    "expected 'duhu' predicate"
                );
                assert!(
                    has_pred(&form, "klama", &compiler),
                    "expected 'klama' type predicate"
                );
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_ka_with_ceu_binds_open_variable() {
        // lo ka ce'u melbi kei cu barda
        // ce'u should resolve to the same variable as the quantified entity
        let (form, compiler) = compile_abstraction(
            AbstractionKind::Ka,
            "melbi",
            vec![Sumti::ProSumti("ce'u".into())],
        );

        // Should be Exists(_v0, And(ka(_v0), And(melbi_event, barda_event)))
        // The key: ce'u resolves to _v0, which is the same as the description variable
        // With events, melbi_x1 role pred has (ev, _v0) — the bound var
        match &form {
            LogicalForm::Exists(var, _body) => {
                let var_name = resolve(&compiler, var);
                // ka type pred should reference the description variable
                let ka_args = get_pred_args(&form, "ka", &compiler).unwrap();
                let ka_arg0 = match &ka_args[0] {
                    LogicalTerm::Variable(v) => resolve(&compiler, v),
                    other => panic!("expected Variable for ka arg, got {:?}", other),
                };
                assert_eq!(
                    ka_arg0, var_name,
                    "ka predicate arg should be the quantified variable"
                );
                // melbi_x1 role pred should have the same variable as its entity arg
                let melbi_x1_args = get_pred_args(&form, "melbi_x1", &compiler).unwrap();
                let melbi_entity = match &melbi_x1_args[1] {
                    LogicalTerm::Variable(v) => resolve(&compiler, v),
                    other => panic!("expected Variable for melbi_x1 entity, got {:?}", other),
                };
                assert_eq!(
                    melbi_entity, var_name,
                    "ce'u should resolve to the same variable as ka's entity"
                );
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_ni_abstraction_produces_ni_predicate() {
        let (form, compiler) = compile_abstraction(
            AbstractionKind::Ni,
            "gleki",
            vec![Sumti::ProSumti("mi".into())],
        );

        match &form {
            LogicalForm::Exists(_, _) => {
                // Use the recursive helpers that descend into Exists
                assert!(has_pred(&form, "ni", &compiler), "expected 'ni' predicate");
                assert!(
                    has_pred(&form, "gleki", &compiler),
                    "expected 'gleki' type predicate"
                );
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_siho_abstraction_produces_siho_predicate() {
        let (form, compiler) = compile_abstraction(
            AbstractionKind::Siho,
            "klama",
            vec![Sumti::ProSumti("mi".into())],
        );

        match &form {
            LogicalForm::Exists(_, _) => {
                // Use the recursive helpers that descend into Exists
                assert!(
                    has_pred(&form, "siho", &compiler),
                    "expected 'siho' predicate"
                );
                assert!(
                    has_pred(&form, "klama", &compiler),
                    "expected 'klama' type predicate"
                );
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_nu_abstraction_still_works() {
        let (form, compiler) = compile_abstraction(
            AbstractionKind::Nu,
            "klama",
            vec![Sumti::ProSumti("mi".into())],
        );

        match &form {
            LogicalForm::Exists(_, _) => {
                // Use the recursive helpers that descend into Exists
                assert!(has_pred(&form, "nu", &compiler), "expected 'nu' predicate");
                assert!(
                    has_pred(&form, "klama", &compiler),
                    "expected 'klama' type predicate"
                );
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_ceu_outside_ka_is_rejected() {
        // `ce'u` outside a `ka` abstraction has no binder. The old behavior minted a
        // fresh variable that stayed FREE through compilation (the da/de/di safety net
        // does not close `_v` fresh vars) — a non-ground form leaking toward the store.
        // Fail closed: a semantic error is accumulated (NibliError::Semantic downstream),
        // and no free variable escapes.
        let selbris = vec![Selbri::Root("melbi".into())];
        let sumtis = vec![Sumti::ProSumti("ce'u".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        assert!(
            compiler
                .errors
                .iter()
                .any(|e| e.contains("ce'u outside a ka abstraction")),
            "bare ce'u must accumulate a semantic error, got: {:?}",
            compiler.errors
        );
        // The placeholder term is the rigid Unspecified, never a free variable.
        let x1_args =
            get_pred_args(&form, "melbi_x1", &compiler).expect("expected melbi_x1 role predicate");
        assert!(
            matches!(&x1_args[1], LogicalTerm::Unspecified),
            "rejected ce'u compiles to Unspecified (no free variable), got {:?}",
            x1_args[1]
        );
    }

    // ─── BAI modal tag tests ──────────────────────────────────────

    #[test]
    fn test_bai_ria_produces_conjoined_rinka() {
        // mi klama ri'a do → And(klama(mi, ...), rinka(do, mi, ...))
        // Buffer layout:
        //   sumtis: [0: mi, 1: do, 2: ModalTagged(Fixed(Ria), 1)]
        //   selbris: [0: klama]
        //   bridi: { relation: 0, head_terms: [0], tail_terms: [2] }
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                          // 0
            Sumti::ProSumti("do".into()),                          // 1
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Ria), 1)), // 2
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![2],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // klama is event-decomposed, rinka is a flat modal Predicate
        assert!(
            has_pred(&form, "klama", &compiler),
            "expected klama type predicate"
        );
        assert!(
            has_pred(&form, "klama_x1", &compiler),
            "expected klama_x1 role"
        );
        // Check klama_x1 has mi
        let klama_x1 = get_pred_args(&form, "klama_x1", &compiler).unwrap();
        assert_eq!(
            klama_x1[1],
            LogicalTerm::Constant(compiler.interner.get("mi").unwrap())
        );
        // rinka is a flat Predicate (modal tags are not event-decomposed)
        let rinka_args = get_pred_args(&form, "rinka", &compiler).unwrap();
        // x1 = tagged sumti (do), x2 = main x1 (mi)
        assert_eq!(
            rinka_args[0],
            LogicalTerm::Constant(compiler.interner.get("do").unwrap())
        );
        assert_eq!(
            rinka_args[1],
            LogicalTerm::Constant(compiler.interner.get("mi").unwrap())
        );
    }

    #[test]
    fn test_bai_pio_produces_pilno() {
        // mi citka pi'o lo forca → And(citka(mi, ...), pilno(lo_forca_var, mi, ...))
        // Buffer:
        //   sumtis: [0: mi, 1: Description(Lo, 1), 2: ModalTagged(Fixed(Pio), 1)]
        //   selbris: [0: citka, 1: forca]
        let selbris = vec![
            Selbri::Root("citka".into()), // 0
            Selbri::Root("forca".into()), // 1
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                          // 0
            Sumti::Description((Gadri::Lo, 1)),                    // 1
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Pio), 1)), // 2
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![2],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Should be ∃x.(forca_event(x) ∧ And(citka_event, pilno_event))
        // The outermost is Exists wrapping the description's quantifier
        match &form {
            LogicalForm::Exists(_, _) => {
                // Check all expected predicates exist (recursive through Exists)
                assert!(
                    has_pred(&form, "forca", &compiler),
                    "expected forca restrictor type pred"
                );
                assert!(
                    has_pred(&form, "citka", &compiler),
                    "expected citka type pred"
                );
                assert!(
                    has_pred(&form, "pilno", &compiler),
                    "expected pilno type pred"
                );
            }
            other => panic!(
                "expected Exists wrapping modal conjunction, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_fio_produces_custom_modal() {
        // mi klama fi'o zbasu do → And(klama(mi,...), zbasu(do, mi,...))
        // Buffer:
        //   sumtis: [0: mi, 1: do, 2: ModalTagged(Fio(1), 1)]
        //   selbris: [0: klama, 1: zbasu]
        let selbris = vec![
            Selbri::Root("klama".into()), // 0
            Selbri::Root("zbasu".into()), // 1
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),              // 0
            Sumti::ProSumti("do".into()),              // 1
            Sumti::ModalTagged((ModalTag::Fio(1), 1)), // 2
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![2],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // klama is event-decomposed, zbasu is a flat modal Predicate
        assert!(
            has_pred(&form, "klama", &compiler),
            "expected klama type predicate"
        );
        assert!(
            has_pred(&form, "zbasu", &compiler),
            "expected zbasu modal predicate"
        );
        // zbasu is flat: zbasu(do, mi, ...)
        let zbasu_args = get_pred_args(&form, "zbasu", &compiler).unwrap();
        assert_eq!(
            zbasu_args[0],
            LogicalTerm::Constant(compiler.interner.get("do").unwrap())
        );
        assert_eq!(
            zbasu_args[1],
            LogicalTerm::Constant(compiler.interner.get("mi").unwrap())
        );
    }

    #[test]
    fn test_fio_arity_one_selbri_errors() {
        // `mi barda fi'o prenu fe'u do` — `prenu` (person) is a 1-place selbri, so
        // the modal has no x2 slot to carry the main bridi's x1 (`mi`). A 1-place
        // modal that silently drops that link loses meaning, so it must fail closed.
        // (Only `fi'o` reaches this — every BAI modal gismu is arity >= 2.) `prenu`
        // is a curated-fallback arity-1 gismu, so this fires in both the XML and
        // no-XML builds.
        let selbris = vec![
            Selbri::Root("barda".into()), // 0
            Selbri::Root("prenu".into()), // 1 (arity 1)
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),              // 0
            Sumti::ProSumti("do".into()),              // 1
            Sumti::ModalTagged((ModalTag::Fio(1), 1)), // 2: fi'o prenu, inner=do
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![2],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (_form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            !compiler.errors.is_empty(),
            "a 1-place fi'o modal must fail closed"
        );
        assert!(
            compiler.errors.iter().any(|e| e.contains("Modal tag")),
            "error should name the modal-arity limitation, got: {:?}",
            compiler.errors
        );
    }

    #[test]
    fn test_multiple_bai_tags_conjoin() {
        // mi klama ri'a do pi'o ti → And(And(klama(...), rinka(do,mi,...)), pilno(ti,mi,...))
        let selbris = vec![Selbri::Root("klama".into())]; // 0
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                          // 0
            Sumti::ProSumti("do".into()),                          // 1
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Ria), 1)), // 2
            Sumti::ProSumti("ti".into()),                          // 3
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Pio), 3)), // 4
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![2, 4],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // All three predicates should be present as event-decomposed forms
        assert!(
            has_pred(&form, "klama", &compiler),
            "expected klama type predicate"
        );
        assert!(
            has_pred(&form, "rinka", &compiler),
            "expected rinka type predicate"
        );
        assert!(
            has_pred(&form, "pilno", &compiler),
            "expected pilno type predicate"
        );
    }

    // ─── Numeric quantifier tests ──────────────────────────────────

    #[test]
    fn test_re_lo_produces_count_2() {
        // re lo gerku cu barda → Count(_v0, 2, And(gerku(_v0,...), barda(_v0,...)))
        // Buffer:
        //   sumtis: [0: QuantifiedDescription(2, Lo, 0)]
        //   selbris: [0: gerku, 1: barda]
        //   bridi: { relation: 1, head_terms: [0], tail_terms: [] }
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("barda".into()), // 1
        ];
        let sumtis = vec![
            Sumti::QuantifiedDescription((2, Gadri::Lo, 0)), // 0
        ];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Should be Count { var: _v0, count: 2, body: And(gerku_event, barda_event) }
        // With event decomposition, restrictor and predicate are event-wrapped
        match &form {
            LogicalForm::Count { var, count, body } => {
                assert_eq!(*count, 2);
                assert!(resolve(&compiler, var).starts_with("_v"));
                // The body should contain both gerku and barda type predicates
                assert!(
                    has_pred(body, "gerku", &compiler),
                    "expected gerku restrictor type pred"
                );
                assert!(
                    has_pred(body, "barda", &compiler),
                    "expected barda type pred"
                );
            }
            other => panic!("expected Count, got {:?}", other),
        }
    }

    #[test]
    fn test_no_lo_produces_count_0() {
        // no lo gerku cu barda → Count(_v0, 0, And(gerku(_v0,...), barda(_v0,...)))
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("barda".into()), // 1
        ];
        let sumtis = vec![
            Sumti::QuantifiedDescription((0, Gadri::Lo, 0)), // 0
        ];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, _) = compile_one(selbris, sumtis, bridi);

        match &form {
            LogicalForm::Count { count, .. } => assert_eq!(*count, 0),
            other => panic!("expected Count with count=0, got {:?}", other),
        }
    }

    #[test]
    fn test_pa_lo_produces_count_1() {
        // pa lo gerku cu barda → Count(_v0, 1, ...)
        let selbris = vec![Selbri::Root("gerku".into()), Selbri::Root("barda".into())];
        let sumtis = vec![Sumti::QuantifiedDescription((1, Gadri::Lo, 0))];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, _) = compile_one(selbris, sumtis, bridi);

        match &form {
            LogicalForm::Count { count, .. } => assert_eq!(*count, 1),
            other => panic!("expected Count with count=1, got {:?}", other),
        }
    }

    #[test]
    fn test_lo_still_produces_exists() {
        // Regression: lo gerku cu barda → Exists (not Count)
        let selbris = vec![Selbri::Root("gerku".into()), Selbri::Root("barda".into())];
        let sumtis = vec![Sumti::Description((Gadri::Lo, 0))];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, _) = compile_one(selbris, sumtis, bridi);

        assert!(
            matches!(&form, LogicalForm::Exists(_, _)),
            "expected Exists, got {:?}",
            form
        );
    }

    // ─── Afterthought sentence connective tests ───────────────────

    /// Helper: compile a connected sentence from two simple bridi.
    fn compile_connected(
        conn: SentenceConnective,
        left_selbri: &str,
        left_sumti: &str,
        right_selbri: &str,
        right_sumti: &str,
    ) -> (LogicalForm, SemanticCompiler) {
        let selbris = vec![
            Selbri::Root(left_selbri.into()),
            Selbri::Root(right_selbri.into()),
        ];
        let sumtis = vec![
            Sumti::ProSumti(left_sumti.into()),
            Sumti::ProSumti(right_sumti.into()),
        ];
        let left_bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let right_bridi = Bridi {
            relation: 1,
            head_terms: vec![1],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let sentences = vec![
            Sentence::Simple(left_bridi),
            Sentence::Simple(right_bridi),
            Sentence::Connected((conn, 0, 1)),
        ];
        let mut compiler = SemanticCompiler::new();
        let form = compiler.compile_sentence(2, &selbris, &sumtis, &sentences);
        (form, compiler)
    }

    #[test]
    fn test_afterthought_je_compiles_to_and() {
        let conn = SentenceConnective::Afterthought((false, Connective::Je, false));
        let (form, _) = compile_connected(conn, "klama", "mi", "prami", "do");
        assert!(
            matches!(&form, LogicalForm::And(_, _)),
            "expected And, got {:?}",
            form
        );
    }

    #[test]
    fn test_afterthought_ja_compiles_to_or() {
        let conn = SentenceConnective::Afterthought((false, Connective::Ja, false));
        let (form, _) = compile_connected(conn, "klama", "mi", "prami", "do");
        assert!(
            matches!(&form, LogicalForm::Or(_, _)),
            "expected Or, got {:?}",
            form
        );
    }

    #[test]
    fn test_afterthought_naja_compiles_to_implies() {
        // .i naja = ¬A ∨ B (material conditional)
        let conn = SentenceConnective::Afterthought((true, Connective::Ja, false));
        let (form, _) = compile_connected(conn, "klama", "mi", "prami", "do");
        // Should be Or(Not(left), right)
        match &form {
            LogicalForm::Or(left, _right) => {
                assert!(
                    matches!(left.as_ref(), LogicalForm::Not(_)),
                    "expected Not on left of Or, got {:?}",
                    left
                );
            }
            other => panic!("expected Or(Not(_), _), got {:?}", other),
        }
    }

    // ─── da/de/di quantifier closure tests ──────────────────────

    #[test]
    fn test_da_produces_exists() {
        // da prami mi → ∃da. event_decomposed_prami(da, mi, ...)
        let selbris = vec![Selbri::Root("prami".into())];
        let sumtis = vec![
            Sumti::ProSumti("da".into()), // 0
            Sumti::ProSumti("mi".into()), // 1
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Outermost should be Exists(da, ...) wrapping the event form
        match &form {
            LogicalForm::Exists(var, _body) => {
                assert_eq!(resolve(&compiler, var), "da");
                // Inside should have prami type pred and role preds
                assert!(
                    has_pred(&form, "prami", &compiler),
                    "expected prami type predicate"
                );
                // prami_x1 should have Variable(da)
                let x1_args = get_pred_args(&form, "prami_x1", &compiler).unwrap();
                match &x1_args[1] {
                    LogicalTerm::Variable(v) => assert_eq!(resolve(&compiler, v), "da"),
                    other => panic!("expected Variable(da) in prami_x1, got {:?}", other),
                }
                // prami_x2 should have Constant(mi)
                let x2_args = get_pred_args(&form, "prami_x2", &compiler).unwrap();
                match &x2_args[1] {
                    LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "mi"),
                    other => panic!("expected Constant(mi) in prami_x2, got {:?}", other),
                }
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_da_de_both_produce_nested_exists() {
        // da prami de → ∃da. ∃de. event_decomposed_prami(da, de, ...)
        let selbris = vec![Selbri::Root("prami".into())];
        let sumtis = vec![
            Sumti::ProSumti("da".into()), // 0
            Sumti::ProSumti("de".into()), // 1
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Should be Exists(da/de, Exists(da/de, Exists(ev, ...)))
        match &form {
            LogicalForm::Exists(v1, inner) => {
                let name1 = resolve(&compiler, v1);
                match inner.as_ref() {
                    LogicalForm::Exists(v2, _body) => {
                        let name2 = resolve(&compiler, v2);
                        // Both da and de should appear (order may vary)
                        let mut names = vec![name1, name2];
                        names.sort();
                        assert_eq!(names, vec!["da", "de"]);
                        // The body is now an event-decomposed form (Exists wrapping event)
                        assert!(
                            has_pred(&form, "prami", &compiler),
                            "expected prami type predicate"
                        );
                    }
                    other => panic!("expected nested Exists, got {:?}", other),
                }
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_da_repeated_wraps_once() {
        // da prami da → ∃da. event_decomposed_prami(da, da, ...) (only one entity Exists)
        let selbris = vec![Selbri::Root("prami".into())];
        let sumtis = vec![
            Sumti::ProSumti("da".into()), // 0
            Sumti::ProSumti("da".into()), // 1 (same variable)
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Should be Exists(da, Exists(ev, ...)) — NOT Exists(da, Exists(da, ...))
        match &form {
            LogicalForm::Exists(var, body) => {
                assert_eq!(resolve(&compiler, var), "da");
                // The body should be the event Exists, not another da Exists
                match body.as_ref() {
                    LogicalForm::Exists(ev_var, _) => {
                        // The inner Exists should be for an event variable, not da again
                        assert!(
                            resolve(&compiler, ev_var).starts_with("_ev"),
                            "expected event variable inside, got: {}",
                            resolve(&compiler, ev_var)
                        );
                    }
                    other => panic!(
                        "expected Exists(ev, ...) inside Exists(da, ...), got {:?}",
                        other
                    ),
                }
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_di_produces_exists() {
        // di barda → ∃di. barda(di, ...)
        let selbris = vec![Selbri::Root("barda".into())];
        let sumtis = vec![Sumti::ProSumti("di".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        match &form {
            LogicalForm::Exists(var, _) => {
                assert_eq!(resolve(&compiler, var), "di");
            }
            other => panic!("expected Exists for di, got {:?}", other),
        }
    }

    #[test]
    fn test_da_with_negation() {
        // da na prami mi → ¬(∃da. prami(da, mi, ...))
        // negation wraps OUTSIDE the existential
        let selbris = vec![Selbri::Root("prami".into())];
        let sumtis = vec![Sumti::ProSumti("da".into()), Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: true,
            tense: None,
            attitudinal: None,
        };

        let (form, _) = compile_one(selbris, sumtis, bridi);

        // Should be Not(Exists(da, Predicate))
        match &form {
            LogicalForm::Not(inner) => {
                assert!(
                    matches!(inner.as_ref(), LogicalForm::Exists(_, _)),
                    "expected Exists inside Not, got {:?}",
                    inner
                );
            }
            other => panic!("expected Not(Exists(...)), got {:?}", other),
        }
    }

    #[test]
    fn test_afterthought_jo_compiles_to_biconditional() {
        // .i jo → Biconditional IR node (expanded at flattening)
        let conn = SentenceConnective::Afterthought((false, Connective::Jo, false));
        let (form, _) = compile_connected(conn, "klama", "mi", "prami", "do");
        assert!(
            matches!(&form, LogicalForm::Biconditional(_, _)),
            "expected Biconditional, got {:?}",
            form
        );
    }

    // ─── ma question pro-sumti tests ─────────────────────────────

    #[test]
    fn test_ma_produces_exists() {
        // ma klama → ∃_v0. event_decomposed_klama(_v0, ...)
        // Each `ma` gets a fresh variable (independent query unknowns).
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("ma".into()), // 0
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Outermost should be Exists wrapping the event form
        match &form {
            LogicalForm::Exists(var, _body) => {
                // ma now generates a fresh variable (_v0), not "ma"
                assert!(resolve(&compiler, var).starts_with("_v"));
                // klama type pred should exist inside
                assert!(
                    has_pred(&form, "klama", &compiler),
                    "expected klama type predicate"
                );
                // klama_x1 should reference the ma variable
                let x1_args = get_pred_args(&form, "klama_x1", &compiler).unwrap();
                match &x1_args[1] {
                    LogicalTerm::Variable(v) => assert_eq!(v, var),
                    other => panic!("expected Variable in klama_x1, got {:?}", other),
                }
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_two_ma_produce_independent_exists() {
        // ma nelci ma → ∃_v1. ∃_v0. event_decomposed_nelci(_v0, _v1, ...)
        // Two `ma` tokens must produce two *different* variables,
        // each wrapped in its own ∃.
        let selbris = vec![Selbri::Root("nelci".into())];
        let sumtis = vec![
            Sumti::ProSumti("ma".into()), // 0
            Sumti::ProSumti("ma".into()), // 1
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Should be ∃v1.(∃v0.(Exists(ev, nelci_event(v0, v1, ...))))
        match &form {
            LogicalForm::Exists(var1, inner) => {
                assert!(resolve(&compiler, var1).starts_with("_v"));
                match inner.as_ref() {
                    LogicalForm::Exists(var0, _body) => {
                        assert!(resolve(&compiler, var0).starts_with("_v"));
                        // The two variables must be different
                        assert_ne!(var0, var1, "two ma should produce different variables");
                        // Check that nelci_x1 and nelci_x2 reference different variables
                        let x1_args = get_pred_args(&form, "nelci_x1", &compiler).unwrap();
                        let x2_args = get_pred_args(&form, "nelci_x2", &compiler).unwrap();
                        match (&x1_args[1], &x2_args[1]) {
                            (LogicalTerm::Variable(a), LogicalTerm::Variable(b)) => {
                                assert_ne!(a, b, "args should reference different vars");
                            }
                            other => {
                                panic!("expected two Variables in role preds, got {:?}", other)
                            }
                        }
                    }
                    other => panic!("expected inner Exists, got {:?}", other),
                }
            }
            other => panic!("expected outer Exists, got {:?}", other),
        }
    }

    // ─── Quantifier-closure scoping: ma_vars frame isolation + da/de/di in
    //     BAI modals / be-bei args get existential closure ───────────────

    #[test]
    fn test_ma_in_rel_clause_not_stolen() {
        // `ma prami lo gerku poi ke'a barda` — the outer `ma` (prami x1) must be
        // existentially closed at the OUTER matrix, not stolen by the nested
        // rel-clause compile_bridi's drain. Pre-fix the nested drain emptied the
        // shared `ma_vars`, leaving the outer ma var FREE.
        let selbris = vec![
            Selbri::Root("prami".into()), // 0
            Selbri::Root("gerku".into()), // 1
            Selbri::Root("barda".into()), // 2
        ];
        let sumtis = vec![
            Sumti::ProSumti("ma".into()),       // 0: ma
            Sumti::Description((Gadri::Lo, 1)), // 1: lo gerku
            Sumti::Restricted((
                1,
                RelClause {
                    kind: RelClauseKind::Poi,
                    body_sentence: 1,
                },
            )), // 2: lo gerku poi ke'a barda
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![0],
                tail_terms: vec![2],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 2, // barda (rel-clause body; implicit ke'a fills x1)
                head_terms: vec![],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        let (form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert!(
            free_vars(&form, &compiler).is_empty(),
            "the outer `ma` must be bound (not stolen by the rel clause): free={:?}",
            free_vars(&form, &compiler)
        );
    }

    // ─── noi (non-restrictive) vs poi (restrictive) relative clauses ────

    /// Compile `ro lo gerku [kind] barda cu klama` (universal). The rel-clause
    /// body (sentence 1) is `barda` with implicit ke'a filling its x1.
    fn compile_ro_lo_gerku_rel_barda_klama(kind: RelClauseKind) -> (LogicalForm, SemanticCompiler) {
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("barda".into()), // 1
            Selbri::Root("klama".into()), // 2
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::RoLo, 0)), // 0: ro lo gerku
            Sumti::Restricted((
                0,
                RelClause {
                    kind,
                    body_sentence: 1,
                },
            )), // 1: ro lo gerku [kind] barda
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 2,
                head_terms: vec![1],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 1, // barda (rel-clause body; implicit ke'a fills x1)
                head_terms: vec![],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        compile_sentence_full(selbris, sumtis, sentences)
    }

    /// Split a `ForAll(_, Or(antecedent, consequent))` into (antecedent, consequent).
    fn forall_or_split(form: &LogicalForm) -> (&LogicalForm, &LogicalForm) {
        match form {
            LogicalForm::ForAll(_, body) => match body.as_ref() {
                LogicalForm::Or(l, r) => (l.as_ref(), r.as_ref()),
                other => panic!("expected Or under ForAll, got {:?}", other),
            },
            other => panic!("expected ForAll root, got {:?}", other),
        }
    }

    #[test]
    fn noi_restrictor_is_in_universal_consequent_not_antecedent() {
        // `ro lo gerku noi barda cu klama`: noi is NON-restrictive, so `barda`
        // must land in the rule's CONSEQUENT (matrix), not its antecedent
        // (domain guard). RED pre-fix (noi was folded into the antecedent).
        let (form, compiler) = compile_ro_lo_gerku_rel_barda_klama(RelClauseKind::Noi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        let (ante, cons) = forall_or_split(&form);
        assert!(
            has_pred(cons, "barda", &compiler),
            "noi: barda must be in the consequent (matrix)"
        );
        assert!(
            !has_pred(ante, "barda", &compiler),
            "noi: barda must NOT be in the antecedent (domain restrictor)"
        );
    }

    #[test]
    fn poi_restrictor_stays_in_universal_antecedent() {
        // Guard: poi is RESTRICTIVE, so `barda` stays in the antecedent. Green
        // before AND after — pins that the noi fix does not leak into poi.
        let (form, compiler) = compile_ro_lo_gerku_rel_barda_klama(RelClauseKind::Poi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        let (ante, cons) = forall_or_split(&form);
        assert!(
            has_pred(ante, "barda", &compiler),
            "poi: barda must be in the antecedent (domain restrictor)"
        );
        assert!(
            !has_pred(cons, "barda", &compiler),
            "poi: barda must NOT be in the consequent"
        );
    }

    #[test]
    fn noi_under_exact_count_is_restrictive_documented_residual() {
        // DOCUMENTED RESIDUAL: under an exact-count quantifier, noi is folded into
        // the counted body (== restrictive), because the principled non-restrictive
        // form `Count(…) ∧ ∀x.(desc→noi)` would need close_quantifier to emit two
        // conjuncts. Pin the current behavior so the limitation stays discoverable.
        // `ci lo gerku noi barda cu klama` → Count{3, body} with barda IN the body.
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("barda".into()), // 1
            Selbri::Root("klama".into()), // 2
        ];
        let sumtis = vec![
            Sumti::QuantifiedDescription((3, Gadri::Lo, 0)), // 0: ci lo gerku
            Sumti::Restricted((
                0,
                RelClause {
                    kind: RelClauseKind::Noi,
                    body_sentence: 1,
                },
            )), // 1: ci lo gerku noi barda
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 2,
                head_terms: vec![1],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 1,
                head_terms: vec![],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        let (form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        match &form {
            LogicalForm::Count { count, body, .. } => {
                assert_eq!(*count, 3);
                assert!(
                    has_pred(body, "barda", &compiler),
                    "documented residual: noi under exact-count is folded into the counted body"
                );
            }
            other => panic!("expected Count root, got {:?}", other),
        }
    }

    #[test]
    fn test_da_in_bai_modal_closed() {
        // `mi klama ri'a da` — the `da` inside the BAI modal must be
        // existentially closed. Pre-fix the args-scan never saw the modal arg.
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                          // 0
            Sumti::ProSumti("da".into()),                          // 1
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Ria), 1)), // 2: ri'a da
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![2],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert!(
            free_vars(&form, &compiler).is_empty(),
            "the modal `da` must be bound: free={:?}",
            free_vars(&form, &compiler)
        );
        assert!(
            count_exists_binding(&form, "da", &compiler) >= 1,
            "an Exists must bind `da`"
        );
    }

    #[test]
    fn test_da_in_be_arg_closed() {
        // `mi klama be da` — the `da` in the be-arg must be existentially closed.
        let selbris = vec![
            Selbri::Root("klama".into()),   // 0
            Selbri::WithArgs((0, vec![1])), // 1: klama be da
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()), // 0
            Sumti::ProSumti("da".into()), // 1 (be-arg)
        ];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert!(
            free_vars(&form, &compiler).is_empty(),
            "the be-arg `da` must be bound: free={:?}",
            free_vars(&form, &compiler)
        );
    }

    #[test]
    fn test_da_in_modal_under_universal_stays_inside_forall() {
        // `ro lo gerku cu klama ri'a da` — the modal `da` is closed by an Exists
        // UNDER the ForAll (∀g.∃d), keeping ForAll at the root (logji rule shape).
        let selbris = vec![
            Selbri::Root("klama".into()), // 0
            Selbri::Root("gerku".into()), // 1
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::RoLo, 1)), // 0: ro lo gerku
            Sumti::ProSumti("da".into()),         // 1
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Ria), 1)), // 2: ri'a da
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![2],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert!(
            matches!(form, LogicalForm::ForAll(_, _)),
            "root must stay ForAll (logji rule shape), got {:?}",
            form
        );
        assert!(
            free_vars(&form, &compiler).is_empty(),
            "the modal `da` must be bound under the ForAll: free={:?}",
            free_vars(&form, &compiler)
        );
        assert!(
            count_exists_binding(&form, "da", &compiler) >= 1,
            "an Exists must bind `da` inside the ForAll"
        );
    }

    #[test]
    fn test_prenex_da_in_modal_not_reclosed() {
        // `ro da zo'u mi klama ri'a da` — `da` is universally bound by the prenex;
        // the modal `da` must NOT be existentially re-closed (negative control for
        // the preserved prenex exclusion).
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                          // 0
            Sumti::ProSumti("da".into()),                          // 1
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Ria), 1)), // 2: ri'a da
        ];
        let sentences = vec![
            Sentence::Prenex((vec!["da".into()], 1)),
            Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![0],
                tail_terms: vec![2],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        let (form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert!(
            free_vars(&form, &compiler).is_empty(),
            "prenex `da` must be bound by the ForAll: free={:?}",
            free_vars(&form, &compiler)
        );
        assert_eq!(
            count_exists_binding(&form, "da", &compiler),
            0,
            "prenex `da` must NOT be existentially re-closed"
        );
    }

    #[test]
    fn test_abstraction_da_not_double_wrapped() {
        // `mi djuno lo nu da broda` — the abstraction body closes its own `da`;
        // the outer existential walk must NOT re-wrap it (binder tracking).
        let selbris = vec![
            Selbri::Root("djuno".into()),                  // 0
            Selbri::Abstraction((AbstractionKind::Nu, 1)), // 1 → sentences[1]
            Selbri::Root("broda".into()),                  // 2
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),       // 0
            Sumti::Description((Gadri::Lo, 1)), // 1: lo nu ...
            Sumti::ProSumti("da".into()),       // 2 (broda body x1)
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![0],
                tail_terms: vec![1],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 2, // broda
                head_terms: vec![2],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        let (form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert_eq!(
            count_exists_binding(&form, "da", &compiler),
            1,
            "`da` must be wrapped exactly once (no double-wrap)"
        );
        assert!(
            free_vars(&form, &compiler).is_empty(),
            "free={:?}",
            free_vars(&form, &compiler)
        );
    }

    // ─── position-aware da/de/di quantifier scope ────────────────

    #[test]
    fn test_da_before_universal_outscopes_it() {
        // `da citka ro lo gerku` ("something eats every dog") — the leading bare
        // var is textually BEFORE the universal, so it OUTSCOPES it: ∃da.∀x.
        // RED before the fix (da was forced inside the universal → ∀x.∃da).
        let selbris = vec![
            Selbri::Root("citka".into()), // 0
            Selbri::Root("gerku".into()), // 1
        ];
        let sumtis = vec![
            Sumti::ProSumti("da".into()),         // 0: da (x1)
            Sumti::Description((Gadri::RoLo, 1)), // 1: ro lo gerku (x2)
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert_eq!(
            binder_spine(&form, &compiler),
            vec![Binder::Exists("da".into()), Binder::ForAll],
            "leading `da` must outscope the universal (∃da.∀x): got {:?}",
            binder_spine(&form, &compiler)
        );
        assert!(
            exists_outscopes_forall(&form, "da", &compiler),
            "`da` existential must dominate the universal"
        );
        assert!(free_vars(&form, &compiler).is_empty());
    }

    #[test]
    fn test_da_after_universal_is_inside_it() {
        // `ro lo gerku cu citka da` ("every dog eats something") — the bare var is
        // textually AFTER the universal, so it stays INSIDE: ∀x.∃da. Contrasts
        // with the before-case; the pair proves surface order now matters (the two
        // were identical before the fix).
        let selbris = vec![
            Selbri::Root("citka".into()), // 0
            Selbri::Root("gerku".into()), // 1
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::RoLo, 1)), // 0: ro lo gerku (x1)
            Sumti::ProSumti("da".into()),         // 1: da (x2)
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert_eq!(
            binder_spine(&form, &compiler).first(),
            Some(&Binder::ForAll),
            "trailing `da` must stay under the universal (∀x.∃da)"
        );
        assert!(
            !exists_outscopes_forall(&form, "da", &compiler),
            "`da` must NOT outscope the universal in the after-case"
        );
        assert!(count_exists_binding(&form, "da", &compiler) >= 1);
        assert!(free_vars(&form, &compiler).is_empty());
    }

    #[test]
    fn test_da_interleaved_between_count_and_universal() {
        // `re lo gerku cu klama da ro lo mlatu` — a bare var between an
        // exact-count description (x1) and a universal (x3). The uniform fold
        // nests them Count > ∃da > ∀ by surface order.
        let selbris = vec![
            Selbri::Root("klama".into()), // 0
            Selbri::Root("gerku".into()), // 1
            Selbri::Root("mlatu".into()), // 2
        ];
        let sumtis = vec![
            Sumti::QuantifiedDescription((2, Gadri::Lo, 1)), // 0: re lo gerku (x1)
            Sumti::ProSumti("da".into()),                    // 1: da (x2)
            Sumti::Description((Gadri::RoLo, 2)),            // 2: ro lo mlatu (x3)
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1, 2],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert_eq!(
            binder_spine(&form, &compiler).first(),
            Some(&Binder::Count(2)),
            "root must be the exact-count quantifier: got {:?}",
            binder_spine(&form, &compiler)
        );
        assert!(
            exists_outscopes_forall(&form, "da", &compiler),
            "`da` (x2) must outscope the universal (x3) it precedes"
        );
        assert_eq!(count_exists_binding(&form, "da", &compiler), 1);
        assert!(free_vars(&form, &compiler).is_empty());
    }

    #[test]
    fn test_be_arg_da_with_universal_stays_innermost() {
        // `ro lo gerku cu klama be da` — the be-arg `da` has no surface position
        // (merged inside apply_selbri), so the safety net closes it INNERMOST,
        // under the universal. The deferred-position default: bound, not free,
        // not double-wrapped.
        let selbris = vec![
            Selbri::Root("klama".into()),   // 0
            Selbri::WithArgs((0, vec![1])), // 1: klama be da
            Selbri::Root("gerku".into()),   // 2
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::RoLo, 2)), // 0: ro lo gerku (x1)
            Sumti::ProSumti("da".into()),         // 1: da (be-arg)
        ];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert_eq!(
            binder_spine(&form, &compiler).first(),
            Some(&Binder::ForAll),
            "root must stay ForAll (logji rule shape)"
        );
        assert!(
            !exists_outscopes_forall(&form, "da", &compiler),
            "a be-arg `da` is closed innermost, under the universal"
        );
        assert_eq!(count_exists_binding(&form, "da", &compiler), 1);
        assert!(free_vars(&form, &compiler).is_empty());
    }

    #[test]
    fn test_restrictor_internal_da_closed_innermost() {
        // `ro lo gerku poi prami fe da cu klama` ("every dog that loves something
        // goes") — the `da` inside the poi-restrictor (x2, via `fe`, leaving x1 for
        // the implicit ke'a) has no bridi-level surface index, so it is bound
        // INSIDE the restrictor's own frame. A DELIBERATE sound default: surface
        // order cannot change a restrictor that defines the quantifier's domain.
        // Characterization lock — `da` is bound (never free) and the root stays a
        // universal.
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("prami".into()), // 1
            Selbri::Root("klama".into()), // 2
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::RoLo, 0)), // 0: ro lo gerku
            Sumti::Restricted((
                0,
                RelClause {
                    kind: RelClauseKind::Poi,
                    body_sentence: 1,
                },
            )), // 1: ro lo gerku poi <body>
            Sumti::ProSumti("da".into()),         // 2: da
            Sumti::Tagged((PlaceTag::Fe, 2)),     // 3: fe da (x2 of the poi body)
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 2, // klama
                head_terms: vec![1],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 1, // prami (rel-clause body: `prami fe da`; ke'a fills x1)
                head_terms: vec![],
                tail_terms: vec![3],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        let (form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert!(
            free_vars(&form, &compiler).is_empty(),
            "the restrictor-internal `da` must be bound: free={:?}",
            free_vars(&form, &compiler)
        );
        assert_eq!(
            binder_spine(&form, &compiler).first(),
            Some(&Binder::ForAll),
            "root must stay ForAll (the `da` is closed inside the restrictor)"
        );
        assert_eq!(count_exists_binding(&form, "da", &compiler), 1);
    }

    #[test]
    fn test_prenex_da_top_level_not_reclosed() {
        // `ro da zo'u da citka lo gerku` — `da` is universally bound by the
        // prenex; the new surface-marker hook must respect `prenex_vars` and NOT
        // record a Bare marker for the top-level `da` arg (no existential re-wrap).
        let selbris = vec![
            Selbri::Root("citka".into()), // 0
            Selbri::Root("gerku".into()), // 1
        ];
        let sumtis = vec![
            Sumti::ProSumti("da".into()),       // 0: da (x1)
            Sumti::Description((Gadri::Lo, 1)), // 1: lo gerku (x2)
        ];
        let sentences = vec![
            Sentence::Prenex((vec!["da".into()], 1)),
            Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![0],
                tail_terms: vec![1],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        let (form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert_eq!(
            count_exists_binding(&form, "da", &compiler),
            0,
            "prenex `da` must NOT be existentially re-closed"
        );
        assert_eq!(
            binder_spine(&form, &compiler).first(),
            Some(&Binder::ForAll),
            "prenex `da` is the outermost ∀"
        );
        assert!(free_vars(&form, &compiler).is_empty());
    }

    #[test]
    fn test_da_repeated_dedups_to_one_exists() {
        // `da citka da` — the same bare var in two places co-refers and is
        // wrapped by exactly one Exists (the surface hook's `introduced` dedup +
        // the safety-net subtraction).
        let selbris = vec![Selbri::Root("citka".into())];
        let sumtis = vec![
            Sumti::ProSumti("da".into()), // 0: da (x1)
            Sumti::ProSumti("da".into()), // 1: da (x2)
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert_eq!(
            count_exists_binding(&form, "da", &compiler),
            1,
            "co-referring `da` must wrap exactly once"
        );
        assert!(free_vars(&form, &compiler).is_empty());
    }

    #[test]
    fn test_be_arg_and_modal_da_de_both_closed() {
        // `mi klama be da ri'a de` — both the be-arg `da` and the modal `de` must
        // be existentially closed, each exactly once.
        let selbris = vec![
            Selbri::Root("klama".into()),   // 0
            Selbri::WithArgs((0, vec![1])), // 1: klama be da
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                          // 0
            Sumti::ProSumti("da".into()),                          // 1 (be-arg)
            Sumti::ProSumti("de".into()),                          // 2
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Ria), 2)), // 3: ri'a de
        ];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![3],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert!(
            free_vars(&form, &compiler).is_empty(),
            "both da and de must be bound: free={:?}",
            free_vars(&form, &compiler)
        );
        assert_eq!(count_exists_binding(&form, "da", &compiler), 1, "da once");
        assert_eq!(count_exists_binding(&form, "de", &compiler), 1, "de once");
    }

    #[test]
    fn test_du_with_da_closed() {
        // `da du mi` — flat du(da, mi); the `da` must be existentially closed
        // (the flat-du shape must not hide the logic var from the walk).
        let selbris = vec![Selbri::Root("du".into())];
        let sumtis = vec![
            Sumti::ProSumti("da".into()), // 0
            Sumti::ProSumti("mi".into()), // 1
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(compiler.errors.is_empty(), "errors: {:?}", compiler.errors);
        assert!(
            free_vars(&form, &compiler).is_empty(),
            "the du `da` must be bound: free={:?}",
            free_vars(&form, &compiler)
        );
        assert_eq!(count_exists_binding(&form, "da", &compiler), 1, "da once");
    }

    // ─── inject_variable ambiguity tests ────────────────────────

    /// Helper: compile a full sentence (not just bridi) to test rel clause handling.
    fn compile_sentence_full(
        selbris: Vec<Selbri>,
        sumtis: Vec<Sumti>,
        sentences: Vec<Sentence>,
    ) -> (LogicalForm, SemanticCompiler) {
        let mut compiler = SemanticCompiler::new();
        let form = compiler.compile_sentence(0, &selbris, &sumtis, &sentences);
        (form, compiler)
    }

    #[test]
    fn test_inject_variable_single_predicate_no_error() {
        // lo gerku poi barda cu klama
        // Rel clause body "barda" has only 1 predicate with unspecified slot — no ambiguity.
        //
        // Buffer layout:
        //   selbris: [0: gerku, 1: barda, 2: klama]
        //   sumtis:  [0: Description(Lo, 0), 1: Restricted(0, poi body=1)]
        //   sentences: [0: Simple(klama, head=[1]), 1: Simple(barda, head=[])]
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("barda".into()), // 1
            Selbri::Root("klama".into()), // 2
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Lo, 0)), // 0: lo gerku
            Sumti::Restricted((
                0,
                RelClause {
                    kind: RelClauseKind::Poi,
                    body_sentence: 1,
                },
            )), // 1: lo gerku poi barda
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 2,
                head_terms: vec![1],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 1,
                head_terms: vec![],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];

        let (_form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        // No errors — single predicate is unambiguous
        assert!(
            compiler.errors.is_empty(),
            "Expected no errors, got: {:?}",
            compiler.errors
        );
    }

    #[test]
    fn test_nested_description_implicit_kea_rejected() {
        // lo gerku poi lo mlatu cu barda
        // The relative-clause body has NO unfilled subject (_x1) slot for the described
        // dog (the cat fills barda's x1), and ke'a is implicit. Per the firewall (book
        // Ch6), the engine REJECTS and demands explicit ke'a rather than guessing.
        //
        // Buffer layout:
        //   selbris: [0: gerku, 1: mlatu, 2: barda]
        //   sumtis:  [0: Description(Lo, 0), 1: Description(Lo, 1), 2: Restricted(0, poi body=1)]
        //   sentences: [0: Simple(barda, head=[2]), 1: Simple(barda, head=[1])]
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("mlatu".into()), // 1
            Selbri::Root("barda".into()), // 2
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Lo, 0)), // 0: lo gerku
            Sumti::Description((Gadri::Lo, 1)), // 1: lo mlatu
            Sumti::Restricted((
                0,
                RelClause {
                    kind: RelClauseKind::Poi,
                    body_sentence: 1,
                },
            )), // 2: lo gerku poi ...
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 2,         // barda (main sentence)
                head_terms: vec![2], // lo gerku poi ...
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 2,         // barda (rel clause body: lo mlatu cu barda)
                head_terms: vec![1], // lo mlatu
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];

        let (_form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        // Firewall: no unambiguous subject slot for the implicit ke'a → rejected.
        assert!(
            !compiler.errors.is_empty(),
            "Expected an ambiguity/ke'a error for an implicit-ke'a nested description"
        );
        assert!(
            compiler.errors.iter().any(|e| e.contains("ke'a")),
            "Error should direct the user to explicit ke'a, got: {:?}",
            compiler.errors
        );
    }

    #[test]
    fn test_inject_variable_with_explicit_kea_no_error() {
        // lo gerku poi ke'a barda cu klama
        // ke'a used explicitly — no injection needed, no error.
        //
        // Buffer layout:
        //   selbris: [0: gerku, 1: barda, 2: klama]
        //   sumtis:  [0: Description(Lo, 0), 1: ProSumti("ke'a"), 2: Restricted(0, poi body=1)]
        //   sentences: [0: Simple(klama, head=[2]), 1: Simple(barda, head=[1])]
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("barda".into()), // 1
            Selbri::Root("klama".into()), // 2
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Lo, 0)), // 0: lo gerku
            Sumti::ProSumti("ke'a".into()),     // 1: ke'a
            Sumti::Restricted((
                0,
                RelClause {
                    kind: RelClauseKind::Poi,
                    body_sentence: 1,
                },
            )), // 2: lo gerku poi ke'a barda
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 2,
                head_terms: vec![2],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 1,
                head_terms: vec![1], // ke'a as head term
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];

        let (_form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        // No errors — ke'a was used explicitly
        assert!(
            compiler.errors.is_empty(),
            "Expected no errors, got: {:?}",
            compiler.errors
        );
    }

    #[test]
    fn test_single_predicate_injects_head_into_subject() {
        // lo gerku poi barda cu klama
        // The relative-clause body `barda` has exactly one unfilled subject (_x1) slot,
        // so the described dog is injected there. Verify no error AND that the dog's
        // variable actually appears in barda_x1 (the same variable bound by gerku).
        //
        // Buffer layout:
        //   selbris: [0: gerku, 1: barda, 2: klama]
        //   sumtis:  [0: Description(Lo, 0), 1: Restricted(0, poi body=1)]
        //   sentences: [0: Simple(klama, head=[1]), 1: Simple(barda, head=[])]
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("barda".into()), // 1
            Selbri::Root("klama".into()), // 2
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Lo, 0)), // 0: lo gerku
            Sumti::Restricted((
                0,
                RelClause {
                    kind: RelClauseKind::Poi,
                    body_sentence: 1,
                },
            )), // 1: lo gerku poi barda
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 2,
                head_terms: vec![1],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 1,
                head_terms: vec![],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];

        let (form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(
            compiler.errors.is_empty(),
            "Expected no errors for a single-predicate clause, got: {:?}",
            compiler.errors
        );
        let barda_args = get_pred_args(&form, "barda_x1", &compiler)
            .expect("barda_x1 role predicate should be present");
        let gerku_args = get_pred_args(&form, "gerku_x1", &compiler)
            .expect("gerku_x1 role predicate should be present");
        // The implicit ke'a (dog) variable is injected into barda's subject slot, and it
        // must be the SAME variable bound by the gerku description.
        assert!(
            matches!(barda_args[1], LogicalTerm::Variable(_)),
            "dog variable should be injected into barda_x1, got {:?}",
            barda_args[1]
        );
        assert_eq!(
            barda_args[1], gerku_args[1],
            "barda_x1 must bind the same variable as gerku_x1 (the described dog)"
        );
    }

    #[test]
    fn test_nested_description_two_place_rejected() {
        // lo gerku poi lo mlatu cu batci  (book Ch6 canonical reject case)
        // batci is 2-place (x1 bites x2); the cat fills batci_x1, so the dog's place
        // would be the non-subject batci_x2. Implicit ke'a cannot safely target a
        // non-subject slot -> reject and demand explicit ke'a.
        //
        // Buffer layout:
        //   selbris: [0: gerku, 1: mlatu, 2: batci]
        //   sumtis:  [0: Description(Lo, 0), 1: Description(Lo, 1), 2: Restricted(0, poi body=1)]
        //   sentences: [0: Simple(batci, head=[2]), 1: Simple(batci, head=[1])]
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("mlatu".into()), // 1
            Selbri::Root("batci".into()), // 2
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Lo, 0)), // 0: lo gerku
            Sumti::Description((Gadri::Lo, 1)), // 1: lo mlatu
            Sumti::Restricted((
                0,
                RelClause {
                    kind: RelClauseKind::Poi,
                    body_sentence: 1,
                },
            )), // 2: lo gerku poi lo mlatu cu batci
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 2,
                head_terms: vec![2],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 2,
                head_terms: vec![1], // lo mlatu fills batci_x1; batci_x2 is the dog's place
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];

        let (_form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(
            !compiler.errors.is_empty(),
            "Expected a ke'a error: the dog's batci_x2 place cannot be filled implicitly"
        );
    }

    #[test]
    fn test_count_unspecified_predicates_single() {
        let mut compiler = SemanticCompiler::new();
        let rel = compiler.interner.get_or_intern("gerku");
        let form = LogicalForm::Predicate {
            relation: rel,
            args: vec![LogicalTerm::Unspecified],
        };
        assert_eq!(
            SemanticCompiler::count_unspecified_predicates(&form, &compiler.interner),
            1
        );
    }

    #[test]
    fn test_count_unspecified_predicates_none() {
        let mut compiler = SemanticCompiler::new();
        let rel = compiler.interner.get_or_intern("gerku");
        let var = compiler.interner.get_or_intern("x");
        let form = LogicalForm::Predicate {
            relation: rel,
            args: vec![LogicalTerm::Variable(var)],
        };
        assert_eq!(
            SemanticCompiler::count_unspecified_predicates(&form, &compiler.interner),
            0
        );
    }

    #[test]
    fn test_count_unspecified_predicates_conjunction() {
        let mut compiler = SemanticCompiler::new();
        let rel1 = compiler.interner.get_or_intern("gerku");
        let rel2 = compiler.interner.get_or_intern("mlatu");
        let form = LogicalForm::And(
            Box::new(LogicalForm::Predicate {
                relation: rel1,
                args: vec![LogicalTerm::Unspecified],
            }),
            Box::new(LogicalForm::Predicate {
                relation: rel2,
                args: vec![LogicalTerm::Unspecified],
            }),
        );
        assert_eq!(
            SemanticCompiler::count_unspecified_predicates(&form, &compiler.interner),
            2
        );
    }

    #[test]
    fn test_inject_variable_fills_first_unspecified() {
        let mut compiler = SemanticCompiler::new();
        let rel = compiler.interner.get_or_intern("gerku");
        let var = compiler.interner.get_or_intern("_v0");
        let form = LogicalForm::Predicate {
            relation: rel,
            args: vec![LogicalTerm::Unspecified, LogicalTerm::Unspecified],
        };
        let injected = SemanticCompiler::inject_variable(form, var, &compiler.interner);
        match injected {
            LogicalForm::Predicate { args, .. } => {
                assert!(matches!(args[0], LogicalTerm::Variable(_)));
                assert!(matches!(args[1], LogicalTerm::Unspecified));
            }
            other => panic!("expected Predicate, got {:?}", other),
        }
    }

    // ─── Panel-finding regressions (2026-06-10): meaning loss ────

    #[test]
    fn test_fa_tag_beyond_arity_errors() {
        // fu do gerku → `fu` targets x5 but gerku is 2-place: semantic error,
        // never a silent drop of `do`.
        let selbris = vec![Selbri::Root("gerku".into())];
        let sumtis = vec![
            Sumti::ProSumti("do".into()),     // 0
            Sumti::Tagged((PlaceTag::Fu, 0)), // 1: fu do
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![1],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (_form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            !compiler.errors.is_empty(),
            "over-arity FA tag must produce a semantic error"
        );
        assert!(
            compiler.errors.iter().any(|e| e.contains("fu")),
            "error should name the offending tag, got: {:?}",
            compiler.errors
        );
    }

    #[test]
    fn test_fa_tag_within_arity_no_error() {
        // fe do gerku → `fe` targets x2; gerku is 2-place: fine.
        let selbris = vec![Selbri::Root("gerku".into())];
        let sumtis = vec![
            Sumti::ProSumti("do".into()),     // 0
            Sumti::Tagged((PlaceTag::Fe, 0)), // 1: fe do
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![1],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            compiler.errors.is_empty(),
            "in-range FA tag must not error, got: {:?}",
            compiler.errors
        );
        let x2 = get_pred_args(&form, "gerku_x2", &compiler).unwrap();
        let do_term = LogicalTerm::Constant(compiler.interner.get("do").unwrap());
        assert_eq!(x2[1], do_term, "fe must place `do` into gerku_x2");
    }

    #[test]
    fn test_untagged_overflow_known_arity_errors() {
        // `gerku mi do ti` — gerku is a KNOWN 2-place gismu, so the 3rd untagged
        // sumti (`ti`) overflows with no slot: fail closed instead of silently
        // dropping it.
        let selbris = vec![Selbri::Root("gerku".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()), // 0
            Sumti::ProSumti("do".into()), // 1
            Sumti::ProSumti("ti".into()), // 2
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1, 2],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (_form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            !compiler.errors.is_empty(),
            "untagged sumti over a known arity must error"
        );
        assert!(
            compiler.errors.iter().any(|e| e.contains("overflow")),
            "error should mention the overflow, got: {:?}",
            compiler.errors
        );
    }

    #[test]
    fn test_untagged_overflow_unknown_arity_no_error() {
        // An UNKNOWN selbri defaults to arity 2, but its real arity may be higher,
        // so an untagged overflow is NOT an error there (matches today's behavior —
        // the no-XML build defaults many proxy words to 2).
        let selbris = vec![Selbri::Root("zzzzz".into())];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()), // 0
            Sumti::ProSumti("do".into()), // 1
            Sumti::ProSumti("ti".into()), // 2
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![1, 2],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (_form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            compiler.errors.is_empty(),
            "unknown-arity overflow must not error, got: {:?}",
            compiler.errors
        );
    }

    #[test]
    fn test_tag_collision_errors() {
        // `fe do fe ti gerku` — both `fe` tags target x2: a place set twice must
        // error, not silently last-wins (dropping `do`).
        let selbris = vec![Selbri::Root("gerku".into())];
        let sumtis = vec![
            Sumti::ProSumti("do".into()),     // 0
            Sumti::ProSumti("ti".into()),     // 1
            Sumti::Tagged((PlaceTag::Fe, 0)), // 2: fe do
            Sumti::Tagged((PlaceTag::Fe, 1)), // 3: fe ti
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![2, 3],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (_form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            !compiler.errors.is_empty(),
            "a tag re-targeting a filled place must error"
        );
        assert!(
            compiler.errors.iter().any(|e| e.contains("already filled")),
            "error should mention the collision, got: {:?}",
            compiler.errors
        );
    }

    #[test]
    fn test_connected_in_be_arg_errors() {
        // `mi klama be lo gerku .e lo mlatu` — the be-arg is a connected sumti,
        // a position the distributor does not descend into. It must fail closed,
        // not silently keep only the left operand (`lo gerku`).
        let selbris = vec![
            Selbri::Root("klama".into()),   // 0
            Selbri::Root("gerku".into()),   // 1
            Selbri::Root("mlatu".into()),   // 2
            Selbri::WithArgs((0, vec![2])), // 3: klama be <be-arg id 2>
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Lo, 1)),              // 0: lo gerku
            Sumti::Description((Gadri::Lo, 2)),              // 1: lo mlatu
            Sumti::Connected((0, Connective::Je, false, 1)), // 2: lo gerku .e lo mlatu
            Sumti::ProSumti("mi".into()),                    // 3: mi
        ];
        let bridi = Bridi {
            relation: 3,
            head_terms: vec![3],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (_form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            !compiler.errors.is_empty(),
            "a connected sumti in a be-arg must error"
        );
        assert!(
            compiler
                .errors
                .iter()
                .any(|e| e.contains("Connected sumti")),
            "error should name the connected-sumti limitation, got: {:?}",
            compiler.errors
        );
    }

    #[test]
    fn test_tanru_in_poi_not_falsely_rejected() {
        // lo gerku poi sutra bajra cu klama — the tanru `sutra bajra` shares
        // ONE event, so its two unfilled x1 roles are one candidate subject
        // slot; the firewall must not reject, and injection must fill BOTH x1
        // roles with the dog's variable.
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("sutra".into()), // 1
            Selbri::Root("bajra".into()), // 2
            Selbri::Tanru((1, 2)),        // 3: sutra bajra
            Selbri::Root("klama".into()), // 4
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Lo, 0)), // 0: lo gerku
            Sumti::Restricted((
                0,
                RelClause {
                    kind: RelClauseKind::Poi,
                    body_sentence: 1,
                },
            )), // 1: lo gerku poi sutra bajra
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 4,
                head_terms: vec![1],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 3,
                head_terms: vec![],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        let (form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(
            compiler.errors.is_empty(),
            "valid tanru-in-poi clause must not be rejected, got: {:?}",
            compiler.errors
        );
        let bajra_x1 = get_pred_args(&form, "bajra_x1", &compiler).unwrap();
        let sutra_x1 = get_pred_args(&form, "sutra_x1", &compiler).unwrap();
        let gerku_x1 = get_pred_args(&form, "gerku_x1", &compiler).unwrap();
        assert_eq!(
            bajra_x1[1], gerku_x1[1],
            "tanru head x1 must bind the dog variable"
        );
        assert_eq!(
            sutra_x1[1], gerku_x1[1],
            "tanru modifier x1 must bind the dog variable"
        );
        assert_eq!(
            bajra_x1[0], sutra_x1[0],
            "tanru must keep the shared event variable"
        );
    }

    #[test]
    fn test_rel_clause_on_name_conjoined_not_dropped() {
        // la .adam. poi gerku cu klama → And(klama(adam...), gerku(adam...)):
        // the clause on a name (no quantifier) must be conjoined into the
        // matrix, not compiled-then-dropped. An assertion asserts both
        // conjuncts; a query requires both.
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("klama".into()), // 1
        ];
        let sumtis = vec![
            Sumti::Name("adam".into()), // 0
            Sumti::Restricted((
                0,
                RelClause {
                    kind: RelClauseKind::Poi,
                    body_sentence: 1,
                },
            )), // 1: la .adam. poi gerku
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 1,
                head_terms: vec![1],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        let (form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(
            compiler.errors.is_empty(),
            "single-subject-slot clause on a name must compile cleanly, got: {:?}",
            compiler.errors
        );
        let adam = LogicalTerm::Constant(compiler.interner.get("adam").unwrap());
        let klama_x1 =
            get_pred_args(&form, "klama_x1", &compiler).expect("matrix klama must be present");
        assert_eq!(klama_x1[1], adam);
        let gerku_x1 = get_pred_args(&form, "gerku_x1", &compiler)
            .expect("the poi clause's gerku must be conjoined, not dropped");
        assert_eq!(
            gerku_x1[1], adam,
            "the name must be substituted into the clause's subject slot"
        );
    }

    #[test]
    fn test_rel_clause_on_name_firewall_still_applies() {
        // la .adam. poi lo mlatu cu batci → the clause has NO unfilled subject
        // slot for Adam (the cat fills batci_x1): ambiguous implicit ke'a must
        // be rejected on names too, exactly like on lo descriptions.
        let selbris = vec![
            Selbri::Root("mlatu".into()), // 0
            Selbri::Root("batci".into()), // 1
        ];
        let sumtis = vec![
            Sumti::Name("adam".into()),         // 0
            Sumti::Description((Gadri::Lo, 0)), // 1: lo mlatu
            Sumti::Restricted((
                0,
                RelClause {
                    kind: RelClauseKind::Poi,
                    body_sentence: 1,
                },
            )), // 2: la .adam. poi lo mlatu cu batci
        ];
        let sentences = vec![
            Sentence::Simple(Bridi {
                relation: 1,
                head_terms: vec![2],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 1,
                head_terms: vec![1], // lo mlatu fills batci_x1
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        let (_form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(
            !compiler.errors.is_empty(),
            "ambiguous implicit-ke'a clause on a name must be rejected"
        );
        assert!(
            compiler.errors.iter().any(|e| e.contains("ke'a")),
            "error should direct the user to explicit ke'a, got: {:?}",
            compiler.errors
        );
    }

    #[test]
    fn test_da_after_universal_closes_inside_forall() {
        // ro lo gerku cu citka da → ∀x.(gerku(x) → ∃da. citka(x, da)):
        // left-to-right Lojban scope puts the bare-var existential INSIDE the
        // universal. The old Exists-over-ForAll root dead-ended logji's rule
        // dispatch and silently lost the whole assertion.
        fn exists_da_somewhere(f: &LogicalForm, c: &SemanticCompiler) -> bool {
            match f {
                LogicalForm::Exists(v, inner) => {
                    c.interner.resolve(v) == "da" || exists_da_somewhere(inner, c)
                }
                LogicalForm::And(l, r)
                | LogicalForm::Or(l, r)
                | LogicalForm::Biconditional(l, r)
                | LogicalForm::Xor(l, r) => exists_da_somewhere(l, c) || exists_da_somewhere(r, c),
                LogicalForm::Not(i)
                | LogicalForm::ForAll(_, i)
                | LogicalForm::Past(i)
                | LogicalForm::Present(i)
                | LogicalForm::Future(i)
                | LogicalForm::Obligatory(i)
                | LogicalForm::Permitted(i) => exists_da_somewhere(i, c),
                LogicalForm::Count { body, .. } => exists_da_somewhere(body, c),
                LogicalForm::Predicate { .. } => false,
            }
        }

        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("citka".into()), // 1
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::RoLo, 0)), // 0: ro lo gerku
            Sumti::ProSumti("da".into()),         // 1: da
        ];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        match &form {
            LogicalForm::ForAll(_, body) => {
                assert!(
                    exists_da_somewhere(body, &compiler),
                    "∃da must be nested inside the ∀ body, got: {:?}",
                    form
                );
            }
            other => panic!(
                "root must stay ForAll (logji's rule shape), got {:?}",
                other
            ),
        }
    }

    // ─── Tense wrapper tests ──────────────────────────────────

    #[test]
    fn test_tense_pu_produces_past() {
        // pu mi klama → Past(klama(mi, ...))
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: Some(Tense::Pu),
            attitudinal: None,
        };
        let (form, _) = compile_one(selbris, sumtis, bridi);
        assert!(matches!(form, LogicalForm::Past(_)));
    }

    #[test]
    fn test_tense_ca_produces_present() {
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: Some(Tense::Ca),
            attitudinal: None,
        };
        let (form, _) = compile_one(selbris, sumtis, bridi);
        assert!(matches!(form, LogicalForm::Present(_)));
    }

    #[test]
    fn test_tense_ba_produces_future() {
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: Some(Tense::Ba),
            attitudinal: None,
        };
        let (form, _) = compile_one(selbris, sumtis, bridi);
        assert!(matches!(form, LogicalForm::Future(_)));
    }

    // ─── Attitudinal tests ────────────────────────────────────

    #[test]
    fn test_attitudinal_ei_produces_obligatory() {
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: Some(Attitudinal::Ei),
        };
        let (form, _) = compile_one(selbris, sumtis, bridi);
        assert!(matches!(form, LogicalForm::Obligatory(_)));
    }

    #[test]
    fn test_attitudinal_ehe_produces_permitted() {
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: Some(Attitudinal::Ehe),
        };
        let (form, _) = compile_one(selbris, sumtis, bridi);
        assert!(matches!(form, LogicalForm::Permitted(_)));
    }

    // ─── Negation test ────────────────────────────────────────

    #[test]
    fn test_bridi_negation_produces_not() {
        // na mi klama → Not(klama(mi, ...))
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: true,
            tense: None,
            attitudinal: None,
        };
        let (form, _) = compile_one(selbris, sumtis, bridi);
        assert!(matches!(form, LogicalForm::Not(_)));
    }

    // ─── Conversion SE tests ──────────────────────────────────

    #[test]
    fn test_se_conversion_swaps_args() {
        // se prami mi do → prami(do, mi, ...) (x1↔x2 swapped)
        let selbris = vec![
            Selbri::Root("prami".into()),
            Selbri::Converted((Conversion::Se, 0)),
        ];
        let sumtis = vec![Sumti::ProSumti("mi".into()), Sumti::ProSumti("do".into())];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        // With event decomposition, form is Exists(ev, And(prami(ev), prami_x1(ev, ...), prami_x2(ev, ...)))
        // After se-conversion: x1 and x2 are swapped
        // head=mi goes to x1 position, tail=do goes to x2 position
        // se swaps these: mi→x2, do→x1
        assert!(
            matches!(&form, LogicalForm::Exists(_, _)),
            "expected Exists, got {:?}",
            form
        );
        assert!(
            has_pred(&form, "prami", &compiler),
            "expected prami type predicate"
        );
        // Check prami_x1 has do (originally x2, swapped to x1)
        let x1_args = get_pred_args(&form, "prami_x1", &compiler).unwrap();
        match &x1_args[1] {
            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "do"),
            other => panic!(
                "expected Constant(do) in prami_x1 after se-swap, got {:?}",
                other
            ),
        }
        // Check prami_x2 has mi (originally x1, swapped to x2)
        let x2_args = get_pred_args(&form, "prami_x2", &compiler).unwrap();
        match &x2_args[1] {
            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "mi"),
            other => panic!(
                "expected Constant(mi) in prami_x2 after se-swap, got {:?}",
                other
            ),
        }
    }

    // ─── Unspecified sumti (zo'e) test ────────────────────────

    #[test]
    fn test_zo_e_compiles_to_unspecified() {
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![Sumti::Unspecified];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        // With event decomposition, form is Exists(ev, And(klama(ev), klama_x1(ev, zo'e), ...))
        assert!(
            matches!(&form, LogicalForm::Exists(_, _)),
            "expected Exists, got {:?}",
            form
        );
        // Check that klama_x1 has Unspecified (zo'e) in its entity arg
        let x1_args =
            get_pred_args(&form, "klama_x1", &compiler).expect("expected klama_x1 role predicate");
        assert!(
            matches!(x1_args[1], LogicalTerm::Unspecified),
            "expected Unspecified in klama_x1, got {:?}",
            x1_args[1]
        );
    }

    // ─── Event decomposition (Neo-Davidsonian) tests ──────────

    #[test]
    fn test_event_decompose_basic() {
        // mi klama → ∃e. klama(e) ∧ klama_x1(e, mi) ∧ klama_x2(e, zo'e) ∧ ...
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Top level should be Exists (event variable)
        assert!(matches!(&form, LogicalForm::Exists(_, _)));
        // Type predicate exists
        assert!(has_pred(&form, "klama", &compiler));
        // x1 role has Constant("mi")
        let x1 = get_pred_args(&form, "klama_x1", &compiler).unwrap();
        assert_eq!(
            x1[1],
            LogicalTerm::Constant(compiler.interner.get("mi").unwrap())
        );
        // Event variable is shared between type and role predicates
        let type_args = get_pred_args(&form, "klama", &compiler).unwrap();
        assert!(matches!(&type_args[0], LogicalTerm::Variable(_)));
        assert_eq!(type_args[0], x1[0], "event var should be shared");
    }

    #[test]
    fn test_event_decompose_all_roles_emitted() {
        // klama has arity 5, all roles should be emitted
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        for i in 1..=5 {
            let role = format!("klama_x{}", i);
            assert!(has_pred(&form, &role, &compiler), "expected {} role", role);
        }
        // No x6 for a 5-arity predicate
        assert!(!has_pred(&form, "klama_x6", &compiler));
    }

    #[test]
    fn test_event_tanru_shared_event() {
        // sutra gerku → ∃e. gerku(e) ∧ gerku_x1(e, x1) ∧ sutra_x1(e, x1)
        // modifier and head share the SAME event variable
        let selbris = vec![
            Selbri::Root("sutra".into()), // 0
            Selbri::Root("gerku".into()), // 1
            Selbri::Tanru((0, 1)),        // 2
        ];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 2,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Should have head type predicate
        assert!(has_pred(&form, "gerku", &compiler));
        // Should have head x1 role
        assert!(has_pred(&form, "gerku_x1", &compiler));
        // Should have modifier x1 role (NOT a full sutra predicate)
        assert!(has_pred(&form, "sutra_x1", &compiler));

        // Both roles should share the same event variable
        let gerku_x1 = get_pred_args(&form, "gerku_x1", &compiler).unwrap();
        let sutra_x1 = get_pred_args(&form, "sutra_x1", &compiler).unwrap();
        assert_eq!(
            gerku_x1[0], sutra_x1[0],
            "event var should be shared between head and modifier"
        );

        // Both x1 entity args should be mi
        let mi = LogicalTerm::Constant(compiler.interner.get("mi").unwrap());
        assert_eq!(gerku_x1[1], mi);
        assert_eq!(sutra_x1[1], mi);
    }

    #[test]
    fn test_event_tanru_no_intersective_fallacy() {
        // barda gerku → NOT And(barda(x1), gerku(x1, ...))
        // Instead: ∃e. gerku(e) ∧ gerku_x1(e, x1) ∧ barda_x1(e, x1)
        // The modifier "barda" is event-bound, not a standalone predication
        let selbris = vec![
            Selbri::Root("barda".into()), // 0
            Selbri::Root("gerku".into()), // 1
            Selbri::Tanru((0, 1)),        // 2
        ];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 2,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // There should be NO standalone "barda" type predicate
        // Only "barda_x1" role predicate (event-bound modifier)
        let preds = collect_predicates(&form, &compiler);
        let barda_preds: Vec<_> = preds.iter().filter(|(n, _)| n == "barda").collect();
        assert!(
            barda_preds.is_empty(),
            "should NOT have standalone barda predicate, got {:?}",
            barda_preds
        );
        assert!(
            has_pred(&form, "barda_x1", &compiler),
            "should have event-bound barda_x1 role"
        );
    }

    #[test]
    fn test_event_decompose_with_quantifier() {
        // lo gerku cu klama → ∃x. (∃e1. gerku(e1) ∧ gerku_x1(e1, x)) ∧ (∃e2. klama(e2) ∧ klama_x1(e2, x) ∧ ...)
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("klama".into()), // 1
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Lo, 0)), // 0: lo gerku
        ];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Outer Exists for the description variable
        assert!(matches!(&form, LogicalForm::Exists(_, _)));
        // Both gerku and klama predicates exist
        assert!(has_pred(&form, "gerku", &compiler));
        assert!(has_pred(&form, "klama", &compiler));
        // Both have x1 roles
        assert!(has_pred(&form, "gerku_x1", &compiler));
        assert!(has_pred(&form, "klama_x1", &compiler));
    }

    #[test]
    fn test_event_conversion_se() {
        // mi se prami do → prami(do, mi, ...) with se-swapped args
        // Event form: ∃e. prami(e) ∧ prami_x1(e, do) ∧ prami_x2(e, mi)
        let selbris = vec![
            Selbri::Root("prami".into()),           // 0
            Selbri::Converted((Conversion::Se, 0)), // 1
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()), // 0
            Sumti::ProSumti("do".into()), // 1
        ];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![1],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // se swaps x1 and x2: mi goes to x2, do goes to x1
        let x1 = get_pred_args(&form, "prami_x1", &compiler).unwrap();
        let x2 = get_pred_args(&form, "prami_x2", &compiler).unwrap();
        assert_eq!(
            x1[1],
            LogicalTerm::Constant(compiler.interner.get("do").unwrap())
        );
        assert_eq!(
            x2[1],
            LogicalTerm::Constant(compiler.interner.get("mi").unwrap())
        );
    }

    // ─── Name (la cmevla) test ────────────────────────────────

    #[test]
    fn test_la_name_compiles_to_constant() {
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![Sumti::Name("alis".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        // With event decomposition, form is Exists(ev, And(klama(ev), klama_x1(ev, alis), ...))
        assert!(
            matches!(&form, LogicalForm::Exists(_, _)),
            "expected Exists, got {:?}",
            form
        );
        let x1_args =
            get_pred_args(&form, "klama_x1", &compiler).expect("expected klama_x1 role predicate");
        match &x1_args[1] {
            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "alis"),
            other => panic!("expected Constant(alis), got {:?}", other),
        }
    }

    // ─── Number sumti (li PA) test ────────────────────────────

    #[test]
    fn test_number_sumti_compiles_to_number() {
        let selbris = vec![Selbri::Root("namcu".into())];
        let sumtis = vec![Sumti::Number(42.0)];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        // With event decomposition, form is Exists(ev, And(namcu(ev), namcu_x1(ev, 42.0), ...))
        assert!(
            matches!(&form, LogicalForm::Exists(_, _)),
            "expected Exists, got {:?}",
            form
        );
        let x1_args =
            get_pred_args(&form, "namcu_x1", &compiler).expect("expected namcu_x1 role predicate");
        assert!(
            matches!(x1_args[1], LogicalTerm::Number(n) if n == 42.0),
            "expected Number(42.0) in namcu_x1, got {:?}",
            x1_args[1]
        );
    }

    // ─── Quoted literal test ──────────────────────────────────

    #[test]
    fn test_quoted_literal_compiles_to_constant() {
        let selbris = vec![Selbri::Root("valsi".into())];
        let sumtis = vec![Sumti::QuotedLiteral("coi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        // With event decomposition, form is Exists(ev, And(valsi(ev), valsi_x1(ev, coi), ...))
        assert!(
            matches!(&form, LogicalForm::Exists(_, _)),
            "expected Exists, got {:?}",
            form
        );
        let x1_args =
            get_pred_args(&form, "valsi_x1", &compiler).expect("expected valsi_x1 role predicate");
        match &x1_args[1] {
            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "coi"),
            other => panic!("expected Constant(coi), got {:?}", other),
        }
    }

    // ─── Selbri connective tests ──────────────────────────────

    #[test]
    fn test_selbri_connective_je_produces_and() {
        // mi klama je sutra → And(klama(mi,...), sutra(mi,...))
        let selbris = vec![
            Selbri::Root("klama".into()),
            Selbri::Root("sutra".into()),
            Selbri::Connected((0, Connective::Je, 1)),
        ];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 2,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, _) = compile_one(selbris, sumtis, bridi);
        assert!(matches!(form, LogicalForm::And(_, _)));
    }

    #[test]
    fn test_selbri_connective_ja_produces_or() {
        let selbris = vec![
            Selbri::Root("klama".into()),
            Selbri::Root("sutra".into()),
            Selbri::Connected((0, Connective::Ja, 1)),
        ];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 2,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, _) = compile_one(selbris, sumtis, bridi);
        assert!(matches!(form, LogicalForm::Or(_, _)));
    }

    #[test]
    fn test_selbri_connective_jo_produces_biconditional() {
        let selbris = vec![
            Selbri::Root("klama".into()),
            Selbri::Root("sutra".into()),
            Selbri::Connected((0, Connective::Jo, 1)),
        ];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 2,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, _) = compile_one(selbris, sumtis, bridi);
        assert!(matches!(form, LogicalForm::Biconditional(_, _)));
    }

    #[test]
    fn test_selbri_connective_ju_produces_xor() {
        let selbris = vec![
            Selbri::Root("klama".into()),
            Selbri::Root("sutra".into()),
            Selbri::Connected((0, Connective::Ju, 1)),
        ];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 2,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, _) = compile_one(selbris, sumtis, bridi);
        assert!(matches!(form, LogicalForm::Xor(_, _)));
    }

    #[test]
    fn test_connected_selbri_uses_max_arity_for_right_operand() {
        // `mi prami je klama do ti` — left `prami` is 2-place, right `klama` is
        // 5-place. The connected selbri's effective arity must be max(2,5)=5 so
        // the place counter captures `ti` (x3) instead of dropping it; the right
        // operand `klama` then receives `ti` in its x3. `prami je klama` is a valid
        // mixed-arity selbri connective (each operand fits its own arity) — no error.
        let selbris = vec![
            Selbri::Root("prami".into()),              // 0 (2-place)
            Selbri::Root("klama".into()),              // 1 (5-place)
            Selbri::Connected((0, Connective::Je, 1)), // 2: prami je klama
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()), // 0
            Sumti::ProSumti("do".into()), // 1
            Sumti::ProSumti("ti".into()), // 2
        ];
        let bridi = Bridi {
            relation: 2,
            head_terms: vec![0],
            tail_terms: vec![1, 2],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            compiler.errors.is_empty(),
            "mixed-arity selbri connective must not error/overflow, got: {:?}",
            compiler.errors
        );
        let x3 = get_pred_args(&form, "klama_x3", &compiler)
            .expect("klama_x3 role predicate must exist");
        let ti = LogicalTerm::Constant(compiler.interner.get("ti").unwrap());
        assert_eq!(x3[1], ti, "klama's x3 must be `ti`, not Unspecified");
    }

    // ─── Arity from dictionary ────────────────────────────────

    #[test]
    fn test_known_gismu_gets_correct_arity() {
        // klama has arity 5, so there should be 5 role predicates (klama_x1..klama_x5)
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        // With event decomposition, check that all 5 role predicates exist
        assert!(
            matches!(&form, LogicalForm::Exists(_, _)),
            "expected Exists, got {:?}",
            form
        );
        assert!(
            has_pred(&form, "klama", &compiler),
            "expected klama type predicate"
        );
        for i in 1..=5 {
            let role = format!("klama_x{}", i);
            assert!(
                has_pred(&form, &role, &compiler),
                "klama should have role predicate {}",
                role
            );
        }
    }

    #[test]
    fn test_unknown_gismu_defaults_to_arity_2() {
        // An unrecognized word should default to arity 2 → 2 role predicates
        let selbris = vec![Selbri::Root("xyzzy".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into())];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        // With event decomposition, check that there are 2 role predicates
        assert!(
            matches!(&form, LogicalForm::Exists(_, _)),
            "expected Exists, got {:?}",
            form
        );
        assert!(
            has_pred(&form, "xyzzy", &compiler),
            "expected xyzzy type predicate"
        );
        assert!(
            has_pred(&form, "xyzzy_x1", &compiler),
            "expected xyzzy_x1 role"
        );
        assert!(
            has_pred(&form, "xyzzy_x2", &compiler),
            "expected xyzzy_x2 role"
        );
        // Should NOT have xyzzy_x3
        assert!(
            !has_pred(&form, "xyzzy_x3", &compiler),
            "unknown word should default to arity 2, but found xyzzy_x3"
        );
    }

    // ─── Sentence connective tests ────────────────────────────

    #[test]
    fn test_sentence_connective_ge_gi_produces_and() {
        // ge mi klama gi do sutra → And(klama(mi,...), sutra(do,...))
        let selbris = vec![Selbri::Root("klama".into()), Selbri::Root("sutra".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into()), Sumti::ProSumti("do".into())];
        let sentences = vec![
            Sentence::Connected((
                SentenceConnective::GeGi,
                1, // left sentence idx
                2, // right sentence idx
            )),
            Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![0],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 1,
                head_terms: vec![1],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        let (form, _) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(matches!(form, LogicalForm::And(_, _)));
    }

    #[test]
    fn test_sentence_connective_go_gi_produces_biconditional() {
        // go mi klama gi do sutra → Biconditional(klama(mi,...), klama(do,...))
        let selbris = vec![Selbri::Root("klama".into()), Selbri::Root("sutra".into())];
        let sumtis = vec![Sumti::ProSumti("mi".into()), Sumti::ProSumti("do".into())];
        let sentences = vec![
            Sentence::Connected((
                SentenceConnective::GoGi,
                1, // left sentence idx
                2, // right sentence idx
            )),
            Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![0],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 1,
                head_terms: vec![1],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];
        let (form, _) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(
            matches!(form, LogicalForm::Biconditional(_, _)),
            "expected Biconditional, got {:?}",
            form
        );
    }

    // ─── Fresh variable generation ────────────────────────────

    #[test]
    fn test_fresh_vars_are_unique() {
        let mut compiler = SemanticCompiler::new();
        let v1 = compiler.fresh_var();
        let v2 = compiler.fresh_var();
        let v3 = compiler.fresh_var();
        assert_ne!(v1, v2);
        assert_ne!(v2, v3);
        assert_ne!(v1, v3);
        assert_eq!(compiler.interner.resolve(&v1), "_v0");
        assert_eq!(compiler.interner.resolve(&v2), "_v1");
        assert_eq!(compiler.interner.resolve(&v3), "_v2");
    }

    // ─── BAI tag gismu mapping ────────────────────────────────

    #[test]
    fn test_bai_to_gismu_mapping() {
        assert_eq!(SemanticCompiler::bai_to_gismu(&BaiTag::Ria), "rinka");
        assert_eq!(SemanticCompiler::bai_to_gismu(&BaiTag::Nii), "nibli");
        assert_eq!(SemanticCompiler::bai_to_gismu(&BaiTag::Mui), "mukti");
        assert_eq!(SemanticCompiler::bai_to_gismu(&BaiTag::Kiu), "krinu");
        assert_eq!(SemanticCompiler::bai_to_gismu(&BaiTag::Pio), "pilno");
        assert_eq!(SemanticCompiler::bai_to_gismu(&BaiTag::Bai), "basti");
    }

    // ─── inject_variable into conjunction ─────────────────────

    #[test]
    fn test_inject_variable_into_and() {
        let mut compiler = SemanticCompiler::new();
        let rel1 = compiler.interner.get_or_intern("gerku");
        let rel2 = compiler.interner.get_or_intern("barda");
        let var = compiler.interner.get_or_intern("_v0");
        let form = LogicalForm::And(
            Box::new(LogicalForm::Predicate {
                relation: rel1,
                args: vec![LogicalTerm::Unspecified],
            }),
            Box::new(LogicalForm::Predicate {
                relation: rel2,
                args: vec![LogicalTerm::Unspecified],
            }),
        );
        let injected = SemanticCompiler::inject_variable(form, var, &compiler.interner);
        match injected {
            LogicalForm::And(left, right) => {
                // inject_variable fills the FIRST unspecified in the first predicate found
                match left.as_ref() {
                    LogicalForm::Predicate { args, .. } => {
                        assert!(matches!(args[0], LogicalTerm::Variable(_)));
                    }
                    other => panic!("expected Predicate, got {:?}", other),
                }
                match right.as_ref() {
                    LogicalForm::Predicate { args, .. } => {
                        assert!(matches!(args[0], LogicalTerm::Variable(_)));
                    }
                    other => panic!("expected Predicate, got {:?}", other),
                }
            }
            other => panic!("expected And, got {:?}", other),
        }
    }

    // ─── No-arg predicate ─────────────────────────────────────

    #[test]
    fn test_predicate_with_no_explicit_args() {
        // Just "klama" alone → should produce event-decomposed form with all Unspecified role args
        let selbris = vec![Selbri::Root("klama".into())];
        let sumtis: Vec<Sumti> = vec![];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        // With event decomposition, should be Exists(ev, And(klama(ev), klama_x1(ev, zo'e), ...))
        assert!(
            matches!(&form, LogicalForm::Exists(_, _)),
            "expected Exists, got {:?}",
            form
        );
        assert!(
            has_pred(&form, "klama", &compiler),
            "expected klama type predicate"
        );
        // All role predicates should have Unspecified in entity position
        for i in 1..=5 {
            let role = format!("klama_x{}", i);
            let role_args = get_pred_args(&form, &role, &compiler)
                .unwrap_or_else(|| panic!("expected {} role predicate", role));
            assert!(
                matches!(role_args[1], LogicalTerm::Unspecified),
                "expected Unspecified in {}, got {:?}",
                role,
                role_args[1]
            );
        }
    }

    // ─── C5: Description term opacity tests ──────────────────────

    #[test]
    fn test_la_gadri_compiles_to_constant() {
        // la gerku cu barda → Constant("gerku") in x1 role predicate
        let selbris = vec![Selbri::Root("gerku".into()), Selbri::Root("barda".into())];
        let sumtis = vec![Sumti::Description((Gadri::La, 0))];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        let args =
            get_pred_args(&form, "barda_x1", &compiler).expect("expected barda_x1 role predicate");
        // x1 arg (index 1 after event) should be Constant("gerku")
        match &args[1] {
            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "gerku"),
            other => panic!("expected Constant(gerku), got {:?}", other),
        }
    }

    #[test]
    fn test_le_description_stays_description() {
        // le gerku cu barda → Description("gerku") in x1 role predicate
        let selbris = vec![Selbri::Root("gerku".into()), Selbri::Root("barda".into())];
        let sumtis = vec![Sumti::Description((Gadri::Le, 0))];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        let args =
            get_pred_args(&form, "barda_x1", &compiler).expect("expected barda_x1 role predicate");
        match &args[1] {
            LogicalTerm::Description(d) => assert_eq!(resolve(&compiler, d), "gerku"),
            other => panic!("expected Description(gerku), got {:?}", other),
        }
    }

    #[test]
    fn test_ro_le_uses_opaque_domain_restrictor() {
        // ro le gerku cu sutra → ForAll(_v0, Or(Not(le_domain_gerku(_v0)), ...))
        let selbris = vec![Selbri::Root("gerku".into()), Selbri::Root("sutra".into())];
        let sumtis = vec![Sumti::Description((Gadri::RoLe, 0))];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        // Must be ForAll at the top
        assert!(
            matches!(&form, LogicalForm::ForAll(_, _)),
            "expected ForAll, got {:?}",
            form
        );
        // The restrictor should be le_domain_gerku (not gerku)
        assert!(
            has_pred(&form, "le_domain_gerku", &compiler),
            "expected opaque le_domain_gerku restrictor"
        );
        assert!(
            !has_pred(&form, "gerku", &compiler),
            "veridical gerku should NOT appear as restrictor for ro le"
        );
    }

    #[test]
    fn test_ro_lo_still_veridical() {
        // ro lo gerku cu sutra → ForAll with veridical gerku restrictor
        let selbris = vec![Selbri::Root("gerku".into()), Selbri::Root("sutra".into())];
        let sumtis = vec![Sumti::Description((Gadri::RoLo, 0))];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            matches!(&form, LogicalForm::ForAll(_, _)),
            "expected ForAll, got {:?}",
            form
        );
        // The restrictor should use veridical gerku (event-decomposed)
        assert!(
            has_pred(&form, "gerku", &compiler),
            "expected veridical gerku restrictor for ro lo"
        );
        assert!(
            !has_pred(&form, "le_domain_gerku", &compiler),
            "le_domain_gerku should NOT appear for ro lo"
        );
    }

    #[test]
    fn test_pa_le_uses_opaque_domain_restrictor() {
        // re le gerku cu sutra → Count with le_domain_gerku restrictor
        let selbris = vec![Selbri::Root("gerku".into()), Selbri::Root("sutra".into())];
        let sumtis = vec![Sumti::QuantifiedDescription((2, Gadri::Le, 0))];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            matches!(&form, LogicalForm::Count { count: 2, .. }),
            "expected Count(2), got {:?}",
            form
        );
        assert!(
            has_pred(&form, "le_domain_gerku", &compiler),
            "expected opaque le_domain_gerku restrictor for PA le"
        );
        assert!(
            !has_pred(&form, "gerku", &compiler),
            "veridical gerku should NOT appear for PA le"
        );
    }

    #[test]
    fn test_pa_lo_still_veridical() {
        // re lo gerku cu sutra → Count with veridical gerku restrictor
        let selbris = vec![Selbri::Root("gerku".into()), Selbri::Root("sutra".into())];
        let sumtis = vec![Sumti::QuantifiedDescription((2, Gadri::Lo, 0))];
        let bridi = Bridi {
            relation: 1,
            head_terms: vec![0],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        let (form, compiler) = compile_one(selbris, sumtis, bridi);
        assert!(
            matches!(&form, LogicalForm::Count { count: 2, .. }),
            "expected Count(2), got {:?}",
            form
        );
        assert!(
            has_pred(&form, "gerku", &compiler),
            "expected veridical gerku restrictor for PA lo"
        );
        assert!(
            !has_pred(&form, "le_domain_gerku", &compiler),
            "le_domain_gerku should NOT appear for PA lo"
        );
    }
}
