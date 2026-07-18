//! Semantic compiler: flat AST buffer → First-Order Logic IR.
//!
//! Walks the WIT AST buffer (flat arrays of `Predicate`, `Argument`, `Sentence`) and
//! compiles each sentence into a [`IrForm`] tree. Key transformations:
//!
//! - **Quantifier scoping**: determiner descriptions (`lo`/`le`/`la`/`ro lo`) introduce
//!   quantified variables; scopes are closed outward after the proposition body is compiled.
//! - **Quantifier closure**: bare logic variables (`da`/`de`/`di`) are wrapped in
//!   `Exists`; Skolemization itself happens downstream in nibli-reason at assertion time.
//! - **Connective expansion**: argument/predicate/sentence connectives expand into FOL
//!   `And`/`Or`/`Not`/`Biconditional`/`Xor` combinations.
//! - **Conversion**: `se`/`te`/`ve`/`xe` permute argument places.
//! - **Abstraction**: `nu`/`du'u`/`ka`/`ni`/`si'o` reify inner proposition as 1-place predicates.
//! - **Relative clauses**: `poi`/`voi` (restrictive) conjoin a domain restrictor;
//!   `noi` (non-restrictive) conjoins its body at the MATRIX level (consequent for
//!   universals, body conjunct for existentials/counts) so it does not narrow the
//!   quantifier domain. Residual: under exact-count quantifiers `noi` is still
//!   treated restrictively (documented limitation).
//! - **Modal tags**: `via` tags produce conjoined modal predications.
//! - **String interning**: all relation names and variable names use [`lasso::Rodeo`]
//!   for zero-copy comparison and deduplication.

use crate::dictionary::LexiconSchema;
use crate::ir::{IrForm, IrTerm};
use lasso::Rodeo;
use nibli_types::ast::{
    AbstractionKind, Argument, Connective, Conversion, DeonticMood, Determiner, Marker, ModalTag,
    Predicate, Proposition, RelClauseKind, Sentence, SentenceConnective, Tense,
};

mod compile;
mod helpers;
mod predicate;

/// The kind of quantifier introduced by a determiner description.
#[derive(Debug, Clone)]
pub(crate) enum QuantifierKind {
    /// lo → ∃x (veridical existential, restrictor = predicate predicate)
    Existential,
    /// ro lo → ∀x (veridical universal, restrictor = predicate predicate)
    Universal,
    /// ro le → ∀x (referential universal, restrictor = opaque the_domain predicate)
    UniversalLe,
    /// PA lo → exactly N (veridical, restrictor = predicate predicate)
    ExactCount(u32),
    /// PA le → exactly N (referential, restrictor = opaque the_domain predicate)
    ExactCountLe(u32),
}

/// Tracks a quantifier introduced by a description (lo/le/ro lo/ro le/PA lo),
/// with an optional relative clause restrictor.
pub(crate) struct QuantifierEntry {
    /// The fresh variable bound by this quantifier.
    var: lasso::Spur,
    /// Index into the predicate array for the description predicate (restrictor source).
    desc_id: u32,
    /// Optional restrictive (poi/voi) relative clause body, already compiled.
    /// Folded on the domain side: antecedent for ∀, conjunct for ∃/Count.
    restrictor: Option<IrForm>,
    /// Optional non-restrictive (noi) relative clause body, already compiled.
    /// Folded on the MATRIX side (consequent for ∀, body conjunct for ∃/Count) so
    /// it does not narrow the quantifier domain — see `close_quantifier`.
    incidental_restrictor: Option<IrForm>,
    /// What kind of quantifier this description introduces.
    kind: QuantifierKind,
}

/// One scope introduction in a proposition, recorded in left-to-right SURFACE order so
/// quantifier nesting can follow Lojban scope (leftmost = outermost). Folding the
/// list in reverse interleaves bare-variable existentials among the description
/// quantifiers, so `da citka ro lo gerku` compiles `∃da.∀x` and `ro lo gerku cu
/// citka da` compiles `∀x.∃da`.
pub(crate) enum ScopeMarker {
    /// A determiner description (lo/le/ro lo/ro le/PA lo) → closed via `close_quantifier`.
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
    ref_used: bool,
    /// When inside a ka abstraction, holds the variable that ce'u resolves to.
    /// This is the x1 arg from the enclosing description quantifier.
    property_open_var: Option<lasso::Spur>,
    /// Fresh variables generated for `ma` query pro-argument. Each `ma` gets
    /// an independent variable (unlike da/de/di which co-refer). These are
    /// wrapped in ∃ during quantifier closure.
    question_vars: Vec<lasso::Spur>,
    /// Accumulated semantic errors (e.g., ambiguous inject_variable).
    /// Checked after compilation; if non-empty, compile_buffer returns error.
    pub errors: Vec<String>,
    /// Monotonically increasing counter for generating fresh event variable names.
    event_counter: usize,
    /// Relative clause bodies attached to argument that introduce NO quantifier
    /// (la names, le descriptions, pro-argument). The clause term is already
    /// substituted in; `compile_proposition` drains its frame's entries and conjoins
    /// them into the proposition matrix (previously these were silently dropped —
    /// panel finding 2026-06-10).
    pending_matrix_conjuncts: Vec<IrForm>,
    /// One-shot: the implicit `ke'a` subject of a relative clause, to be placed
    /// as the x1 ARGUMENT of the clause's main proposition BEFORE predicate conversion —
    /// the same position an explicit subject occupies. Consumed by the first
    /// `compile_proposition` of the clause body. This makes `poi se prami la .alis.`
    /// route `ke'a` through `se` conversion to the correct underlying role
    /// (prami_x2), instead of post-hoc `inject_variable` wrongly filling the
    /// conversion-vacated `prami_x1` slot. Skipped (left in place) when the
    /// proposition's own terms carry an explicit `ke'a` — see the skip rule in
    /// `compile_proposition`.
    pending_clause_subject: Option<lasso::Spur>,
    /// Logic variables (`da`/`de`/`di`) bound by an enclosing prenex
    /// (`ro da ... zo'u`). These are universally quantified by the prenex
    /// lowering, so `compile_proposition` must NOT existentially close them the way it
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
            ref_used: false,
            property_open_var: None,
            question_vars: Vec::new(),
            errors: Vec::new(),
            event_counter: 0,
            pending_matrix_conjuncts: Vec::new(),
            pending_clause_subject: None,
            prenex_vars: std::collections::HashSet::new(),
        }
    }
}

#[cfg(test)]
mod tests;
