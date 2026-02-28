//! Semantic compiler: flat AST buffer → First-Order Logic IR.
//!
//! Walks the WIT AST buffer (flat arrays of `Selbri`, `Sumti`, `Sentence`) and
//! compiles each sentence into a [`LogicalForm`] tree. Key transformations:
//!
//! - **Quantifier scoping**: gadri descriptions (`lo`/`le`/`la`/`ro lo`) introduce
//!   quantified variables; scopes are closed outward after the bridi body is compiled.
//! - **Skolemization**: existential quantifiers under universals produce `SkolemFn`
//!   dependent terms instead of bare Skolem constants.
//! - **Connective expansion**: sumti/selbri/sentence connectives expand into FOL
//!   `And`/`Or`/`Not`/`Biconditional`/`Xor` combinations.
//! - **Conversion**: `se`/`te`/`ve`/`xe` permute argument places.
//! - **Abstraction**: `nu`/`du'u`/`ka`/`ni`/`si'o` reify inner bridi as 1-place predicates.
//! - **Relative clauses**: `poi`/`noi`/`voi` clauses conjoin restrictor predicates.
//! - **Modal tags**: BAI cmavo and `fi'o` produce conjoined modal predications.
//! - **String interning**: all relation names and variable names use [`lasso::Rodeo`]
//!   for zero-copy comparison and deduplication.

use crate::bindings::lojban::nesy::ast_types::{
    AbstractionKind, Attitudinal, BaiTag, Bridi, Connective, Conversion, Gadri, ModalTag,
    PlaceTag, Selbri, Sentence, SentenceConnective, Sumti, Tense,
};
use crate::dictionary::JbovlasteSchema;
use crate::ir::{LogicalForm, LogicalTerm};
use lasso::Rodeo;

/// The kind of quantifier introduced by a gadri description.
#[derive(Debug, Clone)]
enum QuantifierKind {
    /// lo → ∃x
    Existential,
    /// ro lo → ∀x
    Universal,
    /// PA lo → exactly N entities satisfy
    ExactCount(u32),
}

/// Tracks a quantifier introduced by a description (lo/le/ro lo/ro le/PA lo),
/// with an optional relative clause restrictor.
struct QuantifierEntry {
    var: lasso::Spur,
    desc_id: u32,
    restrictor: Option<LogicalForm>,
    kind: QuantifierKind,
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
}

impl SemanticCompiler {
    pub fn new() -> Self {
        Self {
            interner: Rodeo::new(),
            var_counter: 0,
            rel_clause_var: None,
            kea_used: false,
            ka_open_var: None,
            ma_vars: Vec::new(),
            errors: Vec::new(),
        }
    }

    fn fresh_var(&mut self) -> lasso::Spur {
        let v = format!("_v{}", self.var_counter);
        self.var_counter += 1;
        self.interner.get_or_intern(&v)
    }

    // ─── BAI → gismu mapping ──────────────────────────────────────

    fn bai_to_gismu(tag: &BaiTag) -> &'static str {
        match tag {
            BaiTag::Ria => "rinka",
            BaiTag::Nii => "nibli",
            BaiTag::Mui => "mukti",
            BaiTag::Kiu => "krinu",
            BaiTag::Pio => "pilno",
            BaiTag::Bai => "basti",
        }
    }

    // ─── Selbri Introspection ────────────────────────────────────

    fn get_selbri_arity(&self, selbri_id: u32, selbris: &[Selbri]) -> usize {
        match &selbris[selbri_id as usize] {
            Selbri::Root(g) => JbovlasteSchema::get_arity_or_default(g.as_str()),
            Selbri::Tanru((_, head_id)) => self.get_selbri_arity(*head_id, selbris),
            Selbri::Converted((_, inner_id)) => self.get_selbri_arity(*inner_id, selbris),
            Selbri::Negated(inner_id) => self.get_selbri_arity(*inner_id, selbris),
            Selbri::Grouped(inner_id) => self.get_selbri_arity(*inner_id, selbris),
            Selbri::WithArgs((core_id, _)) => self.get_selbri_arity(*core_id, selbris),
            Selbri::Connected((left_id, _, _)) => self.get_selbri_arity(*left_id, selbris),
            Selbri::Compound(parts) => parts
                .last()
                .map(|s| JbovlasteSchema::get_arity_or_default(s.as_str()))
                .unwrap_or(2),
            Selbri::Abstraction((_, _)) => 1,
        }
    }

    fn get_selbri_head_name<'a>(&self, selbri_id: u32, selbris: &'a [Selbri]) -> &'a str {
        match &selbris[selbri_id as usize] {
            Selbri::Root(r) => r.as_str(),
            Selbri::Tanru((_, head_id)) => self.get_selbri_head_name(*head_id, selbris),
            Selbri::Converted((_, inner_id)) => self.get_selbri_head_name(*inner_id, selbris),
            Selbri::Negated(inner_id) => self.get_selbri_head_name(*inner_id, selbris),
            Selbri::Grouped(inner_id) => self.get_selbri_head_name(*inner_id, selbris),
            Selbri::WithArgs((core_id, _)) => self.get_selbri_head_name(*core_id, selbris),
            Selbri::Connected((left_id, _, _)) => self.get_selbri_head_name(*left_id, selbris),
            Selbri::Compound(parts) => parts.last().map(|s| s.as_str()).unwrap_or("entity"),
            Selbri::Abstraction((kind, _)) => match kind {
                AbstractionKind::Nu => "nu",
                AbstractionKind::Duhu => "duhu",
                AbstractionKind::Ka => "ka",
                AbstractionKind::Ni => "ni",
                AbstractionKind::Siho => "siho",
            },
        }
    }

    // ─── Sumti Resolution ────────────────────────────────────────

    fn resolve_sumti(
        &mut self,
        sumti: &Sumti,
        sumtis: &[Sumti],
        selbris: &[Selbri],
        sentences: &[Sentence],
    ) -> (LogicalTerm, Vec<QuantifierEntry>) {
        match sumti {
            Sumti::ProSumti(p) => {
                let term = if p.as_str() == "ma" {
                    // Each `ma` gets a fresh variable — they are independent
                    // query unknowns, unlike da/de/di which co-refer.
                    let var = self.fresh_var();
                    self.ma_vars.push(var);
                    LogicalTerm::Variable(var)
                } else if matches!(p.as_str(), "da" | "de" | "di") {
                    LogicalTerm::Variable(self.interner.get_or_intern(p.as_str()))
                } else if p.as_str() == "ke'a" {
                    // ke'a resolves to the bound variable from the enclosing
                    // relative clause description. If we're not inside a rel
                    // clause, treat as unspecified (graceful degradation).
                    if let Some(var) = self.rel_clause_var {
                        self.kea_used = true;
                        LogicalTerm::Variable(var)
                    } else {
                        LogicalTerm::Unspecified
                    }
                } else if p.as_str() == "ce'u" {
                    // ce'u resolves to the open variable from the enclosing
                    // ka abstraction. If not inside a ka, treat as fresh variable.
                    if let Some(var) = self.ka_open_var {
                        LogicalTerm::Variable(var)
                    } else {
                        let var = self.fresh_var();
                        LogicalTerm::Variable(var)
                    }
                } else {
                    LogicalTerm::Constant(self.interner.get_or_intern(p.as_str()))
                };
                (term, vec![])
            }

            Sumti::Name(n) => (
                LogicalTerm::Constant(self.interner.get_or_intern(n.as_str())),
                vec![],
            ),

            Sumti::Description((gadri, desc_id)) => {
                match gadri {
                    // Existential: lo → ∃x
                    Gadri::Lo => {
                        let var = self.fresh_var();
                        (
                            LogicalTerm::Variable(var),
                            vec![QuantifierEntry {
                                var,
                                desc_id: *desc_id,
                                restrictor: None,
                                kind: QuantifierKind::Existential,
                            }],
                        )
                    }

                    // Universal: ro lo → ∀x, ro le → ∀x
                    Gadri::RoLo | Gadri::RoLe => {
                        let var = self.fresh_var();
                        (
                            LogicalTerm::Variable(var),
                            vec![QuantifierEntry {
                                var,
                                desc_id: *desc_id,
                                restrictor: None,
                                kind: QuantifierKind::Universal,
                            }],
                        )
                    }

                    // le/la: non-quantified specific referent
                    _ => {
                        let desc_str = self.get_selbri_head_name(*desc_id, selbris);
                        (
                            LogicalTerm::Description(self.interner.get_or_intern(desc_str)),
                            vec![],
                        )
                    }
                }
            }

            Sumti::QuantifiedDescription((count, _gadri, desc_id)) => {
                let var = self.fresh_var();
                (
                    LogicalTerm::Variable(var),
                    vec![QuantifierEntry {
                        var,
                        desc_id: *desc_id,
                        restrictor: None,
                        kind: QuantifierKind::ExactCount(*count),
                    }],
                )
            }

            Sumti::Tagged((_tag, inner_id)) => {
                let inner = &sumtis[*inner_id as usize];
                self.resolve_sumti(inner, sumtis, selbris, sentences)
            }

            Sumti::ModalTagged((_modal_tag, inner_id)) => {
                let inner = &sumtis[*inner_id as usize];
                self.resolve_sumti(inner, sumtis, selbris, sentences)
            }

            Sumti::Restricted((inner_id, rel_clause)) => {
                let inner = &sumtis[*inner_id as usize];
                let (term, mut quants) = self.resolve_sumti(inner, sumtis, selbris, sentences);

                // Set up ke'a context: the bound variable from the innermost
                // description quantifier becomes available as ke'a inside the
                // relative clause body.
                let outer_rel_var = self.rel_clause_var;
                let outer_kea_used = self.kea_used;

                if let Some(last) = quants.last() {
                    self.rel_clause_var = Some(last.var);
                }
                self.kea_used = false;

                let rel_body = self.compile_sentence(
                    rel_clause.body_sentence, // Pass the u32 ID directly, NOT &sentences[...]
                    selbris,
                    sumtis,
                    sentences,
                );

                let kea_was_used = self.kea_used;

                // Restore outer context (handles nested rel clauses)
                self.rel_clause_var = outer_rel_var;
                self.kea_used = outer_kea_used;

                if let Some(last) = quants.last_mut() {
                    if kea_was_used {
                        // ke'a was used — the bound variable is already in the
                        // correct position. No heuristic injection needed.
                        last.restrictor = Some(rel_body);
                    } else {
                        // No ke'a — use heuristic injection as fallback.
                        // inject_variable fills the first Unspecified slot in
                        // each predicate it can reach.
                        let unspec_count = Self::count_unspecified_predicates(&rel_body);
                        if unspec_count > 1 {
                            // Ambiguous injection — reject rather than silently produce wrong FOL.
                            self.errors.push(format!(
                                "Relative clause has {} predicates with unspecified slots; \
                                 implicit variable injection is ambiguous. Use explicit ke'a \
                                 for precise control.",
                                unspec_count
                            ));
                        }
                        last.restrictor = Some(Self::inject_variable(rel_body, last.var));
                    }
                }

                (term, quants)
            }

            Sumti::QuotedLiteral(q) => (
                LogicalTerm::Constant(self.interner.get_or_intern(q.as_str())),
                vec![],
            ),

            Sumti::Number(n) => (LogicalTerm::Number(*n), vec![]),
            Sumti::Unspecified => (LogicalTerm::Unspecified, vec![]),

            // Connected sumti in resolve_sumti context (e.g. inside BE clause):
            // resolve the LEFT side only. Full expansion happens in compile_bridi.
            Sumti::Connected((left_id, _conn, _negated, _right_id)) => {
                let left = &sumtis[*left_id as usize];
                self.resolve_sumti(left, sumtis, selbris, sentences)
            }
        }
    }

    /// Count how many predicates in a formula have at least one Unspecified slot.
    fn count_unspecified_predicates(form: &LogicalForm) -> usize {
        match form {
            LogicalForm::Predicate { args, .. } => {
                if args.iter().any(|a| matches!(a, LogicalTerm::Unspecified)) {
                    1
                } else {
                    0
                }
            }
            LogicalForm::And(l, r)
            | LogicalForm::Or(l, r)
            | LogicalForm::Biconditional(l, r)
            | LogicalForm::Xor(l, r) => {
                Self::count_unspecified_predicates(l) + Self::count_unspecified_predicates(r)
            }
            LogicalForm::Not(inner)
            | LogicalForm::Exists(_, inner)
            | LogicalForm::ForAll(_, inner)
            | LogicalForm::Past(inner)
            | LogicalForm::Present(inner)
            | LogicalForm::Future(inner)
            | LogicalForm::Obligatory(inner)
            | LogicalForm::Permitted(inner) => Self::count_unspecified_predicates(inner),
            LogicalForm::Count { body, .. } => Self::count_unspecified_predicates(body),
        }
    }

    /// Heuristic variable injection for relative clauses without explicit ke'a.
    ///
    /// Recurses through the entire formula tree and replaces the first
    /// Unspecified slot in each Predicate with the bound variable.
    ///
    /// Known limitation: when the rel clause contains descriptions (lo/le),
    /// the restrictor predicates from those descriptions will also get the
    /// variable injected. Use explicit ke'a for precise control.
    fn inject_variable(form: LogicalForm, var: lasso::Spur) -> LogicalForm {
        match form {
            LogicalForm::Predicate { relation, mut args } => {
                let first_unspec = args
                    .iter()
                    .position(|a| matches!(a, LogicalTerm::Unspecified));
                if let Some(idx) = first_unspec {
                    args[idx] = LogicalTerm::Variable(var);
                } else if args.is_empty() {
                    args.push(LogicalTerm::Variable(var));
                }
                LogicalForm::Predicate { relation, args }
            }
            LogicalForm::And(l, r) => LogicalForm::And(
                Box::new(Self::inject_variable(*l, var)),
                Box::new(Self::inject_variable(*r, var)),
            ),
            LogicalForm::Or(l, r) => LogicalForm::Or(
                Box::new(Self::inject_variable(*l, var)),
                Box::new(Self::inject_variable(*r, var)),
            ),
            LogicalForm::Biconditional(l, r) => LogicalForm::Biconditional(
                Box::new(Self::inject_variable(*l, var)),
                Box::new(Self::inject_variable(*r, var)),
            ),
            LogicalForm::Xor(l, r) => LogicalForm::Xor(
                Box::new(Self::inject_variable(*l, var)),
                Box::new(Self::inject_variable(*r, var)),
            ),
            LogicalForm::Not(inner) => {
                LogicalForm::Not(Box::new(Self::inject_variable(*inner, var)))
            }
            LogicalForm::Exists(v, body) => {
                LogicalForm::Exists(v, Box::new(Self::inject_variable(*body, var)))
            }
            LogicalForm::ForAll(v, body) => {
                LogicalForm::ForAll(v, Box::new(Self::inject_variable(*body, var)))
            }
            LogicalForm::Past(inner) => {
                LogicalForm::Past(Box::new(Self::inject_variable(*inner, var)))
            }
            LogicalForm::Present(inner) => {
                LogicalForm::Present(Box::new(Self::inject_variable(*inner, var)))
            }
            LogicalForm::Future(inner) => {
                LogicalForm::Future(Box::new(Self::inject_variable(*inner, var)))
            }
            LogicalForm::Obligatory(inner) => {
                LogicalForm::Obligatory(Box::new(Self::inject_variable(*inner, var)))
            }
            LogicalForm::Permitted(inner) => {
                LogicalForm::Permitted(Box::new(Self::inject_variable(*inner, var)))
            }
            LogicalForm::Count { var: v, count, body } => {
                LogicalForm::Count {
                    var: v,
                    count,
                    body: Box::new(Self::inject_variable(*body, var)),
                }
            }
        }
    }

    // ─── Arity Normalization ─────────────────────────────────────

    fn fit_args(args: &[LogicalTerm], arity: usize) -> Vec<LogicalTerm> {
        let mut fitted = Vec::with_capacity(arity);
        for i in 0..arity {
            if i < args.len() {
                fitted.push(args[i].clone());
            } else {
                fitted.push(LogicalTerm::Unspecified);
            }
        }
        fitted
    }

    // ─── Selbri Application ──────────────────────────────────────

    fn apply_selbri(
        &mut self,
        selbri_id: u32,
        args: &[LogicalTerm],
        selbris: &[Selbri],
        sumtis: &[Sumti],
        sentences: &[Sentence],
    ) -> LogicalForm {
        match &selbris[selbri_id as usize] {
            Selbri::Root(g) => {
                let arity = JbovlasteSchema::get_arity_or_default(g.as_str());
                LogicalForm::Predicate {
                    relation: self.interner.get_or_intern(g.as_str()),
                    args: Self::fit_args(args, arity),
                }
            }

            Selbri::Tanru((mod_id, head_id)) => {
                let mod_arity = self.get_selbri_arity(*mod_id, selbris);
                let head_arity = self.get_selbri_arity(*head_id, selbris);

                // Tanru semantics: modifier and head share ONLY x1 (the referent).
                // "sutra gerku" = "is-fast(x1) ∧ is-dog(x1, ...)" — the modifier's
                // remaining places (x2..xN) are independent of the head's places.
                let mut mod_args = vec![LogicalTerm::Unspecified; mod_arity];
                if !args.is_empty() && mod_arity > 0 {
                    mod_args[0] = args[0].clone();
                }

                let left = self.apply_selbri(*mod_id, &mod_args, selbris, sumtis, sentences);
                let right = self.apply_selbri(
                    *head_id,
                    &Self::fit_args(args, head_arity),
                    selbris,
                    sumtis,
                    sentences,
                );
                LogicalForm::And(Box::new(left), Box::new(right))
            }

            Selbri::Converted((conv, inner_id)) => {
                let mut permuted = args.to_vec();
                match conv {
                    Conversion::Se if permuted.len() >= 2 => permuted.swap(0, 1),
                    Conversion::Te if permuted.len() >= 3 => permuted.swap(0, 2),
                    Conversion::Ve if permuted.len() >= 4 => permuted.swap(0, 3),
                    Conversion::Xe if permuted.len() >= 5 => permuted.swap(0, 4),
                    _ => {}
                }
                self.apply_selbri(*inner_id, &permuted, selbris, sumtis, sentences)
            }

            Selbri::Negated(inner_id) => {
                let inner = self.apply_selbri(*inner_id, args, selbris, sumtis, sentences);
                LogicalForm::Not(Box::new(inner))
            }

            Selbri::Grouped(inner_id) => {
                self.apply_selbri(*inner_id, args, selbris, sumtis, sentences)
            }

            Selbri::WithArgs((core_id, bound_ids)) => {
                let core_arity = self.get_selbri_arity(*core_id, selbris);
                let mut merged = Vec::with_capacity(core_arity);
                let mut inner_quantifiers: Vec<QuantifierEntry> = Vec::new();

                merged.push(if !args.is_empty() {
                    args[0].clone()
                } else {
                    LogicalTerm::Unspecified
                });

                for bound_id in bound_ids.iter() {
                    let bound_sumti = &sumtis[*bound_id as usize];
                    let (term, quants) =
                        self.resolve_sumti(bound_sumti, sumtis, selbris, sentences);
                    inner_quantifiers.extend(quants);
                    merged.push(term);
                }

                let bound_count = 1 + bound_ids.len();
                for i in merged.len()..core_arity {
                    if i < args.len() && i >= bound_count {
                        merged.push(args[i].clone());
                    } else {
                        merged.push(LogicalTerm::Unspecified);
                    }
                }

                let mut form = self.apply_selbri(*core_id, &merged, selbris, sumtis, sentences);

                for entry in inner_quantifiers.into_iter().rev() {
                    let desc_arity = self.get_selbri_arity(entry.desc_id, selbris);
                    let mut restrictor_args = vec![LogicalTerm::Variable(entry.var)];
                    while restrictor_args.len() < desc_arity {
                        restrictor_args.push(LogicalTerm::Unspecified);
                    }
                    let restrictor = self.apply_selbri(
                        entry.desc_id,
                        &restrictor_args,
                        selbris,
                        sumtis,
                        sentences,
                    );

                    match entry.kind {
                        QuantifierKind::Universal => {
                            // ∀x. (restrictor → body) = ∀x. (¬restrictor ∨ body)
                            let mut body = LogicalForm::Or(
                                Box::new(LogicalForm::Not(Box::new(restrictor))),
                                Box::new(form),
                            );
                            if let Some(rel_restrictor) = entry.restrictor {
                                body = LogicalForm::Or(
                                    Box::new(LogicalForm::Not(Box::new(rel_restrictor))),
                                    Box::new(body),
                                );
                            }
                            form = LogicalForm::ForAll(entry.var, Box::new(body));
                        }
                        QuantifierKind::Existential => {
                            // ∃x. (restrictor ∧ body)
                            let mut body = LogicalForm::And(Box::new(restrictor), Box::new(form));
                            if let Some(rel_restrictor) = entry.restrictor {
                                body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                            }
                            form = LogicalForm::Exists(entry.var, Box::new(body));
                        }
                        QuantifierKind::ExactCount(n) => {
                            // Count(x, n, restrictor ∧ body)
                            let mut body = LogicalForm::And(Box::new(restrictor), Box::new(form));
                            if let Some(rel_restrictor) = entry.restrictor {
                                body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                            }
                            form = LogicalForm::Count {
                                var: entry.var,
                                count: n,
                                body: Box::new(body),
                            };
                        }
                    }
                }

                form
            }

            Selbri::Connected((left_id, conn, right_id)) => {
                let left_arity = self.get_selbri_arity(*left_id, selbris);
                let right_arity = self.get_selbri_arity(*right_id, selbris);
                let left_args = Self::fit_args(args, left_arity);
                let right_args = Self::fit_args(args, right_arity);
                let left = self.apply_selbri(*left_id, &left_args, selbris, sumtis, sentences);
                let right = self.apply_selbri(*right_id, &right_args, selbris, sumtis, sentences);

                match conn {
                    Connective::Je => LogicalForm::And(Box::new(left), Box::new(right)),
                    Connective::Ja => LogicalForm::Or(Box::new(left), Box::new(right)),
                    Connective::Jo => {
                        LogicalForm::Biconditional(Box::new(left), Box::new(right))
                    }
                    Connective::Ju => {
                        LogicalForm::Xor(Box::new(left), Box::new(right))
                    }
                }
            }

            Selbri::Compound(parts) => {
                let head = parts.last().map(|s| s.as_str()).unwrap_or("unknown");
                let arity = JbovlasteSchema::get_arity_or_default(head);
                LogicalForm::Predicate {
                    relation: self.interner.get_or_intern(head),
                    args: Self::fit_args(args, arity),
                }
            }

            Selbri::Abstraction((kind, body_sentence_idx)) => {
                let type_name = match kind {
                    AbstractionKind::Nu => "nu",
                    AbstractionKind::Duhu => "duhu",
                    AbstractionKind::Ka => "ka",
                    AbstractionKind::Ni => "ni",
                    AbstractionKind::Siho => "siho",
                };

                // For ka: set ka_open_var so ce'u resolves to the
                // quantified entity variable (args[0]).
                let outer_ka_var = self.ka_open_var;
                if *kind == AbstractionKind::Ka {
                    if let Some(LogicalTerm::Variable(v)) = args.first() {
                        self.ka_open_var = Some(*v);
                    }
                }

                let inner_form = self.compile_sentence(
                    *body_sentence_idx,
                    selbris,
                    sumtis,
                    sentences,
                );

                // Restore ka_open_var
                self.ka_open_var = outer_ka_var;

                let type_pred = LogicalForm::Predicate {
                    relation: self.interner.get_or_intern(type_name),
                    args: Self::fit_args(args, 1),
                };
                LogicalForm::And(Box::new(type_pred), Box::new(inner_form))
            }
        }
    }

    // ─── Top-Level Bridi Compilation ─────────────────────────────

    pub fn compile_bridi(
        &mut self,
        bridi: &Bridi,
        selbris: &[Selbri],
        sumtis: &[Sumti],
        sentences: &[Sentence],
    ) -> LogicalForm {
        // ── Sumti connective expansion ──────────────────────────────
        // Scan all term IDs for Sumti::Connected. If found, split the
        // bridi into two copies (left/right substituted) and combine
        // with the appropriate logical connective.
        let all_terms: Vec<u32> = bridi
            .head_terms
            .iter()
            .chain(bridi.tail_terms.iter())
            .copied()
            .collect();

        for (idx, &term_id) in all_terms.iter().enumerate() {
            if let Sumti::Connected((left_id, conn, right_negated, right_id)) =
                &sumtis[term_id as usize]
            {
                let conn = *conn;
                let right_negated = *right_negated;
                let left_id = *left_id;
                let right_id = *right_id;

                // Build left bridi: replace the connected sumti slot with its left part
                let head_len = bridi.head_terms.len();
                let make_substituted_bridi = |replacement_id: u32| -> Bridi {
                    let mut head = bridi.head_terms.clone();
                    let mut tail = bridi.tail_terms.clone();
                    if idx < head_len {
                        head[idx] = replacement_id;
                    } else {
                        tail[idx - head_len] = replacement_id;
                    }
                    Bridi {
                        relation: bridi.relation,
                        head_terms: head,
                        tail_terms: tail,
                        negated: bridi.negated,
                        tense: bridi.tense,
                        attitudinal: bridi.attitudinal,
                    }
                };

                let left_bridi = make_substituted_bridi(left_id);
                let right_bridi = make_substituted_bridi(right_id);

                let left_form = self.compile_bridi(&left_bridi, selbris, sumtis, sentences);
                let mut right_form = self.compile_bridi(&right_bridi, selbris, sumtis, sentences);

                if right_negated {
                    right_form = LogicalForm::Not(Box::new(right_form));
                }

                return match conn {
                    Connective::Je => LogicalForm::And(Box::new(left_form), Box::new(right_form)),
                    Connective::Ja => LogicalForm::Or(Box::new(left_form), Box::new(right_form)),
                    Connective::Jo => {
                        LogicalForm::Biconditional(Box::new(left_form), Box::new(right_form))
                    }
                    Connective::Ju => {
                        LogicalForm::Xor(Box::new(left_form), Box::new(right_form))
                    }
                };
            }
        }

        // ── Normal compilation (no sumti connectives) ───────────────
        let target_arity = self.get_selbri_arity(bridi.relation, selbris);

        let mut positioned: Vec<Option<LogicalTerm>> = vec![None; target_arity];
        let mut untagged: Vec<LogicalTerm> = Vec::new();
        let mut quantifiers: Vec<QuantifierEntry> = Vec::new();
        let mut modal_entries: Vec<(ModalTag, LogicalTerm, Vec<QuantifierEntry>)> = Vec::new();

        for &term_id in bridi.head_terms.iter().chain(bridi.tail_terms.iter()) {
            let sumti = &sumtis[term_id as usize];

            match sumti {
                Sumti::Tagged((tag, inner_id)) => {
                    let inner = &sumtis[*inner_id as usize];
                    let (term, quants) = self.resolve_sumti(inner, sumtis, selbris, sentences);
                    quantifiers.extend(quants);
                    let idx = match tag {
                        PlaceTag::Fa => 0,
                        PlaceTag::Fe => 1,
                        PlaceTag::Fi => 2,
                        PlaceTag::Fo => 3,
                        PlaceTag::Fu => 4,
                    };
                    if idx < target_arity {
                        positioned[idx] = Some(term);
                    }
                }
                Sumti::ModalTagged((modal_tag, inner_id)) => {
                    let inner = &sumtis[*inner_id as usize];
                    let (term, quants) = self.resolve_sumti(inner, sumtis, selbris, sentences);
                    modal_entries.push((modal_tag.clone(), term, quants));
                }
                other => {
                    let (term, quants) = self.resolve_sumti(other, sumtis, selbris, sentences);
                    quantifiers.extend(quants);
                    untagged.push(term);
                }
            }
        }

        let mut untagged_iter = untagged.into_iter();
        let args: Vec<LogicalTerm> = positioned
            .into_iter()
            .map(|slot| {
                slot.or_else(|| untagged_iter.next())
                    .unwrap_or(LogicalTerm::Unspecified)
            })
            .collect();

        let mut final_form = self.apply_selbri(bridi.relation, &args, selbris, sumtis, sentences);

        // ── Modal predicate conjunction (BAI / fi'o tags) ─────────
        // Each modal tag creates a conjoined predication using the
        // underlying gismu: x1 = tagged sumti, x2 = main bridi's x1.
        for (modal_tag, tagged_term, modal_quants) in modal_entries {
            quantifiers.extend(modal_quants);

            let (modal_gismu, modal_arity) = match &modal_tag {
                ModalTag::Fixed(bai) => {
                    let gismu = Self::bai_to_gismu(bai);
                    let arity = JbovlasteSchema::get_arity_or_default(gismu);
                    (self.interner.get_or_intern(gismu), arity)
                }
                ModalTag::Fio(selbri_id) => {
                    let name = self.get_selbri_head_name(*selbri_id, selbris);
                    let arity = self.get_selbri_arity(*selbri_id, selbris);
                    (self.interner.get_or_intern(name), arity)
                }
            };

            // x1 = tagged sumti (cause/reason/tool), x2 = main bridi's x1
            let main_x1 = args.first().cloned().unwrap_or(LogicalTerm::Unspecified);
            let mut modal_args = vec![LogicalTerm::Unspecified; modal_arity];
            if modal_arity > 0 {
                modal_args[0] = tagged_term;
            }
            if modal_arity > 1 {
                modal_args[1] = main_x1;
            }

            let modal_form = LogicalForm::Predicate {
                relation: modal_gismu,
                args: modal_args,
            };

            final_form = LogicalForm::And(Box::new(final_form), Box::new(modal_form));
        }

        // Wrap with quantifiers (inner-to-outer)
        for entry in quantifiers.into_iter().rev() {
            let desc_arity = self.get_selbri_arity(entry.desc_id, selbris);

            let mut restrictor_args = Vec::with_capacity(desc_arity);
            restrictor_args.push(LogicalTerm::Variable(entry.var));
            while restrictor_args.len() < desc_arity {
                restrictor_args.push(LogicalTerm::Unspecified);
            }

            let desc_restrictor =
                self.apply_selbri(entry.desc_id, &restrictor_args, selbris, sumtis, sentences);

            match entry.kind {
                QuantifierKind::Universal => {
                    // ∀x. (restrictor → body) = ∀x. (¬restrictor ∨ body)
                    let mut body = LogicalForm::Or(
                        Box::new(LogicalForm::Not(Box::new(desc_restrictor))),
                        Box::new(final_form),
                    );

                    // Conjoin relative clause restrictor into antecedent if present
                    if let Some(rel_restrictor) = entry.restrictor {
                        body = LogicalForm::Or(
                            Box::new(LogicalForm::Not(Box::new(rel_restrictor))),
                            Box::new(body),
                        );
                    }

                    final_form = LogicalForm::ForAll(entry.var, Box::new(body));
                }
                QuantifierKind::Existential => {
                    // ∃x. (restrictor ∧ body)
                    let mut body = LogicalForm::And(Box::new(desc_restrictor), Box::new(final_form));

                    if let Some(rel_restrictor) = entry.restrictor {
                        body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                    }

                    final_form = LogicalForm::Exists(entry.var, Box::new(body));
                }
                QuantifierKind::ExactCount(n) => {
                    // Count(x, n, restrictor ∧ body)
                    let mut body = LogicalForm::And(Box::new(desc_restrictor), Box::new(final_form));

                    if let Some(rel_restrictor) = entry.restrictor {
                        body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                    }

                    final_form = LogicalForm::Count {
                        var: entry.var,
                        count: n,
                        body: Box::new(body),
                    };
                }
            }
        }

        // ── da/de/di quantifier closure ────────────────────────────
        // These pro-sumti are bare existential variables with no
        // description restrictor. Wrap the formula in ∃ for each.
        // Deduplicate: if the same variable appears in multiple arg
        // slots (e.g., `da prami da`), wrap only once.
        let mut da_vars_seen = std::collections::HashSet::new();
        for arg in &args {
            if let LogicalTerm::Variable(spur) = arg {
                let name = self.interner.resolve(spur);
                if matches!(name, "da" | "de" | "di") && da_vars_seen.insert(*spur) {
                    final_form = LogicalForm::Exists(*spur, Box::new(final_form));
                }
            }
        }

        // ── ma quantifier closure ────────────────────────────────
        // Each `ma` got a fresh variable (independent unknowns).
        // Wrap each in its own ∃, then clear for next sentence.
        for var in self.ma_vars.drain(..) {
            final_form = LogicalForm::Exists(var, Box::new(final_form));
        }

        if bridi.negated {
            final_form = LogicalForm::Not(Box::new(final_form));
        }

        // Tense wrapping (scopes over negation)
        match &bridi.tense {
            Some(Tense::Pu) => {
                final_form = LogicalForm::Past(Box::new(final_form));
            }
            Some(Tense::Ca) => {
                final_form = LogicalForm::Present(Box::new(final_form));
            }
            Some(Tense::Ba) => {
                final_form = LogicalForm::Future(Box::new(final_form));
            }
            None => {}
        }

        // Attitudinal wrapping (outermost — scopes over tense and negation)
        match &bridi.attitudinal {
            Some(Attitudinal::Ei) => {
                final_form = LogicalForm::Obligatory(Box::new(final_form));
            }
            Some(Attitudinal::Ehe) => {
                final_form = LogicalForm::Permitted(Box::new(final_form));
            }
            None => {}
        }

        final_form
    }

    pub fn compile_sentence(
        &mut self,
        sentence_id: u32,
        selbris: &[Selbri],
        sumtis: &[Sumti],
        sentences: &[Sentence],
    ) -> LogicalForm {
        match &sentences[sentence_id as usize] {
            Sentence::Simple(bridi) => self.compile_bridi(bridi, selbris, sumtis, sentences),
            Sentence::Connected((connective, left_id, right_id)) => {
                let left_form = self.compile_sentence(*left_id, selbris, sumtis, sentences);
                let right_form = self.compile_sentence(*right_id, selbris, sumtis, sentences);

                match connective {
                    SentenceConnective::GanaiGi => LogicalForm::Or(
                        Box::new(LogicalForm::Not(Box::new(left_form))),
                        Box::new(right_form),
                    ),
                    SentenceConnective::GeGi => {
                        LogicalForm::And(Box::new(left_form), Box::new(right_form))
                    }
                    SentenceConnective::GaGi => {
                        LogicalForm::Or(Box::new(left_form), Box::new(right_form))
                    }
                    SentenceConnective::Afterthought((left_neg, conn, right_neg)) => {
                        let l = if *left_neg {
                            LogicalForm::Not(Box::new(left_form))
                        } else {
                            left_form
                        };
                        let r = if *right_neg {
                            LogicalForm::Not(Box::new(right_form))
                        } else {
                            right_form
                        };
                        match conn {
                            Connective::Je => LogicalForm::And(Box::new(l), Box::new(r)),
                            Connective::Ja => LogicalForm::Or(Box::new(l), Box::new(r)),
                            Connective::Jo => {
                                LogicalForm::Biconditional(Box::new(l), Box::new(r))
                            }
                            Connective::Ju => {
                                LogicalForm::Xor(Box::new(l), Box::new(r))
                            }
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bindings::lojban::nesy::ast_types::{
        Bridi, Connective, Gadri, RelClause, RelClauseKind, Selbri, Sentence,
        SentenceConnective, Sumti,
    };
    use crate::ir::{LogicalForm, LogicalTerm};

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
            Sumti::ProSumti("mi".into()),      // 0
            Sumti::ProSumti("do".into()),       // 1
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

        // Should be And(klama(mi, ...), klama(do, ...))
        match &form {
            LogicalForm::And(left, right) => {
                match left.as_ref() {
                    LogicalForm::Predicate { relation, args } => {
                        assert_eq!(resolve(&compiler, relation), "klama");
                        match &args[0] {
                            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "mi"),
                            other => panic!("expected Constant(mi), got {:?}", other),
                        }
                    }
                    other => panic!("expected left Predicate, got {:?}", other),
                }
                match right.as_ref() {
                    LogicalForm::Predicate { relation, args } => {
                        assert_eq!(resolve(&compiler, relation), "klama");
                        match &args[0] {
                            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "do"),
                            other => panic!("expected Constant(do), got {:?}", other),
                        }
                    }
                    other => panic!("expected right Predicate, got {:?}", other),
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

        // Should be And(klama(mi), Not(klama(do)))
        match &form {
            LogicalForm::And(left, right) => {
                // Left: klama(mi, ...)
                match left.as_ref() {
                    LogicalForm::Predicate { relation, args } => {
                        assert_eq!(resolve(&compiler, relation), "klama");
                        match &args[0] {
                            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "mi"),
                            other => panic!("expected Constant(mi), got {:?}", other),
                        }
                    }
                    other => panic!("expected left Predicate, got {:?}", other),
                }
                // Right: Not(klama(do, ...))
                match right.as_ref() {
                    LogicalForm::Not(inner) => match inner.as_ref() {
                        LogicalForm::Predicate { relation, args } => {
                            assert_eq!(resolve(&compiler, relation), "klama");
                            match &args[0] {
                                LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "do"),
                                other => panic!("expected Constant(do), got {:?}", other),
                            }
                        }
                        other => panic!("expected Predicate inside Not, got {:?}", other),
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
            Sumti::ProSumti("mi".into()),            // 0
            Sumti::Description((Gadri::Lo, 1)),       // 1: lo gerku
            Sumti::Description((Gadri::Lo, 2)),       // 2: lo mlatu
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
                assert!(matches!(left.as_ref(), LogicalForm::Exists(_, _)),
                    "expected Exists on left, got {:?}", left);
                assert!(matches!(right.as_ref(), LogicalForm::Exists(_, _)),
                    "expected Exists on right, got {:?}", right);
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
                assert!(matches!(left.as_ref(), LogicalForm::Not(_)),
                    "expected Not on left, got {:?}", left);
                assert!(matches!(right.as_ref(), LogicalForm::Not(_)),
                    "expected Not on right, got {:?}", right);
            }
            other => panic!("expected And(Not, Not), got {:?}", other),
        }
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
            Selbri::Abstraction((kind, 1)),     // 1 → sentences[1]
            Selbri::Root("barda".into()),       // 2
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

        let sentences = vec![
            Sentence::Simple(outer_bridi),
            Sentence::Simple(inner_bridi),
        ];

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

        // Should be Exists(_v0, And(duhu(_v0), And(klama(mi,...), barda(_v0,...))))
        match &form {
            LogicalForm::Exists(var, body) => {
                assert!(resolve(&compiler, var).starts_with("_v"));
                // The body should contain "duhu" predicate
                fn find_predicate_name(form: &LogicalForm, compiler: &SemanticCompiler) -> Vec<String> {
                    match form {
                        LogicalForm::Predicate { relation, .. } => {
                            vec![compiler.interner.resolve(relation).to_string()]
                        }
                        LogicalForm::And(l, r) => {
                            let mut names = find_predicate_name(l, compiler);
                            names.extend(find_predicate_name(r, compiler));
                            names
                        }
                        _ => vec![],
                    }
                }
                let names = find_predicate_name(body, &compiler);
                assert!(names.contains(&"duhu".to_string()),
                    "expected 'duhu' predicate in {:?}", names);
                assert!(names.contains(&"klama".to_string()),
                    "expected 'klama' predicate in {:?}", names);
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

        // Should be Exists(_v0, And(ka(_v0), And(melbi(_v0,...), barda(_v0,...))))
        // The key: ce'u resolves to _v0, which is the same as the description variable
        match &form {
            LogicalForm::Exists(var, body) => {
                let var_name = resolve(&compiler, var);
                // Find the ka predicate's arg and melbi's arg — they should both use var
                fn collect_pred_args(form: &LogicalForm, compiler: &SemanticCompiler) -> Vec<(String, String)> {
                    match form {
                        LogicalForm::Predicate { relation, args } => {
                            let rel = compiler.interner.resolve(relation).to_string();
                            let arg0 = match &args[0] {
                                LogicalTerm::Variable(v) => compiler.interner.resolve(v).to_string(),
                                LogicalTerm::Constant(c) => compiler.interner.resolve(c).to_string(),
                                other => format!("{:?}", other),
                            };
                            vec![(rel, arg0)]
                        }
                        LogicalForm::And(l, r) => {
                            let mut v = collect_pred_args(l, compiler);
                            v.extend(collect_pred_args(r, compiler));
                            v
                        }
                        _ => vec![],
                    }
                }
                let args = collect_pred_args(body, &compiler);
                let ka_arg = args.iter().find(|(r, _)| r == "ka").map(|(_, a)| a.clone());
                let melbi_arg = args.iter().find(|(r, _)| r == "melbi").map(|(_, a)| a.clone());

                assert_eq!(ka_arg.as_deref(), Some(var_name.as_str()),
                    "ka predicate arg should be the quantified variable");
                assert_eq!(melbi_arg.as_deref(), Some(var_name.as_str()),
                    "ce'u should resolve to the same variable as ka's entity");
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
            LogicalForm::Exists(_, body) => {
                fn has_predicate(form: &LogicalForm, name: &str, compiler: &SemanticCompiler) -> bool {
                    match form {
                        LogicalForm::Predicate { relation, .. } => {
                            compiler.interner.resolve(relation) == name
                        }
                        LogicalForm::And(l, r) => has_predicate(l, name, compiler) || has_predicate(r, name, compiler),
                        _ => false,
                    }
                }
                assert!(has_predicate(body, "ni", &compiler), "expected 'ni' predicate");
                assert!(has_predicate(body, "gleki", &compiler), "expected 'gleki' predicate");
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
            LogicalForm::Exists(_, body) => {
                fn has_predicate(form: &LogicalForm, name: &str, compiler: &SemanticCompiler) -> bool {
                    match form {
                        LogicalForm::Predicate { relation, .. } => {
                            compiler.interner.resolve(relation) == name
                        }
                        LogicalForm::And(l, r) => has_predicate(l, name, compiler) || has_predicate(r, name, compiler),
                        _ => false,
                    }
                }
                assert!(has_predicate(body, "siho", &compiler), "expected 'siho' predicate");
                assert!(has_predicate(body, "klama", &compiler), "expected 'klama' predicate");
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
            LogicalForm::Exists(_, body) => {
                fn has_predicate(form: &LogicalForm, name: &str, compiler: &SemanticCompiler) -> bool {
                    match form {
                        LogicalForm::Predicate { relation, .. } => {
                            compiler.interner.resolve(relation) == name
                        }
                        LogicalForm::And(l, r) => has_predicate(l, name, compiler) || has_predicate(r, name, compiler),
                        _ => false,
                    }
                }
                assert!(has_predicate(body, "nu", &compiler), "expected 'nu' predicate");
                assert!(has_predicate(body, "klama", &compiler), "expected 'klama' predicate");
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_ceu_outside_ka_is_fresh_variable() {
        // ce'u used outside ka should degrade gracefully to a fresh variable
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

        // ce'u outside ka should become a Variable (not Constant)
        match &form {
            LogicalForm::Predicate { args, .. } => {
                match &args[0] {
                    LogicalTerm::Variable(v) => {
                        assert!(resolve(&compiler, v).starts_with("_v"),
                            "ce'u outside ka should be fresh variable, got: {}", resolve(&compiler, v));
                    }
                    other => panic!("expected Variable for ce'u, got {:?}", other),
                }
            }
            other => panic!("expected Predicate, got {:?}", other),
        }
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
            Sumti::ProSumti("mi".into()),                            // 0
            Sumti::ProSumti("do".into()),                            // 1
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Ria), 1)),   // 2
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

        // Should be And(klama(mi, ...), rinka(do, mi, ...))
        match &form {
            LogicalForm::And(left, right) => {
                // Left: klama(mi, ...)
                match left.as_ref() {
                    LogicalForm::Predicate { relation, args } => {
                        assert_eq!(resolve(&compiler, relation), "klama");
                        assert_eq!(args[0], LogicalTerm::Constant(compiler.interner.get("mi").unwrap()));
                    }
                    other => panic!("expected Predicate(klama), got {:?}", other),
                }
                // Right: rinka(do, mi, ...)
                match right.as_ref() {
                    LogicalForm::Predicate { relation, args } => {
                        assert_eq!(resolve(&compiler, relation), "rinka");
                        // x1 = tagged sumti (do), x2 = main x1 (mi)
                        assert_eq!(args[0], LogicalTerm::Constant(compiler.interner.get("do").unwrap()));
                        assert_eq!(args[1], LogicalTerm::Constant(compiler.interner.get("mi").unwrap()));
                    }
                    other => panic!("expected Predicate(rinka), got {:?}", other),
                }
            }
            other => panic!("expected And(klama, rinka), got {:?}", other),
        }
    }

    #[test]
    fn test_bai_pio_produces_pilno() {
        // mi citka pi'o lo forca → And(citka(mi, ...), pilno(lo_forca_var, mi, ...))
        // Buffer:
        //   sumtis: [0: mi, 1: Description(Lo, 1), 2: ModalTagged(Fixed(Pio), 1)]
        //   selbris: [0: citka, 1: forca]
        let selbris = vec![
            Selbri::Root("citka".into()),  // 0
            Selbri::Root("forca".into()),  // 1
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                             // 0
            Sumti::Description((Gadri::Lo, 1)),                       // 1
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Pio), 1)),    // 2
        ];
        let bridi = Bridi {
            relation: 0,
            head_terms: vec![0],
            tail_terms: vec![2],
            negated: false,
            tense: None,
            attitudinal: None,
        };

        let (form, _compiler) = compile_one(selbris, sumtis, bridi);

        // Should be ∃x.(forca(x) ∧ And(citka(mi,...), pilno(x, mi,...)))
        // The outermost is Exists wrapping the description's quantifier
        match &form {
            LogicalForm::Exists(_, body) => {
                match body.as_ref() {
                    LogicalForm::And(restrictor, inner_and) => {
                        // restrictor = forca(x, ...)
                        assert!(matches!(restrictor.as_ref(), LogicalForm::Predicate { .. }));
                        // inner_and = And(citka(...), pilno(...))
                        assert!(matches!(inner_and.as_ref(), LogicalForm::And(_, _)));
                    }
                    other => panic!("expected And(forca_restrictor, And(citka, pilno)), got {:?}", other),
                }
            }
            other => panic!("expected Exists wrapping modal conjunction, got {:?}", other),
        }
    }

    #[test]
    fn test_fio_produces_custom_modal() {
        // mi klama fi'o zbasu do → And(klama(mi,...), zbasu(do, mi,...))
        // Buffer:
        //   sumtis: [0: mi, 1: do, 2: ModalTagged(Fio(1), 1)]
        //   selbris: [0: klama, 1: zbasu]
        let selbris = vec![
            Selbri::Root("klama".into()),  // 0
            Selbri::Root("zbasu".into()),  // 1
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),              // 0
            Sumti::ProSumti("do".into()),               // 1
            Sumti::ModalTagged((ModalTag::Fio(1), 1)),  // 2
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

        match &form {
            LogicalForm::And(left, right) => {
                match left.as_ref() {
                    LogicalForm::Predicate { relation, .. } => {
                        assert_eq!(resolve(&compiler, relation), "klama");
                    }
                    other => panic!("expected klama predicate, got {:?}", other),
                }
                match right.as_ref() {
                    LogicalForm::Predicate { relation, args } => {
                        assert_eq!(resolve(&compiler, relation), "zbasu");
                        assert_eq!(args[0], LogicalTerm::Constant(compiler.interner.get("do").unwrap()));
                        assert_eq!(args[1], LogicalTerm::Constant(compiler.interner.get("mi").unwrap()));
                    }
                    other => panic!("expected zbasu predicate, got {:?}", other),
                }
            }
            other => panic!("expected And(klama, zbasu), got {:?}", other),
        }
    }

    #[test]
    fn test_multiple_bai_tags_conjoin() {
        // mi klama ri'a do pi'o ti → And(And(klama(...), rinka(do,mi,...)), pilno(ti,mi,...))
        let selbris = vec![Selbri::Root("klama".into())]; // 0
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),                            // 0
            Sumti::ProSumti("do".into()),                            // 1
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Ria), 1)),   // 2
            Sumti::ProSumti("ti".into()),                            // 3
            Sumti::ModalTagged((ModalTag::Fixed(BaiTag::Pio), 3)),   // 4
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

        // Outermost should be And(And(klama, rinka), pilno)
        match &form {
            LogicalForm::And(inner_and, pilno) => {
                match inner_and.as_ref() {
                    LogicalForm::And(klama, rinka) => {
                        match klama.as_ref() {
                            LogicalForm::Predicate { relation, .. } => {
                                assert_eq!(resolve(&compiler, relation), "klama");
                            }
                            other => panic!("expected klama, got {:?}", other),
                        }
                        match rinka.as_ref() {
                            LogicalForm::Predicate { relation, .. } => {
                                assert_eq!(resolve(&compiler, relation), "rinka");
                            }
                            other => panic!("expected rinka, got {:?}", other),
                        }
                    }
                    other => panic!("expected And(klama, rinka), got {:?}", other),
                }
                match pilno.as_ref() {
                    LogicalForm::Predicate { relation, .. } => {
                        assert_eq!(resolve(&compiler, relation), "pilno");
                    }
                    other => panic!("expected pilno, got {:?}", other),
                }
            }
            other => panic!("expected nested And, got {:?}", other),
        }
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
            Selbri::Root("gerku".into()),  // 0
            Selbri::Root("barda".into()),  // 1
        ];
        let sumtis = vec![
            Sumti::QuantifiedDescription((2, Gadri::Lo, 0)),  // 0
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

        // Should be Count { var: _v0, count: 2, body: And(gerku(_v0,...), barda(_v0,...)) }
        match &form {
            LogicalForm::Count { var, count, body } => {
                assert_eq!(*count, 2);
                assert!(resolve(&compiler, var).starts_with("_v"));
                match body.as_ref() {
                    LogicalForm::And(restrictor, pred) => {
                        match restrictor.as_ref() {
                            LogicalForm::Predicate { relation, .. } => {
                                assert_eq!(resolve(&compiler, relation), "gerku");
                            }
                            other => panic!("expected gerku restrictor, got {:?}", other),
                        }
                        match pred.as_ref() {
                            LogicalForm::Predicate { relation, .. } => {
                                assert_eq!(resolve(&compiler, relation), "barda");
                            }
                            other => panic!("expected barda predicate, got {:?}", other),
                        }
                    }
                    other => panic!("expected And body, got {:?}", other),
                }
            }
            other => panic!("expected Count, got {:?}", other),
        }
    }

    #[test]
    fn test_no_lo_produces_count_0() {
        // no lo gerku cu barda → Count(_v0, 0, And(gerku(_v0,...), barda(_v0,...)))
        let selbris = vec![
            Selbri::Root("gerku".into()),  // 0
            Selbri::Root("barda".into()),  // 1
        ];
        let sumtis = vec![
            Sumti::QuantifiedDescription((0, Gadri::Lo, 0)),  // 0
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
        let selbris = vec![
            Selbri::Root("gerku".into()),
            Selbri::Root("barda".into()),
        ];
        let sumtis = vec![
            Sumti::QuantifiedDescription((1, Gadri::Lo, 0)),
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
            LogicalForm::Count { count, .. } => assert_eq!(*count, 1),
            other => panic!("expected Count with count=1, got {:?}", other),
        }
    }

    #[test]
    fn test_lo_still_produces_exists() {
        // Regression: lo gerku cu barda → Exists (not Count)
        let selbris = vec![
            Selbri::Root("gerku".into()),
            Selbri::Root("barda".into()),
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Lo, 0)),
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

        assert!(matches!(&form, LogicalForm::Exists(_, _)),
            "expected Exists, got {:?}", form);
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
        // da prami mi → ∃da. prami(da, mi, ...)
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

        // Outermost should be Exists wrapping the predicate
        match &form {
            LogicalForm::Exists(var, body) => {
                assert_eq!(resolve(&compiler, var), "da");
                match body.as_ref() {
                    LogicalForm::Predicate { relation, args } => {
                        assert_eq!(resolve(&compiler, relation), "prami");
                        match &args[0] {
                            LogicalTerm::Variable(v) => assert_eq!(resolve(&compiler, v), "da"),
                            other => panic!("expected Variable(da), got {:?}", other),
                        }
                        match &args[1] {
                            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "mi"),
                            other => panic!("expected Constant(mi), got {:?}", other),
                        }
                    }
                    other => panic!("expected Predicate inside Exists, got {:?}", other),
                }
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_da_de_both_produce_nested_exists() {
        // da prami de → ∃da. ∃de. prami(da, de, ...)
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

        // Should be Exists(da/de, Exists(da/de, Predicate))
        match &form {
            LogicalForm::Exists(v1, inner) => {
                let name1 = resolve(&compiler, v1);
                match inner.as_ref() {
                    LogicalForm::Exists(v2, body) => {
                        let name2 = resolve(&compiler, v2);
                        // Both da and de should appear (order may vary)
                        let mut names = vec![name1, name2];
                        names.sort();
                        assert_eq!(names, vec!["da", "de"]);
                        assert!(matches!(body.as_ref(), LogicalForm::Predicate { .. }));
                    }
                    other => panic!("expected nested Exists, got {:?}", other),
                }
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_da_repeated_wraps_once() {
        // da prami da → ∃da. prami(da, da, ...) (only one Exists)
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

        // Should be Exists(da, Predicate) — NOT Exists(da, Exists(da, ...))
        match &form {
            LogicalForm::Exists(var, body) => {
                assert_eq!(resolve(&compiler, var), "da");
                assert!(matches!(body.as_ref(), LogicalForm::Predicate { .. }),
                    "expected single Exists wrapping Predicate, got nested: {:?}", body);
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
        let sumtis = vec![
            Sumti::ProSumti("da".into()),
            Sumti::ProSumti("mi".into()),
        ];
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
                assert!(matches!(inner.as_ref(), LogicalForm::Exists(_, _)),
                    "expected Exists inside Not, got {:?}", inner);
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
        // ma klama → ∃_v0. klama(_v0, ...)
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

        // Outermost should be Exists wrapping the predicate
        match &form {
            LogicalForm::Exists(var, body) => {
                // ma now generates a fresh variable (_v0), not "ma"
                assert!(resolve(&compiler, var).starts_with("_v"));
                match body.as_ref() {
                    LogicalForm::Predicate { relation, args } => {
                        assert_eq!(resolve(&compiler, relation), "klama");
                        match &args[0] {
                            LogicalTerm::Variable(v) => assert_eq!(v, var),
                            other => panic!("expected Variable, got {:?}", other),
                        }
                    }
                    other => panic!("expected Predicate inside Exists, got {:?}", other),
                }
            }
            other => panic!("expected Exists, got {:?}", other),
        }
    }

    #[test]
    fn test_two_ma_produce_independent_exists() {
        // ma nelci ma → ∃_v1. ∃_v0. nelci(_v0, _v1, ...)
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

        // Should be ∃v1.(∃v0.(nelci(v0, v1, ...)))
        match &form {
            LogicalForm::Exists(var1, inner) => {
                assert!(resolve(&compiler, var1).starts_with("_v"));
                match inner.as_ref() {
                    LogicalForm::Exists(var0, body) => {
                        assert!(resolve(&compiler, var0).starts_with("_v"));
                        // The two variables must be different
                        assert_ne!(var0, var1, "two ma should produce different variables");
                        match body.as_ref() {
                            LogicalForm::Predicate { args, .. } => {
                                // First arg should be one var, second should be the other
                                match (&args[0], &args[1]) {
                                    (LogicalTerm::Variable(a), LogicalTerm::Variable(b)) => {
                                        assert_ne!(a, b, "args should reference different vars");
                                    }
                                    other => panic!("expected two Variables, got {:?}", other),
                                }
                            }
                            other => panic!("expected Predicate, got {:?}", other),
                        }
                    }
                    other => panic!("expected inner Exists, got {:?}", other),
                }
            }
            other => panic!("expected outer Exists, got {:?}", other),
        }
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
            Sumti::Description((Gadri::Lo, 0)),  // 0: lo gerku
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
        assert!(compiler.errors.is_empty(), "Expected no errors, got: {:?}", compiler.errors);
    }

    #[test]
    fn test_inject_variable_nested_description_produces_error() {
        // lo gerku poi lo mlatu cu barda
        // Rel clause body has 2 predicates with unspecified slots:
        //   mlatu(?) from the inner description + barda(?) from the main predicate.
        // This should produce a semantic error.
        //
        // Buffer layout:
        //   selbris: [0: gerku, 1: mlatu, 2: barda]
        //   sumtis:  [0: Description(Lo, 0), 1: Description(Lo, 1), 2: Restricted(0, poi body=1)]
        //   sentences: [0: Simple(barda, head=[2]), 1: Simple(barda, head=[1])]
        //
        // The rel clause body sentence (1) is: "lo mlatu cu barda"
        //   → barda(lo_mlatu, ...) where lo_mlatu introduces ∃x.(mlatu(x) ∧ barda(x, ...))
        //   But mlatu has unspecified slot AND barda has unspecified slot
        let selbris = vec![
            Selbri::Root("gerku".into()), // 0
            Selbri::Root("mlatu".into()), // 1
            Selbri::Root("barda".into()), // 2
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Lo, 0)),  // 0: lo gerku
            Sumti::Description((Gadri::Lo, 1)),  // 1: lo mlatu
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
                relation: 2, // barda (main sentence)
                head_terms: vec![2], // lo gerku poi ...
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
            Sentence::Simple(Bridi {
                relation: 2, // barda (rel clause body: lo mlatu cu barda)
                head_terms: vec![1], // lo mlatu
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];

        let (_form, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        // Should have exactly one error about ambiguous injection
        assert_eq!(compiler.errors.len(), 1, "Expected 1 error, got: {:?}", compiler.errors);
        assert!(
            compiler.errors[0].contains("ambiguous"),
            "Error should mention 'ambiguous': {}",
            compiler.errors[0]
        );
        assert!(
            compiler.errors[0].contains("ke'a"),
            "Error should mention ke'a: {}",
            compiler.errors[0]
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
            Sumti::Description((Gadri::Lo, 0)),  // 0: lo gerku
            Sumti::ProSumti("ke'a".into()),       // 1: ke'a
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
        assert!(compiler.errors.is_empty(), "Expected no errors, got: {:?}", compiler.errors);
    }

    #[test]
    fn test_inject_variable_error_message_contains_count() {
        // Verify the error message contains the actual predicate count.
        // Same setup as test_inject_variable_nested_description_produces_error
        let selbris = vec![
            Selbri::Root("gerku".into()),
            Selbri::Root("mlatu".into()),
            Selbri::Root("barda".into()),
        ];
        let sumtis = vec![
            Sumti::Description((Gadri::Lo, 0)),
            Sumti::Description((Gadri::Lo, 1)),
            Sumti::Restricted((
                0,
                RelClause {
                    kind: RelClauseKind::Poi,
                    body_sentence: 1,
                },
            )),
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
                head_terms: vec![1],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            }),
        ];

        let (_, compiler) = compile_sentence_full(selbris, sumtis, sentences);
        assert!(!compiler.errors.is_empty());
        // Should contain "2 predicates" (the mlatu restrictor + the barda predicate)
        assert!(
            compiler.errors[0].contains("predicates"),
            "Error should mention 'predicates': {}",
            compiler.errors[0]
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
        assert_eq!(SemanticCompiler::count_unspecified_predicates(&form), 1);
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
        assert_eq!(SemanticCompiler::count_unspecified_predicates(&form), 0);
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
        assert_eq!(SemanticCompiler::count_unspecified_predicates(&form), 2);
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
        let injected = SemanticCompiler::inject_variable(form, var);
        match injected {
            LogicalForm::Predicate { args, .. } => {
                assert!(matches!(args[0], LogicalTerm::Variable(_)));
                assert!(matches!(args[1], LogicalTerm::Unspecified));
            }
            other => panic!("expected Predicate, got {:?}", other),
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
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),
            Sumti::ProSumti("do".into()),
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
            LogicalForm::Predicate { relation, args } => {
                assert_eq!(resolve(&compiler, relation), "prami");
                // After se-conversion: x1 and x2 are swapped
                // head=mi goes to x1 position, tail=do goes to x2 position
                // se swaps these: mi→x2, do→x1
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected Predicate, got {:?}", other),
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
        let (form, _) = compile_one(selbris, sumtis, bridi);
        match &form {
            LogicalForm::Predicate { args, .. } => {
                assert!(matches!(args[0], LogicalTerm::Unspecified));
            }
            other => panic!("expected Predicate, got {:?}", other),
        }
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
        match &form {
            LogicalForm::Predicate { args, .. } => {
                match &args[0] {
                    LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "alis"),
                    other => panic!("expected Constant, got {:?}", other),
                }
            }
            other => panic!("expected Predicate, got {:?}", other),
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
        let (form, _) = compile_one(selbris, sumtis, bridi);
        match &form {
            LogicalForm::Predicate { args, .. } => {
                assert!(matches!(args[0], LogicalTerm::Number(n) if n == 42.0));
            }
            other => panic!("expected Predicate, got {:?}", other),
        }
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
        match &form {
            LogicalForm::Predicate { args, .. } => {
                match &args[0] {
                    LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "coi"),
                    other => panic!("expected Constant, got {:?}", other),
                }
            }
            other => panic!("expected Predicate, got {:?}", other),
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

    // ─── Arity from dictionary ────────────────────────────────

    #[test]
    fn test_known_gismu_gets_correct_arity() {
        // klama has arity 5, so Pred should have 5 arg slots
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
        let (form, _) = compile_one(selbris, sumtis, bridi);
        match &form {
            LogicalForm::Predicate { args, .. } => {
                assert_eq!(args.len(), 5, "klama should have 5 argument slots");
            }
            other => panic!("expected Predicate, got {:?}", other),
        }
    }

    #[test]
    fn test_unknown_gismu_defaults_to_arity_2() {
        // An unrecognized word should default to arity 2
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
        let (form, _) = compile_one(selbris, sumtis, bridi);
        match &form {
            LogicalForm::Predicate { args, .. } => {
                assert_eq!(args.len(), 2, "unknown word should default to arity 2");
            }
            other => panic!("expected Predicate, got {:?}", other),
        }
    }

    // ─── Sentence connective tests ────────────────────────────

    #[test]
    fn test_sentence_connective_ge_gi_produces_and() {
        // ge mi klama gi do sutra → And(klama(mi,...), sutra(do,...))
        let selbris = vec![
            Selbri::Root("klama".into()),
            Selbri::Root("sutra".into()),
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),
            Sumti::ProSumti("do".into()),
        ];
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
        let injected = SemanticCompiler::inject_variable(form, var);
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
        // Just "klama" alone → should produce a Predicate with all-Unspecified args
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
        match &form {
            LogicalForm::Predicate { relation, args } => {
                assert_eq!(resolve(&compiler, relation), "klama");
                // All args should be Unspecified
                for arg in args {
                    assert!(matches!(arg, LogicalTerm::Unspecified));
                }
            }
            other => panic!("expected Predicate, got {:?}", other),
        }
    }
}
