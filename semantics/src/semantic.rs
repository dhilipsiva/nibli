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
    /// Monotonically increasing counter for generating fresh event variable names.
    event_counter: usize,
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
            event_counter: 0,
        }
    }

    fn fresh_var(&mut self) -> lasso::Spur {
        let v = format!("_v{}", self.var_counter);
        self.var_counter += 1;
        self.interner.get_or_intern(&v)
    }

    fn fresh_event_var(&mut self) -> lasso::Spur {
        let v = format!("_ev{}", self.event_counter);
        self.event_counter += 1;
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
                        let unspec_count =
                            Self::count_unspecified_predicates(&rel_body, &self.interner);
                        if unspec_count > 1 {
                            // Ambiguous injection — reject rather than silently produce wrong FOL.
                            self.errors.push(format!(
                                "Relative clause has {} predicates with unspecified slots; \
                                 implicit variable injection is ambiguous. Use explicit ke'a \
                                 for precise control.",
                                unspec_count
                            ));
                        }
                        last.restrictor =
                            Some(Self::inject_variable(rel_body, last.var, &self.interner));
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
    fn count_unspecified_predicates(form: &LogicalForm, interner: &Rodeo) -> usize {
        match form {
            LogicalForm::Predicate { relation, args } => {
                let rel_name = interner.resolve(relation);
                // For event role predicates (_xN), only count _x1 roles as injection targets
                if rel_name.contains("_x") {
                    if rel_name.ends_with("_x1")
                        && args.len() >= 2
                        && matches!(&args[1], LogicalTerm::Unspecified)
                    {
                        1
                    } else {
                        0
                    }
                } else if args.iter().any(|a| matches!(a, LogicalTerm::Unspecified)) {
                    // Non-role predicates: original behavior
                    1
                } else {
                    0
                }
            }
            LogicalForm::And(l, r)
            | LogicalForm::Or(l, r)
            | LogicalForm::Biconditional(l, r)
            | LogicalForm::Xor(l, r) => {
                Self::count_unspecified_predicates(l, interner)
                    + Self::count_unspecified_predicates(r, interner)
            }
            LogicalForm::Not(inner)
            | LogicalForm::Exists(_, inner)
            | LogicalForm::ForAll(_, inner)
            | LogicalForm::Past(inner)
            | LogicalForm::Present(inner)
            | LogicalForm::Future(inner)
            | LogicalForm::Obligatory(inner)
            | LogicalForm::Permitted(inner) => {
                Self::count_unspecified_predicates(inner, interner)
            }
            LogicalForm::Count { body, .. } => {
                Self::count_unspecified_predicates(body, interner)
            }
        }
    }

    /// Heuristic variable injection for relative clauses without explicit ke'a.
    ///
    /// For event-decomposed forms, only injects into `_x1` role predicates
    /// (the x1 place = the referent). Other role predicates (_x2, _x3, etc.)
    /// and type predicates are left unchanged.
    ///
    /// For non-event predicates, uses original behavior: replaces the first
    /// Unspecified slot.
    fn inject_variable(form: LogicalForm, var: lasso::Spur, interner: &Rodeo) -> LogicalForm {
        match form {
            LogicalForm::Predicate { relation, mut args } => {
                let rel_name = interner.resolve(&relation);
                if rel_name.contains("_x") {
                    // Event role predicate: only inject into _x1
                    if rel_name.ends_with("_x1") && args.len() >= 2 {
                        if matches!(&args[1], LogicalTerm::Unspecified) {
                            args[1] = LogicalTerm::Variable(var);
                        }
                    }
                    // Skip _x2, _x3, etc. — don't inject ke'a there
                } else {
                    // Non-role predicate (including 1-ary type predicates): original behavior
                    let first_unspec = args
                        .iter()
                        .position(|a| matches!(a, LogicalTerm::Unspecified));
                    if let Some(idx) = first_unspec {
                        args[idx] = LogicalTerm::Variable(var);
                    } else if args.is_empty() {
                        args.push(LogicalTerm::Variable(var));
                    }
                }
                LogicalForm::Predicate { relation, args }
            }
            LogicalForm::And(l, r) => LogicalForm::And(
                Box::new(Self::inject_variable(*l, var, interner)),
                Box::new(Self::inject_variable(*r, var, interner)),
            ),
            LogicalForm::Or(l, r) => LogicalForm::Or(
                Box::new(Self::inject_variable(*l, var, interner)),
                Box::new(Self::inject_variable(*r, var, interner)),
            ),
            LogicalForm::Biconditional(l, r) => LogicalForm::Biconditional(
                Box::new(Self::inject_variable(*l, var, interner)),
                Box::new(Self::inject_variable(*r, var, interner)),
            ),
            LogicalForm::Xor(l, r) => LogicalForm::Xor(
                Box::new(Self::inject_variable(*l, var, interner)),
                Box::new(Self::inject_variable(*r, var, interner)),
            ),
            LogicalForm::Not(inner) => {
                LogicalForm::Not(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            LogicalForm::Exists(v, body) => {
                LogicalForm::Exists(v, Box::new(Self::inject_variable(*body, var, interner)))
            }
            LogicalForm::ForAll(v, body) => {
                LogicalForm::ForAll(v, Box::new(Self::inject_variable(*body, var, interner)))
            }
            LogicalForm::Past(inner) => {
                LogicalForm::Past(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            LogicalForm::Present(inner) => {
                LogicalForm::Present(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            LogicalForm::Future(inner) => {
                LogicalForm::Future(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            LogicalForm::Obligatory(inner) => {
                LogicalForm::Obligatory(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            LogicalForm::Permitted(inner) => {
                LogicalForm::Permitted(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            LogicalForm::Count { var: v, count, body } => LogicalForm::Count {
                var: v,
                count,
                body: Box::new(Self::inject_variable(*body, var, interner)),
            },
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

    // ─── Event Decomposition (Neo-Davidsonian) ─────────────────

    /// Decompose a predication into Neo-Davidsonian event structure:
    /// `relation(a1, a2, ...)` → `∃e. relation(e) ∧ relation_x1(e, a1) ∧ relation_x2(e, a2) ∧ ...`
    /// All role predicates are emitted (including Unspecified/zo'e) so that
    /// inject_variable can still find and fill x1 slots for relative clauses.
    fn event_decompose(&mut self, relation: &str, args: &[LogicalTerm]) -> LogicalForm {
        let ev = self.fresh_event_var();
        let ev_term = LogicalTerm::Variable(ev);

        // Type predicate: relation(e)
        let type_pred = LogicalForm::Predicate {
            relation: self.interner.get_or_intern(relation),
            args: vec![ev_term.clone()],
        };

        // Role predicates: relation_xN(e, argN) for each arg
        let mut form = type_pred;
        for (i, arg) in args.iter().enumerate() {
            let role_name = format!("{}_x{}", relation, i + 1);
            let role_pred = LogicalForm::Predicate {
                relation: self.interner.get_or_intern(&role_name),
                args: vec![ev_term.clone(), arg.clone()],
            };
            form = LogicalForm::And(Box::new(form), Box::new(role_pred));
        }

        // Wrap in ∃e
        LogicalForm::Exists(ev, Box::new(form))
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
                let fitted = Self::fit_args(args, arity);
                self.event_decompose(g.as_str(), &fitted)
            }

            Selbri::Tanru((mod_id, head_id)) => {
                let mod_name = self.get_selbri_head_name(*mod_id, selbris);
                let head_name = self.get_selbri_head_name(*head_id, selbris);
                let mod_arity = self.get_selbri_arity(*mod_id, selbris);
                let head_arity = self.get_selbri_arity(*head_id, selbris);

                // Tanru semantics: modifier and head share ONLY x1 (the referent).
                // Neo-Davidsonian: modifier and head share the SAME event variable.
                // "sutra gerku" = ∃e. gerku(e) ∧ gerku_x1(e, x1) ∧ sutra_x1(e, x1)
                let mut mod_args = vec![LogicalTerm::Unspecified; mod_arity];
                if !args.is_empty() && mod_arity > 0 {
                    mod_args[0] = args[0].clone();
                }
                let head_args = Self::fit_args(args, head_arity);

                // Shared event variable
                let ev = self.fresh_event_var();
                let ev_term = LogicalTerm::Variable(ev);

                // Head type predicate: head(e)
                let type_pred = LogicalForm::Predicate {
                    relation: self.interner.get_or_intern(&head_name),
                    args: vec![ev_term.clone()],
                };
                let mut form = type_pred;

                // Head role predicates
                for (i, arg) in head_args.iter().enumerate() {
                    if matches!(arg, LogicalTerm::Unspecified) {
                        continue;
                    }
                    let role = format!("{}_x{}", head_name, i + 1);
                    let role_pred = LogicalForm::Predicate {
                        relation: self.interner.get_or_intern(&role),
                        args: vec![ev_term.clone(), arg.clone()],
                    };
                    form = LogicalForm::And(Box::new(form), Box::new(role_pred));
                }

                // Modifier role predicates (share event, x1 only typically)
                for (i, arg) in mod_args.iter().enumerate() {
                    if matches!(arg, LogicalTerm::Unspecified) {
                        continue;
                    }
                    let role = format!("{}_x{}", mod_name, i + 1);
                    let role_pred = LogicalForm::Predicate {
                        relation: self.interner.get_or_intern(&role),
                        args: vec![ev_term.clone(), arg.clone()],
                    };
                    form = LogicalForm::And(Box::new(form), Box::new(role_pred));
                }

                LogicalForm::Exists(ev, Box::new(form))
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
                let fitted = Self::fit_args(args, arity);
                self.event_decompose(head, &fitted)
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
            LogicalForm::And(l, r) | LogicalForm::Or(l, r) | LogicalForm::Biconditional(l, r)
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

        // Should be And(klama_event(mi), klama_event(do))
        // Each side is an event-decomposed form (Exists wrapping type+role preds)
        match &form {
            LogicalForm::And(left, right) => {
                // Left: event-decomposed klama with mi in x1
                assert!(has_pred(left, "klama", &compiler), "left should have klama type pred");
                let x1_args = get_pred_args(left, "klama_x1", &compiler).unwrap();
                match &x1_args[1] {
                    LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "mi"),
                    other => panic!("expected Constant(mi) in klama_x1, got {:?}", other),
                }
                // Right: event-decomposed klama with do in x1
                assert!(has_pred(right, "klama", &compiler), "right should have klama type pred");
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
                assert!(has_pred(left, "klama", &compiler), "left should have klama type pred");
                let x1_args = get_pred_args(left, "klama_x1", &compiler).unwrap();
                match &x1_args[1] {
                    LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "mi"),
                    other => panic!("expected Constant(mi) in klama_x1, got {:?}", other),
                }
                // Right: Not(klama_event(do))
                match right.as_ref() {
                    LogicalForm::Not(inner) => {
                        assert!(has_pred(inner, "klama", &compiler), "Not body should have klama type pred");
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

        // Should be Exists(_v0, And(duhu(_v0), And(klama_event, barda_event)))
        // With event decomposition, klama and barda are wrapped in Exists
        match &form {
            LogicalForm::Exists(var, _body) => {
                assert!(resolve(&compiler, var).starts_with("_v"));
                // Use the recursive helpers that descend into Exists
                assert!(has_pred(&form, "duhu", &compiler),
                    "expected 'duhu' predicate");
                assert!(has_pred(&form, "klama", &compiler),
                    "expected 'klama' type predicate");
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
                assert_eq!(ka_arg0, var_name,
                    "ka predicate arg should be the quantified variable");
                // melbi_x1 role pred should have the same variable as its entity arg
                let melbi_x1_args = get_pred_args(&form, "melbi_x1", &compiler).unwrap();
                let melbi_entity = match &melbi_x1_args[1] {
                    LogicalTerm::Variable(v) => resolve(&compiler, v),
                    other => panic!("expected Variable for melbi_x1 entity, got {:?}", other),
                };
                assert_eq!(melbi_entity, var_name,
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
            LogicalForm::Exists(_, _) => {
                // Use the recursive helpers that descend into Exists
                assert!(has_pred(&form, "ni", &compiler), "expected 'ni' predicate");
                assert!(has_pred(&form, "gleki", &compiler), "expected 'gleki' type predicate");
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
                assert!(has_pred(&form, "siho", &compiler), "expected 'siho' predicate");
                assert!(has_pred(&form, "klama", &compiler), "expected 'klama' type predicate");
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
                assert!(has_pred(&form, "klama", &compiler), "expected 'klama' type predicate");
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
        // With event decomposition, form is Exists(ev, And(type_pred, role_preds...))
        assert!(matches!(&form, LogicalForm::Exists(_, _)), "expected Exists, got {:?}", form);
        // Check the melbi_x1 role predicate has a Variable for ce'u
        let x1_args = get_pred_args(&form, "melbi_x1", &compiler)
            .expect("expected melbi_x1 role predicate");
        match &x1_args[1] {
            LogicalTerm::Variable(v) => {
                assert!(resolve(&compiler, v).starts_with("_v"),
                    "ce'u outside ka should be fresh variable, got: {}", resolve(&compiler, v));
            }
            other => panic!("expected Variable for ce'u in melbi_x1, got {:?}", other),
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

        // klama is event-decomposed, rinka is a flat modal Predicate
        assert!(has_pred(&form, "klama", &compiler), "expected klama type predicate");
        assert!(has_pred(&form, "klama_x1", &compiler), "expected klama_x1 role");
        // Check klama_x1 has mi
        let klama_x1 = get_pred_args(&form, "klama_x1", &compiler).unwrap();
        assert_eq!(klama_x1[1], LogicalTerm::Constant(compiler.interner.get("mi").unwrap()));
        // rinka is a flat Predicate (modal tags are not event-decomposed)
        let rinka_args = get_pred_args(&form, "rinka", &compiler).unwrap();
        // x1 = tagged sumti (do), x2 = main x1 (mi)
        assert_eq!(rinka_args[0], LogicalTerm::Constant(compiler.interner.get("do").unwrap()));
        assert_eq!(rinka_args[1], LogicalTerm::Constant(compiler.interner.get("mi").unwrap()));
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

        let (form, compiler) = compile_one(selbris, sumtis, bridi);

        // Should be ∃x.(forca_event(x) ∧ And(citka_event, pilno_event))
        // The outermost is Exists wrapping the description's quantifier
        match &form {
            LogicalForm::Exists(_, _) => {
                // Check all expected predicates exist (recursive through Exists)
                assert!(has_pred(&form, "forca", &compiler), "expected forca restrictor type pred");
                assert!(has_pred(&form, "citka", &compiler), "expected citka type pred");
                assert!(has_pred(&form, "pilno", &compiler), "expected pilno type pred");
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

        // klama is event-decomposed, zbasu is a flat modal Predicate
        assert!(has_pred(&form, "klama", &compiler), "expected klama type predicate");
        assert!(has_pred(&form, "zbasu", &compiler), "expected zbasu modal predicate");
        // zbasu is flat: zbasu(do, mi, ...)
        let zbasu_args = get_pred_args(&form, "zbasu", &compiler).unwrap();
        assert_eq!(zbasu_args[0], LogicalTerm::Constant(compiler.interner.get("do").unwrap()));
        assert_eq!(zbasu_args[1], LogicalTerm::Constant(compiler.interner.get("mi").unwrap()));
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

        // All three predicates should be present as event-decomposed forms
        assert!(has_pred(&form, "klama", &compiler), "expected klama type predicate");
        assert!(has_pred(&form, "rinka", &compiler), "expected rinka type predicate");
        assert!(has_pred(&form, "pilno", &compiler), "expected pilno type predicate");
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

        // Should be Count { var: _v0, count: 2, body: And(gerku_event, barda_event) }
        // With event decomposition, restrictor and predicate are event-wrapped
        match &form {
            LogicalForm::Count { var, count, body } => {
                assert_eq!(*count, 2);
                assert!(resolve(&compiler, var).starts_with("_v"));
                // The body should contain both gerku and barda type predicates
                assert!(has_pred(body, "gerku", &compiler), "expected gerku restrictor type pred");
                assert!(has_pred(body, "barda", &compiler), "expected barda type pred");
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
                assert!(has_pred(&form, "prami", &compiler), "expected prami type predicate");
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
                        assert!(has_pred(&form, "prami", &compiler), "expected prami type predicate");
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
                        assert!(resolve(&compiler, ev_var).starts_with("_ev"),
                            "expected event variable inside, got: {}", resolve(&compiler, ev_var));
                    }
                    other => panic!("expected Exists(ev, ...) inside Exists(da, ...), got {:?}", other),
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
                assert!(has_pred(&form, "klama", &compiler), "expected klama type predicate");
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
                            other => panic!("expected two Variables in role preds, got {:?}", other),
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
    fn test_inject_variable_nested_description_no_error_with_events() {
        // lo gerku poi lo mlatu cu barda
        // With event decomposition, the description variable fills the _x1 role slot,
        // so there is only 1 unspecified _x1 role (not 2). No ambiguity error.
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
        // With event decomposition, the description variable fills _x1 roles,
        // so inject_variable finds at most 1 unspecified _x1 target — no error.
        assert!(compiler.errors.is_empty(),
            "Expected no errors with event decomposition, got: {:?}", compiler.errors);
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
    fn test_inject_variable_no_error_with_event_decomposition() {
        // With event decomposition, the description variable fills _x1 role slots,
        // so nested descriptions no longer produce ambiguity errors.
        // Same setup as test_inject_variable_nested_description_no_error_with_events
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
        // With event decomposition, no ambiguity error is produced
        assert!(compiler.errors.is_empty(),
            "Expected no errors with event decomposition, got: {:?}", compiler.errors);
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
        // With event decomposition, form is Exists(ev, And(prami(ev), prami_x1(ev, ...), prami_x2(ev, ...)))
        // After se-conversion: x1 and x2 are swapped
        // head=mi goes to x1 position, tail=do goes to x2 position
        // se swaps these: mi→x2, do→x1
        assert!(matches!(&form, LogicalForm::Exists(_, _)), "expected Exists, got {:?}", form);
        assert!(has_pred(&form, "prami", &compiler), "expected prami type predicate");
        // Check prami_x1 has do (originally x2, swapped to x1)
        let x1_args = get_pred_args(&form, "prami_x1", &compiler).unwrap();
        match &x1_args[1] {
            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "do"),
            other => panic!("expected Constant(do) in prami_x1 after se-swap, got {:?}", other),
        }
        // Check prami_x2 has mi (originally x1, swapped to x2)
        let x2_args = get_pred_args(&form, "prami_x2", &compiler).unwrap();
        match &x2_args[1] {
            LogicalTerm::Constant(c) => assert_eq!(resolve(&compiler, c), "mi"),
            other => panic!("expected Constant(mi) in prami_x2 after se-swap, got {:?}", other),
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
        assert!(matches!(&form, LogicalForm::Exists(_, _)), "expected Exists, got {:?}", form);
        // Check that klama_x1 has Unspecified (zo'e) in its entity arg
        let x1_args = get_pred_args(&form, "klama_x1", &compiler)
            .expect("expected klama_x1 role predicate");
        assert!(matches!(x1_args[1], LogicalTerm::Unspecified),
            "expected Unspecified in klama_x1, got {:?}", x1_args[1]);
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
        assert_eq!(x1[1], LogicalTerm::Constant(compiler.interner.get("mi").unwrap()));
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
            Selbri::Root("sutra".into()),      // 0
            Selbri::Root("gerku".into()),       // 1
            Selbri::Tanru((0, 1)),              // 2
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
        assert_eq!(gerku_x1[0], sutra_x1[0], "event var should be shared between head and modifier");

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
            Selbri::Root("barda".into()),      // 0
            Selbri::Root("gerku".into()),       // 1
            Selbri::Tanru((0, 1)),              // 2
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
        assert!(barda_preds.is_empty(), "should NOT have standalone barda predicate, got {:?}", barda_preds);
        assert!(has_pred(&form, "barda_x1", &compiler), "should have event-bound barda_x1 role");
    }

    #[test]
    fn test_event_decompose_with_quantifier() {
        // lo gerku cu klama → ∃x. (∃e1. gerku(e1) ∧ gerku_x1(e1, x)) ∧ (∃e2. klama(e2) ∧ klama_x1(e2, x) ∧ ...)
        let selbris = vec![
            Selbri::Root("gerku".into()),       // 0
            Selbri::Root("klama".into()),       // 1
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
            Selbri::Root("prami".into()),       // 0
            Selbri::Converted((Conversion::Se, 0)), // 1
        ];
        let sumtis = vec![
            Sumti::ProSumti("mi".into()),       // 0
            Sumti::ProSumti("do".into()),        // 1
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
        assert_eq!(x1[1], LogicalTerm::Constant(compiler.interner.get("do").unwrap()));
        assert_eq!(x2[1], LogicalTerm::Constant(compiler.interner.get("mi").unwrap()));
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
        assert!(matches!(&form, LogicalForm::Exists(_, _)), "expected Exists, got {:?}", form);
        let x1_args = get_pred_args(&form, "klama_x1", &compiler)
            .expect("expected klama_x1 role predicate");
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
        assert!(matches!(&form, LogicalForm::Exists(_, _)), "expected Exists, got {:?}", form);
        let x1_args = get_pred_args(&form, "namcu_x1", &compiler)
            .expect("expected namcu_x1 role predicate");
        assert!(matches!(x1_args[1], LogicalTerm::Number(n) if n == 42.0),
            "expected Number(42.0) in namcu_x1, got {:?}", x1_args[1]);
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
        assert!(matches!(&form, LogicalForm::Exists(_, _)), "expected Exists, got {:?}", form);
        let x1_args = get_pred_args(&form, "valsi_x1", &compiler)
            .expect("expected valsi_x1 role predicate");
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
        assert!(matches!(&form, LogicalForm::Exists(_, _)), "expected Exists, got {:?}", form);
        assert!(has_pred(&form, "klama", &compiler), "expected klama type predicate");
        for i in 1..=5 {
            let role = format!("klama_x{}", i);
            assert!(has_pred(&form, &role, &compiler),
                "klama should have role predicate {}", role);
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
        assert!(matches!(&form, LogicalForm::Exists(_, _)), "expected Exists, got {:?}", form);
        assert!(has_pred(&form, "xyzzy", &compiler), "expected xyzzy type predicate");
        assert!(has_pred(&form, "xyzzy_x1", &compiler), "expected xyzzy_x1 role");
        assert!(has_pred(&form, "xyzzy_x2", &compiler), "expected xyzzy_x2 role");
        // Should NOT have xyzzy_x3
        assert!(!has_pred(&form, "xyzzy_x3", &compiler),
            "unknown word should default to arity 2, but found xyzzy_x3");
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
        assert!(matches!(&form, LogicalForm::Exists(_, _)), "expected Exists, got {:?}", form);
        assert!(has_pred(&form, "klama", &compiler), "expected klama type predicate");
        // All role predicates should have Unspecified in entity position
        for i in 1..=5 {
            let role = format!("klama_x{}", i);
            let role_args = get_pred_args(&form, &role, &compiler)
                .unwrap_or_else(|| panic!("expected {} role predicate", role));
            assert!(matches!(role_args[1], LogicalTerm::Unspecified),
                "expected Unspecified in {}, got {:?}", role, role_args[1]);
        }
    }
}
