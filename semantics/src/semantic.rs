use crate::bindings::lojban::nesy::ast_types::{
    AbstractionKind, BaiTag, Bridi, Connective, Conversion, Gadri, ModalTag, PlaceTag, Selbri,
    Sentence, SentenceConnective, Sumti, Tense,
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

pub struct SemanticCompiler {
    pub interner: Rodeo,
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
}

impl SemanticCompiler {
    pub fn new() -> Self {
        Self {
            interner: Rodeo::new(),
            var_counter: 0,
            rel_clause_var: None,
            kea_used: false,
            ka_open_var: None,
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
                let term = if matches!(p.as_str(), "da" | "de" | "di") {
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
                        let not_l = LogicalForm::Not(Box::new(left.clone()));
                        let not_r = LogicalForm::Not(Box::new(right.clone()));
                        LogicalForm::And(
                            Box::new(LogicalForm::Or(Box::new(not_l), Box::new(right))),
                            Box::new(LogicalForm::Or(Box::new(not_r), Box::new(left))),
                        )
                    }
                    Connective::Ju => LogicalForm::And(
                        Box::new(LogicalForm::Or(
                            Box::new(left.clone()),
                            Box::new(right.clone()),
                        )),
                        Box::new(LogicalForm::Not(Box::new(LogicalForm::And(
                            Box::new(left),
                            Box::new(right),
                        )))),
                    ),
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
                        // Biconditional: (A → B) ∧ (B → A)
                        let not_l = LogicalForm::Not(Box::new(left_form.clone()));
                        let not_r = LogicalForm::Not(Box::new(right_form.clone()));
                        LogicalForm::And(
                            Box::new(LogicalForm::Or(Box::new(not_l), Box::new(right_form))),
                            Box::new(LogicalForm::Or(Box::new(not_r), Box::new(left_form))),
                        )
                    }
                    Connective::Ju => {
                        // XOR: (A ∨ B) ∧ ¬(A ∧ B)
                        LogicalForm::And(
                            Box::new(LogicalForm::Or(
                                Box::new(left_form.clone()),
                                Box::new(right_form.clone()),
                            )),
                            Box::new(LogicalForm::Not(Box::new(LogicalForm::And(
                                Box::new(left_form),
                                Box::new(right_form),
                            )))),
                        )
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

        if bridi.negated {
            final_form = LogicalForm::Not(Box::new(final_form));
        }

        // Tense wrapping (outermost — scopes over negation)
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
                                // Biconditional: (¬L ∨ R) ∧ (¬R ∨ L)
                                let not_l = LogicalForm::Not(Box::new(l.clone()));
                                let not_r = LogicalForm::Not(Box::new(r.clone()));
                                LogicalForm::And(
                                    Box::new(LogicalForm::Or(Box::new(not_l), Box::new(r))),
                                    Box::new(LogicalForm::Or(Box::new(not_r), Box::new(l))),
                                )
                            }
                            Connective::Ju => {
                                // XOR: (L ∨ R) ∧ ¬(L ∧ R)
                                LogicalForm::And(
                                    Box::new(LogicalForm::Or(
                                        Box::new(l.clone()),
                                        Box::new(r.clone()),
                                    )),
                                    Box::new(LogicalForm::Not(Box::new(LogicalForm::And(
                                        Box::new(l),
                                        Box::new(r),
                                    )))),
                                )
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
        Bridi, Connective, Selbri, Sentence, SentenceConnective, Sumti,
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
        };

        let (form, _) = compile_one(selbris, sumtis, bridi);
        // Biconditional is And(Or(Not(L), R), Or(Not(R), L))
        match &form {
            LogicalForm::And(left, right) => {
                assert!(matches!(left.as_ref(), LogicalForm::Or(_, _)));
                assert!(matches!(right.as_ref(), LogicalForm::Or(_, _)));
            }
            other => panic!("expected And(Or, Or) biconditional, got {:?}", other),
        }
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
        };

        let (form, _) = compile_one(selbris, sumtis, bridi);
        // XOR is And(Or(L, R), Not(And(L, R)))
        match &form {
            LogicalForm::And(or_part, not_part) => {
                assert!(matches!(or_part.as_ref(), LogicalForm::Or(_, _)));
                assert!(matches!(not_part.as_ref(), LogicalForm::Not(_)));
            }
            other => panic!("expected And(Or, Not(And)) XOR, got {:?}", other),
        }
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
        };
        let outer_bridi = Bridi {
            relation: 2,
            head_terms: vec![desc_sumti_idx],
            tail_terms: vec![],
            negated: false,
            tense: None,
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
        };
        let right_bridi = Bridi {
            relation: 1,
            head_terms: vec![1],
            tail_terms: vec![],
            negated: false,
            tense: None,
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

    #[test]
    fn test_afterthought_jo_compiles_to_biconditional() {
        // .i jo = (¬L ∨ R) ∧ (¬R ∨ L)
        let conn = SentenceConnective::Afterthought((false, Connective::Jo, false));
        let (form, _) = compile_connected(conn, "klama", "mi", "prami", "do");
        match &form {
            LogicalForm::And(left, right) => {
                assert!(
                    matches!(left.as_ref(), LogicalForm::Or(_, _)),
                    "expected Or on left of And, got {:?}",
                    left
                );
                assert!(
                    matches!(right.as_ref(), LogicalForm::Or(_, _)),
                    "expected Or on right of And, got {:?}",
                    right
                );
            }
            other => panic!("expected And(Or(_,_), Or(_,_)), got {:?}", other),
        }
    }
}
