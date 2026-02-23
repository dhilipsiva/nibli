use crate::bindings::lojban::nesy::ast_types::{
    Bridi, Connective, Conversion, Gadri, PlaceTag, Selbri, Sumti, Tense,
};
use crate::dictionary::JbovlasteSchema;
use crate::ir::{LogicalForm, LogicalTerm};
use lasso::Rodeo;

/// Tracks a quantifier introduced by a description (lo/le/ro lo/ro le),
/// with an optional relative clause restrictor.
struct QuantifierEntry {
    var: lasso::Spur,
    desc_id: u32,
    restrictor: Option<LogicalForm>,
    /// If true, wraps as ∀x.(restrictor → body) instead of ∃x.(restrictor ∧ body)
    universal: bool,
}

pub struct SemanticCompiler {
    pub interner: Rodeo,
    pub var_counter: usize,
}

impl SemanticCompiler {
    pub fn new() -> Self {
        Self {
            interner: Rodeo::new(),
            var_counter: 0,
        }
    }

    fn fresh_var(&mut self) -> lasso::Spur {
        let v = format!("_v{}", self.var_counter);
        self.var_counter += 1;
        self.interner.get_or_intern(&v)
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
            Selbri::Abstraction(_) => 1,
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
            Selbri::Abstraction(_) => "nu",
        }
    }

    // ─── Sumti Resolution ────────────────────────────────────────

    fn resolve_sumti(
        &mut self,
        sumti: &Sumti,
        sumtis: &[Sumti],
        selbris: &[Selbri],
        sentences: &[Bridi],
    ) -> (LogicalTerm, Vec<QuantifierEntry>) {
        match sumti {
            Sumti::ProSumti(p) => {
                let term = if matches!(p.as_str(), "da" | "de" | "di") {
                    LogicalTerm::Variable(self.interner.get_or_intern(p.as_str()))
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
                                universal: false,
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
                                universal: true,
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

            Sumti::Tagged((_tag, inner_id)) => {
                let inner = &sumtis[*inner_id as usize];
                self.resolve_sumti(inner, sumtis, selbris, sentences)
            }

            Sumti::Restricted((inner_id, rel_clause)) => {
                let inner = &sumtis[*inner_id as usize];
                let (term, mut quants) = self.resolve_sumti(inner, sumtis, selbris, sentences);

                let rel_body = self.compile_bridi(
                    &sentences[rel_clause.body_sentence as usize],
                    selbris,
                    sumtis,
                    sentences,
                );

                if let Some(last) = quants.last_mut() {
                    last.restrictor = Some(Self::inject_variable(rel_body, last.var));
                }

                (term, quants)
            }

            Sumti::QuotedLiteral(q) => (
                LogicalTerm::Constant(self.interner.get_or_intern(q.as_str())),
                vec![],
            ),

            Sumti::Unspecified => (LogicalTerm::Unspecified, vec![]),
        }
    }

    fn inject_variable(form: LogicalForm, var: lasso::Spur) -> LogicalForm {
        match form {
            LogicalForm::Predicate { relation, mut args } => {
                // Find the FIRST Unspecified slot in any position and bind the
                // relative-clause variable there.  This handles cases like
                // "lo gerku poi mi nelci" where x1 is already filled ("mi")
                // and the bound variable belongs in x2.
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
            LogicalForm::Not(inner) => {
                LogicalForm::Not(Box::new(Self::inject_variable(*inner, var)))
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
            other => other,
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
        sentences: &[Bridi],
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

                    if entry.universal {
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
                    } else {
                        // ∃x. (restrictor ∧ body)
                        let mut body = LogicalForm::And(Box::new(restrictor), Box::new(form));
                        if let Some(rel_restrictor) = entry.restrictor {
                            body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                        }
                        form = LogicalForm::Exists(entry.var, Box::new(body));
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

            Selbri::Abstraction(body_sentence_idx) => {
                // nu abstraction: compile inner bridi as standalone formula,
                // conjoin with Pred("nu", [x1]).
                // Result: And(Pred("nu", [x1]), inner_formula)
                //
                // When used in "lo nu mi klama cu barda":
                //   ∃e. (nu(e) ∧ klama(mi,...) ∧ barda(e,...))
                let inner_form = self.compile_bridi(
                    &sentences[*body_sentence_idx as usize],
                    selbris,
                    sumtis,
                    sentences,
                );
                let nu_pred = LogicalForm::Predicate {
                    relation: self.interner.get_or_intern("nu"),
                    args: Self::fit_args(args, 1),
                };
                LogicalForm::And(Box::new(nu_pred), Box::new(inner_form))
            }
        }
    }

    // ─── Top-Level Bridi Compilation ─────────────────────────────

    pub fn compile_bridi(
        &mut self,
        bridi: &Bridi,
        selbris: &[Selbri],
        sumtis: &[Sumti],
        sentences: &[Bridi],
    ) -> LogicalForm {
        let target_arity = self.get_selbri_arity(bridi.relation, selbris);

        let mut positioned: Vec<Option<LogicalTerm>> = vec![None; target_arity];
        let mut untagged: Vec<LogicalTerm> = Vec::new();
        let mut quantifiers: Vec<QuantifierEntry> = Vec::new();

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

            if entry.universal {
                // ∀x. (restrictor → body) = ∀x. (¬restrictor ∨ body)
                let mut body = LogicalForm::Or(
                    Box::new(LogicalForm::Not(Box::new(desc_restrictor))),
                    Box::new(final_form),
                );

                // Conjoin relative clause restrictor into antecedent if present
                if let Some(rel_restrictor) = entry.restrictor {
                    // ∀x. ((restrictor ∧ rel_clause) → body)
                    // = ∀x. (¬(restrictor ∧ rel_clause) ∨ body)
                    // = ∀x. (¬restrictor ∨ ¬rel_clause ∨ body)
                    // But cleaner: just wrap the rel_clause into the antecedent
                    body = LogicalForm::Or(
                        Box::new(LogicalForm::Not(Box::new(rel_restrictor))),
                        Box::new(body),
                    );
                }

                final_form = LogicalForm::ForAll(entry.var, Box::new(body));
            } else {
                // ∃x. (restrictor ∧ body)
                let mut body = LogicalForm::And(Box::new(desc_restrictor), Box::new(final_form));

                if let Some(rel_restrictor) = entry.restrictor {
                    body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                }

                final_form = LogicalForm::Exists(entry.var, Box::new(body));
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
}
