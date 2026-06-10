//! Helper methods for the semantic compiler.
//!
//! Provides fresh variable generation, sumti resolution, relative clause
//! handling, argument fitting, and variable injection for implicit ke'a.
use super::*;

impl SemanticCompiler {
    /// Generates a fresh entity variable name (_v0, _v1, ...) and interns it.
    pub(crate) fn fresh_var(&mut self) -> lasso::Spur {
        let v = format!("_v{}", self.var_counter);
        self.var_counter += 1;
        self.interner.get_or_intern(&v)
    }

    /// Generates a fresh event variable name (_ev0, _ev1, ...) and interns it.
    pub(crate) fn fresh_event_var(&mut self) -> lasso::Spur {
        let v = format!("_ev{}", self.event_counter);
        self.event_counter += 1;
        self.interner.get_or_intern(&v)
    }

    /// Maps a BAI modal tag to its underlying gismu relation name.
    pub(crate) fn bai_to_gismu(tag: &BaiTag) -> &'static str {
        match tag {
            BaiTag::Ria => "rinka",
            BaiTag::Nii => "nibli",
            BaiTag::Mui => "mukti",
            BaiTag::Kiu => "krinu",
            BaiTag::Pio => "pilno",
            BaiTag::Bai => "basti",
        }
    }

    /// Resolves the arity of a selbri by recursing through tanru, conversions, etc.
    pub(crate) fn get_selbri_arity(&self, selbri_id: u32, selbris: &[Selbri]) -> usize {
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

    /// Extracts the head gismu or lujvo name from a possibly nested selbri.
    pub(crate) fn get_selbri_head_name<'a>(
        &self,
        selbri_id: u32,
        selbris: &'a [Selbri],
    ) -> &'a str {
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

    /// Builds an opaque le_domain_X restrictor predicate for le descriptions.
    pub(crate) fn build_le_domain_restrictor(
        &mut self,
        desc_id: u32,
        var: lasso::Spur,
        selbris: &[Selbri],
    ) -> LogicalForm {
        let head_name = self.get_selbri_head_name(desc_id, selbris);
        let domain_name = format!("le_domain_{}", head_name);
        LogicalForm::Predicate {
            relation: self.interner.get_or_intern(&domain_name),
            args: vec![LogicalTerm::Variable(var)],
        }
    }

    /// Resolves a sumti AST node into a logical term and any quantifiers it introduces.
    pub(crate) fn resolve_sumti(
        &mut self,
        sumti: &Sumti,
        sumtis: &[Sumti],
        selbris: &[Selbri],
        sentences: &[Sentence],
    ) -> (LogicalTerm, Vec<QuantifierEntry>) {
        match sumti {
            Sumti::ProSumti(p) => {
                let term = if p.as_str() == "ma" {
                    let var = self.fresh_var();
                    self.ma_vars.push(var);
                    LogicalTerm::Variable(var)
                } else if matches!(p.as_str(), "da" | "de" | "di") {
                    LogicalTerm::Variable(self.interner.get_or_intern(p.as_str()))
                } else if p.as_str() == "ke'a" {
                    if let Some(var) = self.rel_clause_var {
                        self.kea_used = true;
                        LogicalTerm::Variable(var)
                    } else {
                        LogicalTerm::Unspecified
                    }
                } else if p.as_str() == "ce'u" {
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
            Sumti::Description((gadri, desc_id)) => match gadri {
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
                Gadri::RoLo => {
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
                Gadri::RoLe => {
                    let var = self.fresh_var();
                    (
                        LogicalTerm::Variable(var),
                        vec![QuantifierEntry {
                            var,
                            desc_id: *desc_id,
                            restrictor: None,
                            kind: QuantifierKind::UniversalLe,
                        }],
                    )
                }
                Gadri::La => {
                    let name = self.get_selbri_head_name(*desc_id, selbris);
                    (
                        LogicalTerm::Constant(self.interner.get_or_intern(name)),
                        vec![],
                    )
                }
                Gadri::Le => {
                    let desc_str = self.get_selbri_head_name(*desc_id, selbris);
                    (
                        LogicalTerm::Description(self.interner.get_or_intern(desc_str)),
                        vec![],
                    )
                }
            },
            Sumti::QuantifiedDescription((count, gadri, desc_id)) => {
                let var = self.fresh_var();
                let kind = match gadri {
                    Gadri::Le => QuantifierKind::ExactCountLe(*count),
                    _ => QuantifierKind::ExactCount(*count),
                };
                (
                    LogicalTerm::Variable(var),
                    vec![QuantifierEntry {
                        var,
                        desc_id: *desc_id,
                        restrictor: None,
                        kind,
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

                let outer_rel_var = self.rel_clause_var;
                let outer_kea_used = self.kea_used;

                // The clause binds the quantifier variable introduced by the
                // inner sumti (lo / ro lo / PA lo). Sumti that introduce NO
                // quantifier (la names, le descriptions, pro-sumti) get a fresh
                // clause variable instead, substituted by the resolved term
                // after the body is compiled.
                let clause_var = match quants.last() {
                    Some(last) => last.var,
                    None => self.fresh_var(),
                };
                self.rel_clause_var = Some(clause_var);
                self.kea_used = false;

                let rel_body =
                    self.compile_sentence(rel_clause.body_sentence, selbris, sumtis, sentences);

                let kea_was_used = self.kea_used;
                self.rel_clause_var = outer_rel_var;
                self.kea_used = outer_kea_used;

                let new_restrictor = if kea_was_used {
                    rel_body
                } else {
                    let unspec_count =
                        Self::count_unspecified_predicates(&rel_body, &self.interner);
                    if unspec_count == 1 {
                        // Exactly one candidate subject (_x1) slot: inject the
                        // described entity's variable there.
                        Self::inject_variable(rel_body, clause_var, &self.interner)
                    } else {
                        // Firewall (book Ch6): reject rather than guess.
                        // 0 = the referent has no subject (_x1) slot to bind into (its
                        //     place would be a non-subject slot); >1 = multiple candidate
                        //     subject slots. Either way, require explicit ke'a.
                        self.errors.push(if unspec_count == 0 {
                            "Relative clause: the described entity has no unambiguous \
                             subject (x1) slot to bind into; use explicit ke'a to mark its \
                             place."
                                .to_string()
                        } else {
                            format!(
                                "Relative clause has {} predicates with unspecified subject \
                                 slots; implicit variable injection is ambiguous. Use \
                                 explicit ke'a for precise control.",
                                unspec_count
                            )
                        });
                        rel_body
                    }
                };

                if let Some(last) = quants.last_mut() {
                    // Stacked clauses (`poi P poi Q`) nest as Restricted(Restricted(...)),
                    // so the inner recursion already set a restrictor for this quantifier.
                    // CONJOIN rather than overwrite, to keep every clause's predicate.
                    last.restrictor = Some(match last.restrictor.take() {
                        Some(existing) => {
                            LogicalForm::And(Box::new(existing), Box::new(new_restrictor))
                        }
                        None => new_restrictor,
                    });
                } else {
                    // No quantifier: the clause restricts a rigid term (la name,
                    // le description, pro-sumti). Substitute the term for the
                    // clause variable and queue the clause for conjunction into
                    // the bridi matrix. Previously the compiled clause was
                    // silently DISCARDED here, so `la .adam. poi gerku cu klama`
                    // answered TRUE with only klama(adam) known (panel finding
                    // 2026-06-10).
                    let bound = Self::substitute_variable(new_restrictor, clause_var, &term);
                    self.pending_matrix_conjuncts.push(bound);
                }

                (term, quants)
            }
            Sumti::QuotedLiteral(q) => (
                LogicalTerm::Constant(self.interner.get_or_intern(q.as_str())),
                vec![],
            ),
            Sumti::Number(n) => (LogicalTerm::Number(*n), vec![]),
            Sumti::Unspecified => (LogicalTerm::Unspecified, vec![]),
            Sumti::Connected((left_id, _conn, _negated, _right_id)) => {
                let left = &sumtis[*left_id as usize];
                self.resolve_sumti(left, sumtis, selbris, sentences)
            }
        }
    }

    /// Counts candidate subject slots for relative clause ambiguity detection.
    ///
    /// Role predicates (`rel_x1(ev, subject)`) that share the SAME event
    /// variable describe one predication — e.g. a tanru's modifier and head —
    /// so their unfilled subject slots count as ONE candidate
    /// (`inject_variable` fills them all with the same entity). Distinct
    /// event variables (separate predications) and non-role predicates count
    /// individually.
    pub(crate) fn count_unspecified_predicates(form: &LogicalForm, interner: &Rodeo) -> usize {
        let mut events: std::collections::HashSet<lasso::Spur> = std::collections::HashSet::new();
        let mut others = 0usize;
        Self::collect_unspecified_subject_slots(form, interner, &mut events, &mut others);
        events.len() + others
    }

    fn collect_unspecified_subject_slots(
        form: &LogicalForm,
        interner: &Rodeo,
        events: &mut std::collections::HashSet<lasso::Spur>,
        others: &mut usize,
    ) {
        match form {
            LogicalForm::Predicate { relation, args } => {
                let rel_name = interner.resolve(relation);
                if rel_name.contains("_x") {
                    if rel_name.ends_with("_x1")
                        && args.len() >= 2
                        && matches!(&args[1], LogicalTerm::Unspecified)
                    {
                        if let LogicalTerm::Variable(ev) = &args[0] {
                            events.insert(*ev);
                        } else {
                            *others += 1;
                        }
                    }
                } else if args.iter().any(|a| matches!(a, LogicalTerm::Unspecified)) {
                    *others += 1;
                }
            }
            LogicalForm::And(l, r)
            | LogicalForm::Or(l, r)
            | LogicalForm::Biconditional(l, r)
            | LogicalForm::Xor(l, r) => {
                Self::collect_unspecified_subject_slots(l, interner, events, others);
                Self::collect_unspecified_subject_slots(r, interner, events, others);
            }
            LogicalForm::Not(inner)
            | LogicalForm::Exists(_, inner)
            | LogicalForm::ForAll(_, inner)
            | LogicalForm::Past(inner)
            | LogicalForm::Present(inner)
            | LogicalForm::Future(inner)
            | LogicalForm::Obligatory(inner)
            | LogicalForm::Permitted(inner) => {
                Self::collect_unspecified_subject_slots(inner, interner, events, others)
            }
            LogicalForm::Count { body, .. } => {
                Self::collect_unspecified_subject_slots(body, interner, events, others)
            }
        }
    }

    /// Replaces the first Unspecified slot in each predicate with the given variable.
    pub(crate) fn inject_variable(
        form: LogicalForm,
        var: lasso::Spur,
        interner: &Rodeo,
    ) -> LogicalForm {
        match form {
            LogicalForm::Predicate { relation, mut args } => {
                let rel_name = interner.resolve(&relation);
                if rel_name.contains("_x") {
                    if rel_name.ends_with("_x1") && args.len() >= 2 {
                        if matches!(&args[1], LogicalTerm::Unspecified) {
                            args[1] = LogicalTerm::Variable(var);
                        }
                    }
                } else {
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
            LogicalForm::Count {
                var: v,
                count,
                body,
            } => LogicalForm::Count {
                var: v,
                count,
                body: Box::new(Self::inject_variable(*body, var, interner)),
            },
        }
    }

    /// Replaces every occurrence of `Variable(var)` with the given replacement
    /// term. Used to bind a relative clause compiled against a fresh clause
    /// variable to a rigid term (proper-name constant, `le` description,
    /// pro-sumti). A binder that shadows `var` stops the substitution.
    pub(crate) fn substitute_variable(
        form: LogicalForm,
        var: lasso::Spur,
        replacement: &LogicalTerm,
    ) -> LogicalForm {
        match form {
            LogicalForm::Predicate { relation, mut args } => {
                for a in args.iter_mut() {
                    if matches!(a, LogicalTerm::Variable(v) if *v == var) {
                        *a = replacement.clone();
                    }
                }
                LogicalForm::Predicate { relation, args }
            }
            LogicalForm::And(l, r) => LogicalForm::And(
                Box::new(Self::substitute_variable(*l, var, replacement)),
                Box::new(Self::substitute_variable(*r, var, replacement)),
            ),
            LogicalForm::Or(l, r) => LogicalForm::Or(
                Box::new(Self::substitute_variable(*l, var, replacement)),
                Box::new(Self::substitute_variable(*r, var, replacement)),
            ),
            LogicalForm::Biconditional(l, r) => LogicalForm::Biconditional(
                Box::new(Self::substitute_variable(*l, var, replacement)),
                Box::new(Self::substitute_variable(*r, var, replacement)),
            ),
            LogicalForm::Xor(l, r) => LogicalForm::Xor(
                Box::new(Self::substitute_variable(*l, var, replacement)),
                Box::new(Self::substitute_variable(*r, var, replacement)),
            ),
            LogicalForm::Not(inner) => LogicalForm::Not(Box::new(Self::substitute_variable(
                *inner,
                var,
                replacement,
            ))),
            LogicalForm::Exists(v, body) => {
                if v == var {
                    LogicalForm::Exists(v, body) // shadowed: substitution stops here
                } else {
                    LogicalForm::Exists(
                        v,
                        Box::new(Self::substitute_variable(*body, var, replacement)),
                    )
                }
            }
            LogicalForm::ForAll(v, body) => {
                if v == var {
                    LogicalForm::ForAll(v, body) // shadowed: substitution stops here
                } else {
                    LogicalForm::ForAll(
                        v,
                        Box::new(Self::substitute_variable(*body, var, replacement)),
                    )
                }
            }
            LogicalForm::Past(inner) => LogicalForm::Past(Box::new(Self::substitute_variable(
                *inner,
                var,
                replacement,
            ))),
            LogicalForm::Present(inner) => LogicalForm::Present(Box::new(
                Self::substitute_variable(*inner, var, replacement),
            )),
            LogicalForm::Future(inner) => LogicalForm::Future(Box::new(Self::substitute_variable(
                *inner,
                var,
                replacement,
            ))),
            LogicalForm::Obligatory(inner) => LogicalForm::Obligatory(Box::new(
                Self::substitute_variable(*inner, var, replacement),
            )),
            LogicalForm::Permitted(inner) => LogicalForm::Permitted(Box::new(
                Self::substitute_variable(*inner, var, replacement),
            )),
            LogicalForm::Count {
                var: v,
                count,
                body,
            } => {
                if v == var {
                    LogicalForm::Count {
                        var: v,
                        count,
                        body,
                    } // shadowed
                } else {
                    LogicalForm::Count {
                        var: v,
                        count,
                        body: Box::new(Self::substitute_variable(*body, var, replacement)),
                    }
                }
            }
        }
    }

    /// Pads or truncates an argument list to exactly the target arity.
    pub(crate) fn fit_args(args: &[LogicalTerm], arity: usize) -> Vec<LogicalTerm> {
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
}
