//! Selbri compilation: maps selbri AST nodes to FOL logic forms.
//!
//! Handles root predicates, tanru, conversion (se/te/ve/xe), negation,
//! ke...ke'e grouping, be...bei...be'o arguments, connected selbri,
//! zei compounds, and abstraction (nu/du'u/ka/ni/si'o). All predicates
//! are event-decomposed into Neo-Davidsonian form.
use super::*;

impl SemanticCompiler {
    /// Decomposes a predicate into Neo-Davidsonian event form with role predicates.
    pub(crate) fn event_decompose(
        &mut self,
        relation: &str,
        args: &[LogicalTerm],
    ) -> LogicalForm {
        let ev = self.fresh_event_var();
        let ev_term = LogicalTerm::Variable(ev);

        let type_pred = LogicalForm::Predicate {
            relation: self.interner.get_or_intern(relation),
            args: vec![ev_term.clone()],
        };

        let mut form = type_pred;
        for (i, arg) in args.iter().enumerate() {
            let role_name = format!("{}_x{}", relation, i + 1);
            let role_pred = LogicalForm::Predicate {
                relation: self.interner.get_or_intern(&role_name),
                args: vec![ev_term.clone(), arg.clone()],
            };
            form = LogicalForm::And(Box::new(form), Box::new(role_pred));
        }

        LogicalForm::Exists(ev, Box::new(form))
    }

    /// Compiles a selbri node with given arguments into a FOL logic form.
    pub(crate) fn apply_selbri(
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

                let mut mod_args = vec![LogicalTerm::Unspecified; mod_arity];
                if !args.is_empty() && mod_arity > 0 {
                    mod_args[0] = args[0].clone();
                }
                let head_args = Self::fit_args(args, head_arity);

                let ev = self.fresh_event_var();
                let ev_term = LogicalTerm::Variable(ev);

                let type_pred = LogicalForm::Predicate {
                    relation: self.interner.get_or_intern(&head_name),
                    args: vec![ev_term.clone()],
                };
                let mut form = type_pred;

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
                            let mut body = LogicalForm::And(Box::new(restrictor), Box::new(form));
                            if let Some(rel_restrictor) = entry.restrictor {
                                body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                            }
                            form = LogicalForm::Exists(entry.var, Box::new(body));
                        }
                        QuantifierKind::ExactCount(n) => {
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
                        QuantifierKind::UniversalLe => {
                            let le_restrictor =
                                self.build_le_domain_restrictor(entry.desc_id, entry.var, selbris);
                            let mut body = LogicalForm::Or(
                                Box::new(LogicalForm::Not(Box::new(le_restrictor))),
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
                        QuantifierKind::ExactCountLe(n) => {
                            let le_restrictor =
                                self.build_le_domain_restrictor(entry.desc_id, entry.var, selbris);
                            let mut body =
                                LogicalForm::And(Box::new(le_restrictor), Box::new(form));
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
                if left_arity != right_arity {
                    eprintln!(
                        "[Arity Warning] Connected selbri: left arity {} != right arity {}. \
                         Arguments will be fitted independently to each predicate.",
                        left_arity, right_arity
                    );
                }
                let left_args = Self::fit_args(args, left_arity);
                let right_args = Self::fit_args(args, right_arity);
                let left = self.apply_selbri(*left_id, &left_args, selbris, sumtis, sentences);
                let right = self.apply_selbri(*right_id, &right_args, selbris, sumtis, sentences);

                match conn {
                    Connective::Je => LogicalForm::And(Box::new(left), Box::new(right)),
                    Connective::Ja => LogicalForm::Or(Box::new(left), Box::new(right)),
                    Connective::Jo => LogicalForm::Biconditional(Box::new(left), Box::new(right)),
                    Connective::Ju => LogicalForm::Xor(Box::new(left), Box::new(right)),
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

                let outer_ka_var = self.ka_open_var;
                if *kind == AbstractionKind::Ka {
                    if let Some(LogicalTerm::Variable(v)) = args.first() {
                        self.ka_open_var = Some(*v);
                    }
                }

                let inner_form =
                    self.compile_sentence(*body_sentence_idx, selbris, sumtis, sentences);
                self.ka_open_var = outer_ka_var;

                let type_pred = LogicalForm::Predicate {
                    relation: self.interner.get_or_intern(type_name),
                    args: Self::fit_args(args, 1),
                };
                LogicalForm::And(Box::new(type_pred), Box::new(inner_form))
            }
        }
    }
}
