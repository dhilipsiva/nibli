//! Helper methods for the semantic compiler.
//!
//! Provides fresh variable generation, argument resolution, relative clause
//! handling, argument fitting, and variable injection for implicit `it`.
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

    /// Closes a single quantifier `entry` around `form_to_wrap` and returns the
    /// wrapped form. The restrictive poi/voi clause (`entry.restrictor`) is folded
    /// on the DOMAIN side (antecedent for ∀, conjunct for ∃/Count) — it narrows
    /// what the quantifier ranges over. The non-restrictive noi clause
    /// (`entry.incidental_restrictor`) is folded on the MATRIX side (consequent for ∀,
    /// body conjunct for ∃/Count) — it asserts an incidental property of the
    /// domain members without narrowing the domain. `∀x. P(x) → (Q(x) ∧ noi(x))`
    /// is exactly `(∀x. P→Q) ∧ (∀x. P→noi)`, the standard non-restrictive reading.
    /// Residual: under an exact-count quantifier `noi` is folded into the counted
    /// body (== restrictive) — a documented limitation, since the principled form
    /// `Count(…) ∧ ∀x.(P→noi)` would need to return two conjuncts.
    /// Shared by the proposition-level closure (`compile_proposition`) and the be/bei closure
    /// (`apply_predicate`) so any change to quantifier lowering is made in one place.
    pub(crate) fn close_quantifier(
        &mut self,
        entry: QuantifierEntry,
        form_to_wrap: IrForm,
        predicates: &[Predicate],
        arguments: &[Argument],
        sentences: &[Sentence],
    ) -> IrForm {
        let desc_arity = self.get_predicate_arity(entry.desc_id, predicates);

        let mut restrictor_args = Vec::with_capacity(desc_arity);
        restrictor_args.push(IrTerm::Variable(entry.var));
        while restrictor_args.len() < desc_arity {
            restrictor_args.push(IrTerm::Unspecified);
        }

        let desc_restrictor = self.apply_predicate(
            entry.desc_id,
            &restrictor_args,
            predicates,
            arguments,
            sentences,
        );

        match entry.kind {
            QuantifierKind::Universal => {
                // noi (non-restrictive): conjoin into the consequent (matrix side).
                let matrix = match entry.incidental_restrictor {
                    Some(noi) => IrForm::And(Box::new(form_to_wrap), Box::new(noi)),
                    None => form_to_wrap,
                };
                let mut body = IrForm::Or(
                    Box::new(IrForm::Not(Box::new(desc_restrictor))),
                    Box::new(matrix),
                );

                if let Some(rel_restrictor) = entry.restrictor {
                    body = IrForm::Or(
                        Box::new(IrForm::Not(Box::new(rel_restrictor))),
                        Box::new(body),
                    );
                }

                IrForm::ForAll(entry.var, Box::new(body))
            }
            QuantifierKind::Existential => {
                let mut body = IrForm::And(Box::new(desc_restrictor), Box::new(form_to_wrap));

                if let Some(rel_restrictor) = entry.restrictor {
                    body = IrForm::And(Box::new(rel_restrictor), Box::new(body));
                }

                // noi: under ∃ a matrix conjunct is logically identical to a
                // restrictor conjunct (∧ is flat), so folding into the body is exact.
                if let Some(noi) = entry.incidental_restrictor {
                    body = IrForm::And(Box::new(noi), Box::new(body));
                }

                IrForm::Exists(entry.var, Box::new(body))
            }
            QuantifierKind::ExactCount(n) => {
                let mut body = IrForm::And(Box::new(desc_restrictor), Box::new(form_to_wrap));

                if let Some(rel_restrictor) = entry.restrictor {
                    body = IrForm::And(Box::new(rel_restrictor), Box::new(body));
                }

                // noi under exact-count stays restrictive (documented residual).
                if let Some(noi) = entry.incidental_restrictor {
                    body = IrForm::And(Box::new(noi), Box::new(body));
                }

                IrForm::Count {
                    var: entry.var,
                    count: n,
                    body: Box::new(body),
                }
            }
            QuantifierKind::UniversalLe => {
                let le_restrictor =
                    self.build_the_domain_restrictor(entry.desc_id, entry.var, predicates);
                let matrix = match entry.incidental_restrictor {
                    Some(noi) => IrForm::And(Box::new(form_to_wrap), Box::new(noi)),
                    None => form_to_wrap,
                };
                let mut body = IrForm::Or(
                    Box::new(IrForm::Not(Box::new(le_restrictor))),
                    Box::new(matrix),
                );

                if let Some(rel_restrictor) = entry.restrictor {
                    body = IrForm::Or(
                        Box::new(IrForm::Not(Box::new(rel_restrictor))),
                        Box::new(body),
                    );
                }

                IrForm::ForAll(entry.var, Box::new(body))
            }
            QuantifierKind::ExactCountLe(n) => {
                let le_restrictor =
                    self.build_the_domain_restrictor(entry.desc_id, entry.var, predicates);
                let mut body = IrForm::And(Box::new(le_restrictor), Box::new(form_to_wrap));

                if let Some(rel_restrictor) = entry.restrictor {
                    body = IrForm::And(Box::new(rel_restrictor), Box::new(body));
                }

                // noi under exact-count stays restrictive (documented residual).
                if let Some(noi) = entry.incidental_restrictor {
                    body = IrForm::And(Box::new(noi), Box::new(body));
                }

                IrForm::Count {
                    var: entry.var,
                    count: n,
                    body: Box::new(body),
                }
            }
        }
    }

    /// Resolves the arity of a predicate by recursing through pair, conversions, etc.
    pub(crate) fn get_predicate_arity(&self, predicate_id: u32, predicates: &[Predicate]) -> usize {
        match &predicates[predicate_id as usize] {
            Predicate::Root(g) => LexiconSchema::get_arity_or_default(g.as_str()),
            Predicate::Pair((_, head_id)) => self.get_predicate_arity(*head_id, predicates),
            Predicate::Converted((_, inner_id)) => self.get_predicate_arity(*inner_id, predicates),
            Predicate::Negated(inner_id) => self.get_predicate_arity(*inner_id, predicates),
            Predicate::Grouped(inner_id) => self.get_predicate_arity(*inner_id, predicates),
            Predicate::WithArgs((core_id, _)) => self.get_predicate_arity(*core_id, predicates),
            Predicate::Abstraction((_, _)) => 1,
        }
    }

    /// Extracts the head relation name from a possibly nested predicate.
    pub(crate) fn get_predicate_head_name<'a>(
        &self,
        predicate_id: u32,
        predicates: &'a [Predicate],
    ) -> &'a str {
        match &predicates[predicate_id as usize] {
            Predicate::Root(r) => r.as_str(),
            Predicate::Pair((_, head_id)) => self.get_predicate_head_name(*head_id, predicates),
            Predicate::Converted((_, inner_id)) => {
                self.get_predicate_head_name(*inner_id, predicates)
            }
            Predicate::Negated(inner_id) => self.get_predicate_head_name(*inner_id, predicates),
            Predicate::Grouped(inner_id) => self.get_predicate_head_name(*inner_id, predicates),
            Predicate::WithArgs((core_id, _)) => self.get_predicate_head_name(*core_id, predicates),
            Predicate::Abstraction((kind, _)) => match kind {
                AbstractionKind::Event => "event",
                AbstractionKind::Fact => "fact",
                AbstractionKind::Property => "property",
                AbstractionKind::Amount => "amount",
                AbstractionKind::Concept => "concept",
            },
        }
    }

    /// Flattens a (possibly nested) modifier stack into its full unit list.
    ///
    /// Returns the stack's true HEAD unit as `(name, arity, swaps)` and pushes
    /// every other unit into `modifiers` (surface order, left to right), each
    /// with the conversion swap chain (outermost first, as x1↔x{n} target
    /// indices 1..=4) collected from its own `Converted` layers. The pair arm
    /// of `apply_predicate` maps each unit's argument vector through these
    /// swaps (fit-then-swap, mirroring the `Predicate::Converted` arm), so a
    /// converted unit keeps its surface place structure: `menli se ponse` puts
    /// the shared x1 in ponse_x2 (possessed), not ponse_x1. Before 2026-07-12
    /// the pair arm flattened units WITHOUT the swap — silently compiling
    /// `menli se ponse` identically to `menli ponse`, a CLL-fidelity bug.
    ///
    /// Grouping is head-selection only in the shared-event encoding: every
    /// unit's role predicates land on the ONE shared event, so `[big fast] dog`
    /// and `big fast dog` compile to the same buffer (head `dog`, modifiers
    /// `big` + `fast`). Before 2026-07-19 a nested pair SIDE was collapsed to
    /// a single head name, silently dropping the other unit(s) of a 3+ stack
    /// from the compiled buffer — silent assertion loss, fixed by this
    /// recursive walk.
    pub(crate) fn collect_stack_units<'a>(
        &self,
        predicate_id: u32,
        predicates: &'a [Predicate],
        swaps: Vec<usize>,
        modifiers: &mut Vec<(&'a str, usize, Vec<usize>)>,
    ) -> (&'a str, usize, Vec<usize>) {
        match &predicates[predicate_id as usize] {
            Predicate::Converted((conv, inner_id)) => {
                let mut s = swaps;
                s.push(match conv {
                    Conversion::Swap12 => 1,
                    Conversion::Swap13 => 2,
                    Conversion::Swap14 => 3,
                    Conversion::Swap15 => 4,
                });
                self.collect_stack_units(*inner_id, predicates, s, modifiers)
            }
            Predicate::Grouped(inner_id) => {
                self.collect_stack_units(*inner_id, predicates, swaps, modifiers)
            }
            Predicate::Pair((mod_id, head_id)) => {
                // The modifier side contributes ALL of its units as modifiers
                // of the shared event — including its own internal head.
                let m = self.collect_stack_units(*mod_id, predicates, Vec::new(), modifiers);
                modifiers.push(m);
                self.collect_stack_units(*head_id, predicates, swaps, modifiers)
            }
            _ => (
                self.get_predicate_head_name(predicate_id, predicates),
                self.get_predicate_arity(predicate_id, predicates),
                swaps,
            ),
        }
    }

    /// Builds an opaque the_domain_X restrictor predicate for le descriptions.
    pub(crate) fn build_the_domain_restrictor(
        &mut self,
        desc_id: u32,
        var: lasso::Spur,
        predicates: &[Predicate],
    ) -> IrForm {
        let head_name = self.get_predicate_head_name(desc_id, predicates);
        let domain_name = format!("the_domain_{}", head_name);
        IrForm::Predicate {
            relation: self.interner.get_or_intern(&domain_name),
            args: vec![IrTerm::Variable(var)],
        }
    }

    /// Resolves a argument AST node into a logical term and any quantifiers it introduces.
    pub(crate) fn resolve_argument(
        &mut self,
        argument: &Argument,
        arguments: &[Argument],
        predicates: &[Predicate],
        sentences: &[Sentence],
    ) -> (IrTerm, Vec<QuantifierEntry>) {
        match argument {
            Argument::Variable(v) => (
                // The `$` sigil is preserved into the interner — variable
                // identity IS the sigiled string (the free-variable and
                // scope-marker passes key on it); `validate_ast_buffer`
                // rejects sigil-less payloads at the compile boundary.
                (IrTerm::Variable(self.interner.get_or_intern(v.as_str()))),
                vec![],
            ),
            Argument::Marker(marker) => {
                let term = match marker {
                    Marker::Witness => {
                        let var = self.fresh_var();
                        self.question_vars.push(var);
                        IrTerm::Variable(var)
                    }
                    Marker::It => {
                        if let Some(var) = self.rel_clause_var {
                            self.ref_used = true;
                            IrTerm::Variable(var)
                        } else {
                            IrTerm::Unspecified
                        }
                    }
                    Marker::Slot => {
                        if let Some(var) = self.property_open_var {
                            IrTerm::Variable(var)
                        } else {
                            // `slot` is the open place of a `property { … }` abstraction;
                            // outside one it has no binder. The old "degrade to a fresh
                            // variable" behavior leaked a FREE variable through compilation —
                            // the free-variable safety net does not close `_v` fresh vars, so
                            // the form reached the reasoner non-ground (the exact shape the
                            // groundness boundary at `assert_typed_fact` now drops). Fail
                            // closed at the SOURCE instead: reject with a semantic error.
                            self.errors.push(
                                "`slot` outside a `property { … }` abstraction has no \
                                 binder — the open place is only meaningful inside a \
                                 property block"
                                    .to_string(),
                            );
                            IrTerm::Unspecified
                        }
                    }
                };
                (term, vec![])
            }
            Argument::Pronoun(p) => (
                IrTerm::Constant(self.interner.get_or_intern(p.as_str())),
                vec![],
            ),
            Argument::Name(n) => (
                IrTerm::Constant(self.interner.get_or_intern(n.as_str())),
                vec![],
            ),
            Argument::Description((determiner, desc_id)) => match determiner {
                Determiner::Indefinite => {
                    let var = self.fresh_var();
                    (
                        IrTerm::Variable(var),
                        vec![QuantifierEntry {
                            var,
                            desc_id: *desc_id,
                            restrictor: None,
                            incidental_restrictor: None,
                            kind: QuantifierKind::Existential,
                        }],
                    )
                }
                Determiner::Every => {
                    let var = self.fresh_var();
                    (
                        IrTerm::Variable(var),
                        vec![QuantifierEntry {
                            var,
                            desc_id: *desc_id,
                            restrictor: None,
                            incidental_restrictor: None,
                            kind: QuantifierKind::Universal,
                        }],
                    )
                }
                Determiner::EveryThe => {
                    let var = self.fresh_var();
                    (
                        IrTerm::Variable(var),
                        vec![QuantifierEntry {
                            var,
                            desc_id: *desc_id,
                            restrictor: None,
                            incidental_restrictor: None,
                            kind: QuantifierKind::UniversalLe,
                        }],
                    )
                }
                Determiner::Definite => {
                    let desc_str = self.get_predicate_head_name(*desc_id, predicates);
                    (
                        IrTerm::Description(self.interner.get_or_intern(desc_str)),
                        vec![],
                    )
                }
            },
            Argument::QuantifiedDescription((count, determiner, desc_id)) => {
                let var = self.fresh_var();
                let kind = match determiner {
                    Determiner::Definite => QuantifierKind::ExactCountLe(*count),
                    _ => QuantifierKind::ExactCount(*count),
                };
                (
                    IrTerm::Variable(var),
                    vec![QuantifierEntry {
                        var,
                        desc_id: *desc_id,
                        restrictor: None,
                        incidental_restrictor: None,
                        kind,
                    }],
                )
            }
            Argument::Tagged((_tag, inner_id)) => {
                let inner = &arguments[*inner_id as usize];
                self.resolve_argument(inner, arguments, predicates, sentences)
            }
            Argument::ModalTagged((_modal_tag, inner_id)) => {
                let inner = &arguments[*inner_id as usize];
                self.resolve_argument(inner, arguments, predicates, sentences)
            }
            Argument::Restricted((inner_id, rel_clause)) => {
                let inner = &arguments[*inner_id as usize];
                let (term, mut quants) =
                    self.resolve_argument(inner, arguments, predicates, sentences);

                let outer_rel_var = self.rel_clause_var;
                let outer_ref_used = self.ref_used;

                // The clause binds the quantifier variable introduced by the
                // inner argument (lo / ro lo / PA lo). Argument that introduce NO
                // quantifier (la names, le descriptions, pro-argument) get a fresh
                // clause variable instead, substituted by the resolved term
                // after the body is compiled.
                let clause_var = match quants.last() {
                    Some(last) => last.var,
                    None => self.fresh_var(),
                };
                self.rel_clause_var = Some(clause_var);
                self.ref_used = false;
                // Offer the clause variable as the implicit `it` subject (x1) of
                // the clause's main proposition, consumed there before predicate
                // conversion. Save/restore so a nested Restricted clause does not
                // steal this one.
                let outer_clause_subject = self.pending_clause_subject.take();
                self.pending_clause_subject = Some(clause_var);

                let rel_body = self.compile_sentence(
                    rel_clause.body_sentence,
                    predicates,
                    arguments,
                    sentences,
                );

                let kea_was_used = self.ref_used;
                self.rel_clause_var = outer_rel_var;
                self.ref_used = outer_ref_used;
                self.pending_clause_subject = outer_clause_subject;

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
                        //     subject slots. Either way, require an explicit `it`.
                        self.errors.push(if unspec_count == 0 {
                            "Relative clause: the described entity has no unambiguous \
                             subject (x1) slot to bind into; use an explicit `it` to mark \
                             its place."
                                .to_string()
                        } else {
                            format!(
                                "Relative clause has {} predicates with unspecified subject \
                                 slots; implicit variable injection is ambiguous. Use an \
                                 explicit `it` for precise control.",
                                unspec_count
                            )
                        });
                        rel_body
                    }
                };

                if let Some(last) = quants.last_mut() {
                    // Stacked clauses (`poi P poi Q`, `noi P noi Q`) nest as
                    // Restricted(Restricted(...)), so the inner recursion already set the
                    // matching field for this quantifier. CONJOIN rather than overwrite,
                    // to keep every clause's predicate. Route by clause kind: poi/voi
                    // narrow the domain (`restrictor`); noi is non-restrictive and folds
                    // at the matrix level (`incidental_restrictor`, see `close_quantifier`).
                    // Mixed stacks (`poi P noi Q`) populate both fields independently.
                    match rel_clause.kind {
                        RelClauseKind::Incidental => {
                            last.incidental_restrictor =
                                Some(match last.incidental_restrictor.take() {
                                    Some(existing) => {
                                        IrForm::And(Box::new(existing), Box::new(new_restrictor))
                                    }
                                    None => new_restrictor,
                                });
                        }
                        RelClauseKind::Restrictive => {
                            last.restrictor = Some(match last.restrictor.take() {
                                Some(existing) => {
                                    IrForm::And(Box::new(existing), Box::new(new_restrictor))
                                }
                                None => new_restrictor,
                            });
                        }
                    }
                } else {
                    // No quantifier: the clause restricts a rigid term (la name,
                    // le description, pro-argument). Substitute the term for the
                    // clause variable and queue the clause for conjunction into
                    // the proposition matrix. Previously the compiled clause was
                    // silently DISCARDED here, so `la .adam. poi gerku cu klama`
                    // answered TRUE with only klama(adam) known (panel finding
                    // 2026-06-10).
                    let bound = Self::substitute_variable(new_restrictor, clause_var, &term);
                    self.pending_matrix_conjuncts.push(bound);
                }

                (term, quants)
            }
            Argument::QuotedLiteral(q) => (
                IrTerm::Constant(self.interner.get_or_intern(q.as_str())),
                vec![],
            ),
            Argument::Number(n) => (IrTerm::Number(*n), vec![]),
            Argument::Unspecified => (IrTerm::Unspecified, vec![]),
        }
    }

    /// Counts candidate subject slots for relative clause ambiguity detection.
    ///
    /// Role predicates (`rel_x1(ev, subject)`) that share the SAME event
    /// variable describe one predication — e.g. a pair's modifier and head —
    /// so their unfilled subject slots count as ONE candidate
    /// (`inject_variable` fills them all with the same entity). Distinct
    /// event variables (separate predications) and non-role predicates count
    /// individually.
    pub(crate) fn count_unspecified_predicates(form: &IrForm, interner: &Rodeo) -> usize {
        let mut events: std::collections::HashSet<lasso::Spur> = std::collections::HashSet::new();
        let mut others = 0usize;
        Self::collect_unspecified_subject_slots(form, interner, &mut events, &mut others);
        events.len() + others
    }

    fn collect_unspecified_subject_slots(
        form: &IrForm,
        interner: &Rodeo,
        events: &mut std::collections::HashSet<lasso::Spur>,
        others: &mut usize,
    ) {
        match form {
            IrForm::Predicate { relation, args } => {
                let rel_name = interner.resolve(relation);
                if rel_name.contains("_x") {
                    if rel_name.ends_with("_x1")
                        && args.len() >= 2
                        && matches!(&args[1], IrTerm::Unspecified)
                    {
                        if let IrTerm::Variable(ev) = &args[0] {
                            events.insert(*ev);
                        } else {
                            *others += 1;
                        }
                    }
                } else if args.iter().any(|a| matches!(a, IrTerm::Unspecified)) {
                    *others += 1;
                }
            }
            IrForm::And(l, r)
            | IrForm::Or(l, r)
            | IrForm::Biconditional(l, r)
            | IrForm::Xor(l, r) => {
                Self::collect_unspecified_subject_slots(l, interner, events, others);
                Self::collect_unspecified_subject_slots(r, interner, events, others);
            }
            IrForm::Not(inner)
            | IrForm::Exists(_, inner)
            | IrForm::ForAll(_, inner)
            | IrForm::Past(inner)
            | IrForm::Present(inner)
            | IrForm::Future(inner)
            | IrForm::Obligatory(inner)
            | IrForm::Permitted(inner) => {
                Self::collect_unspecified_subject_slots(inner, interner, events, others)
            }
            IrForm::Count { body, .. } => {
                Self::collect_unspecified_subject_slots(body, interner, events, others)
            }
        }
    }

    /// Replaces the first Unspecified slot in each predicate with the given variable.
    pub(crate) fn inject_variable(form: IrForm, var: lasso::Spur, interner: &Rodeo) -> IrForm {
        match form {
            IrForm::Predicate { relation, mut args } => {
                let rel_name = interner.resolve(&relation);
                if rel_name.contains("_x") {
                    if rel_name.ends_with("_x1") && args.len() >= 2 {
                        if matches!(&args[1], IrTerm::Unspecified) {
                            args[1] = IrTerm::Variable(var);
                        }
                    }
                } else {
                    let first_unspec = args.iter().position(|a| matches!(a, IrTerm::Unspecified));
                    if let Some(idx) = first_unspec {
                        args[idx] = IrTerm::Variable(var);
                    } else if args.is_empty() {
                        args.push(IrTerm::Variable(var));
                    }
                }
                IrForm::Predicate { relation, args }
            }
            IrForm::And(l, r) => IrForm::And(
                Box::new(Self::inject_variable(*l, var, interner)),
                Box::new(Self::inject_variable(*r, var, interner)),
            ),
            IrForm::Or(l, r) => IrForm::Or(
                Box::new(Self::inject_variable(*l, var, interner)),
                Box::new(Self::inject_variable(*r, var, interner)),
            ),
            IrForm::Biconditional(l, r) => IrForm::Biconditional(
                Box::new(Self::inject_variable(*l, var, interner)),
                Box::new(Self::inject_variable(*r, var, interner)),
            ),
            IrForm::Xor(l, r) => IrForm::Xor(
                Box::new(Self::inject_variable(*l, var, interner)),
                Box::new(Self::inject_variable(*r, var, interner)),
            ),
            IrForm::Not(inner) => {
                IrForm::Not(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            IrForm::Exists(v, body) => {
                IrForm::Exists(v, Box::new(Self::inject_variable(*body, var, interner)))
            }
            IrForm::ForAll(v, body) => {
                IrForm::ForAll(v, Box::new(Self::inject_variable(*body, var, interner)))
            }
            IrForm::Past(inner) => {
                IrForm::Past(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            IrForm::Present(inner) => {
                IrForm::Present(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            IrForm::Future(inner) => {
                IrForm::Future(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            IrForm::Obligatory(inner) => {
                IrForm::Obligatory(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            IrForm::Permitted(inner) => {
                IrForm::Permitted(Box::new(Self::inject_variable(*inner, var, interner)))
            }
            IrForm::Count {
                var: v,
                count,
                body,
            } => IrForm::Count {
                var: v,
                count,
                body: Box::new(Self::inject_variable(*body, var, interner)),
            },
        }
    }

    /// Replaces every occurrence of `Variable(var)` with the given replacement
    /// term. Used to bind a relative clause compiled against a fresh clause
    /// variable to a rigid term (proper-name constant, `le` description,
    /// pro-argument). A binder that shadows `var` stops the substitution.
    pub(crate) fn substitute_variable(
        form: IrForm,
        var: lasso::Spur,
        replacement: &IrTerm,
    ) -> IrForm {
        match form {
            IrForm::Predicate { relation, mut args } => {
                for a in args.iter_mut() {
                    if matches!(a, IrTerm::Variable(v) if *v == var) {
                        *a = replacement.clone();
                    }
                }
                IrForm::Predicate { relation, args }
            }
            IrForm::And(l, r) => IrForm::And(
                Box::new(Self::substitute_variable(*l, var, replacement)),
                Box::new(Self::substitute_variable(*r, var, replacement)),
            ),
            IrForm::Or(l, r) => IrForm::Or(
                Box::new(Self::substitute_variable(*l, var, replacement)),
                Box::new(Self::substitute_variable(*r, var, replacement)),
            ),
            IrForm::Biconditional(l, r) => IrForm::Biconditional(
                Box::new(Self::substitute_variable(*l, var, replacement)),
                Box::new(Self::substitute_variable(*r, var, replacement)),
            ),
            IrForm::Xor(l, r) => IrForm::Xor(
                Box::new(Self::substitute_variable(*l, var, replacement)),
                Box::new(Self::substitute_variable(*r, var, replacement)),
            ),
            IrForm::Not(inner) => IrForm::Not(Box::new(Self::substitute_variable(
                *inner,
                var,
                replacement,
            ))),
            IrForm::Exists(v, body) => {
                if v == var {
                    IrForm::Exists(v, body) // shadowed: substitution stops here
                } else {
                    IrForm::Exists(
                        v,
                        Box::new(Self::substitute_variable(*body, var, replacement)),
                    )
                }
            }
            IrForm::ForAll(v, body) => {
                if v == var {
                    IrForm::ForAll(v, body) // shadowed: substitution stops here
                } else {
                    IrForm::ForAll(
                        v,
                        Box::new(Self::substitute_variable(*body, var, replacement)),
                    )
                }
            }
            IrForm::Past(inner) => IrForm::Past(Box::new(Self::substitute_variable(
                *inner,
                var,
                replacement,
            ))),
            IrForm::Present(inner) => IrForm::Present(Box::new(Self::substitute_variable(
                *inner,
                var,
                replacement,
            ))),
            IrForm::Future(inner) => IrForm::Future(Box::new(Self::substitute_variable(
                *inner,
                var,
                replacement,
            ))),
            IrForm::Obligatory(inner) => IrForm::Obligatory(Box::new(Self::substitute_variable(
                *inner,
                var,
                replacement,
            ))),
            IrForm::Permitted(inner) => IrForm::Permitted(Box::new(Self::substitute_variable(
                *inner,
                var,
                replacement,
            ))),
            IrForm::Count {
                var: v,
                count,
                body,
            } => {
                if v == var {
                    IrForm::Count {
                        var: v,
                        count,
                        body,
                    } // shadowed
                } else {
                    IrForm::Count {
                        var: v,
                        count,
                        body: Box::new(Self::substitute_variable(*body, var, replacement)),
                    }
                }
            }
        }
    }

    /// Pads or truncates an argument list to exactly the target arity.
    pub(crate) fn fit_args(args: &[IrTerm], arity: usize) -> Vec<IrTerm> {
        let mut fitted = Vec::with_capacity(arity);
        for i in 0..arity {
            if i < args.len() {
                fitted.push(args[i].clone());
            } else {
                fitted.push(IrTerm::Unspecified);
            }
        }
        fitted
    }
}
