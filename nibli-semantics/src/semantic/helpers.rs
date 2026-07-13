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
    /// Shared by the bridi-level closure (`compile_proposition`) and the be/bei closure
    /// (`apply_predicate`) so any change to quantifier lowering is made in one place.
    pub(crate) fn close_quantifier(
        &mut self,
        entry: QuantifierEntry,
        form_to_wrap: LogicalForm,
        selbris: &[Predicate],
        sumtis: &[Argument],
        sentences: &[Sentence],
    ) -> LogicalForm {
        let desc_arity = self.get_predicate_arity(entry.desc_id, selbris);

        let mut restrictor_args = Vec::with_capacity(desc_arity);
        restrictor_args.push(LogicalTerm::Variable(entry.var));
        while restrictor_args.len() < desc_arity {
            restrictor_args.push(LogicalTerm::Unspecified);
        }

        let desc_restrictor =
            self.apply_predicate(entry.desc_id, &restrictor_args, selbris, sumtis, sentences);

        match entry.kind {
            QuantifierKind::Universal => {
                // noi (non-restrictive): conjoin into the consequent (matrix side).
                let matrix = match entry.incidental_restrictor {
                    Some(noi) => LogicalForm::And(Box::new(form_to_wrap), Box::new(noi)),
                    None => form_to_wrap,
                };
                let mut body = LogicalForm::Or(
                    Box::new(LogicalForm::Not(Box::new(desc_restrictor))),
                    Box::new(matrix),
                );

                if let Some(rel_restrictor) = entry.restrictor {
                    body = LogicalForm::Or(
                        Box::new(LogicalForm::Not(Box::new(rel_restrictor))),
                        Box::new(body),
                    );
                }

                LogicalForm::ForAll(entry.var, Box::new(body))
            }
            QuantifierKind::Existential => {
                let mut body = LogicalForm::And(Box::new(desc_restrictor), Box::new(form_to_wrap));

                if let Some(rel_restrictor) = entry.restrictor {
                    body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                }

                // noi: under ∃ a matrix conjunct is logically identical to a
                // restrictor conjunct (∧ is flat), so folding into the body is exact.
                if let Some(noi) = entry.incidental_restrictor {
                    body = LogicalForm::And(Box::new(noi), Box::new(body));
                }

                LogicalForm::Exists(entry.var, Box::new(body))
            }
            QuantifierKind::ExactCount(n) => {
                let mut body = LogicalForm::And(Box::new(desc_restrictor), Box::new(form_to_wrap));

                if let Some(rel_restrictor) = entry.restrictor {
                    body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                }

                // noi under exact-count stays restrictive (documented residual).
                if let Some(noi) = entry.incidental_restrictor {
                    body = LogicalForm::And(Box::new(noi), Box::new(body));
                }

                LogicalForm::Count {
                    var: entry.var,
                    count: n,
                    body: Box::new(body),
                }
            }
            QuantifierKind::UniversalLe => {
                let le_restrictor =
                    self.build_le_domain_restrictor(entry.desc_id, entry.var, selbris);
                let matrix = match entry.incidental_restrictor {
                    Some(noi) => LogicalForm::And(Box::new(form_to_wrap), Box::new(noi)),
                    None => form_to_wrap,
                };
                let mut body = LogicalForm::Or(
                    Box::new(LogicalForm::Not(Box::new(le_restrictor))),
                    Box::new(matrix),
                );

                if let Some(rel_restrictor) = entry.restrictor {
                    body = LogicalForm::Or(
                        Box::new(LogicalForm::Not(Box::new(rel_restrictor))),
                        Box::new(body),
                    );
                }

                LogicalForm::ForAll(entry.var, Box::new(body))
            }
            QuantifierKind::ExactCountLe(n) => {
                let le_restrictor =
                    self.build_le_domain_restrictor(entry.desc_id, entry.var, selbris);
                let mut body = LogicalForm::And(Box::new(le_restrictor), Box::new(form_to_wrap));

                if let Some(rel_restrictor) = entry.restrictor {
                    body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                }

                // noi under exact-count stays restrictive (documented residual).
                if let Some(noi) = entry.incidental_restrictor {
                    body = LogicalForm::And(Box::new(noi), Box::new(body));
                }

                LogicalForm::Count {
                    var: entry.var,
                    count: n,
                    body: Box::new(body),
                }
            }
        }
    }

    /// Maps a BAI modal tag to its underlying gismu relation name.
    pub(crate) fn modal_relation_name(tag: &ModalRelation) -> &'static str {
        match tag {
            ModalRelation::Ria => "rinka",
            ModalRelation::Nii => "nibli",
            ModalRelation::Mui => "mukti",
            ModalRelation::Kiu => "krinu",
            ModalRelation::Pio => "pilno",
            ModalRelation::Bai => "basti",
        }
    }

    /// Resolves the arity of a selbri by recursing through tanru, conversions, etc.
    pub(crate) fn get_predicate_arity(&self, selbri_id: u32, selbris: &[Predicate]) -> usize {
        match &selbris[selbri_id as usize] {
            Predicate::Root(g) => LexiconSchema::get_arity_or_default(g.as_str()),
            Predicate::Tanru((_, head_id)) => self.get_predicate_arity(*head_id, selbris),
            Predicate::Converted((_, inner_id)) => self.get_predicate_arity(*inner_id, selbris),
            Predicate::Negated(inner_id) => self.get_predicate_arity(*inner_id, selbris),
            Predicate::Grouped(inner_id) => self.get_predicate_arity(*inner_id, selbris),
            Predicate::WithArgs((core_id, _)) => self.get_predicate_arity(*core_id, selbris),
            // A connected selbri (`broda je brode`) shares its sumti across both
            // operands; each takes only its own arity's worth (via `fit_args` in
            // `apply_predicate`). The EFFECTIVE arity is max(left, right) so the place
            // counter sizes for — and captures — every sumti the larger operand
            // needs; a left-only arity dropped the higher operand's slots.
            Predicate::Connected((left_id, _, right_id)) => self
                .get_predicate_arity(*left_id, selbris)
                .max(self.get_predicate_arity(*right_id, selbris)),
            Predicate::Compound(parts) => parts
                .last()
                .map(|s| LexiconSchema::get_arity_or_default(s.as_str()))
                .unwrap_or(2),
            Predicate::Abstraction((_, _)) => 1,
        }
    }

    /// Extracts the head gismu or lujvo name from a possibly nested selbri.
    pub(crate) fn get_predicate_head_name<'a>(
        &self,
        selbri_id: u32,
        selbris: &'a [Predicate],
    ) -> &'a str {
        match &selbris[selbri_id as usize] {
            Predicate::Root(r) => r.as_str(),
            Predicate::Tanru((_, head_id)) => self.get_predicate_head_name(*head_id, selbris),
            Predicate::Converted((_, inner_id)) => self.get_predicate_head_name(*inner_id, selbris),
            Predicate::Negated(inner_id) => self.get_predicate_head_name(*inner_id, selbris),
            Predicate::Grouped(inner_id) => self.get_predicate_head_name(*inner_id, selbris),
            Predicate::WithArgs((core_id, _)) => self.get_predicate_head_name(*core_id, selbris),
            Predicate::Connected((left_id, _, _)) => {
                self.get_predicate_head_name(*left_id, selbris)
            }
            Predicate::Compound(parts) => parts.last().map(|s| s.as_str()).unwrap_or("entity"),
            Predicate::Abstraction((kind, _)) => match kind {
                AbstractionKind::Nu => "nu",
                AbstractionKind::Duhu => "duhu",
                AbstractionKind::Ka => "ka",
                AbstractionKind::Ni => "ni",
                AbstractionKind::Siho => "siho",
            },
        }
    }

    /// Resolves a tanru UNIT to its base head name, arity, and the conversion
    /// swap chain (outermost first, as x1↔x{n} target indices 1..=4) collected
    /// from `Converted` layers on the way down. The tanru arm of `apply_predicate`
    /// maps each unit's argument vector through these swaps (fit-then-swap,
    /// mirroring the `Predicate::Converted` arm), so a converted unit keeps its
    /// surface place structure: `menli se ponse` puts the shared x1 in
    /// ponse_x2 (possessed), not ponse_x1. Before 2026-07-12 the tanru arm
    /// flattened units through `get_predicate_head_name`/`get_predicate_arity`,
    /// which unwrap `Converted` WITHOUT the swap — silently compiling
    /// `menli se ponse` identically to `menli ponse`, a CLL-fidelity bug.
    pub(crate) fn get_predicate_unit_base<'a>(
        &self,
        selbri_id: u32,
        selbris: &'a [Predicate],
    ) -> (&'a str, usize, Vec<usize>) {
        let mut swaps: Vec<usize> = Vec::new();
        let mut id = selbri_id;
        loop {
            match &selbris[id as usize] {
                Predicate::Converted((conv, inner_id)) => {
                    swaps.push(match conv {
                        Conversion::Se => 1,
                        Conversion::Te => 2,
                        Conversion::Ve => 3,
                        Conversion::Xe => 4,
                    });
                    id = *inner_id;
                }
                Predicate::Grouped(inner_id) => id = *inner_id,
                _ => break,
            }
        }
        (
            self.get_predicate_head_name(id, selbris),
            self.get_predicate_arity(id, selbris),
            swaps,
        )
    }

    /// Builds an opaque le_domain_X restrictor predicate for le descriptions.
    pub(crate) fn build_le_domain_restrictor(
        &mut self,
        desc_id: u32,
        var: lasso::Spur,
        selbris: &[Predicate],
    ) -> LogicalForm {
        let head_name = self.get_predicate_head_name(desc_id, selbris);
        let domain_name = format!("le_domain_{}", head_name);
        LogicalForm::Predicate {
            relation: self.interner.get_or_intern(&domain_name),
            args: vec![LogicalTerm::Variable(var)],
        }
    }

    /// Resolves a sumti AST node into a logical term and any quantifiers it introduces.
    pub(crate) fn resolve_argument(
        &mut self,
        sumti: &Argument,
        sumtis: &[Argument],
        selbris: &[Predicate],
        sentences: &[Sentence],
    ) -> (LogicalTerm, Vec<QuantifierEntry>) {
        match sumti {
            Argument::Pronoun(p) => {
                let term = if p.as_str() == "ma" {
                    let var = self.fresh_var();
                    self.question_vars.push(var);
                    LogicalTerm::Variable(var)
                } else if matches!(p.as_str(), "da" | "de" | "di") {
                    LogicalTerm::Variable(self.interner.get_or_intern(p.as_str()))
                } else if p.as_str() == "ke'a" {
                    if let Some(var) = self.rel_clause_var {
                        self.ref_used = true;
                        LogicalTerm::Variable(var)
                    } else {
                        LogicalTerm::Unspecified
                    }
                } else if p.as_str() == "ce'u" {
                    if let Some(var) = self.property_open_var {
                        LogicalTerm::Variable(var)
                    } else {
                        // `ce'u` is the open place of a `ka` property abstraction; outside
                        // one it has no binder. The old "degrade to a fresh variable"
                        // behavior leaked a FREE variable through compilation — the da/de/di
                        // free-variable safety net does not close `_v` fresh vars, so the
                        // form reached logji non-ground (the exact shape the groundness
                        // boundary at `assert_typed_fact` now drops). Fail closed at the
                        // SOURCE instead: reject with a semantic error.
                        self.errors.push(
                            "ce'u outside a ka abstraction has no binder — property \
                             placeholders are only meaningful inside `lo ka ... kei`"
                                .to_string(),
                        );
                        LogicalTerm::Unspecified
                    }
                } else {
                    LogicalTerm::Constant(self.interner.get_or_intern(p.as_str()))
                };
                (term, vec![])
            }
            Argument::Name(n) => (
                LogicalTerm::Constant(self.interner.get_or_intern(n.as_str())),
                vec![],
            ),
            Argument::Description((gadri, desc_id)) => match gadri {
                Determiner::Lo => {
                    let var = self.fresh_var();
                    (
                        LogicalTerm::Variable(var),
                        vec![QuantifierEntry {
                            var,
                            desc_id: *desc_id,
                            restrictor: None,
                            incidental_restrictor: None,
                            kind: QuantifierKind::Existential,
                        }],
                    )
                }
                Determiner::RoLo => {
                    let var = self.fresh_var();
                    (
                        LogicalTerm::Variable(var),
                        vec![QuantifierEntry {
                            var,
                            desc_id: *desc_id,
                            restrictor: None,
                            incidental_restrictor: None,
                            kind: QuantifierKind::Universal,
                        }],
                    )
                }
                Determiner::RoLe => {
                    let var = self.fresh_var();
                    (
                        LogicalTerm::Variable(var),
                        vec![QuantifierEntry {
                            var,
                            desc_id: *desc_id,
                            restrictor: None,
                            incidental_restrictor: None,
                            kind: QuantifierKind::UniversalLe,
                        }],
                    )
                }
                Determiner::La => {
                    let name = self.get_predicate_head_name(*desc_id, selbris);
                    (
                        LogicalTerm::Constant(self.interner.get_or_intern(name)),
                        vec![],
                    )
                }
                Determiner::Le => {
                    let desc_str = self.get_predicate_head_name(*desc_id, selbris);
                    (
                        LogicalTerm::Description(self.interner.get_or_intern(desc_str)),
                        vec![],
                    )
                }
            },
            Argument::QuantifiedDescription((count, gadri, desc_id)) => {
                let var = self.fresh_var();
                let kind = match gadri {
                    Determiner::Le => QuantifierKind::ExactCountLe(*count),
                    _ => QuantifierKind::ExactCount(*count),
                };
                (
                    LogicalTerm::Variable(var),
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
                let inner = &sumtis[*inner_id as usize];
                self.resolve_argument(inner, sumtis, selbris, sentences)
            }
            Argument::ModalTagged((_modal_tag, inner_id)) => {
                let inner = &sumtis[*inner_id as usize];
                self.resolve_argument(inner, sumtis, selbris, sentences)
            }
            Argument::Restricted((inner_id, rel_clause)) => {
                let inner = &sumtis[*inner_id as usize];
                let (term, mut quants) = self.resolve_argument(inner, sumtis, selbris, sentences);

                let outer_rel_var = self.rel_clause_var;
                let outer_ref_used = self.ref_used;

                // The clause binds the quantifier variable introduced by the
                // inner sumti (lo / ro lo / PA lo). Argument that introduce NO
                // quantifier (la names, le descriptions, pro-sumti) get a fresh
                // clause variable instead, substituted by the resolved term
                // after the body is compiled.
                let clause_var = match quants.last() {
                    Some(last) => last.var,
                    None => self.fresh_var(),
                };
                self.rel_clause_var = Some(clause_var);
                self.ref_used = false;
                // Offer the clause variable as the implicit ke'a subject (x1) of
                // the clause's main bridi, consumed there before selbri
                // conversion. Save/restore so a nested Restricted clause does not
                // steal this one.
                let outer_clause_subject = self.pending_clause_subject.take();
                self.pending_clause_subject = Some(clause_var);

                let rel_body =
                    self.compile_sentence(rel_clause.body_sentence, selbris, sumtis, sentences);

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
                    // Stacked clauses (`poi P poi Q`, `noi P noi Q`) nest as
                    // Restricted(Restricted(...)), so the inner recursion already set the
                    // matching field for this quantifier. CONJOIN rather than overwrite,
                    // to keep every clause's predicate. Route by clause kind: poi/voi
                    // narrow the domain (`restrictor`); noi is non-restrictive and folds
                    // at the matrix level (`incidental_restrictor`, see `close_quantifier`).
                    // Mixed stacks (`poi P noi Q`) populate both fields independently.
                    match rel_clause.kind {
                        RelClauseKind::Noi => {
                            last.incidental_restrictor =
                                Some(match last.incidental_restrictor.take() {
                                    Some(existing) => LogicalForm::And(
                                        Box::new(existing),
                                        Box::new(new_restrictor),
                                    ),
                                    None => new_restrictor,
                                });
                        }
                        RelClauseKind::Poi | RelClauseKind::Voi => {
                            last.restrictor = Some(match last.restrictor.take() {
                                Some(existing) => {
                                    LogicalForm::And(Box::new(existing), Box::new(new_restrictor))
                                }
                                None => new_restrictor,
                            });
                        }
                    }
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
            Argument::QuotedLiteral(q) => (
                LogicalTerm::Constant(self.interner.get_or_intern(q.as_str())),
                vec![],
            ),
            Argument::Number(n) => (LogicalTerm::Number(*n), vec![]),
            Argument::Unspecified => (LogicalTerm::Unspecified, vec![]),
            Argument::Connected((left_id, _conn, _negated, _right_id)) => {
                // A connected sumti filling a place — bare, or under a place tag /
                // BAI modal — is distributed in `compile_proposition` (see
                // `find_connected_term`/`distribute_connected`) and never reaches
                // here. This arm is only hit for a connected sumti in a position the
                // distributor doesn't descend into (a be/bei argument or a
                // relative-clause body), where keeping the left operand silently
                // drops the right. FAIL CLOSED instead of losing meaning.
                self.errors.push(
                    "Connected sumti (`.e`/`.a`/`.o`/`.u`) in a be/bei argument or \
                     relative-clause body is not supported; restate it as separate \
                     sentences or place the connective at the bridi level."
                        .to_string(),
                );
                // Still resolve the left operand best-effort so a term is returned;
                // the pushed error fail-closes the assertion.
                let left = &sumtis[*left_id as usize];
                self.resolve_argument(left, sumtis, selbris, sentences)
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
