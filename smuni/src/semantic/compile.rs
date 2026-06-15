//! Bridi and sentence compilation: the main compilation entry points.
//!
//! Compiles bridi (predication) nodes and sentence connectives into FOL.
//! Handles place tags (fa/fe/fi/fo/fu), modal tags (BAI, fi'o), sumti
//! connective expansion, quantifier closure, da/de/di existential wrapping,
//! tense wrappers (pu/ca/ba), and deontic attitudinals (ei/e'e).
use super::*;

impl SemanticCompiler {
    /// Compiles a bridi (predication) into FOL with quantifier scoping and tense wrapping.
    pub fn compile_bridi(
        &mut self,
        bridi: &Bridi,
        selbris: &[Selbri],
        sumtis: &[Sumti],
        sentences: &[Sentence],
    ) -> LogicalForm {
        // Frame-local checkpoint for rel clauses attached to non-quantifier
        // sumti (see `pending_matrix_conjuncts`): only conjuncts pushed by
        // THIS bridi's sumti are drained into THIS bridi's matrix; nested
        // bridi (rel clause bodies, abstractions) drain their own.
        let matrix_conjunct_checkpoint = self.pending_matrix_conjuncts.len();

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
                    Connective::Ju => LogicalForm::Xor(Box::new(left_form), Box::new(right_form)),
                };
            }
        }

        let target_arity = self.get_selbri_arity(bridi.relation, selbris);

        let mut positioned: Vec<Option<LogicalTerm>> = vec![None; target_arity];

        // A relative clause's implicit `ke'a` subject occupies x1 (the CLL
        // default), pushing the clause's explicit sumti to x2+. Place it as the
        // x1 ARGUMENT here — BEFORE `apply_selbri` runs any `se`/`te`/`ve`/`xe`
        // conversion — so `poi se prami la .alis.` routes `ke'a` through the
        // conversion to the correct underlying role (prami_x2), exactly as an
        // explicit subject would. One-shot: only the clause's main (first) bridi
        // consumes it; nested bridi (abstraction bodies) see `None`. Marking
        // `kea_used` makes the caller skip the post-hoc `inject_variable`, which
        // cannot see conversion and would refill the vacated x1 slot.
        if bridi.head_terms.is_empty() && target_arity >= 1 {
            if let Some(subject) = self.pending_clause_subject.take() {
                positioned[0] = Some(LogicalTerm::Variable(subject));
                self.kea_used = true;
            }
        }

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
                    } else {
                        // FAIL CLOSED: a place tag beyond the selbri's arity has no
                        // slot to bind into. Silently dropping the tagged term loses
                        // meaning (panel finding 2026-06-10) — reject instead.
                        let tag_name = match tag {
                            PlaceTag::Fa => "fa",
                            PlaceTag::Fe => "fe",
                            PlaceTag::Fi => "fi",
                            PlaceTag::Fo => "fo",
                            PlaceTag::Fu => "fu",
                        };
                        self.errors.push(format!(
                            "Place tag `{}` targets place x{}, but the selbri only has \
                             {} place(s); the tagged term cannot be placed.",
                            tag_name,
                            idx + 1,
                            target_arity
                        ));
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

        // Conjoin rel clauses attached to non-quantifier sumti (la names, le
        // descriptions, pro-sumti) into the bridi matrix. These were
        // previously compiled then silently DISCARDED (panel finding
        // 2026-06-10), so `la .adam. poi gerku cu klama` answered TRUE with
        // only klama(adam) known.
        let pending: Vec<LogicalForm> = self
            .pending_matrix_conjuncts
            .split_off(matrix_conjunct_checkpoint);
        for conj in pending {
            final_form = LogicalForm::And(Box::new(final_form), Box::new(conj));
        }

        // Bare logic variables (da/de/di) used as arguments get existential
        // closure. Lojban scope is left-to-right: in `ro lo gerku cu citka da`
        // the universal outscopes the existential (∀x.∃y), so when a universal
        // description is closed, bare-var existentials are wrapped INSIDE
        // (before the ForAll), keeping ForAll at the root — logji's assertion
        // dispatch compiles rules only from a ForAll root, and the old
        // Exists-over-ForAll shape dead-ended, silently losing the whole
        // assertion (panel finding 2026-06-10). Purely existential sentences
        // keep the original outermost wrap.
        let mut da_vars_seen = std::collections::HashSet::new();
        let mut da_vars: Vec<lasso::Spur> = Vec::new();
        for arg in &args {
            if let LogicalTerm::Variable(spur) = arg {
                let name = self.interner.resolve(spur);
                // Skip vars bound by an enclosing prenex — those are universally
                // quantified by the prenex lowering, not existentially closed here.
                if matches!(name, "da" | "de" | "di")
                    && !self.prenex_vars.contains(spur)
                    && da_vars_seen.insert(*spur)
                {
                    da_vars.push(*spur);
                }
            }
        }
        let has_universal_quantifier = quantifiers.iter().any(|e| {
            matches!(
                e.kind,
                QuantifierKind::Universal | QuantifierKind::UniversalLe
            )
        });
        if has_universal_quantifier {
            for var in &da_vars {
                final_form = LogicalForm::Exists(*var, Box::new(final_form));
            }
        }

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
                    let mut body = LogicalForm::Or(
                        Box::new(LogicalForm::Not(Box::new(desc_restrictor))),
                        Box::new(final_form),
                    );

                    if let Some(rel_restrictor) = entry.restrictor {
                        body = LogicalForm::Or(
                            Box::new(LogicalForm::Not(Box::new(rel_restrictor))),
                            Box::new(body),
                        );
                    }

                    final_form = LogicalForm::ForAll(entry.var, Box::new(body));
                }
                QuantifierKind::Existential => {
                    let mut body =
                        LogicalForm::And(Box::new(desc_restrictor), Box::new(final_form));

                    if let Some(rel_restrictor) = entry.restrictor {
                        body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                    }

                    final_form = LogicalForm::Exists(entry.var, Box::new(body));
                }
                QuantifierKind::ExactCount(n) => {
                    let mut body =
                        LogicalForm::And(Box::new(desc_restrictor), Box::new(final_form));

                    if let Some(rel_restrictor) = entry.restrictor {
                        body = LogicalForm::And(Box::new(rel_restrictor), Box::new(body));
                    }

                    final_form = LogicalForm::Count {
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
                        Box::new(final_form),
                    );

                    if let Some(rel_restrictor) = entry.restrictor {
                        body = LogicalForm::Or(
                            Box::new(LogicalForm::Not(Box::new(rel_restrictor))),
                            Box::new(body),
                        );
                    }

                    final_form = LogicalForm::ForAll(entry.var, Box::new(body));
                }
                QuantifierKind::ExactCountLe(n) => {
                    let le_restrictor =
                        self.build_le_domain_restrictor(entry.desc_id, entry.var, selbris);
                    let mut body = LogicalForm::And(Box::new(le_restrictor), Box::new(final_form));

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

        // Rare corner: a rel clause on a non-quantifier sumti nested inside a
        // description restrictor (e.g. the be-arg in `lo gerku be la .adam.
        // poi prenu`) pushes its conjunct while the closure loop above
        // compiles the restrictor — too late to join the matrix. Conjoin it
        // at the top level when sound (no universal: the root stays a ground
        // conjunction); under a universal the root must remain ForAll for
        // rule compilation, so FAIL CLOSED rather than silently drop.
        let late: Vec<LogicalForm> = self
            .pending_matrix_conjuncts
            .split_off(matrix_conjunct_checkpoint);
        if !late.is_empty() {
            if has_universal_quantifier {
                self.errors.push(
                    "Relative clause on a name/description inside a universal \
                     description's restrictor cannot be represented; restate it \
                     as a separate sentence."
                        .to_string(),
                );
            } else {
                for conj in late {
                    final_form = LogicalForm::And(Box::new(final_form), Box::new(conj));
                }
            }
        }

        if !has_universal_quantifier {
            for var in &da_vars {
                final_form = LogicalForm::Exists(*var, Box::new(final_form));
            }
        }

        for var in self.ma_vars.drain(..) {
            final_form = LogicalForm::Exists(var, Box::new(final_form));
        }

        if bridi.negated {
            final_form = LogicalForm::Not(Box::new(final_form));
        }

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

    /// Compiles a sentence node (simple bridi or connected sentences) into FOL.
    pub fn compile_sentence(
        &mut self,
        sentence_id: u32,
        selbris: &[Selbri],
        sumtis: &[Sumti],
        sentences: &[Sentence],
    ) -> LogicalForm {
        match &sentences[sentence_id as usize] {
            Sentence::Simple(bridi) => self.compile_bridi(bridi, selbris, sumtis, sentences),
            Sentence::Prenex((vars, body_id)) => {
                // `ro da [ro de ...] zo'u BODY` → ∀da. ∀de. … BODY.
                // Intern each prenex variable and mark it bound so the body's
                // compile_bridi does NOT existentially close it; then wrap the
                // compiled body in nested ForAll (outermost = first variable).
                let spurs: Vec<lasso::Spur> = vars
                    .iter()
                    .map(|v| self.interner.get_or_intern(v))
                    .collect();
                let saved: Vec<lasso::Spur> = spurs
                    .iter()
                    .filter(|s| self.prenex_vars.insert(**s))
                    .copied()
                    .collect();

                let mut form = self.compile_sentence(*body_id, selbris, sumtis, sentences);

                // Wrap inner-to-outer so the first variable is the outermost ∀.
                for spur in spurs.iter().rev() {
                    form = LogicalForm::ForAll(*spur, Box::new(form));
                }

                // Restore: only remove the vars THIS prenex introduced (a nested
                // prenex may share a name with an outer one).
                for s in saved {
                    self.prenex_vars.remove(&s);
                }
                form
            }
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
                    SentenceConnective::GoGi => {
                        LogicalForm::Biconditional(Box::new(left_form), Box::new(right_form))
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
                            Connective::Jo => LogicalForm::Biconditional(Box::new(l), Box::new(r)),
                            Connective::Ju => LogicalForm::Xor(Box::new(l), Box::new(r)),
                        }
                    }
                }
            }
        }
    }
}
