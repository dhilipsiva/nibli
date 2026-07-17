//! Proposition and sentence compilation: the main compilation entry points.
//!
//! Compiles predication nodes and sentence connectives into FOL. Handles place
//! tags, modal tags (the `via` custom modal), quantifier closure, existential
//! wrapping, tense wrappers, and deontic moods.
use super::*;

impl SemanticCompiler {
    /// Compiles a proposition (predication) into FOL with quantifier scoping and tense wrapping.
    pub fn compile_proposition(
        &mut self,
        proposition: &Proposition,
        predicates: &[Predicate],
        arguments: &[Argument],
        sentences: &[Sentence],
    ) -> LogicalForm {
        // Frame-local checkpoint for rel clauses attached to non-quantifier
        // argument (see `pending_matrix_conjuncts`): only conjuncts pushed by
        // THIS proposition's argument are drained into THIS proposition's matrix; nested
        // proposition (rel clause bodies, abstractions) drain their own.
        let matrix_conjunct_checkpoint = self.pending_matrix_conjuncts.len();
        // Frame-scoped `ma` closure: each `compile_proposition` frame drains only the
        // `ma` vars pushed during ITS frame (see the drain near the end). A
        // nested proposition (rel-clause body, abstraction body) takes its own
        // checkpoint AFTER any ancestor pushes, so it can no longer steal an
        // enclosing proposition's pending `ma` var (mirrors `matrix_conjunct_checkpoint`).
        let ma_checkpoint = self.question_vars.len();

        let all_terms: Vec<u32> = proposition
            .head_terms
            .iter()
            .chain(proposition.tail_terms.iter())
            .copied()
            .collect();

        let target_arity = self.get_predicate_arity(proposition.relation, predicates);

        let mut positioned: Vec<Option<LogicalTerm>> = vec![None; target_arity];

        // A relative clause's implicit `it` subject occupies x1 (the CLL
        // default), pushing the clause's explicit argument to x2+. Place it as the
        // x1 ARGUMENT here — BEFORE `apply_predicate` runs any `se`/`te`/`ve`/`xe`
        // conversion — so `poi se prami la .alis.` routes `it` through the
        // conversion to the correct underlying role (prami_x2), exactly as an
        // explicit subject would. One-shot: the first empty-head proposition WITHOUT
        // its own explicit `it` consumes it; nested proposition (abstraction bodies)
        // see `None`. Marking `ref_used` makes the caller skip the post-hoc
        // `inject_variable`, which cannot see conversion and would refill the
        // vacated x1 slot.
        //
        // SKIP RULE: when the proposition's own direct terms already carry an
        // explicit `it` — bare, or under a `fa`..`fu` place tag (the shape the
        // KR front-end emits for all-named args: empty head + FA-tagged tail,
        // e.g. `where loves(lover: Alis, loved: it)`) — the user has placed the
        // clause variable, and injecting would double-fill x1: a hard "place
        // already filled" reject for a place-tagged `it` colliding with the
        // pre-fill, or a silently self-referring x1 for a lone tagged `it`.
        // The explicit `it` resolves in the term loop below and sets `ref_used`
        // itself, exactly like the positional spelling (whose non-empty head
        // never reaches this branch) — so named ≡ positional, including leaving
        // `pending_clause_subject` untouched. The scan is SHALLOW: a `it`
        // nested in a Description/Restricted/Abstraction belongs to the inner
        // clause; a BAI-modal-carried `it` (`ModalTagged`) is not place-filling
        // and keeps the implicit-x1 default.
        if proposition.head_terms.is_empty()
            && target_arity >= 1
            && self.pending_clause_subject.is_some()
            && !Self::terms_contain_explicit_kea(&all_terms, arguments)
        {
            if let Some(subject) = self.pending_clause_subject.take() {
                positioned[0] = Some(LogicalTerm::Variable(subject));
                self.ref_used = true;
            }
        }

        // Surface-ordered scope introductions (descriptions + bare da/de/di),
        // folded in reverse below so the leftmost binder is outermost.
        let mut markers: Vec<ScopeMarker> = Vec::new();
        // da/de/di already recorded as a `Bare` marker — dedups a co-referring
        // `da` and lets the safety-net residual pass skip surface-captured vars.
        let mut introduced: std::collections::HashSet<lasso::Spur> =
            std::collections::HashSet::new();
        let mut modal_entries: Vec<(ModalTag, LogicalTerm, Vec<QuantifierEntry>)> = Vec::new();
        // Untagged argument that overflowed the predicate's arity (placed nowhere).
        // Preserves the prior silent-drop behaviour for over-arity untagged
        // argument, and drives the fail-closed `du` n-ary check below.
        let mut overflow_untagged: usize = 0;
        // CLL place counter (CLL ch.9, FA cmavo): `fa/fe/fi/fo/fu` set the place
        // number; a following UNTAGGED argument fills the place AFTER the last tag,
        // not the first free slot. Starts at x1 and skips slots already filled
        // (a `it` x1 pre-fill, or an out-of-order tag).
        let mut next_place: usize = 0;

        for &term_id in proposition
            .head_terms
            .iter()
            .chain(proposition.tail_terms.iter())
        {
            match &arguments[term_id as usize] {
                Argument::Tagged((tag, inner_id)) => {
                    let inner = &arguments[*inner_id as usize];
                    let (term, quants) =
                        self.resolve_argument(inner, arguments, predicates, sentences);
                    self.record_bare_marker(&term, &mut introduced, &mut markers);
                    markers.extend(quants.into_iter().map(ScopeMarker::Desc));
                    let idx = *tag as usize;
                    if idx >= target_arity {
                        // FAIL CLOSED: a named argument beyond the predicate's arity
                        // has no slot to bind into. Silently dropping the tagged term
                        // loses meaning (panel finding 2026-06-10) — reject instead.
                        self.errors.push(format!(
                            "A named argument targets place x{}, but the predicate only has \
                             {} place(s); it cannot be placed.",
                            idx + 1,
                            target_arity
                        ));
                    } else if positioned[idx].is_some() {
                        // FAIL CLOSED: a named argument re-targeting an already-filled
                        // place would last-win and drop the earlier term.
                        self.errors.push(format!(
                            "A named argument targets place x{}, which is already filled; \
                             the same place cannot be set twice.",
                            idx + 1
                        ));
                    } else {
                        positioned[idx] = Some(term);
                        next_place = idx + 1; // CLL: resume AFTER the tagged place
                    }
                }
                Argument::ModalTagged((modal_tag, inner_id)) => {
                    let inner = &arguments[*inner_id as usize];
                    let (term, quants) =
                        self.resolve_argument(inner, arguments, predicates, sentences);
                    // A bare `da`/`de`/`di` carried by a BAI modal (`ri'a da`) is
                    // introduced at this surface position. Its description quants
                    // (rare: `ri'a lo broda`) stay innermost (appended after the
                    // loop, with the modal predicate).
                    self.record_bare_marker(&term, &mut introduced, &mut markers);
                    // BAI modals are not place-filling — they do NOT advance the
                    // place counter.
                    modal_entries.push((*modal_tag, term, quants));
                }
                other => {
                    let (term, quants) =
                        self.resolve_argument(other, arguments, predicates, sentences);
                    self.record_bare_marker(&term, &mut introduced, &mut markers);
                    markers.extend(quants.into_iter().map(ScopeMarker::Desc));
                    // Skip slots already filled (`it` x1, or an out-of-order tag),
                    // then fill the current place and advance.
                    while next_place < target_arity && positioned[next_place].is_some() {
                        next_place += 1;
                    }
                    if next_place < target_arity {
                        positioned[next_place] = Some(term);
                        next_place += 1;
                    } else {
                        overflow_untagged += 1;
                    }
                }
            }
        }

        let args: Vec<LogicalTerm> = positioned
            .into_iter()
            .map(|slot| slot.unwrap_or(LogicalTerm::Unspecified))
            .collect();

        // Fail-closed: untagged argument that overflow the predicate's places were
        // dropped above (counted in `overflow_untagged`); reject rather than lose
        // meaning. `du` (a 2-place identity, consumed binary by nibli-reason's union-find)
        // gets a specific message; any other predicate errors too — but ONLY when its
        // arity is KNOWN in jbovlaste (an unknown word defaults to arity 2 and its
        // real arity may be higher, so an "overflow" there is unprovable; this also
        // keeps the no-XML build, where many proxy words default to 2, from
        // false-firing).
        let head_name = self.get_predicate_head_name(proposition.relation, predicates);
        if overflow_untagged > 0 {
            if head_name == nibli_types::relations::IDENTITY {
                self.errors.push(format!(
                    "`du` (identity) is a 2-place relation, but {} extra argument were supplied; \
                     n-ary identity is unsupported.",
                    overflow_untagged
                ));
            } else if LexiconSchema::get_arity(head_name).is_some() {
                self.errors.push(format!(
                    "{} untagged argument overflow the predicate `{}`'s {} place(s); the extra \
                     argument cannot be placed.",
                    overflow_untagged, head_name, target_arity
                ));
            }
        }

        let mut final_form = self.apply_predicate(
            proposition.relation,
            &args,
            predicates,
            arguments,
            sentences,
        );

        for (modal_tag, tagged_term, modal_quants) in modal_entries {
            markers.extend(modal_quants.into_iter().map(ScopeMarker::Desc));

            let (modal_gismu, modal_arity) = match &modal_tag {
                ModalTag::Custom(predicate_id) => {
                    let name = self.get_predicate_head_name(*predicate_id, predicates);
                    let arity = self.get_predicate_arity(*predicate_id, predicates);
                    (self.interner.get_or_intern(name), arity)
                }
            };

            // FAIL CLOSED: a modal relates its tagged argument (the modal predicate's x1)
            // to the main proposition's x1 (its x2), so the modal predicate needs at least 2
            // places. A 1-place predicate has no x2 to carry the main-proposition link — only
            // reachable via a `via` tag over an arity-1 predicate (every curated modal is
            // arity >= 2). Silently dropping `main_x1` loses meaning, so reject.
            if modal_arity < 2 {
                let modal_name = self.interner.resolve(&modal_gismu).to_string();
                self.errors.push(format!(
                    "Modal tag `{}` maps to a {}-place predicate, but a modal needs at \
                     least 2 places (x1 = the tag's own argument, x2 = the main proposition's \
                     x1 link); the main proposition's x1 cannot be carried.",
                    modal_name, modal_arity
                ));
                continue;
            }

            let main_x1 = args.first().cloned().unwrap_or(LogicalTerm::Unspecified);
            let mut modal_args = vec![LogicalTerm::Unspecified; modal_arity];
            modal_args[0] = tagged_term;
            modal_args[1] = main_x1;

            let modal_form = LogicalForm::Predicate {
                relation: modal_gismu,
                args: modal_args,
            };

            final_form = LogicalForm::And(Box::new(final_form), Box::new(modal_form));
        }

        // Conjoin rel clauses attached to non-quantifier argument (la names, le
        // descriptions, pro-argument) into the proposition matrix. These were
        // previously compiled then silently DISCARDED (panel finding
        // 2026-06-10), so `la .adam. poi gerku cu klama` answered TRUE with
        // only klama(adam) known.
        let pending: Vec<LogicalForm> = self
            .pending_matrix_conjuncts
            .split_off(matrix_conjunct_checkpoint);
        for conj in pending {
            final_form = LogicalForm::And(Box::new(final_form), Box::new(conj));
        }

        // Quantifier scope follows Lojban surface order (leftmost = outermost).
        // `markers` recorded every scope introduction — description quantifiers
        // AND bare logic variables (da/de/di) — in source order during the term
        // loop above. Folding the list in REVERSE makes the first-introduced
        // quantifier the outermost binder, so `da citka ro lo gerku` yields
        // `∃da.∀x` (the leading bare var outscopes the universal — an
        // Exists-over-ForAll root that nibli-reason's assertion dispatch now accepts by
        // skolemizing the leading ∃) while `ro lo gerku cu citka da` yields
        // `∀x.∃da` (unchanged).
        //
        // Safety net: a da/de/di reachable only via a merged predicate — a be/bei
        // role arg (`klama be da`) or any var the surface loop did not capture —
        // has no well-defined surface position, so it is collected from the built
        // `final_form` and closed INNERMOST (the conservative default). This
        // guarantees no bare var is ever left free; `introduced` excludes the
        // surface-captured vars so none is double-wrapped. Binder tracking in
        // `collect_free_logic_vars` skips abstraction-bound and prenex-bound vars,
        // and the description bodies / rel-clause restrictors are not folded into
        // `final_form` yet (they wrap below), so they are correctly out of scope.
        //
        // This innermost closure is a DELIBERATE, ACCEPTED boundary (not a
        // deferred TODO): a be/bei-arg or restrictor-internal `da` is soundly
        // closed innermost. A restrictor-internal `da` can never diverge (it is
        // bound inside the very quantifier whose domain the restrictor defines);
        // the ONLY construct where surface order would differ is an obscure
        // be-arg `da` preceding a tail-term universal (`klama be da ro lo gerku`),
        // where innermost gives ∀∃ vs surface ∃∀ — and even there innermost
        // merely under-claims (sound for assertions). Surface interleaving would
        // need source spans the flat AST does not carry, for ~zero semantic gain.
        // Locked by `test_da_in_be_arg_closed`,
        // `test_be_arg_da_with_universal_stays_innermost`, and
        // `test_restrictor_internal_da_closed_innermost`.
        let mut all_free_seen = std::collections::HashSet::new();
        let mut all_free: Vec<lasso::Spur> = Vec::new();
        let mut bound_vars: Vec<lasso::Spur> = Vec::new();
        Self::collect_free_logic_vars(
            &final_form,
            &self.interner,
            &self.prenex_vars,
            &mut bound_vars,
            &mut all_free_seen,
            &mut all_free,
        );
        for var in &all_free {
            if !introduced.contains(var) {
                final_form = LogicalForm::Exists(*var, Box::new(final_form));
            }
        }

        let has_universal_quantifier = markers.iter().any(|m| {
            matches!(
                m,
                ScopeMarker::Desc(e)
                    if matches!(e.kind, QuantifierKind::Universal | QuantifierKind::UniversalLe)
            )
        });

        for marker in markers.into_iter().rev() {
            final_form = match marker {
                ScopeMarker::Desc(entry) => {
                    self.close_quantifier(entry, final_form, predicates, arguments, sentences)
                }
                ScopeMarker::Bare(var) => LogicalForm::Exists(var, Box::new(final_form)),
            };
        }

        // Rare corner: a rel clause on a non-quantifier argument nested inside a
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

        for var in self.question_vars.drain(ma_checkpoint..) {
            final_form = LogicalForm::Exists(var, Box::new(final_form));
        }

        if proposition.negated {
            final_form = LogicalForm::Not(Box::new(final_form));
        }

        match &proposition.tense {
            Some(Tense::Past) => {
                final_form = LogicalForm::Past(Box::new(final_form));
            }
            Some(Tense::Now) => {
                final_form = LogicalForm::Present(Box::new(final_form));
            }
            Some(Tense::Future) => {
                final_form = LogicalForm::Future(Box::new(final_form));
            }
            None => {}
        }

        match &proposition.deontic {
            Some(DeonticMood::Obligation) => {
                final_form = LogicalForm::Obligatory(Box::new(final_form));
            }
            Some(DeonticMood::Permission) => {
                final_form = LogicalForm::Permitted(Box::new(final_form));
            }
            None => {}
        }

        final_form
    }

    /// Walk a compiled `LogicalForm` collecting free `da`/`de`/`di` logic
    /// variables for existential closure. Tracks binders (`Exists`/`ForAll`/
    /// `Count`) so a var already bound (e.g. by an abstraction body's own
    /// closure) is skipped — no double-wrap — and excludes prenex-bound vars.
    /// Dedups via `seen`; `out` preserves first-appearance order.
    fn collect_free_logic_vars(
        form: &LogicalForm,
        interner: &Rodeo,
        prenex: &std::collections::HashSet<lasso::Spur>,
        bound: &mut Vec<lasso::Spur>,
        seen: &mut std::collections::HashSet<lasso::Spur>,
        out: &mut Vec<lasso::Spur>,
    ) {
        match form {
            LogicalForm::Predicate { args, .. } => {
                for arg in args {
                    if let LogicalTerm::Variable(spur) = arg {
                        let name = interner.resolve(spur);
                        if name.starts_with('$')
                            && !bound.contains(spur)
                            && !prenex.contains(spur)
                            && seen.insert(*spur)
                        {
                            out.push(*spur);
                        }
                    }
                }
            }
            LogicalForm::And(l, r)
            | LogicalForm::Or(l, r)
            | LogicalForm::Biconditional(l, r)
            | LogicalForm::Xor(l, r) => {
                Self::collect_free_logic_vars(l, interner, prenex, bound, seen, out);
                Self::collect_free_logic_vars(r, interner, prenex, bound, seen, out);
            }
            LogicalForm::Not(inner)
            | LogicalForm::Past(inner)
            | LogicalForm::Present(inner)
            | LogicalForm::Future(inner)
            | LogicalForm::Obligatory(inner)
            | LogicalForm::Permitted(inner) => {
                Self::collect_free_logic_vars(inner, interner, prenex, bound, seen, out);
            }
            LogicalForm::Exists(v, body) | LogicalForm::ForAll(v, body) => {
                bound.push(*v);
                Self::collect_free_logic_vars(body, interner, prenex, bound, seen, out);
                bound.pop();
            }
            LogicalForm::Count { var, body, .. } => {
                bound.push(*var);
                Self::collect_free_logic_vars(body, interner, prenex, bound, seen, out);
                bound.pop();
            }
        }
    }

    /// Record a surface-ordered `Bare` scope marker if `term` is a bare logic
    /// variable (`da`/`de`/`di`) seen for the first time in this proposition frame and
    /// not prenex-bound. Dedups a co-referring var via `introduced`. Reads only
    /// `self.interner`/`self.prenex_vars`; mutates the caller's frame-local
    /// `introduced`/`markers`.
    fn record_bare_marker(
        &self,
        term: &LogicalTerm,
        introduced: &mut std::collections::HashSet<lasso::Spur>,
        markers: &mut Vec<ScopeMarker>,
    ) {
        if let LogicalTerm::Variable(spur) = term {
            let spur = *spur;
            let is_logic_var = self.interner.resolve(&spur).starts_with('$');
            if is_logic_var && !self.prenex_vars.contains(&spur) && introduced.insert(spur) {
                markers.push(ScopeMarker::Bare(spur));
            }
        }
    }

    /// Shallow scan of a proposition's direct terms for an explicit `it` (the
    /// bound-entity marker) — bare, or under place-tag wrappers (unwrapped
    /// transitively). Does NOT descend into Description/Restricted/Abstraction
    /// arguments (a nested clause's `it` belongs to that clause), and does NOT
    /// count a modal-carried `it` (`ModalTagged` is not place-filling, so it
    /// cannot collide with the implicit-x1 injection — see the skip rule at the
    /// call site). Mirrors the nibli-kr render-side `has_explicit_keha` scan.
    fn terms_contain_explicit_kea(term_ids: &[u32], arguments: &[Argument]) -> bool {
        term_ids.iter().any(|&id| {
            let mut s = &arguments[id as usize];
            loop {
                match s {
                    Argument::Tagged((_, inner_id)) => s = &arguments[*inner_id as usize],
                    Argument::Pronoun(p) => return p.as_str() == "it",
                    _ => return false,
                }
            }
        })
    }

    /// Compiles a sentence node (simple proposition or connected sentences) into FOL.
    pub fn compile_sentence(
        &mut self,
        sentence_id: u32,
        predicates: &[Predicate],
        arguments: &[Argument],
        sentences: &[Sentence],
    ) -> LogicalForm {
        match &sentences[sentence_id as usize] {
            Sentence::Simple(proposition) => {
                self.compile_proposition(proposition, predicates, arguments, sentences)
            }
            Sentence::Prenex((vars, body_id)) => {
                // `ro da [ro de ...] zo'u BODY` → ∀da. ∀de. … BODY.
                // Intern each prenex variable and mark it bound so the body's
                // compile_proposition does NOT existentially close it; then wrap the
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

                let mut form = self.compile_sentence(*body_id, predicates, arguments, sentences);

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
            Sentence::Quantified((kind, var, restr_id, clause_id, body_id)) => {
                // Block binder: `exactly N [the] X $v: body` / `every the X
                // $v: body`. The `$v` binds by the prenex mechanism (marked
                // bound so no frame closes it existentially), the domain is
                // built exactly like the term-position twin (close_quantifier's
                // shapes), and any where-clause folds on the DOMAIN side.
                let spur = self.interner.get_or_intern(var);
                let newly_bound = self.prenex_vars.insert(spur);
                let var_term = LogicalTerm::Variable(spur);

                let mut domain = match kind {
                    nibli_types::ast::BlockQuant::ExactCount(_) => {
                        // Indefinite restrictor: `X($v, _, …)` — the
                        // term-position ExactCount shape.
                        let desc_arity = self.get_predicate_arity(*restr_id, predicates);
                        let mut restrictor_args = Vec::with_capacity(desc_arity);
                        restrictor_args.push(var_term.clone());
                        while restrictor_args.len() < desc_arity {
                            restrictor_args.push(LogicalTerm::Unspecified);
                        }
                        self.apply_predicate(
                            *restr_id,
                            &restrictor_args,
                            predicates,
                            arguments,
                            sentences,
                        )
                    }
                    nibli_types::ast::BlockQuant::ExactCountDefinite(_)
                    | nibli_types::ast::BlockQuant::UniversalDefinite => {
                        // Opaque definite domain: `the_domain_<head>($v)` —
                        // the term-position ExactCountLe/UniversalLe shape.
                        self.build_the_domain_restrictor(*restr_id, spur, predicates)
                    }
                };
                if let Some(cl) = clause_id {
                    let clause_form = self.compile_sentence(*cl, predicates, arguments, sentences);
                    domain = LogicalForm::And(Box::new(domain), Box::new(clause_form));
                }

                let body_form = self.compile_sentence(*body_id, predicates, arguments, sentences);

                let form = match kind {
                    nibli_types::ast::BlockQuant::ExactCount(n)
                    | nibli_types::ast::BlockQuant::ExactCountDefinite(n) => LogicalForm::Count {
                        var: spur,
                        count: *n,
                        body: Box::new(LogicalForm::And(Box::new(domain), Box::new(body_form))),
                    },
                    nibli_types::ast::BlockQuant::UniversalDefinite => LogicalForm::ForAll(
                        spur,
                        Box::new(LogicalForm::Or(
                            Box::new(LogicalForm::Not(Box::new(domain))),
                            Box::new(body_form),
                        )),
                    ),
                };

                if newly_bound {
                    self.prenex_vars.remove(&spur);
                }
                form
            }
            Sentence::Connected((connective, left_id, right_id)) => {
                let left_form = self.compile_sentence(*left_id, predicates, arguments, sentences);
                let right_form = self.compile_sentence(*right_id, predicates, arguments, sentences);

                match connective {
                    SentenceConnective::Implies => LogicalForm::Or(
                        Box::new(LogicalForm::Not(Box::new(left_form))),
                        Box::new(right_form),
                    ),
                    SentenceConnective::And => {
                        LogicalForm::And(Box::new(left_form), Box::new(right_form))
                    }
                    SentenceConnective::Afterthought(conn) => match conn {
                        Connective::And => {
                            LogicalForm::And(Box::new(left_form), Box::new(right_form))
                        }
                        Connective::Or => {
                            LogicalForm::Or(Box::new(left_form), Box::new(right_form))
                        }
                        Connective::Iff => {
                            LogicalForm::Biconditional(Box::new(left_form), Box::new(right_form))
                        }
                        Connective::Whether => {
                            LogicalForm::Xor(Box::new(left_form), Box::new(right_form))
                        }
                    },
                }
            }
        }
    }
}
