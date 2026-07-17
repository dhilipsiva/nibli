//! Predicate compilation: maps predicate AST nodes to FOL logic forms.
//!
//! Handles root predicates, pair, conversion (se/te/ve/xe), negation,
//! ke...ke'e grouping, be...bei...be'o arguments, connected predicate,
//! and abstraction (event/fact/property/amount/concept). All predicates
//! are event-decomposed into Neo-Davidsonian form.
use super::*;
use lasso::Spur;

impl SemanticCompiler {
    /// Decomposes a predicate into Neo-Davidsonian event form with role predicates.
    pub(crate) fn event_decompose(&mut self, relation: &str, args: &[IrTerm]) -> IrForm {
        let ev = self.fresh_event_var();
        let ev_term = IrTerm::Variable(ev);

        let type_pred = IrForm::Predicate {
            relation: self.interner.get_or_intern(relation),
            args: vec![ev_term.clone()],
        };

        let mut form = type_pred;
        for (i, arg) in args.iter().enumerate() {
            let role_name = format!("{}_x{}", relation, i + 1);
            let role_pred = IrForm::Predicate {
                relation: self.interner.get_or_intern(&role_name),
                args: vec![ev_term.clone(), arg.clone()],
            };
            form = IrForm::And(Box::new(form), Box::new(role_pred));
        }

        IrForm::Exists(ev, Box::new(form))
    }

    /// Stable content key for an abstraction body, used to give two abstractions
    /// with the SAME content the SAME opaque marker (so `lo du'u P` matches `lo du'u P`
    /// across assert/query) while DIFFERENT contents get different markers (so
    /// `believe P` does not satisfy a `believe Q` query). The key resolves interned
    /// relation/constant names to strings and renames bound/event variables to
    /// first-seen positional indices, so it is invariant to the fresh event-var names
    /// each compile mints. Reasoning never reads the inner body (nibli-reason skips it behind
    /// the marker), so this key IS the only content identity that survives.
    fn abstraction_content_key(&self, body: &IrForm) -> String {
        let mut vars: std::collections::HashMap<Spur, usize> = std::collections::HashMap::new();
        let mut out = String::new();
        self.canon_form(body, &mut vars, &mut out);
        out
    }

    fn canon_var(spur: Spur, vars: &mut std::collections::HashMap<Spur, usize>) -> usize {
        let next = vars.len();
        *vars.entry(spur).or_insert(next)
    }

    fn canon_term(
        &self,
        term: &IrTerm,
        vars: &mut std::collections::HashMap<Spur, usize>,
        out: &mut String,
    ) {
        match term {
            IrTerm::Variable(s) => {
                out.push('v');
                out.push_str(&Self::canon_var(*s, vars).to_string());
            }
            IrTerm::Constant(s) => {
                out.push_str("c:");
                out.push_str(self.interner.resolve(s));
            }
            IrTerm::Description(s) => {
                out.push_str("d:");
                out.push_str(self.interner.resolve(s));
            }
            IrTerm::Unspecified => out.push('_'),
            IrTerm::Number(n) => {
                out.push_str("n:");
                out.push_str(&n.to_bits().to_string());
            }
        }
        out.push(';');
    }

    fn canon_form(
        &self,
        form: &IrForm,
        vars: &mut std::collections::HashMap<Spur, usize>,
        out: &mut String,
    ) {
        match form {
            IrForm::Predicate { relation, args } => {
                out.push('P');
                out.push_str(self.interner.resolve(relation));
                out.push('(');
                for a in args {
                    self.canon_term(a, vars, out);
                }
                out.push(')');
            }
            IrForm::And(l, r) => {
                out.push_str("&(");
                self.canon_form(l, vars, out);
                self.canon_form(r, vars, out);
                out.push(')');
            }
            IrForm::Or(l, r) => {
                out.push_str("|(");
                self.canon_form(l, vars, out);
                self.canon_form(r, vars, out);
                out.push(')');
            }
            IrForm::Not(i) => {
                out.push_str("!(");
                self.canon_form(i, vars, out);
                out.push(')');
            }
            IrForm::Exists(v, b) => {
                out.push('E');
                out.push_str(&Self::canon_var(*v, vars).to_string());
                out.push('(');
                self.canon_form(b, vars, out);
                out.push(')');
            }
            IrForm::ForAll(v, b) => {
                out.push('A');
                out.push_str(&Self::canon_var(*v, vars).to_string());
                out.push('(');
                self.canon_form(b, vars, out);
                out.push(')');
            }
            IrForm::Past(i) => self.canon_wrap("past", i, vars, out),
            IrForm::Present(i) => self.canon_wrap("now", i, vars, out),
            IrForm::Future(i) => self.canon_wrap("future", i, vars, out),
            IrForm::Obligatory(i) => self.canon_wrap("oblig", i, vars, out),
            IrForm::Permitted(i) => self.canon_wrap("perm", i, vars, out),
            IrForm::Count { var, count, body } => {
                out.push('#');
                out.push_str(&count.to_string());
                out.push(':');
                out.push_str(&Self::canon_var(*var, vars).to_string());
                out.push('(');
                self.canon_form(body, vars, out);
                out.push(')');
            }
            IrForm::Biconditional(l, r) => {
                out.push_str("<->(");
                self.canon_form(l, vars, out);
                self.canon_form(r, vars, out);
                out.push(')');
            }
            IrForm::Xor(l, r) => {
                out.push_str("^(");
                self.canon_form(l, vars, out);
                self.canon_form(r, vars, out);
                out.push(')');
            }
        }
    }

    fn canon_wrap(
        &self,
        tag: &str,
        inner: &IrForm,
        vars: &mut std::collections::HashMap<Spur, usize>,
        out: &mut String,
    ) {
        out.push_str(tag);
        out.push('(');
        self.canon_form(inner, vars, out);
        out.push(')');
    }

    /// Compiles a predicate node with given arguments into a FOL logic form.
    pub(crate) fn apply_predicate(
        &mut self,
        predicate_id: u32,
        args: &[IrTerm],
        predicates: &[Predicate],
        arguments: &[Argument],
        sentences: &[Sentence],
    ) -> IrForm {
        match &predicates[predicate_id as usize] {
            Predicate::Root(g) => {
                // The identity relation is a pure binary equivalence with no
                // event structure. It MUST stay a flat 2-arg predicate —
                // nibli-reason's union-find ingestion and identity-query arm
                // only match `relations::IDENTITY` at arity 2, so the
                // Neo-Davidsonian event form would silently disable equality
                // reasoning. (The >2-place fail-closed reject lives in
                // `compile_proposition`, where the dropped-overflow argument are visible.)
                if g == nibli_types::relations::IDENTITY {
                    let fitted = Self::fit_args(args, 2);
                    return IrForm::Predicate {
                        relation: self
                            .interner
                            .get_or_intern(nibli_types::relations::IDENTITY),
                        args: fitted,
                    };
                }
                let arity = LexiconSchema::get_arity_or_default(g.as_str());
                let fitted = Self::fit_args(args, arity);
                self.event_decompose(g.as_str(), &fitted)
            }
            Predicate::Pair((mod_id, head_id)) => {
                // Per-unit (name, arity, conversion swaps): a converted unit's
                // args are mapped fit-then-swap through its swap chain, exactly
                // like the `Predicate::Converted` arm — `menli se ponse` puts the
                // shared x1 in ponse_x2, and `se ponse datni` as a restrictor
                // modifier likewise (the pre-2026-07-12 flatten dropped the
                // swap silently).
                let (mod_name, mod_arity, mod_swaps) =
                    self.get_predicate_unit_base(*mod_id, predicates);
                let (head_name, head_arity, head_swaps) =
                    self.get_predicate_unit_base(*head_id, predicates);

                let mut mod_args = vec![IrTerm::Unspecified; mod_arity];
                if !args.is_empty() && mod_arity > 0 {
                    mod_args[0] = args[0].clone();
                }
                for &idx in &mod_swaps {
                    if idx < mod_args.len() {
                        mod_args.swap(0, idx);
                    }
                }
                let mut head_args = Self::fit_args(args, head_arity);
                for &idx in &head_swaps {
                    if idx < head_args.len() {
                        head_args.swap(0, idx);
                    }
                }

                let ev = self.fresh_event_var();
                let ev_term = IrTerm::Variable(ev);

                let type_pred = IrForm::Predicate {
                    relation: self.interner.get_or_intern(&head_name),
                    args: vec![ev_term.clone()],
                };
                let mut form = type_pred;

                // Emit ALL head roles, including Unspecified — exactly like root
                // event decomposition. Skipping Unspecified roles left `poi <pair>`
                // clauses with no injectable _x1 slot, so the ambiguity firewall
                // FALSELY rejected valid clauses (panel finding 2026-06-10).
                for (i, arg) in head_args.iter().enumerate() {
                    let role = format!("{}_x{}", head_name, i + 1);
                    let role_pred = IrForm::Predicate {
                        relation: self.interner.get_or_intern(&role),
                        args: vec![ev_term.clone(), arg.clone()],
                    };
                    form = IrForm::And(Box::new(form), Box::new(role_pred));
                }

                // Modifier roles likewise emit Unspecified slots (shared event var
                // keeps modifier and head describing one predication).
                for (i, arg) in mod_args.iter().enumerate() {
                    let role = format!("{}_x{}", mod_name, i + 1);
                    let role_pred = IrForm::Predicate {
                        relation: self.interner.get_or_intern(&role),
                        args: vec![ev_term.clone(), arg.clone()],
                    };
                    form = IrForm::And(Box::new(form), Box::new(role_pred));
                }

                IrForm::Exists(ev, Box::new(form))
            }
            Predicate::Converted((conv, inner_id)) => {
                let mut permuted = args.to_vec();
                match conv {
                    Conversion::Swap12 if permuted.len() >= 2 => permuted.swap(0, 1),
                    Conversion::Swap13 if permuted.len() >= 3 => permuted.swap(0, 2),
                    Conversion::Swap14 if permuted.len() >= 4 => permuted.swap(0, 3),
                    Conversion::Swap15 if permuted.len() >= 5 => permuted.swap(0, 4),
                    _ => {}
                }
                self.apply_predicate(*inner_id, &permuted, predicates, arguments, sentences)
            }
            Predicate::Negated(inner_id) => {
                let inner = self.apply_predicate(*inner_id, args, predicates, arguments, sentences);
                IrForm::Not(Box::new(inner))
            }
            Predicate::Grouped(inner_id) => {
                self.apply_predicate(*inner_id, args, predicates, arguments, sentences)
            }
            Predicate::WithArgs((core_id, bound_ids)) => {
                let core_arity = self.get_predicate_arity(*core_id, predicates);
                let mut merged = Vec::with_capacity(core_arity);
                let mut inner_quantifiers: Vec<QuantifierEntry> = Vec::new();

                merged.push(if !args.is_empty() {
                    args[0].clone()
                } else {
                    IrTerm::Unspecified
                });

                for bound_id in bound_ids.iter() {
                    let bound_argument = &arguments[*bound_id as usize];
                    let (term, quants) =
                        self.resolve_argument(bound_argument, arguments, predicates, sentences);
                    inner_quantifiers.extend(quants);
                    merged.push(term);
                }

                let bound_count = 1 + bound_ids.len();
                for i in merged.len()..core_arity {
                    if i < args.len() && i >= bound_count {
                        merged.push(args[i].clone());
                    } else {
                        merged.push(IrTerm::Unspecified);
                    }
                }

                let mut form =
                    self.apply_predicate(*core_id, &merged, predicates, arguments, sentences);

                for entry in inner_quantifiers.into_iter().rev() {
                    form = self.close_quantifier(entry, form, predicates, arguments, sentences);
                }

                form
            }
            Predicate::Abstraction((kind, body_sentence_idx)) => {
                let type_name = match kind {
                    AbstractionKind::Event => "event",
                    AbstractionKind::Fact => "fact",
                    AbstractionKind::Property => "property",
                    AbstractionKind::Amount => "amount",
                    AbstractionKind::Concept => "concept",
                };

                let outer_ka_var = self.property_open_var;
                if *kind == AbstractionKind::Property {
                    if let Some(IrTerm::Variable(v)) = args.first() {
                        self.property_open_var = Some(*v);
                    }
                }

                let inner_form =
                    self.compile_sentence(*body_sentence_idx, predicates, arguments, sentences);
                self.property_open_var = outer_ka_var;

                let type_pred = IrForm::Predicate {
                    relation: self.interner.get_or_intern(type_name),
                    args: Self::fit_args(args, 1),
                };
                // Opacity marker: a content-hashed unary predicate over the abstraction
                // referent. nibli-reason MATCHES it (same-content abstractions unify; different
                // contents do not) but SKIPS the body behind it, so the body's predicates
                // never become free-standing ground facts — asserting `mi krici lo du'u P`
                // ("I believe that P") no longer makes a bare query `P` return TRUE. The
                // body is retained only for rendering; `__abs_` markers and the type
                // predicate are dropped by the renderer.
                let key = self.abstraction_content_key(&inner_form);
                let marker_rel = format!("__abs_{:016x}", fnv1a_hash(&key));
                let referent = args.first().cloned().unwrap_or(IrTerm::Unspecified);
                let marker = IrForm::Predicate {
                    relation: self.interner.get_or_intern(&marker_rel),
                    args: vec![referent],
                };
                IrForm::And(
                    Box::new(type_pred),
                    Box::new(IrForm::And(Box::new(marker), Box::new(inner_form))),
                )
            }
        }
    }
}

/// Deterministic FNV-1a 64-bit hash of the abstraction content key. Stability is
/// only required within a single process (assert + query share the same binary),
/// which FNV-1a trivially satisfies; collisions are astronomically unlikely for the
/// short structural keys produced by `abstraction_content_key`.
fn fnv1a_hash(s: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

#[cfg(test)]
mod fnv1a_tests {
    // The `__abs_<hash>` opacity keys depend on FNV-1a's collision resistance —
    // a weakened mix (e.g. `^=` → `|=`, which saturates bits) would silently
    // conflate DIFFERENT abstractions into one opaque constant. Pin the exact
    // algorithm with the published FNV-1a reference vectors.
    #[test]
    fn fnv1a_matches_reference_vectors() {
        assert_eq!(super::fnv1a_hash(""), 0xcbf29ce484222325);
        assert_eq!(super::fnv1a_hash("a"), 0xaf63dc4c8601ec8c);
        assert_eq!(super::fnv1a_hash("foobar"), 0x85944171f73967e8);
    }
}
