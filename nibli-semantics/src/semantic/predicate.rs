//! Predicate compilation: maps predicate AST nodes to FOL logic forms.
//!
//! Handles root predicates, pair, conversion (se/te/ve/xe), negation,
//! ke...ke'e grouping, be...bei...be'o arguments, connected predicate,
//! and abstraction (event/fact/property/amount/concept). All predicates
//! are event-decomposed into Neo-Davidsonian form.
use super::*;
use lasso::Spur;
use nibli_types::abstraction::encode_v1 as encode_abstraction_marker_v1;
#[cfg(test)]
use nibli_types::abstraction::{
    canonicalize_relation as canonicalize_abstraction_marker,
    encode_v1_with_digest as encode_abstraction_marker_v1_with_digest,
};

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

    /// Stable, injective content key for an abstraction body. Every node/term
    /// carries an explicit tag and every string is length-prefixed; bound/event
    /// variables are alpha-renamed to first-seen ordinals. This is semantic
    /// identity, so delimiter-concatenated text and `Debug` formatting are both
    /// deliberately excluded.
    fn abstraction_content_key(&self, kind: AbstractionKind, body: &IrForm) -> Vec<u8> {
        let mut vars: std::collections::HashMap<Spur, usize> = std::collections::HashMap::new();
        let mut out = vec![match kind {
            AbstractionKind::Event => 0xa0,
            AbstractionKind::Fact => 0xa1,
            AbstractionKind::Property => 0xa2,
            AbstractionKind::Amount => 0xa3,
            AbstractionKind::Concept => 0xa4,
        }];
        self.canon_form(body, &mut vars, &mut out);
        out
    }

    fn canon_u64(value: u64, out: &mut Vec<u8>) {
        out.extend_from_slice(&value.to_be_bytes());
    }

    fn canon_str(value: &str, out: &mut Vec<u8>) {
        Self::canon_u64(value.len() as u64, out);
        out.extend_from_slice(value.as_bytes());
    }

    fn canon_var(spur: Spur, vars: &mut std::collections::HashMap<Spur, usize>) -> usize {
        let next = vars.len();
        *vars.entry(spur).or_insert(next)
    }

    fn canon_term(
        &self,
        term: &IrTerm,
        vars: &mut std::collections::HashMap<Spur, usize>,
        out: &mut Vec<u8>,
    ) {
        match term {
            IrTerm::Variable(s) => {
                out.push(0x00);
                Self::canon_u64(Self::canon_var(*s, vars) as u64, out);
            }
            IrTerm::Constant(s) => {
                out.push(0x01);
                Self::canon_str(self.interner.resolve(s), out);
            }
            IrTerm::Description(s) => {
                out.push(0x02);
                Self::canon_str(self.interner.resolve(s), out);
            }
            IrTerm::Unspecified => out.push(0x03),
            IrTerm::Number(n) => {
                out.push(0x04);
                Self::canon_u64(n.to_bits(), out);
            }
        }
    }

    fn canon_form(
        &self,
        form: &IrForm,
        vars: &mut std::collections::HashMap<Spur, usize>,
        out: &mut Vec<u8>,
    ) {
        match form {
            IrForm::Predicate { relation, args } => {
                let relation = self.interner.resolve(relation);
                if relation.starts_with("__abs_") {
                    // A nested abstraction's body is the following sibling in
                    // the compiled form, so its marker payload would duplicate
                    // that content and grow exponentially with nesting. Encode
                    // only the marker category + referent topology here; the
                    // body itself supplies the lossless nested identity.
                    out.push(0x11);
                } else {
                    out.push(0x10);
                    Self::canon_str(relation, out);
                }
                Self::canon_u64(args.len() as u64, out);
                for a in args {
                    self.canon_term(a, vars, out);
                }
            }
            IrForm::And(l, r) => {
                out.push(0x12);
                self.canon_form(l, vars, out);
                self.canon_form(r, vars, out);
            }
            IrForm::Or(l, r) => {
                out.push(0x13);
                self.canon_form(l, vars, out);
                self.canon_form(r, vars, out);
            }
            IrForm::Not(i) => {
                out.push(0x14);
                self.canon_form(i, vars, out);
            }
            IrForm::Exists(v, b) => {
                out.push(0x15);
                Self::canon_u64(Self::canon_var(*v, vars) as u64, out);
                self.canon_form(b, vars, out);
            }
            IrForm::ForAll(v, b) => {
                out.push(0x16);
                Self::canon_u64(Self::canon_var(*v, vars) as u64, out);
                self.canon_form(b, vars, out);
            }
            IrForm::Past(i) => self.canon_wrap(0x17, i, vars, out),
            IrForm::Present(i) => self.canon_wrap(0x18, i, vars, out),
            IrForm::Future(i) => self.canon_wrap(0x19, i, vars, out),
            IrForm::Obligatory(i) => self.canon_wrap(0x1a, i, vars, out),
            IrForm::Permitted(i) => self.canon_wrap(0x1b, i, vars, out),
            IrForm::Count { var, count, body } => {
                out.push(0x1c);
                Self::canon_u64(*count as u64, out);
                Self::canon_u64(Self::canon_var(*var, vars) as u64, out);
                self.canon_form(body, vars, out);
            }
            IrForm::Biconditional(l, r) => {
                out.push(0x1d);
                self.canon_form(l, vars, out);
                self.canon_form(r, vars, out);
            }
            IrForm::Xor(l, r) => {
                out.push(0x1e);
                self.canon_form(l, vars, out);
                self.canon_form(r, vars, out);
            }
        }
    }

    fn canon_wrap(
        &self,
        tag: u8,
        inner: &IrForm,
        vars: &mut std::collections::HashMap<Spur, usize>,
        out: &mut Vec<u8>,
    ) {
        out.push(tag);
        self.canon_form(inner, vars, out);
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
            Predicate::Pair(_) => {
                // Flatten the WHOLE stack (nested pairs and groups included):
                // one shared event; the head unit contributes the type
                // predicate plus its roles, and every other unit contributes
                // role predicates only — no standalone type predicate (that
                // would be the intersective fallacy). Per-unit (name, arity,
                // conversion swaps): a converted unit's args are mapped
                // fit-then-swap through its swap chain, exactly like the
                // `Predicate::Converted` arm — `menli se ponse` puts the
                // shared x1 in ponse_x2 (the pre-2026-07-12 flatten dropped
                // the swap silently; the pre-2026-07-19 two-unit collapse
                // dropped whole units of a 3+ stack silently).
                let mut modifier_units: Vec<(&str, usize, Vec<usize>)> = Vec::new();
                let (head_name, head_arity, head_swaps) = self.collect_stack_units(
                    predicate_id,
                    predicates,
                    Vec::new(),
                    &mut modifier_units,
                );

                let mut head_args = Self::fit_args(args, head_arity);
                for &idx in &head_swaps {
                    if idx < head_args.len() {
                        head_args.swap(0, idx);
                    }
                }

                let ev = self.fresh_event_var();
                let ev_term = IrTerm::Variable(ev);

                let type_pred = IrForm::Predicate {
                    relation: self.interner.get_or_intern(head_name),
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

                // Modifier roles likewise emit Unspecified slots (the shared
                // event var keeps every unit describing one predication). Each
                // modifier links the referent through its own x1, post-swap.
                for (mod_name, mod_arity, mod_swaps) in &modifier_units {
                    let mut mod_args = vec![IrTerm::Unspecified; *mod_arity];
                    if !args.is_empty() && *mod_arity > 0 {
                        mod_args[0] = args[0].clone();
                    }
                    for &idx in mod_swaps {
                        if idx < mod_args.len() {
                            mod_args.swap(0, idx);
                        }
                    }
                    for (i, arg) in mod_args.iter().enumerate() {
                        let role = format!("{}_x{}", mod_name, i + 1);
                        let role_pred = IrForm::Predicate {
                            relation: self.interner.get_or_intern(&role),
                            args: vec![ev_term.clone(), arg.clone()],
                        };
                        form = IrForm::And(Box::new(form), Box::new(role_pred));
                    }
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
                if *kind == AbstractionKind::Property
                    && let Some(IrTerm::Variable(v)) = args.first()
                {
                    self.property_open_var = Some(*v);
                }

                let inner_form =
                    self.compile_sentence(*body_sentence_idx, predicates, arguments, sentences);
                self.property_open_var = outer_ka_var;

                let type_pred = IrForm::Predicate {
                    relation: self.interner.get_or_intern(type_name),
                    args: Self::fit_args(args, 1),
                };
                // Opacity marker: a lossless alpha-canonical unary predicate over the abstraction
                // referent. nibli-reason MATCHES it (same-content abstractions unify; different
                // contents do not) but SKIPS the body behind it, so the body's predicates
                // never become free-standing ground facts — asserting `mi krici lo du'u P`
                // ("I believe that P") no longer makes a bare query `P` return TRUE. The
                // body is retained only for rendering; `__abs_` markers and the type
                // predicate are dropped by the renderer.
                let key = self.abstraction_content_key(*kind, &inner_form);
                let marker_rel = encode_abstraction_marker_v1(&key);
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

#[cfg(test)]
mod abstraction_identity_tests {
    use super::*;

    #[test]
    fn abstraction_marker_digest_collision_compares_the_lossless_key() {
        let mut compiler = SemanticCompiler::new();
        let relation = compiler.interner.get_or_intern("equals");
        // These two argument lists produced the same delimiter-concatenated
        // key in the old encoder:
        //   c:a; c:b;c:c;  ==  c:a;c:b; c:c;
        let a = compiler.interner.get_or_intern("a");
        let b_semicolon_c_colon_c = compiler.interner.get_or_intern("b;c:c");
        let a_semicolon_c_colon_b = compiler.interner.get_or_intern("a;c:b");
        let c = compiler.interner.get_or_intern("c");
        let left_body = IrForm::Predicate {
            relation,
            args: vec![IrTerm::Constant(a), IrTerm::Constant(b_semicolon_c_colon_c)],
        };
        let right_body = IrForm::Predicate {
            relation,
            args: vec![IrTerm::Constant(a_semicolon_c_colon_b), IrTerm::Constant(c)],
        };
        let left_key = compiler.abstraction_content_key(AbstractionKind::Fact, &left_body);
        let right_key = compiler.abstraction_content_key(AbstractionKind::Fact, &right_body);
        assert_ne!(
            left_key, right_key,
            "tagged length-prefixing must distinguish delimiter-adversarial structures"
        );

        let forced_digest = 0x0123_4567_89ab_cdef;
        let left = encode_abstraction_marker_v1_with_digest(&left_key, forced_digest);
        let right = encode_abstraction_marker_v1_with_digest(&right_key, forced_digest);
        assert_ne!(
            left, right,
            "equal digests must not imply equal abstractions"
        );
        assert_eq!(
            left,
            encode_abstraction_marker_v1_with_digest(&left_key, forced_digest),
            "the same canonical key must remain byte-stable"
        );
        assert_ne!(
            canonicalize_abstraction_marker(&left).unwrap(),
            canonicalize_abstraction_marker(&right).unwrap(),
            "the production canonicalizer must retain distinct full keys after a forced collision"
        );
    }

    #[test]
    fn abstraction_v1_codec_and_marker_are_exact_goldens() {
        let mut compiler = SemanticCompiler::new();
        let x = compiler.interner.get_or_intern("$source_name");
        let dog = compiler.interner.get_or_intern("dog");
        let big = compiler.interner.get_or_intern("big");
        let dog_x = IrForm::Predicate {
            relation: dog,
            args: vec![IrTerm::Variable(x)],
        };
        let big_x = IrForm::Predicate {
            relation: big,
            args: vec![IrTerm::Variable(x)],
        };
        let body = IrForm::Past(Box::new(IrForm::Exists(
            x,
            Box::new(IrForm::And(
                Box::new(dog_x),
                Box::new(IrForm::Not(Box::new(big_x))),
            )),
        )));

        let key = compiler.abstraction_content_key(AbstractionKind::Fact, &body);
        let key_hex = key
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        assert_eq!(
            key_hex,
            "a11715000000000000000012100000000000000003646f67000000000000000100\
             000000000000000014100000000000000003626967000000000000000100000000\
             0000000000"
        );
        assert_eq!(
            encode_abstraction_marker_v1(&key),
            "__abs_v1_9c4d04bf892ae0da_a11715000000000000000012100000000000000003646f67\
             0000000000000001000000000000000000141000000000000000036269670000000000000001\
             000000000000000000"
        );
    }

    #[test]
    fn nested_abstraction_v1_codec_is_an_exact_golden() {
        let mut compiler = SemanticCompiler::new();
        let referent = compiler.interner.get_or_intern("$nested");
        let mut nested_key = vec![0xa0, 0x10];
        nested_key.extend_from_slice(&0_u64.to_be_bytes());
        nested_key.extend_from_slice(&0_u64.to_be_bytes());
        let nested_marker = compiler
            .interner
            .get_or_intern(encode_abstraction_marker_v1(&nested_key));
        let dog = compiler.interner.get_or_intern("dog");
        let body = IrForm::And(
            Box::new(IrForm::Predicate {
                relation: nested_marker,
                args: vec![IrTerm::Variable(referent)],
            }),
            Box::new(IrForm::Predicate {
                relation: dog,
                args: vec![IrTerm::Variable(referent)],
            }),
        );

        let key = compiler.abstraction_content_key(AbstractionKind::Concept, &body);
        let key_hex = key
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        assert_eq!(
            key_hex,
            "a412110000000000000001000000000000000000100000000000000003646f67\
             0000000000000001000000000000000000"
        );
        assert_eq!(
            encode_abstraction_marker_v1(&key),
            "__abs_v1_67c8285d0b92f05f_a41211000000000000000100000000000000000010000000\
             0000000003646f670000000000000001000000000000000000"
        );
    }

    #[test]
    fn abstraction_content_key_is_alpha_canonical() {
        let mut compiler = SemanticCompiler::new();
        let relation = compiler.interner.get_or_intern("dog");
        let x = compiler.interner.get_or_intern("$x");
        let renamed = compiler.interner.get_or_intern("$renamed");
        let left = IrForm::Exists(
            x,
            Box::new(IrForm::Predicate {
                relation,
                args: vec![IrTerm::Variable(x)],
            }),
        );
        let right = IrForm::Exists(
            renamed,
            Box::new(IrForm::Predicate {
                relation,
                args: vec![IrTerm::Variable(renamed)],
            }),
        );
        assert_eq!(
            compiler.abstraction_content_key(AbstractionKind::Fact, &left),
            compiler.abstraction_content_key(AbstractionKind::Fact, &right),
            "bound-variable spelling must not change opaque proposition identity"
        );
    }

    #[test]
    fn abstraction_kind_is_part_of_opaque_identity() {
        let mut compiler = SemanticCompiler::new();
        let relation = compiler.interner.get_or_intern("dog");
        let body = IrForm::Predicate {
            relation,
            args: Vec::new(),
        };
        assert_ne!(
            compiler.abstraction_content_key(AbstractionKind::Event, &body),
            compiler.abstraction_content_key(AbstractionKind::Fact, &body),
            "materialization projects the marker alone, so kind must survive in it"
        );
    }
}
