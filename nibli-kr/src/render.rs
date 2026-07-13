//! The nibli KR renderer: `nibli_types::ast::AstBuffer` → nibli KR text — the
//! inverse of [`crate::emit`], and PARITY LAYER 1 of the 100%-sync guarantee:
//! every `match` in this module is wildcard-free over the `nibli_types::ast`
//! enums (see [`__ast_parity_guard`]), so ADDING AN AST VARIANT BREAKS THIS
//! CRATE'S BUILD until nibli KR decides how to spell it (or rejects it by name).
//!
//! Load-bearing consumers: the render∘parse fixpoint tests (this file) and
//! nibli-formalize's render round-trip gate (every Formalize candidate's
//! canonical re-spelling must re-compile to the same `LogicBuffer`).
//!
//! Totality policy (NIBLI_KR §13): every AST construct nibli-kr's emitter can
//! produce renders (the `ge…gi`/`ganai…gi` sentence connectives + afterthought
//! operators; `via` modals; tense/deontic prefixes; conversions, tanru, and
//! abstractions); §10 out-of-scope constructs (`ri/ra/ru`, `ko`, `go'i`, exotic
//! gadri×NU combinations, exponent-form floats) FAIL CLOSED with a named error.
//! The dead Lojban-only capacity the deleted gerna parser once produced (sumti/
//! selbri connectives, fixed BAI tags, `la`-descriptions, `voi` clauses,
//! forethought or/iff) has been removed from the AST.
//!
//! Fixpoint contract (pinned by tests): for nibli KR-originated buffers,
//! `parse ∘ render ∘ parse` compiles — through smuni — to the SAME
//! LogicBuffer as `parse`, and `render` is text-idempotent
//! (`render(parse(render(x))) == render(parse(x))`). AstBuffer equality is
//! deliberately NOT the contract: the §11 collapses make it unachievable
//! (e.g. a `some`-block's `GeGi` re-parses as an Afterthought `&`).

use nibli_types::ast::{
    AbstractionKind, Argument, AstBuffer, Connective, Conversion, DeonticMood, Determiner,
    ModalTag, Predicate, Proposition, RelClause, RelClauseKind, Sentence, SentenceConnective,
    Tense,
};
use nibli_types::error::NibliError;

/// Render an `AstBuffer` (all roots, one statement per line) to nibli KR text.
pub fn render(buffer: &AstBuffer) -> Result<String, NibliError> {
    let renderer = Renderer { buffer };
    let mut out = Vec::new();
    for &root in &buffer.roots {
        out.push(format!("{}.", renderer.sentence(root, 0)?));
    }
    Ok(out.join("\n")).map_err(|e: NibliError| e)
}

struct Renderer<'a> {
    buffer: &'a AstBuffer,
}

type R<T> = Result<T, NibliError>;

fn nope(msg: impl Into<String>) -> NibliError {
    NibliError::Semantic(format!("render: {}", msg.into()))
}

/// Operator precedence (loosest = smallest). `->`=1, `<->`=2, `^`=3, `|`=4,
/// `&`=5; prenex/blocks are 0 (always parenthesized under an operator);
/// simple bridi are atoms.
const PREC_ATOM: u8 = 6;

impl<'a> Renderer<'a> {
    fn selbri(&self, id: u32) -> R<&Predicate> {
        self.buffer
            .predicates
            .get(id as usize)
            .ok_or_else(|| nope(format!("selbri index {id} out of bounds")))
    }

    fn sumti(&self, id: u32) -> R<&Argument> {
        self.buffer
            .arguments
            .get(id as usize)
            .ok_or_else(|| nope(format!("sumti index {id} out of bounds")))
    }

    fn sentence_node(&self, id: u32) -> R<&Sentence> {
        self.buffer
            .sentences
            .get(id as usize)
            .ok_or_else(|| nope(format!("sentence index {id} out of bounds")))
    }

    // ── sentences / claims ──

    fn sentence(&self, id: u32, min_prec: u8) -> R<String> {
        let (text, prec) = match self.sentence_node(id)? {
            Sentence::Simple(bridi) => (self.bridi(bridi)?, PREC_ATOM),
            Sentence::Prenex((vars, body)) => {
                let vars = vars
                    .iter()
                    .map(|v| format!("${v}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                (format!("all {vars}: {}", self.sentence(*body, 0)?), 0)
            }
            Sentence::Connected((conn, left, right)) => match conn {
                SentenceConnective::Implies => (
                    format!(
                        "{} -> {}",
                        self.sentence(*left, 2)?,
                        self.sentence(*right, 1)?
                    ),
                    1,
                ),
                SentenceConnective::And => (self.binary("&", 5, *left, *right)?, 5),
                SentenceConnective::Afterthought(conn) => {
                    let (op, prec) = match conn {
                        Connective::And => ("&", 5),
                        Connective::Or => ("|", 4),
                        Connective::Iff => ("<->", 2),
                        Connective::Whether => ("^", 3),
                    };
                    (self.binary(op, prec, *left, *right)?, prec)
                }
            },
        };
        Ok(if prec < min_prec {
            format!("({text})")
        } else {
            text
        })
    }

    fn binary(&self, op: &str, prec: u8, left: u32, right: u32) -> R<String> {
        Ok(format!(
            "{} {op} {}",
            self.sentence(left, prec)?,
            self.sentence(right, prec + 1)?
        ))
    }

    // ── bridi ──

    fn bridi(&self, bridi: &Proposition) -> R<String> {
        self.bridi_impl(bridi, false)
    }

    /// Render a relative-clause body bridi whose ke'a is IMPLICIT (gerna-origin
    /// buffers leave the head empty and smuni injects ke'a at x1): spell the
    /// relativized entity as `it` in x1 so the KR re-parses (mandatory-it, §7).
    fn bridi_with_it(&self, bridi: &Proposition) -> R<String> {
        self.bridi_impl(bridi, true)
    }

    fn bridi_impl(&self, bridi: &Proposition, inject_it: bool) -> R<String> {
        let mut prefix = String::new();
        if let Some(att) = &bridi.deontic {
            prefix.push_str(match att {
                DeonticMood::Obligation => "must ",
                DeonticMood::Permission => "may ",
            });
        }
        if let Some(tense) = &bridi.tense {
            prefix.push_str(match tense {
                Tense::Past => "past ",
                Tense::Now => "now ",
                Tense::Future => "future ",
            });
        }
        if bridi.negated {
            prefix.push('~');
        }

        // du with exactly one head and one tail term is the equality spelling
        // (with an injected implicit ke'a, the head IS `it`).
        if let Predicate::Root(root) = self.selbri(bridi.relation)?
            && root == "du"
        {
            if !inject_it && bridi.head_terms.len() == 1 && bridi.tail_terms.len() == 1 {
                return Ok(format!(
                    "{prefix}{} = {}",
                    self.term(bridi.head_terms[0])?,
                    self.term(bridi.tail_terms[0])?
                ));
            }
            if inject_it && bridi.head_terms.is_empty() && bridi.tail_terms.len() == 1 {
                return Ok(format!("{prefix}it = {}", self.term(bridi.tail_terms[0])?));
            }
        }

        // A conversion chain with NO curated converted alias renders by
        // PEELING the swaps and permuting the argument places onto the plain
        // alias with named args (`ta se citka ti` → `eats(x2: that, x1: this)`)
        // — the swap is argument routing, and named args express routing
        // directly. Curated converted aliases still take priority (checked
        // inside predication_selbri via the full-chain lookup below).
        let (relation_id, perm) = self.peel_conversions(bridi.relation)?;
        let head_gismu = self.head_gismu(relation_id)?;
        let relation = self.predication_selbri(relation_id)?;

        // Argument places: heads fill x1.., then the tail runs gerna's CLL
        // counter (an untagged term takes the next place; a FA tag jumps the
        // counter). SURFACE places map through the peeled permutation onto the
        // plain relation's places. Render positionally while plain places stay
        // contiguous from x1, then switch to named args; modal tags render as
        // `via` after the argument list.
        let mut placed: Vec<(usize, Option<u32>)> = Vec::new();
        let mut vias: Vec<(u32, u32)> = Vec::new(); // (modal selbri-ish, term) — see below
        let mut counter = 0usize;
        if inject_it {
            placed.push((counter, None)); // the implicit ke'a — spelled `it`
            counter += 1;
        }
        for &head in &bridi.head_terms {
            placed.push((counter, Some(head)));
            counter += 1;
        }
        for &tail in &bridi.tail_terms {
            match self.sumti(tail)? {
                Argument::Tagged((tag, inner)) => {
                    let place = (*tag as usize);
                    placed.push((place, Some(*inner)));
                    counter = place + 1;
                }
                Argument::ModalTagged((modal, inner)) => {
                    let ModalTag::Custom(selbri) = modal;
                    vias.push((*selbri, *inner));
                }
                Argument::Pronoun(_)
                | Argument::Description(_)
                | Argument::Name(_)
                | Argument::QuotedLiteral(_)
                | Argument::Unspecified
                | Argument::Restricted(_)
                | Argument::Number(_)
                | Argument::QuantifiedDescription(_) => {
                    placed.push((counter, Some(tail)));
                    counter += 1;
                }
            }
        }

        // Map surface places through the peeled conversion permutation.
        let mut placed: Vec<(usize, Option<u32>)> = placed
            .into_iter()
            .map(|(place, term)| {
                if place >= 5 {
                    return Err(nope(format!("argument place x{} out of range", place + 1)));
                }
                Ok((perm[place], term))
            })
            .collect::<R<_>>()?;
        // In inject-it mode, sort by final place so contiguous places render
        // positionally — the leading positional streak is the byte-stable `it`
        // spelling (nibli-semantics compiles named-`it` and positional-`it`
        // where-bodies identically now, but positional stays the canonical
        // rendering). Normal rendering keeps surface order (byte-stable output).
        if inject_it {
            placed.sort_by_key(|(place, _)| *place);
        }

        let mut args: Vec<String> = Vec::new();
        let mut positional_streak = true;
        for (i, (place, term)) in placed.iter().enumerate() {
            positional_streak = positional_streak && *place == i;
            let rendered = match term {
                Some(t) => self.term(*t)?,
                None => "it".into(),
            };
            if positional_streak {
                args.push(rendered);
            } else {
                args.push(format!(
                    "{}: {}",
                    self.place_label(&head_gismu, *place),
                    rendered
                ));
            }
        }

        let mut out = format!("{prefix}{relation}({})", args.join(", "));
        for (selbri, term) in vias {
            let name = match self.selbri(selbri)? {
                Predicate::Root(gismu) => self.alias_or_identity(gismu)?,
                other => {
                    return Err(nope(format!(
                        "a fi'o modal over a non-root selbri has no nibli KR spelling: {other:?}"
                    )));
                }
            };
            out.push_str(&format!(" via {name}({})", self.term(term)?));
        }
        Ok(out)
    }

    /// Peel outer `Converted` layers off a relation, composing their swaps
    /// into a surface-place → plain-place permutation (0-based). Stops early
    /// (identity permutation) when the chain from this node down matches a
    /// CURATED converted alias — those render by name. Only used in bridi
    /// position; restrictors have the selector spelling instead.
    fn peel_conversions(&self, id: u32) -> R<(u32, [usize; 5])> {
        const IDENTITY: [usize; 5] = [0, 1, 2, 3, 4];
        let Predicate::Converted((conv, inner)) = self.selbri(id)? else {
            return Ok((id, IDENTITY));
        };
        // Single-layer chain with a curated converted alias renders by name.
        if let Predicate::Root(gismu) = self.selbri(*inner)? {
            let place: u8 = match conv {
                Conversion::Swap12 => 2,
                Conversion::Swap13 => 3,
                Conversion::Swap14 => 4,
                Conversion::Swap15 => 5,
            };
            if nibli_kr_dictionary::curated::CONVERTED_ALIASES
                .iter()
                .any(|(_, g, swap)| g == gismu && *swap == place)
            {
                return Ok((id, IDENTITY));
            }
        }
        let (base, inner_perm) = self.peel_conversions(*inner)?;
        let swapped = match conv {
            Conversion::Swap12 => 1,
            Conversion::Swap13 => 2,
            Conversion::Swap14 => 3,
            Conversion::Swap15 => 4,
        };
        let mut perm = [0usize; 5];
        for (surface, slot) in perm.iter_mut().enumerate() {
            let after_outer = if surface == 0 {
                swapped
            } else if surface == swapped {
                0
            } else {
                surface
            };
            *slot = inner_perm[after_outer];
        }
        Ok((base, perm))
    }

    /// The head gismu of a relation (for place-label lookup), descending
    /// through wrappers to the head Root/Compound.
    fn head_gismu(&self, id: u32) -> R<String> {
        Ok(match self.selbri(id)? {
            Predicate::Root(g) => g.clone(),
            Predicate::Compound(parts) => parts.last().cloned().unwrap_or_default(),
            Predicate::Pair((_, head)) => self.head_gismu(*head)?,
            Predicate::Converted((_, inner)) => self.head_gismu(*inner)?,
            Predicate::Negated(inner) => self.head_gismu(*inner)?,
            Predicate::Grouped(inner) => self.head_gismu(*inner)?,
            Predicate::WithArgs((core, _)) => self.head_gismu(*core)?,
            Predicate::Abstraction(_) => String::new(),
        })
    }

    /// The nibli KR spelling of a dictionary word: the canonical alias, else the
    /// identity passthrough — which is only honest when the word (a) is
    /// actually in the dictionary (nibli-kr's resolver fails closed on unknowns;
    /// gerna tolerates them at arity 2) and (b) is a legal nibli KR identifier
    /// (apostrophe lujvo are not). Render must NEVER emit unparseable text, so
    /// both cases fail closed by name here.
    fn alias_or_identity(&self, gismu: &str) -> R<String> {
        if let Some(alias) = nibli_kr_dictionary::canonical_alias(gismu) {
            return Ok(alias.to_owned());
        }
        if nibli_lexicon::get_arity(gismu).is_none() {
            return Err(nope(format!(
                "word {gismu:?} is dictionary-unknown (the Lojban front-end tolerates it at \
                 arity 2; nibli KR fails closed on unknown names — NIBLI_KR §13)"
            )));
        }
        let mut chars = gismu.chars();
        let ident_ok = matches!(chars.next(), Some('a'..='z'))
            && chars.all(|c| matches!(c, 'a'..='z' | '0'..='9'));
        if !ident_ok {
            return Err(nope(format!(
                "word {gismu:?} is not a legal nibli KR identifier (apostrophes have no \
                 spelling) and has no alias — curate one"
            )));
        }
        Ok(gismu.to_owned())
    }

    /// Label for SURFACE place `place` (0-based) of `gismu`'s canonical alias:
    /// the dictionary label when curated, else raw `xN`.
    fn place_label(&self, gismu: &str, place: usize) -> String {
        if let Some(alias) = nibli_kr_dictionary::canonical_alias(gismu)
            && let Some(entry) = nibli_kr_dictionary::alias(alias)
            && let Some(label) = entry.place_labels.get(place)
            && !label.is_empty()
        {
            return (*label).to_owned();
        }
        format!("x{}", place + 1)
    }

    /// A selbri in PREDICATION position (no selector spelling available).
    fn predication_selbri(&self, id: u32) -> R<String> {
        self.selbri_text(id, false)
    }

    /// A selbri in RESTRICTOR position (selector spelling available).
    fn restr_selbri(&self, id: u32) -> R<String> {
        self.selbri_text(id, true)
    }

    fn selbri_text(&self, id: u32, selector_ok: bool) -> R<String> {
        Ok(match self.selbri(id)? {
            Predicate::Root(gismu) => self.alias_or_identity(gismu)?,
            Predicate::Compound(parts) => parts
                .iter()
                .map(|p| self.alias_or_identity(p))
                .collect::<R<Vec<_>>>()?
                .into_iter()
                .collect::<Vec<_>>()
                .join("+"),
            Predicate::Pair((modifier, head)) => {
                let modifier_text = match self.selbri(*modifier)? {
                    // A left-nested tanru needs explicit grouping.
                    Predicate::Pair(_) => format!("[{}]", self.selbri_text(*modifier, false)?),
                    _ => self.selbri_text(*modifier, false)?,
                };
                format!("{modifier_text} {}", self.selbri_text(*head, selector_ok)?)
            }
            Predicate::Grouped(inner) => format!("[{}]", self.selbri_text(*inner, false)?),
            Predicate::Negated(inner) => format!("~{}", self.selbri_text(*inner, selector_ok)?),
            Predicate::Converted((conv, inner)) => {
                let Predicate::Root(gismu) = self.selbri(*inner)? else {
                    return Err(nope(
                        "a conversion over a non-root selbri has no nibli KR spelling yet — \
                         curate a converted alias (nibli-kr-dictionary CONVERTED_ALIASES)",
                    ));
                };
                let place: u8 = match conv {
                    Conversion::Swap12 => 2,
                    Conversion::Swap13 => 3,
                    Conversion::Swap14 => 4,
                    Conversion::Swap15 => 5,
                };
                // Curated converted alias first (works everywhere)…
                if let Some((alias, _, _)) = nibli_kr_dictionary::curated::CONVERTED_ALIASES
                    .iter()
                    .find(|(_, g, swap)| g == gismu && *swap == place)
                {
                    return Ok((*alias).to_owned());
                }
                // …else the place selector, in restrictor position only (O8).
                if selector_ok {
                    let alias = self.alias_or_identity(gismu)?;
                    let label = self.place_label(gismu, (place - 1) as usize);
                    return Ok(format!("{alias}.{label}"));
                }
                return Err(nope(format!(
                    "no nibli KR spelling for the {conv:?}-conversion of {gismu:?} in \
                     predication position — curate a converted alias"
                )));
            }
            Predicate::WithArgs((core, be_args)) => {
                let core_text = self.selbri_text(*core, false)?;
                let mut rendered = Vec::new();
                for &arg in be_args {
                    rendered.push(self.term(arg)?);
                }
                format!("{core_text}({})", rendered.join(", "))
            }
            Predicate::Abstraction((kind, body)) => {
                let keyword = match kind {
                    AbstractionKind::Event => "event",
                    AbstractionKind::Fact => "fact",
                    AbstractionKind::Property => "property",
                    AbstractionKind::Amount => "amount",
                    AbstractionKind::Concept => "concept",
                };
                format!("{keyword} {{ {} }}", self.sentence(*body, 0)?)
            }
        })
    }

    // ── terms ──

    fn term(&self, id: u32) -> R<String> {
        Ok(match self.sumti(id)? {
            Argument::Pronoun(word) => match word.as_str() {
                "mi" => "me".into(),
                "do" => "you".into(),
                "mi'o" => "we".into(),
                "ma'a" => "we_all".into(),
                "mi'a" => "we_others".into(),
                "do'o" => "you_all".into(),
                "ti" => "this".into(),
                "ta" => "that".into(),
                "tu" => "yonder".into(),
                "ko'a" => "it_a".into(),
                "ko'e" => "it_e".into(),
                "ko'i" => "it_i".into(),
                "ko'o" => "it_o".into(),
                "ko'u" => "it_u".into(),
                "ke'a" => "it".into(),
                "ce'u" => "slot".into(),
                "ma" => "?".into(),
                "zo'e" => "_".into(),
                "da" => "$da".into(),
                "de" => "$de".into(),
                "di" => "$di".into(),
                other => {
                    // §10 out-of-scope pro-sumti (ri/ra/ru anaphora, ko, an
                    // unresolved go'i, …) fail closed BY NAME — in the
                    // battery this is a genuine coverage signal.
                    return Err(nope(format!(
                        "pro-sumti {other:?} is out of nibli KR's scope (NIBLI_KR §10) — \
                         no spelling exists"
                    )));
                }
            },
            Argument::Name(name) => render_name(name)?,
            Argument::QuotedLiteral(text) => {
                if text.contains('\n') {
                    return Err(nope(
                        "a quoted literal containing a raw newline has no nibli KR spelling \
                         (strings are single-line; NIBLI_KR §3)",
                    ));
                }
                format!("\"{}\"", text.replace('\\', "\\\\").replace('"', "\\\""))
            }
            Argument::Unspecified => "_".into(),
            Argument::Number(value) => {
                let rendered = format!("{value}");
                if !value.is_finite() || rendered.contains('e') || rendered.starts_with('-') {
                    return Err(nope(format!(
                        "number {value} has no nibli KR literal (unsigned decimal only; \
                         NIBLI_KR §3) — fail closed"
                    )));
                }
                rendered
            }
            Argument::Description((gadri, selbri)) => {
                if let Predicate::Abstraction(_) = self.selbri(*selbri)? {
                    return match gadri {
                        Determiner::Indefinite => self.restr_selbri(*selbri),
                        Determiner::Definite
                        | Determiner::UniversalIndefinite
                        | Determiner::UniversalDefinite => Err(nope(
                            "abstractions are hard-wired to the implicit-some description; \
                             other gadri × NU combinations are out of scope \
                             (NIBLI_KR §10)",
                        )),
                    };
                }
                match gadri {
                    Determiner::Indefinite => format!("some {}", self.restr_selbri(*selbri)?),
                    Determiner::Definite => format!("the {}", self.restr_selbri(*selbri)?),
                    Determiner::UniversalIndefinite => {
                        format!("every {}", self.restr_selbri(*selbri)?)
                    }
                    Determiner::UniversalDefinite => {
                        format!("every the {}", self.restr_selbri(*selbri)?)
                    }
                }
            }
            Argument::QuantifiedDescription((count, gadri, selbri)) => match gadri {
                Determiner::Indefinite => {
                    if *count == 0 {
                        format!("no {}", self.restr_selbri(*selbri)?)
                    } else {
                        format!("exactly {count} {}", self.restr_selbri(*selbri)?)
                    }
                }
                Determiner::Definite => {
                    format!("exactly {count} the {}", self.restr_selbri(*selbri)?)
                }
                Determiner::UniversalIndefinite | Determiner::UniversalDefinite => {
                    return Err(nope(format!(
                        "a quantified {gadri:?} description has no nibli KR spelling"
                    )));
                }
            },
            Argument::Restricted((inner, clause)) => {
                format!("{} {}", self.term(*inner)?, self.rel_clause(clause)?)
            }
            Argument::Tagged((_, _)) => {
                return Err(nope(
                    "a place-tagged term outside an argument list has no nibli KR spelling",
                ));
            }
            Argument::ModalTagged((_, _)) => {
                return Err(nope(
                    "a modal-tagged term outside a predication has no nibli KR spelling",
                ));
            }
        })
    }

    fn rel_clause(&self, clause: &RelClause) -> R<String> {
        let keyword = match clause.kind {
            RelClauseKind::Restrictive => "where",
            RelClauseKind::Incidental => "also",
        };
        // Bare-predicate sugar: a body of shape `ke'a <selbri>` (no tail, no
        // prefixes) prints as the sugar form.
        // The bound entity is either an explicit ke'a head (nibli-kr-emitted
        // buffers) or IMPLICIT (gerna leaves the head empty and smuni injects
        // ke'a at x1) — both print as the sugar.
        let head_is_kehah = |bridi: &Proposition| -> R<bool> {
            Ok(match bridi.head_terms.as_slice() {
                [] => true,
                [only] => matches!(self.sumti(*only)?, Argument::Pronoun(w) if w == "ke'a"),
                _ => false,
            })
        };
        if let Sentence::Simple(bridi) = self.sentence_node(clause.body_sentence)?
            && bridi.tail_terms.is_empty()
            && bridi.tense.is_none()
            && bridi.deontic.is_none()
            && head_is_kehah(bridi)?
            && self.bare_body_selbri(bridi.relation)
        {
            let neg = if bridi.negated { "~" } else { "" };
            return Ok(format!(
                "{keyword} {neg}{}",
                self.selbri_text(bridi.relation, false)?
            ));
        }
        // Full-claim body. A gerna-origin Simple body leaves the head EMPTY
        // (smuni injects ke'a at x1) — spell that implicit ke'a as `it` so the
        // rendered KR re-parses (§7 mandatory-it). nibli KR-emitted bodies carry
        // an explicit ke'a (head, or a tail term — nibli-semantics skips its
        // implicit-x1 injection when the body already contains an explicit ke'a)
        // and render through the normal path.
        let has_explicit_keha = |bridi: &Proposition| -> R<bool> {
            for &tail in &bridi.tail_terms {
                let inner = match self.sumti(tail)? {
                    Argument::Tagged((_, inner)) => *inner,
                    _ => tail,
                };
                if matches!(self.sumti(inner)?, Argument::Pronoun(w) if w == "ke'a") {
                    return Ok(true);
                }
            }
            Ok(false)
        };
        let body = match self.sentence_node(clause.body_sentence)? {
            Sentence::Simple(bridi)
                if bridi.head_terms.is_empty() && !has_explicit_keha(bridi)? =>
            {
                self.bridi_with_it(bridi)?
            }
            _ => self.sentence(clause.body_sentence, PREC_ATOM)?,
        };
        Ok(format!("{keyword} {body}"))
    }

    /// Only plain word/tanru/compound selbri qualify for the bare sugar
    /// (anything fancier needs the full-claim body).
    fn bare_body_selbri(&self, id: u32) -> bool {
        match self.selbri(id) {
            Ok(Predicate::Root(_)) | Ok(Predicate::Compound(_)) => true,
            Ok(Predicate::Pair((m, h))) => self.bare_body_selbri(*m) && self.bare_body_selbri(*h),
            Ok(Predicate::Grouped(inner)) => self.bare_body_selbri(*inner),
            Ok(Predicate::Converted(_))
            | Ok(Predicate::Negated(_))
            | Ok(Predicate::WithArgs(_))
            | Ok(Predicate::Abstraction(_)) => false,
            Err(_) => false,
        }
    }
}

fn render_name(name: &str) -> R<String> {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return Err(nope("an empty Name has no nibli KR spelling"));
    };
    if !first.is_ascii_alphabetic() {
        return Err(nope(format!(
            "Name {name:?} does not start with an ASCII letter — no nibli KR spelling"
        )));
    }
    let rest: String = chars.collect();
    let candidate = format!("{}{}", first.to_ascii_uppercase(), rest.replace(' ', "_"));
    if !candidate
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return Err(nope(format!(
            "Name {name:?} contains characters outside [A-Za-z0-9_] — no nibli KR spelling"
        )));
    }
    Ok(candidate)
}

/// PARITY GUARD — never called at runtime; `#[doc(hidden)]` keeps it off the
/// public API. Every `nibli_types::ast` enum nibli KR owns the spelling of is
/// matched here WITHOUT wildcards, so adding a variant fails this crate's
/// build until nibli KR covers it. A new variant obligates, in order:
/// 1. a NIBLI_KR section (spelling, or an explicit §10 out-of-scope
///    entry with justification),
/// 2. a grammar rule in `nibli_kr.pest` + walker arm (or a targeted reject),
/// 3. a render arm in this module (spelling or fail-closed-by-name),
/// 4. a row in the nibli-verify CONSTRUCT_INVENTORY (battery bullet),
/// 5. a golden/twin test.
#[doc(hidden)]
#[allow(clippy::too_many_arguments)] // one parameter per guarded enum, by design
pub fn __ast_parity_guard(
    sumti: &Argument,
    selbri: &Predicate,
    sentence: &Sentence,
    connective: &SentenceConnective,
    gadri: &Determiner,
    abstraction: &AbstractionKind,
    rel_kind: &RelClauseKind,
    modal: &ModalTag,
    conversion: &Conversion,
    logical: &Connective,
    tense: &Tense,
    deontic: &DeonticMood,
) {
    match sumti {
        Argument::Pronoun(_) => {}
        Argument::Description(_) => {}
        Argument::Name(_) => {}
        Argument::QuotedLiteral(_) => {}
        Argument::Unspecified => {}
        Argument::Tagged(_) => {}
        Argument::ModalTagged(_) => {}
        Argument::Restricted(_) => {}
        Argument::Number(_) => {}
        Argument::QuantifiedDescription(_) => {}
    }
    match selbri {
        Predicate::Root(_) => {}
        Predicate::Compound(_) => {}
        Predicate::Pair(_) => {}
        Predicate::Converted(_) => {}
        Predicate::Negated(_) => {}
        Predicate::Grouped(_) => {}
        Predicate::WithArgs(_) => {}
        Predicate::Abstraction(_) => {}
    }
    match sentence {
        Sentence::Simple(_) => {}
        Sentence::Connected(_) => {}
        Sentence::Prenex(_) => {}
    }
    match connective {
        SentenceConnective::Implies => {}
        SentenceConnective::And => {}
        SentenceConnective::Afterthought(_) => {}
    }
    match gadri {
        Determiner::Indefinite => {}
        Determiner::Definite => {}
        Determiner::UniversalIndefinite => {}
        Determiner::UniversalDefinite => {}
    }
    match abstraction {
        AbstractionKind::Event => {}
        AbstractionKind::Fact => {}
        AbstractionKind::Property => {}
        AbstractionKind::Amount => {}
        AbstractionKind::Concept => {}
    }
    match rel_kind {
        RelClauseKind::Restrictive => {}
        RelClauseKind::Incidental => {}
    }
    match modal {
        ModalTag::Custom(_) => {}
    }
    match conversion {
        Conversion::Swap12 => {}
        Conversion::Swap13 => {}
        Conversion::Swap14 => {}
        Conversion::Swap15 => {}
    }
    match logical {
        Connective::And => {}
        Connective::Or => {}
        Connective::Iff => {}
        Connective::Whether => {}
    }
    match tense {
        Tense::Past => {}
        Tense::Now => {}
        Tense::Future => {}
    }
    match deontic {
        DeonticMood::Obligation => {}
        DeonticMood::Permission => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_checked;

    /// smuni-compiled LogicBuffer (Debug form) for nibli KR text.
    fn lb(text: &str) -> String {
        let buffer = parse_checked(text).unwrap_or_else(|e| panic!("parse {text:?}: {e}"));
        format!(
            "{:?}",
            nibli_semantics::compile_from_ast(buffer)
                .unwrap_or_else(|e| panic!("smuni {text:?}: {e}"))
        )
    }

    /// The fixpoint contract: render(parse(x)) reparses to the SAME compiled
    /// LogicBuffer, and rendering is text-idempotent.
    fn fixpoint(text: &str) {
        let buffer = parse_checked(text).unwrap_or_else(|e| panic!("parse {text:?}: {e}"));
        let rendered = render(&buffer).unwrap_or_else(|e| panic!("render {text:?}: {e}"));
        assert_eq!(
            lb(text),
            lb(&rendered),
            "\noriginal: {text}\nrendered: {rendered}\ncompiled LogicBuffers differ"
        );
        let buffer2 = parse_checked(&rendered)
            .unwrap_or_else(|e| panic!("reparse of rendered {rendered:?}: {e}"));
        let rendered2 = render(&buffer2).unwrap();
        assert_eq!(rendered, rendered2, "render is not text-idempotent");
    }

    #[test]
    fn acceptance_corpus_fixpoint() {
        // The §16 acceptance set (checked in, honest-generic spellings —
        // also the fuzz seed). Every payload line must round-trip.
        let corpus = include_str!("../tests/acceptance.nibli");
        let mut checked = 0;
        for line in corpus.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            fixpoint(line);
            checked += 1;
        }
        assert!(checked >= 18, "acceptance corpus shrank: {checked} lines");
    }

    #[test]
    fn out_of_scope_constructs_fail_closed_by_name() {
        use nibli_types::ast::*;
        // Hand-built buffers with §10 constructs: render must name the
        // offender, never guess.
        let mk = |sumti: Argument| AstBuffer {
            predicates: vec![Predicate::Root("gerku".into())],
            arguments: vec![sumti],
            sentences: vec![Sentence::Simple(Proposition {
                relation: 0,
                head_terms: vec![0],
                tail_terms: vec![],
                negated: false,
                tense: None,
                deontic: None,
            })],
            roots: vec![0],
        };
        for (buffer, needle) in [
            (
                mk(Argument::Pronoun("ko".into())),
                "out of nibli KR's scope",
            ),
            (
                mk(Argument::Pronoun("ri".into())),
                "out of nibli KR's scope",
            ),
            (
                mk(Argument::Pronoun("go'i".into())),
                "out of nibli KR's scope",
            ),
            (mk(Argument::Number(f64::INFINITY)), "no nibli KR literal"),
            (mk(Argument::Number(-2.0)), "no nibli KR literal"),
        ] {
            let e = render(&buffer).expect_err("must fail closed");
            assert!(format!("{e}").contains(needle), "{e}");
        }
    }
}
