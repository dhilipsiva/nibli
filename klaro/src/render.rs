//! The Klaro renderer: `nibli_types::ast::AstBuffer` → Klaro text — the
//! inverse of [`crate::emit`], and PARITY LAYER 1 of the 100%-sync guarantee:
//! every `match` in this module is wildcard-free over the `nibli_types::ast`
//! enums (see [`__ast_parity_guard`]), so ADDING AN AST VARIANT BREAKS THIS
//! CRATE'S BUILD until Klaro decides how to spell it (or rejects it by name).
//!
//! Load-bearing consumers: the render∘parse fixpoint tests (this file), the
//! future nibli-verify translation battery (Lojban → gerna AST → render →
//! klaro parse → equal LogicBuffers), and the mechanical `.lojban → .klaro`
//! corpus migration.
//!
//! Totality policy (SURFACE_SYNTAX §13): gerna-reachable constructs render,
//! sometimes via the §11 collapses (forethought `ge/ga/go…gi` → the one
//! operator set; `.inaja` → `->`; `la`+selbri → a Name; BAI → `via`); §10
//! out-of-scope constructs (`ri/ra/ru`, `ko`, `go'i`, exotic gadri×NU
//! combinations, exponent-form floats) FAIL CLOSED with a named error — in
//! the battery, such a failure is a genuine coverage signal, never silence.
//! Selbri connectives on a MAIN relation render via bridi-level expansion
//! (block-every for a universal subject, an operator claim for a constant —
//! see [`Renderer::connected_bridi`]); the remaining deliberate gaps fail
//! closed with named messages: SUMTI connectives, connected selbri outside
//! main-bridi position, and `Converted` over a non-root selbri.
//!
//! Fixpoint contract (pinned by tests): for Klaro-originated buffers,
//! `parse ∘ render ∘ parse` compiles — through smuni — to the SAME
//! LogicBuffer as `parse`, and `render` is text-idempotent
//! (`render(parse(render(x))) == render(parse(x))`). AstBuffer equality is
//! deliberately NOT the contract: the §11 collapses make it unachievable
//! (e.g. a `some`-block's `GeGi` re-parses as an Afterthought `&`).

use nibli_types::ast::{
    AbstractionKind, AstBuffer, Attitudinal, BaiTag, Bridi, Connective, Conversion, Gadri,
    ModalTag, PlaceTag, RelClause, RelClauseKind, Selbri, Sentence, SentenceConnective, Sumti,
    Tense,
};
use nibli_types::error::NibliError;

/// Render an `AstBuffer` (all roots, one statement per line) to Klaro text.
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
    fn selbri(&self, id: u32) -> R<&Selbri> {
        self.buffer
            .selbris
            .get(id as usize)
            .ok_or_else(|| nope(format!("selbri index {id} out of bounds")))
    }

    fn sumti(&self, id: u32) -> R<&Sumti> {
        self.buffer
            .sumtis
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
                SentenceConnective::GanaiGi => (
                    format!(
                        "{} -> {}",
                        self.sentence(*left, 2)?,
                        self.sentence(*right, 1)?
                    ),
                    1,
                ),
                SentenceConnective::GeGi => (self.binary("&", 5, *left, *right)?, 5),
                SentenceConnective::GaGi => (self.binary("|", 4, *left, *right)?, 4),
                SentenceConnective::GoGi => (self.binary("<->", 2, *left, *right)?, 2),
                SentenceConnective::Afterthought((na, conn, nai)) => {
                    // `.inaja` (na + ja) is the material conditional — render
                    // it as the one arrow. Other na/nai flags fold into the
                    // operand bridi when it is simple (fail closed otherwise:
                    // Klaro rejects `~` over compounds).
                    if *na && matches!(conn, Connective::Ja) && !*nai {
                        (
                            format!(
                                "{} -> {}",
                                self.sentence(*left, 2)?,
                                self.sentence(*right, 1)?
                            ),
                            1,
                        )
                    } else {
                        let (op, prec) = match conn {
                            Connective::Je => ("&", 5),
                            Connective::Ja => ("|", 4),
                            Connective::Jo => ("<->", 2),
                            Connective::Ju => ("^", 3),
                        };
                        let l = if *na {
                            self.negated_operand(*left)?
                        } else {
                            self.sentence(*left, prec)?
                        };
                        let r = if *nai {
                            self.negated_operand(*right)?
                        } else {
                            self.sentence(*right, prec + 1)?
                        };
                        (format!("{l} {op} {r}"), prec)
                    }
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

    /// A connective operand carrying a Lojban `na`/`nai` polarity flag: only a
    /// simple, not-already-negated bridi can absorb it as `~`.
    fn negated_operand(&self, id: u32) -> R<String> {
        match self.sentence_node(id)? {
            Sentence::Simple(bridi) if !bridi.negated => {
                let mut flipped = bridi.clone();
                flipped.negated = true;
                Ok(self.bridi(&flipped)?)
            }
            _ => Err(nope(
                "a na/nai connective polarity over a compound (or already-negated) operand \
                 has no Klaro spelling — Klaro rejects `~` over compounds; expand manually",
            )),
        }
    }

    // ── bridi ──

    fn bridi(&self, bridi: &Bridi) -> R<String> {
        self.bridi_impl(bridi, false)
    }

    /// Render a relative-clause body bridi whose ke'a is IMPLICIT (gerna-origin
    /// buffers leave the head empty and smuni injects ke'a at x1): spell the
    /// relativized entity as `it` in x1 so the KR re-parses (mandatory-it, §7).
    fn bridi_with_it(&self, bridi: &Bridi) -> R<String> {
        self.bridi_impl(bridi, true)
    }

    fn bridi_impl(&self, bridi: &Bridi, inject_it: bool) -> R<String> {
        let mut prefix = String::new();
        if let Some(att) = &bridi.attitudinal {
            prefix.push_str(match att {
                Attitudinal::Ei => "must ",
                Attitudinal::Ehe => "may ",
            });
        }
        if let Some(tense) = &bridi.tense {
            prefix.push_str(match tense {
                Tense::Pu => "past ",
                Tense::Ca => "now ",
                Tense::Ba => "future ",
            });
        }
        if bridi.negated {
            prefix.push('~');
        }

        // du with exactly one head and one tail term is the equality spelling
        // (with an injected implicit ke'a, the head IS `it`).
        if let Selbri::Root(root) = self.selbri(bridi.relation)?
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

        // A CONNECTED main selbri renders via bridi-level expansion (the
        // operands share the subject): block-every for a universal subject,
        // a plain operator claim for a constant subject — both probe-proven
        // canonically equal to the Lojban connective compilation.
        if matches!(self.selbri(bridi.relation)?, Selbri::Connected(_)) {
            return self.connected_bridi(bridi, &prefix);
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
        let mut fixed_vias: Vec<(BaiTag, u32)> = Vec::new();
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
                Sumti::Tagged((tag, inner)) => {
                    let place = tag.to_index();
                    placed.push((place, Some(*inner)));
                    counter = place + 1;
                }
                Sumti::ModalTagged((modal, inner)) => match modal {
                    ModalTag::Fio(selbri) => vias.push((*selbri, *inner)),
                    ModalTag::Fixed(bai) => fixed_vias.push((*bai, *inner)),
                },
                Sumti::ProSumti(_)
                | Sumti::Description(_)
                | Sumti::Name(_)
                | Sumti::QuotedLiteral(_)
                | Sumti::Unspecified
                | Sumti::Restricted(_)
                | Sumti::Number(_)
                | Sumti::Connected(_)
                | Sumti::QuantifiedDescription(_) => {
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
        // positionally — named args with `it` trip smuni's implicit-ke'a x1
        // injection (a known collision), while positional `it` lands in its
        // place. Normal rendering keeps surface order (byte-stable output).
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
                Selbri::Root(gismu) => self.alias_or_identity(gismu)?,
                other => {
                    return Err(nope(format!(
                        "a fi'o modal over a non-root selbri has no Klaro spelling: {other:?}"
                    )));
                }
            };
            out.push_str(&format!(" via {name}({})", self.term(term)?));
        }
        for (bai, term) in fixed_vias {
            let gismu = match bai {
                BaiTag::Ria => "rinka",
                BaiTag::Nii => "nibli",
                BaiTag::Mui => "mukti",
                BaiTag::Kiu => "krinu",
                BaiTag::Pio => "pilno",
                BaiTag::Bai => "basti",
            };
            out.push_str(&format!(
                " via {}({})",
                self.alias_or_identity(gismu)?,
                self.term(term)?
            ));
        }
        Ok(out)
    }

    /// Bridi-level expansion of a CONNECTED main selbri (`X A jenai B` and
    /// family). The operands share the subject, so the sentence becomes a
    /// block-every claim (universal-description subject) or a plain operator
    /// claim (constant subject); both shapes are pinned canonically equal to
    /// smuni's selbri-connective compilation by the verify-klaro gate. Fail
    /// closed BY NAME everywhere else — the expansion must never guess scope
    /// (duplicating a `some`-subject would double the quantifier).
    fn connected_bridi(&self, bridi: &Bridi, prefix: &str) -> R<String> {
        if !prefix.is_empty() {
            return Err(nope(
                "a tense/deontic/negation prefix over a connected selbri has no Klaro \
                 spelling yet — expand manually",
            ));
        }
        let Selbri::Connected((left_id, conn, right_id)) = self.selbri(bridi.relation)? else {
            unreachable!("caller matched Connected");
        };
        if bridi.head_terms.len() != 1 || !bridi.tail_terms.is_empty() {
            return Err(nope(
                "a connected selbri sharing arguments beyond x1 has no Klaro spelling \
                 yet — expand manually",
            ));
        }
        let op = match conn {
            Connective::Je => "&",
            Connective::Ja => "|",
            Connective::Jo => "<->",
            Connective::Ju => {
                return Err(nope(
                    "`ju` (whether-or-not) has no Klaro operator — no spelling exists",
                ));
            }
        };
        // gerna spells jenai/janai/jonai as the connective + Negated(right).
        let (right_id, right_neg) = match self.selbri(*right_id)? {
            Selbri::Negated(inner) => (*inner, true),
            _ => (*right_id, false),
        };
        if matches!(
            self.selbri(*left_id)?,
            Selbri::Connected(_) | Selbri::Negated(_)
        ) || matches!(self.selbri(right_id)?, Selbri::Connected(_))
        {
            return Err(nope(
                "a nested or negated-left connected selbri has no Klaro spelling yet",
            ));
        }

        let subject = bridi.head_terms[0];
        match self.sumti(subject)? {
            // Universal subject → the block form, minting `$x` (gerna-origin
            // variables render as $da/$de/$di, so the name cannot collide).
            Sumti::Description((Gadri::RoLo, restr_id)) => {
                let restr = self.restr_selbri(*restr_id)?;
                let left = self.connective_operand(*left_id, "$x", false)?;
                let right = self.connective_operand(right_id, "$x", right_neg)?;
                Ok(format!("every {restr} $x: {left} {op} {right}"))
            }
            // Constant-ish subject → duplication is sound.
            Sumti::Name(_) | Sumti::ProSumti(_) | Sumti::Number(_) | Sumti::QuotedLiteral(_) => {
                let t = self.term(subject)?;
                let left = self.connective_operand(*left_id, &t, false)?;
                let right = self.connective_operand(right_id, &t, right_neg)?;
                Ok(format!("{left} {op} {right}"))
            }
            _ => Err(nope(
                "a connected selbri over a non-universal quantified subject has no Klaro \
                 spelling — expansion would duplicate the quantifier",
            )),
        }
    }

    /// One connective operand as a single-subject predication: peel the
    /// conversion chain and route the subject to its plain place (positional
    /// when it stays x1, named otherwise) — the same routing `bridi()` uses.
    fn connective_operand(&self, selbri_id: u32, subject: &str, negated: bool) -> R<String> {
        let (relation_id, perm) = self.peel_conversions(selbri_id)?;
        let head_gismu = self.head_gismu(relation_id)?;
        let relation = self.predication_selbri(relation_id)?;
        let neg = if negated { "~" } else { "" };
        Ok(if perm[0] == 0 {
            format!("{neg}{relation}({subject})")
        } else {
            format!(
                "{neg}{relation}({}: {subject})",
                self.place_label(&head_gismu, perm[0])
            )
        })
    }

    /// Peel outer `Converted` layers off a relation, composing their swaps
    /// into a surface-place → plain-place permutation (0-based). Stops early
    /// (identity permutation) when the chain from this node down matches a
    /// CURATED converted alias — those render by name. Only used in bridi
    /// position; restrictors have the selector spelling instead.
    fn peel_conversions(&self, id: u32) -> R<(u32, [usize; 5])> {
        const IDENTITY: [usize; 5] = [0, 1, 2, 3, 4];
        let Selbri::Converted((conv, inner)) = self.selbri(id)? else {
            return Ok((id, IDENTITY));
        };
        // Single-layer chain with a curated converted alias renders by name.
        if let Selbri::Root(gismu) = self.selbri(*inner)? {
            let place: u8 = match conv {
                Conversion::Se => 2,
                Conversion::Te => 3,
                Conversion::Ve => 4,
                Conversion::Xe => 5,
            };
            if klaro_dictionary::curated::CONVERTED_ALIASES
                .iter()
                .any(|(_, g, swap)| g == gismu && *swap == place)
            {
                return Ok((id, IDENTITY));
            }
        }
        let (base, inner_perm) = self.peel_conversions(*inner)?;
        let swapped = match conv {
            Conversion::Se => 1,
            Conversion::Te => 2,
            Conversion::Ve => 3,
            Conversion::Xe => 4,
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
            Selbri::Root(g) => g.clone(),
            Selbri::Compound(parts) => parts.last().cloned().unwrap_or_default(),
            Selbri::Tanru((_, head)) => self.head_gismu(*head)?,
            Selbri::Converted((_, inner)) => self.head_gismu(*inner)?,
            Selbri::Negated(inner) => self.head_gismu(*inner)?,
            Selbri::Grouped(inner) => self.head_gismu(*inner)?,
            Selbri::WithArgs((core, _)) => self.head_gismu(*core)?,
            Selbri::Connected((_, _, _)) => String::new(),
            Selbri::Abstraction(_) => String::new(),
        })
    }

    /// The Klaro spelling of a dictionary word: the canonical alias, else the
    /// identity passthrough — which is only honest when the word (a) is
    /// actually in the dictionary (klaro's resolver fails closed on unknowns;
    /// gerna tolerates them at arity 2) and (b) is a legal Klaro identifier
    /// (apostrophe lujvo are not). Render must NEVER emit unparseable text, so
    /// both cases fail closed by name here.
    fn alias_or_identity(&self, gismu: &str) -> R<String> {
        if let Some(alias) = klaro_dictionary::canonical_alias(gismu) {
            return Ok(alias.to_owned());
        }
        if smuni_dictionary::get_arity(gismu).is_none() {
            return Err(nope(format!(
                "word {gismu:?} is dictionary-unknown (the Lojban front-end tolerates it at \
                 arity 2; Klaro fails closed on unknown names — SURFACE_SYNTAX §13)"
            )));
        }
        let mut chars = gismu.chars();
        let ident_ok = matches!(chars.next(), Some('a'..='z'))
            && chars.all(|c| matches!(c, 'a'..='z' | '0'..='9'));
        if !ident_ok {
            return Err(nope(format!(
                "word {gismu:?} is not a legal Klaro identifier (apostrophes have no \
                 spelling) and has no alias — curate one"
            )));
        }
        Ok(gismu.to_owned())
    }

    /// Label for SURFACE place `place` (0-based) of `gismu`'s canonical alias:
    /// the dictionary label when curated, else raw `xN`.
    fn place_label(&self, gismu: &str, place: usize) -> String {
        if let Some(alias) = klaro_dictionary::canonical_alias(gismu)
            && let Some(entry) = klaro_dictionary::alias(alias)
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
            Selbri::Root(gismu) => self.alias_or_identity(gismu)?,
            Selbri::Compound(parts) => parts
                .iter()
                .map(|p| self.alias_or_identity(p))
                .collect::<R<Vec<_>>>()?
                .into_iter()
                .collect::<Vec<_>>()
                .join("+"),
            Selbri::Tanru((modifier, head)) => {
                let modifier_text = match self.selbri(*modifier)? {
                    // A left-nested tanru needs explicit grouping.
                    Selbri::Tanru(_) => format!("[{}]", self.selbri_text(*modifier, false)?),
                    _ => self.selbri_text(*modifier, false)?,
                };
                format!("{modifier_text} {}", self.selbri_text(*head, selector_ok)?)
            }
            Selbri::Grouped(inner) => format!("[{}]", self.selbri_text(*inner, false)?),
            Selbri::Negated(inner) => format!("~{}", self.selbri_text(*inner, selector_ok)?),
            Selbri::Converted((conv, inner)) => {
                let Selbri::Root(gismu) = self.selbri(*inner)? else {
                    return Err(nope(
                        "a conversion over a non-root selbri has no Klaro spelling yet — \
                         curate a converted alias (klaro-dictionary CONVERTED_ALIASES)",
                    ));
                };
                let place: u8 = match conv {
                    Conversion::Se => 2,
                    Conversion::Te => 3,
                    Conversion::Ve => 4,
                    Conversion::Xe => 5,
                };
                // Curated converted alias first (works everywhere)…
                if let Some((alias, _, _)) = klaro_dictionary::curated::CONVERTED_ALIASES
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
                    "no Klaro spelling for the {conv:?}-conversion of {gismu:?} in \
                     predication position — curate a converted alias"
                )));
            }
            Selbri::WithArgs((core, be_args)) => {
                let core_text = self.selbri_text(*core, false)?;
                let mut rendered = Vec::new();
                for &arg in be_args {
                    rendered.push(self.term(arg)?);
                }
                format!("{core_text}({})", rendered.join(", "))
            }
            Selbri::Connected((_, _, _)) => {
                return Err(nope(
                    "a connected selbri outside main-bridi position (restrictor / tanru \
                     unit) has no Klaro spelling — only the bridi-level expansion exists",
                ));
            }
            Selbri::Abstraction((kind, body)) => {
                let keyword = match kind {
                    AbstractionKind::Nu => "event",
                    AbstractionKind::Duhu => "fact",
                    AbstractionKind::Ka => "property",
                    AbstractionKind::Ni => "amount",
                    AbstractionKind::Siho => "concept",
                };
                format!("{keyword} {{ {} }}", self.sentence(*body, 0)?)
            }
        })
    }

    // ── terms ──

    fn term(&self, id: u32) -> R<String> {
        Ok(match self.sumti(id)? {
            Sumti::ProSumti(word) => match word.as_str() {
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
                        "pro-sumti {other:?} is out of Klaro's scope (SURFACE_SYNTAX §10) — \
                         no spelling exists"
                    )));
                }
            },
            Sumti::Name(name) => render_name(name)?,
            Sumti::QuotedLiteral(text) => {
                if text.contains('\n') {
                    return Err(nope(
                        "a quoted literal containing a raw newline has no Klaro spelling \
                         (strings are single-line; SURFACE_SYNTAX §3)",
                    ));
                }
                format!("\"{}\"", text.replace('\\', "\\\\").replace('"', "\\\""))
            }
            Sumti::Unspecified => "_".into(),
            Sumti::Number(value) => {
                let rendered = format!("{value}");
                if !value.is_finite() || rendered.contains('e') || rendered.starts_with('-') {
                    return Err(nope(format!(
                        "number {value} has no Klaro literal (unsigned decimal only; \
                         SURFACE_SYNTAX §3) — fail closed"
                    )));
                }
                rendered
            }
            Sumti::Description((gadri, selbri)) => {
                if let Selbri::Abstraction(_) = self.selbri(*selbri)? {
                    return match gadri {
                        Gadri::Lo => self.restr_selbri(*selbri),
                        Gadri::Le | Gadri::La | Gadri::RoLo | Gadri::RoLe => Err(nope(
                            "abstractions are hard-wired to the implicit-some description; \
                             other gadri × NU combinations are out of scope \
                             (SURFACE_SYNTAX §10)",
                        )),
                    };
                }
                match gadri {
                    Gadri::Lo => format!("some {}", self.restr_selbri(*selbri)?),
                    Gadri::Le => format!("the {}", self.restr_selbri(*selbri)?),
                    Gadri::RoLo => format!("every {}", self.restr_selbri(*selbri)?),
                    Gadri::RoLe => format!("every the {}", self.restr_selbri(*selbri)?),
                    Gadri::La => match self.selbri(*selbri)? {
                        // §11 collapse: la + selbri ≡ a rigid Name.
                        Selbri::Root(word) => render_name(word)?,
                        other => {
                            return Err(nope(format!(
                                "la + a complex selbri has no Klaro spelling: {other:?}"
                            )));
                        }
                    },
                }
            }
            Sumti::QuantifiedDescription((count, gadri, selbri)) => match gadri {
                Gadri::Lo => {
                    if *count == 0 {
                        format!("no {}", self.restr_selbri(*selbri)?)
                    } else {
                        format!("exactly {count} {}", self.restr_selbri(*selbri)?)
                    }
                }
                Gadri::Le => format!("exactly {count} the {}", self.restr_selbri(*selbri)?),
                Gadri::La | Gadri::RoLo | Gadri::RoLe => {
                    return Err(nope(format!(
                        "a quantified {gadri:?} description has no Klaro spelling"
                    )));
                }
            },
            Sumti::Restricted((inner, clause)) => {
                format!("{} {}", self.term(*inner)?, self.rel_clause(clause)?)
            }
            Sumti::Tagged((_, _)) => {
                return Err(nope(
                    "a place-tagged term outside an argument list has no Klaro spelling",
                ));
            }
            Sumti::ModalTagged((_, _)) => {
                return Err(nope(
                    "a modal-tagged term outside a predication has no Klaro spelling",
                ));
            }
            Sumti::Connected((_, _, _, _)) => {
                return Err(nope(
                    "sumti connectives render only via bridi-level expansion — not yet \
                     renderable (translation-battery bullet)",
                ));
            }
        })
    }

    fn rel_clause(&self, clause: &RelClause) -> R<String> {
        let keyword = match clause.kind {
            RelClauseKind::Poi => "where",
            // §11 collapse: the engine treats voi as poi.
            RelClauseKind::Voi => "where",
            RelClauseKind::Noi => "also",
        };
        // Bare-predicate sugar: a body of shape `ke'a <selbri>` (no tail, no
        // prefixes) prints as the sugar form.
        // The bound entity is either an explicit ke'a head (klaro-emitted
        // buffers) or IMPLICIT (gerna leaves the head empty and smuni injects
        // ke'a at x1) — both print as the sugar.
        let head_is_kehah = |bridi: &Bridi| -> R<bool> {
            Ok(match bridi.head_terms.as_slice() {
                [] => true,
                [only] => matches!(self.sumti(*only)?, Sumti::ProSumti(w) if w == "ke'a"),
                _ => false,
            })
        };
        if let Sentence::Simple(bridi) = self.sentence_node(clause.body_sentence)?
            && bridi.tail_terms.is_empty()
            && bridi.tense.is_none()
            && bridi.attitudinal.is_none()
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
        // rendered KR re-parses (§7 mandatory-it). Klaro-emitted bodies carry
        // an explicit ke'a (head, or a tail term once the smuni named-`it`
        // collision is fixed) and render through the normal path.
        let has_explicit_keha = |bridi: &Bridi| -> R<bool> {
            for &tail in &bridi.tail_terms {
                let inner = match self.sumti(tail)? {
                    Sumti::Tagged((_, inner)) => *inner,
                    _ => tail,
                };
                if matches!(self.sumti(inner)?, Sumti::ProSumti(w) if w == "ke'a") {
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
            Ok(Selbri::Root(_)) | Ok(Selbri::Compound(_)) => true,
            Ok(Selbri::Tanru((m, h))) => self.bare_body_selbri(*m) && self.bare_body_selbri(*h),
            Ok(Selbri::Grouped(inner)) => self.bare_body_selbri(*inner),
            Ok(Selbri::Converted(_))
            | Ok(Selbri::Negated(_))
            | Ok(Selbri::WithArgs(_))
            | Ok(Selbri::Connected(_))
            | Ok(Selbri::Abstraction(_)) => false,
            Err(_) => false,
        }
    }
}

fn render_name(name: &str) -> R<String> {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return Err(nope("an empty Name has no Klaro spelling"));
    };
    if !first.is_ascii_alphabetic() {
        return Err(nope(format!(
            "Name {name:?} does not start with an ASCII letter — no Klaro spelling"
        )));
    }
    let rest: String = chars.collect();
    let candidate = format!("{}{}", first.to_ascii_uppercase(), rest.replace(' ', "_"));
    if !candidate
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return Err(nope(format!(
            "Name {name:?} contains characters outside [A-Za-z0-9_] — no Klaro spelling"
        )));
    }
    Ok(candidate)
}

/// PARITY GUARD — never called at runtime; `#[doc(hidden)]` keeps it off the
/// public API. Every `nibli_types::ast` enum Klaro owns the spelling of is
/// matched here WITHOUT wildcards, so adding a variant fails this crate's
/// build until Klaro covers it. A new variant obligates, in order:
/// 1. a SURFACE_SYNTAX section (spelling, or an explicit §10 out-of-scope
///    entry with justification),
/// 2. a grammar rule in `klaro.pest` + walker arm (or a targeted reject),
/// 3. a render arm in this module (spelling or fail-closed-by-name),
/// 4. a row in the nibli-verify CONSTRUCT_INVENTORY (battery bullet),
/// 5. a golden/twin test.
#[doc(hidden)]
#[allow(clippy::too_many_arguments)] // one parameter per guarded enum, by design
pub fn __ast_parity_guard(
    sumti: &Sumti,
    selbri: &Selbri,
    sentence: &Sentence,
    connective: &SentenceConnective,
    gadri: &Gadri,
    abstraction: &AbstractionKind,
    rel_kind: &RelClauseKind,
    place: &PlaceTag,
    bai: &BaiTag,
    modal: &ModalTag,
    conversion: &Conversion,
    logical: &Connective,
    tense: &Tense,
    attitudinal: &Attitudinal,
) {
    match sumti {
        Sumti::ProSumti(_) => {}
        Sumti::Description(_) => {}
        Sumti::Name(_) => {}
        Sumti::QuotedLiteral(_) => {}
        Sumti::Unspecified => {}
        Sumti::Tagged(_) => {}
        Sumti::ModalTagged(_) => {}
        Sumti::Restricted(_) => {}
        Sumti::Number(_) => {}
        Sumti::Connected(_) => {}
        Sumti::QuantifiedDescription(_) => {}
    }
    match selbri {
        Selbri::Root(_) => {}
        Selbri::Compound(_) => {}
        Selbri::Tanru(_) => {}
        Selbri::Converted(_) => {}
        Selbri::Negated(_) => {}
        Selbri::Grouped(_) => {}
        Selbri::WithArgs(_) => {}
        Selbri::Connected(_) => {}
        Selbri::Abstraction(_) => {}
    }
    match sentence {
        Sentence::Simple(_) => {}
        Sentence::Connected(_) => {}
        Sentence::Prenex(_) => {}
    }
    match connective {
        SentenceConnective::GanaiGi => {}
        SentenceConnective::GeGi => {}
        SentenceConnective::GaGi => {}
        SentenceConnective::GoGi => {}
        SentenceConnective::Afterthought(_) => {}
    }
    match gadri {
        Gadri::Lo => {}
        Gadri::Le => {}
        Gadri::La => {}
        Gadri::RoLo => {}
        Gadri::RoLe => {}
    }
    match abstraction {
        AbstractionKind::Nu => {}
        AbstractionKind::Duhu => {}
        AbstractionKind::Ka => {}
        AbstractionKind::Ni => {}
        AbstractionKind::Siho => {}
    }
    match rel_kind {
        RelClauseKind::Poi => {}
        RelClauseKind::Noi => {}
        RelClauseKind::Voi => {}
    }
    match place {
        PlaceTag::Fa => {}
        PlaceTag::Fe => {}
        PlaceTag::Fi => {}
        PlaceTag::Fo => {}
        PlaceTag::Fu => {}
    }
    match bai {
        BaiTag::Ria => {}
        BaiTag::Nii => {}
        BaiTag::Mui => {}
        BaiTag::Kiu => {}
        BaiTag::Pio => {}
        BaiTag::Bai => {}
    }
    match modal {
        ModalTag::Fixed(_) => {}
        ModalTag::Fio(_) => {}
    }
    match conversion {
        Conversion::Se => {}
        Conversion::Te => {}
        Conversion::Ve => {}
        Conversion::Xe => {}
    }
    match logical {
        Connective::Je => {}
        Connective::Ja => {}
        Connective::Jo => {}
        Connective::Ju => {}
    }
    match tense {
        Tense::Pu => {}
        Tense::Ca => {}
        Tense::Ba => {}
    }
    match attitudinal {
        Attitudinal::Ei => {}
        Attitudinal::Ehe => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_checked;

    /// smuni-compiled LogicBuffer (Debug form) for Klaro text.
    fn lb(text: &str) -> String {
        let buffer = parse_checked(text).unwrap_or_else(|e| panic!("parse {text:?}: {e}"));
        format!(
            "{:?}",
            smuni::compile_from_gerna_ast(buffer).unwrap_or_else(|e| panic!("smuni {text:?}: {e}"))
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
        let corpus = include_str!("../tests/acceptance.klaro");
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
        let mk = |sumti: Sumti| AstBuffer {
            selbris: vec![Selbri::Root("gerku".into())],
            sumtis: vec![sumti],
            sentences: vec![Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![0],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
            roots: vec![0],
        };
        for (buffer, needle) in [
            (mk(Sumti::ProSumti("ko".into())), "out of Klaro's scope"),
            (mk(Sumti::ProSumti("ri".into())), "out of Klaro's scope"),
            (mk(Sumti::ProSumti("go'i".into())), "out of Klaro's scope"),
            (mk(Sumti::Number(f64::INFINITY)), "no Klaro literal"),
            (mk(Sumti::Number(-2.0)), "no Klaro literal"),
        ] {
            let e = render(&buffer).expect_err("must fail closed");
            assert!(format!("{e}").contains(needle), "{e}");
        }
    }
}
