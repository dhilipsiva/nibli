//! Sentence-level parsing: simple bridi, forethought connectives, tense, attitudinals.

use super::*;

#[allow(dead_code)]
impl<'a, 'arena> Parser<'a, 'arena> {
    // ─── Tense & Attitudinal ──────────────────────────────────

    /// Try to consume a tense marker (pu/ca/ba).
    pub(crate) fn try_parse_tense(&mut self) -> Option<Tense> {
        let t = match self.peek_cmavo()? {
            "pu" => Tense::Pu,
            "ca" => Tense::Ca,
            "ba" => Tense::Ba,
            _ => return None,
        };
        self.pos += 1;
        Some(t)
    }

    /// Try to consume a deontic attitudinal (ei/ehe).
    pub(crate) fn try_parse_attitudinal(&mut self) -> Option<Attitudinal> {
        let a = match self.peek_cmavo()? {
            "ei" => Attitudinal::Ei,
            "e'e" => Attitudinal::Ehe,
            _ => return None,
        };
        self.pos += 1;
        Some(a)
    }

    // ─── Sentence ─────────────────────────────────────────────

    /// Try to parse a prenex: `(ro (da|de|di))+ zo'u`. Returns the universally
    /// quantified variable names in prenex order, restoring the position if this
    /// is not a prenex (e.g. `ro lo gerku ...` — a universal description — or a
    /// `ro <var>` sequence with no `zo'u` terminator). `zo'u` already lexes as a
    /// plain cmavo.
    fn try_parse_prenex(&mut self) -> Option<Vec<&'arena str>> {
        let saved = self.save();
        let mut vars = Vec::new();
        while self.eat_cmavo("ro") {
            match self.peek_cmavo() {
                Some(v @ ("da" | "de" | "di")) => {
                    let name = &*self.arena.alloc_str(v);
                    self.pos += 1;
                    vars.push(name);
                }
                // `ro` not followed by a logic variable (e.g. `ro lo gerku`):
                // this is a universal description, not a prenex.
                _ => {
                    self.restore(saved);
                    return None;
                }
            }
        }
        if vars.is_empty() || !self.eat_cmavo("zo'u") {
            // No `ro <var>` sequence, or no `zo'u` terminator: not a prenex.
            self.restore(saved);
            return None;
        }
        Some(vars)
    }

    /// Parse a sentence: prenex, forethought connective, or simple bridi.
    pub(crate) fn parse_sentence(&mut self) -> Result<Sentence<'arena>, ParseError> {
        self.enter()?;

        // Prenex `ro da ro de zo'u <sentence>` quantifies a whole (recursive)
        // sentence body. Try it before the forethought/simple paths.
        if let Some(vars) = self.try_parse_prenex() {
            let body = self.parse_sentence()?;
            self.leave();
            return Ok(Sentence::Prenex {
                vars: self.arena.alloc_slice_fill_iter(vars),
                body: self.arena.alloc(body),
            });
        }

        let conn = if self.eat_cmavo("ganai") {
            Some(SentenceConnective::GanaiGi)
        } else if self.eat_cmavo("ge") {
            Some(SentenceConnective::GeGi)
        } else if self.eat_cmavo("ga") {
            Some(SentenceConnective::GaGi)
        } else if self.eat_cmavo("go") {
            Some(SentenceConnective::GoGi)
        } else {
            None
        };

        if let Some(connective) = conn {
            let left = self.parse_sentence()?;

            if !self.eat_cmavo("gi") {
                self.leave();
                return Err(
                    self.error("expected 'gi' after forethought connective and first sentence")
                );
            }

            let right = self.parse_sentence()?;

            self.leave();
            return Ok(Sentence::Connected {
                connective,
                left: self.arena.alloc(left),
                right: self.arena.alloc(right),
            });
        }

        let bridi = self.parse_simple_sentence()?;

        // GIhA bridi-tail connectives: `mi klama gi'e citka` — each tail is a
        // full predication (its own selbri + trailing sumti) sharing the head
        // terms. Desugars to the same `Sentence::Connected`/`Afterthought`
        // shape as `.i je` with the head terms repeated (the shared `&'arena
        // [Sumti]` slice is referenced by every tail's Bridi), so smuni, the
        // flattener, go'i resolution, and logji all apply unchanged. The chain
        // stays ONE sentence → one logic root, which keeps `gi'a`/`gi'o`/`gi'u`
        // a single compound fact (an Or/Iff/Xor must never split into
        // independent facts) while logji's ground-path conjunction flattening
        // stores a `gi'e`'s conjuncts as independently queryable facts.
        //
        // CONSTANT HEADS ONLY: repeating the head is semantically exact for
        // names/pro-sumti constants, but a quantified or description head
        // (`da`, `lo gerku`, `re lo …`) would be RE-QUANTIFIED per tail —
        // officially `da klama gi'e citka` is ∃x(klama(x) ∧ citka(x)), one
        // witness, while the repeated head compiles to two independent ∃s and
        // returns a wrong TRUE on disjoint witnesses. Fail closed until head
        // witnesses are genuinely shared across tails (see TODO.md).
        //
        // The fused spellings `gi'enai`… arrive as single Cmavo tokens (the
        // lexer's `reclassify_fused_giha_nai` pass); the spaced `gi'e nai` is
        // two tokens — both negate the right tail.
        let head_terms = bridi.head_terms;
        let mut sentence = Sentence::Simple(bridi);
        loop {
            let (connective, fused_nai) = match self.peek_cmavo() {
                Some("gi'e") => (Connective::Je, false),
                Some("gi'a") => (Connective::Ja, false),
                Some("gi'o") => (Connective::Jo, false),
                Some("gi'u") => (Connective::Ju, false),
                Some("gi'enai") => (Connective::Je, true),
                Some("gi'anai") => (Connective::Ja, true),
                Some("gi'onai") => (Connective::Jo, true),
                Some("gi'unai") => (Connective::Ju, true),
                _ => break,
            };
            if !head_terms.iter().all(giha_safe_head) {
                self.leave();
                return Err(self.error(
                    "a GIhA bridi-tail (gi'e/gi'a/gi'o/gi'u) with a quantified, \
                     description, or otherwise non-constant head is not supported: \
                     the shared head would be re-quantified per tail, silently \
                     splitting its scope. Restate as separate `.i je` sentences \
                     (making the repetition explicit) or use a name/constant head",
                ));
            }
            self.pos += 1;
            let right_negated = fused_nai || self.eat_cmavo("nai");

            let tail = self.parse_bridi_tail(head_terms)?;
            sentence = Sentence::Connected {
                connective: SentenceConnective::Afterthought {
                    left_negated: false,
                    connective,
                    right_negated,
                },
                left: self.arena.alloc(sentence),
                right: self.arena.alloc(Sentence::Simple(tail)),
            };
        }

        self.leave();
        Ok(sentence)
    }

    /// Parse one GIhA bridi-tail: `[na] selbri tail-terms [vau]`, sharing the
    /// already-parsed head terms. A leading `na` negates this tail only (it
    /// lands on the tail Bridi's `negated` flag, mirroring the simple-sentence
    /// unwrap of a top-level `Selbri::Negated`).
    fn parse_bridi_tail(
        &mut self,
        head_terms: &'arena [Sumti<'arena>],
    ) -> Result<Bridi<'arena>, ParseError> {
        if matches!(self.peek_cmavo(), Some("pu" | "ca" | "ba")) {
            return Err(self.error(
                "a tense marker on a GIhA bridi-tail is not supported (a tense \
                 before the first selbri applies to the first tail only); \
                 restate as separate `.i` sentences to tense each claim",
            ));
        }
        let selbri = match self.try_parse_selbri()? {
            Some(s) => s,
            None => return Err(self.error("expected selbri after bridi-tail connective")),
        };
        let (selbri, negated) = match selbri {
            Selbri::Negated(inner) => (inner.clone(), true),
            other => (other, false),
        };

        let tail_terms = self.parse_terms();
        self.eat_cmavo("vau");

        Ok(Bridi {
            selbri,
            head_terms,
            tail_terms: self.arena.alloc_slice_fill_iter(tail_terms),
            negated,
            tense: None,
            attitudinal: None,
        })
    }

    /// Parse a simple (non-connected) sentence into a Bridi.
    pub(crate) fn parse_simple_sentence(&mut self) -> Result<Bridi<'arena>, ParseError> {
        self.enter()?;

        let mut tense = self.try_parse_tense();
        let mut attitudinal = self.try_parse_attitudinal();

        let head_terms = self.parse_terms();
        while self.eat_pause() {}
        self.eat_cmavo("cu");

        if tense.is_none() {
            tense = self.try_parse_tense();
        }
        if attitudinal.is_none() {
            attitudinal = self.try_parse_attitudinal();
        }

        let selbri = match self.try_parse_selbri()? {
            Some(s) => s,
            None => {
                // No selbri. A clause with head terms but no predicate is a bare
                // sumti / observative — NOT a complete bridi. Fail closed with a
                // clear, distinct error rather than fabricating a `go'i` selbri
                // (which is indistinguishable from an explicit `go'i` and, once
                // resolved with no antecedent, reports the cryptic "go'i has no
                // antecedent"). A dangling sumti connective keeps its precise,
                // positioned diagnostic (matching the terminal unconsumed-token
                // check). Explicit `go'i` is the `Some(_)` branch above.
                self.leave();
                let msg = if head_terms.is_empty() {
                    "expected selbri or terms"
                } else if self.is_dangling_sumti_connective() {
                    self.unconsumed_error_msg()
                } else {
                    "a bridi needs a selbri: a bare sumti is not a complete statement"
                };
                return Err(self.error(msg));
            }
        };

        let (selbri, negated) = match selbri {
            Selbri::Negated(inner) => (inner.clone(), true),
            other => (other, false),
        };

        let tail_terms = self.parse_terms();
        self.eat_cmavo("vau");

        self.leave();
        Ok(Bridi {
            selbri,
            head_terms: self.arena.alloc_slice_fill_iter(head_terms),
            tail_terms: self.arena.alloc_slice_fill_iter(tail_terms),
            negated,
            tense,
            attitudinal,
        })
    }
}

/// True if a head sumti denotes a constant that can be repeated per GIhA tail
/// without changing meaning: names, non-variable pro-sumti, quoted literals,
/// and numbers (plus place-tagged wrappers of those). Everything that mints a
/// fresh witness or quantifier per compilation — descriptions, `da`/`de`/`di`,
/// quantified descriptions, sumti connectives, modal tags, relative clauses,
/// `zo'e` — makes the GIhA loop fail closed (re-quantifying the head per tail
/// would silently split one surface quantifier scope into independent ones).
fn giha_safe_head(s: &Sumti) -> bool {
    match s {
        Sumti::ProSumti(w) => !matches!(*w, "da" | "de" | "di"),
        Sumti::Name(_) | Sumti::QuotedLiteral(_) | Sumti::Number(_) => true,
        // `la <selbri>` is a rigid name — smuni compiles it to a bare Constant
        // (no witness, no quantifier), so repeating it per tail is exact.
        Sumti::Description {
            gadri: Gadri::La, ..
        } => true,
        Sumti::Tagged(_, inner) => giha_safe_head(inner),
        _ => false,
    }
}
