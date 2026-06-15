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
    fn try_parse_prenex(&mut self) -> Option<Vec<String>> {
        let saved = self.save();
        let mut vars = Vec::new();
        while self.eat_cmavo("ro") {
            match self.peek_cmavo() {
                Some(v @ ("da" | "de" | "di")) => {
                    let name = v.to_string();
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
                vars,
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
        self.leave();
        Ok(Sentence::Simple(bridi))
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

        let selbri = if let Some(s) = self.try_parse_selbri()? {
            s
        } else {
            if head_terms.is_empty() {
                self.leave();
                return Err(self.error("expected selbri or terms"));
            }
            Selbri::Root("go'i".to_string())
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
            head_terms,
            tail_terms,
            negated,
            tense,
            attitudinal,
        })
    }
}
