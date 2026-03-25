use super::*;

#[allow(dead_code)]
impl<'a, 'arena> Parser<'a, 'arena> {
    // ─── Sentence ─────────────────────────────────────────────

    pub(crate) fn parse_sentence(&mut self) -> Result<Sentence<'arena>, ParseError> {
        self.enter()?;

        let conn = if self.eat_cmavo("ganai") {
            Some(SentenceConnective::GanaiGi)
        } else if self.eat_cmavo("ge") {
            Some(SentenceConnective::GeGi)
        } else if self.eat_cmavo("ga") {
            Some(SentenceConnective::GaGi)
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
