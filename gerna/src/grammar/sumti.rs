use super::*;

#[allow(dead_code)]
impl<'a, 'arena> Parser<'a, 'arena> {
    // ─── Terms ────────────────────────────────────────────────

    pub(crate) fn parse_terms(&mut self) -> Vec<Sumti<'arena>> {
        let mut terms = Vec::new();
        while let Some(term) = self.try_parse_term() {
            terms.push(term);
        }
        terms
    }

    pub(crate) fn try_parse_term(&mut self) -> Option<Sumti<'arena>> {
        let saved = self.save();

        if let Some(tag) = self.try_parse_place_tag() {
            if let Some(sumti) = self.try_parse_sumti() {
                return Some(Sumti::Tagged(tag, self.arena.alloc(sumti)));
            }
            self.restore(saved);
            return None;
        }

        if let Some(modal) = self.try_parse_modal_tag() {
            if let Some(sumti) = self.try_parse_sumti() {
                return Some(Sumti::ModalTagged(modal, self.arena.alloc(sumti)));
            }
            self.restore(saved);
            return None;
        }

        self.try_parse_sumti()
    }

    pub(crate) fn try_parse_place_tag(&mut self) -> Option<PlaceTag> {
        let tag = match self.peek_cmavo()? {
            "fa" => PlaceTag::Fa,
            "fe" => PlaceTag::Fe,
            "fi" => PlaceTag::Fi,
            "fo" => PlaceTag::Fo,
            "fu" => PlaceTag::Fu,
            _ => return None,
        };
        self.pos += 1;
        Some(tag)
    }

    pub(crate) fn try_parse_bai_tag(&mut self) -> Option<BaiTag> {
        let tag = match self.peek_cmavo()? {
            "ri'a" => BaiTag::Ria,
            "ni'i" => BaiTag::Nii,
            "mu'i" => BaiTag::Mui,
            "ki'u" => BaiTag::Kiu,
            "pi'o" => BaiTag::Pio,
            "ba'i" => BaiTag::Bai,
            _ => return None,
        };
        self.pos += 1;
        Some(tag)
    }

    pub(crate) fn try_parse_fio_tag(&mut self) -> Option<ModalTag<'arena>> {
        if !self.peek_is_cmavo("fi'o") {
            return None;
        }
        let saved = self.save();
        self.pos += 1;

        let selbri = match self.try_parse_selbri_for_description() {
            Some(s) => s,
            None => {
                self.restore(saved);
                return None;
            }
        };

        self.eat_cmavo("fe'u");

        Some(ModalTag::Fio(self.arena.alloc(selbri)))
    }

    pub(crate) fn try_parse_modal_tag(&mut self) -> Option<ModalTag<'arena>> {
        if let Some(bai) = self.try_parse_bai_tag() {
            return Some(ModalTag::Fixed(bai));
        }
        self.try_parse_fio_tag()
    }

    // ─── Sumti ────────────────────────────────────────────────

    pub(crate) fn try_parse_sumti(&mut self) -> Option<Sumti<'arena>> {
        let mut sumti = self.try_parse_bare_sumti()?;

        while let Some(clause) = self.try_parse_rel_clause() {
            sumti = Sumti::Restricted {
                inner: self.arena.alloc(sumti),
                clause,
            };
        }

        if let Some((conn, negated)) = self.try_parse_sumti_connective() {
            if let Some(right) = self.try_parse_sumti() {
                sumti = Sumti::Connected {
                    left: self.arena.alloc(sumti),
                    connective: conn,
                    right_negated: negated,
                    right: self.arena.alloc(right),
                };
            }
        }

        Some(sumti)
    }

    pub(crate) fn try_parse_sumti_connective(&mut self) -> Option<(Connective, bool)> {
        if self.pos + 1 >= self.tokens.len() {
            return None;
        }

        let is_pause = matches!(
            &self.tokens[self.pos],
            NormalizedToken::Standard(LojbanToken::Pause, _)
        );
        if !is_pause {
            return None;
        }

        let conn = match &self.tokens[self.pos + 1] {
            NormalizedToken::Standard(LojbanToken::Cmavo, "e") => Some(Connective::Je),
            NormalizedToken::Standard(LojbanToken::Cmavo, "a") => Some(Connective::Ja),
            NormalizedToken::Standard(LojbanToken::Cmavo, "o") => Some(Connective::Jo),
            NormalizedToken::Standard(LojbanToken::Cmavo, "u") => Some(Connective::Ju),
            _ => None,
        };

        let conn = conn?;
        let saved = self.save();
        self.pos += 2;

        let negated = self.eat_cmavo("nai");

        if self.at_end() || self.at_sentence_boundary() {
            self.restore(saved);
            return None;
        }

        Some((conn, negated))
    }

    pub(crate) fn try_parse_bare_sumti(&mut self) -> Option<Sumti<'arena>> {
        if self.peek_is_cmavo("la") {
            return self.try_parse_la_name();
        }

        if self.peek_is_cmavo("su'o") {
            if let Some(desc) = self.try_parse_suho_description() {
                return Some(desc);
            }
        }

        if self.peek_is_pa_digit() {
            if let Some(desc) = self.try_parse_numeric_quantified_description() {
                return Some(desc);
            }
        }

        if self.peek_is_cmavo("ro") {
            return self.try_parse_ro_description();
        }

        if self.peek_is_any_cmavo(&["lo", "le"]) {
            return self.try_parse_description();
        }

        if let Some(pro) = self.try_parse_pro_sumti() {
            return Some(pro);
        }

        if let Some(NormalizedToken::Quoted(s)) = self.peek() {
            let owned = s.to_string();
            self.pos += 1;
            return Some(Sumti::QuotedLiteral(owned));
        }
        if self.peek_is_cmavo("li") {
            return self.try_parse_li_number();
        }

        None
    }

    pub(crate) fn try_parse_li_number(&mut self) -> Option<Sumti<'arena>> {
        if !self.peek_is_cmavo("li") {
            return None;
        }
        let saved = self.save();
        self.pos += 1;

        let mut integer_digits: Vec<u8> = Vec::new();
        while let Some(d) = self.try_parse_pa_digit() {
            integer_digits.push(d);
        }

        let mut fractional_digits: Vec<u8> = Vec::new();
        if self.eat_cmavo("pi") {
            while let Some(d) = self.try_parse_pa_digit() {
                fractional_digits.push(d);
            }
        }

        if integer_digits.is_empty() && fractional_digits.is_empty() {
            self.restore(saved);
            return None;
        }

        self.eat_cmavo("lo'o");

        let mut value: f64 = 0.0;
        for &d in &integer_digits {
            value = value * 10.0 + d as f64;
        }
        if !fractional_digits.is_empty() {
            let mut frac: f64 = 0.0;
            for &d in fractional_digits.iter().rev() {
                frac = (frac + d as f64) / 10.0;
            }
            value += frac;
        }

        Some(Sumti::Number(value))
    }

    pub(crate) fn try_parse_pa_digit(&mut self) -> Option<u8> {
        let d = match self.peek_cmavo()? {
            "no" => 0,
            "pa" => 1,
            "re" => 2,
            "ci" => 3,
            "vo" => 4,
            "mu" => 5,
            "xa" => 6,
            "ze" => 7,
            "bi" => 8,
            "so" => 9,
            _ => return None,
        };
        self.pos += 1;
        Some(d)
    }

    pub(crate) fn peek_is_pa_digit(&self) -> bool {
        matches!(
            self.peek_cmavo(),
            Some("no" | "pa" | "re" | "ci" | "vo" | "mu" | "xa" | "ze" | "bi" | "so")
        )
    }

    pub(crate) fn try_parse_suho_description(&mut self) -> Option<Sumti<'arena>> {
        if !self.peek_is_cmavo("su'o") {
            return None;
        }
        let saved = self.save();
        self.pos += 1;

        let gadri = match self.peek_cmavo() {
            Some("lo") => {
                self.pos += 1;
                Gadri::Lo
            }
            Some("le") => {
                self.pos += 1;
                Gadri::Le
            }
            _ => {
                self.restore(saved);
                return None;
            }
        };

        let selbri = match self.try_parse_selbri_for_description() {
            Some(s) => s,
            None => {
                self.restore(saved);
                return None;
            }
        };

        self.eat_cmavo("ku");

        Some(Sumti::Description {
            gadri,
            inner: self.arena.alloc(selbri),
        })
    }

    pub(crate) fn try_parse_numeric_quantified_description(&mut self) -> Option<Sumti<'arena>> {
        let saved = self.save();

        let mut digits: Vec<u8> = Vec::new();
        while let Some(d) = self.try_parse_pa_digit() {
            digits.push(d);
        }

        if digits.is_empty() {
            self.restore(saved);
            return None;
        }

        let gadri = match self.peek_cmavo() {
            Some("lo") => {
                self.pos += 1;
                Gadri::Lo
            }
            Some("le") => {
                self.pos += 1;
                Gadri::Le
            }
            _ => {
                self.restore(saved);
                return None;
            }
        };

        let selbri = match self.try_parse_selbri_for_description() {
            Some(s) => s,
            None => {
                self.restore(saved);
                return None;
            }
        };

        self.eat_cmavo("ku");

        let mut count: u32 = 0;
        for d in &digits {
            count = count * 10 + (*d as u32);
        }

        Some(Sumti::QuantifiedDescription {
            count,
            gadri,
            inner: self.arena.alloc(selbri),
        })
    }

    pub(crate) fn try_parse_ro_description(&mut self) -> Option<Sumti<'arena>> {
        if !self.peek_is_cmavo("ro") {
            return None;
        }

        let saved = self.save();
        self.pos += 1;

        let gadri = match self.peek_cmavo() {
            Some("lo") => {
                self.pos += 1;
                Gadri::RoLo
            }
            Some("le") => {
                self.pos += 1;
                Gadri::RoLe
            }
            _ => {
                self.restore(saved);
                return None;
            }
        };

        let selbri = match self.try_parse_selbri_for_description() {
            Some(s) => s,
            None => {
                self.restore(saved);
                return None;
            }
        };

        self.eat_cmavo("ku");

        Some(Sumti::Description {
            gadri,
            inner: self.arena.alloc(selbri),
        })
    }

    pub(crate) fn try_parse_la_name(&mut self) -> Option<Sumti<'arena>> {
        if !self.peek_is_cmavo("la") {
            return None;
        }

        let saved = self.save();
        self.pos += 1;
        self.eat_pause();

        let mut name_parts = Vec::new();
        while self.peek_is_cmevla() {
            if let Some(NormalizedToken::Standard(_, s)) = self.advance() {
                name_parts.push(s.to_string());
            }
            self.eat_pause();
        }

        if name_parts.is_empty() {
            if let Some(selbri) = self.try_parse_selbri_for_description() {
                self.eat_cmavo("ku");
                return Some(Sumti::Description {
                    gadri: Gadri::La,
                    inner: self.arena.alloc(selbri),
                });
            }
            self.restore(saved);
            return None;
        }

        Some(Sumti::Name(name_parts.join(" ")))
    }

    pub(crate) fn try_parse_description(&mut self) -> Option<Sumti<'arena>> {
        let gadri = match self.peek_cmavo()? {
            "lo" => Gadri::Lo,
            "le" => Gadri::Le,
            _ => return None,
        };

        let saved = self.save();
        self.pos += 1;

        let selbri = match self.try_parse_selbri_for_description() {
            Some(s) => s,
            None => {
                self.restore(saved);
                return None;
            }
        };

        self.eat_cmavo("ku");

        Some(Sumti::Description {
            gadri,
            inner: self.arena.alloc(selbri),
        })
    }

    pub(crate) fn try_parse_selbri_for_description(&mut self) -> Option<Selbri<'arena>> {
        let saved = self.save();
        let negated = self.eat_cmavo("na");

        if let Some(tanru) = self.try_parse_tanru() {
            if negated {
                Some(Selbri::Negated(self.arena.alloc(tanru)))
            } else {
                Some(tanru)
            }
        } else {
            if negated {
                self.restore(saved);
            }
            None
        }
    }

    pub(crate) fn try_parse_pro_sumti(&mut self) -> Option<Sumti<'arena>> {
        let cmavo = self.peek_cmavo()?;

        let result = match cmavo {
            "zo'e" => Sumti::Unspecified,
            "mi" | "do" | "mi'o" | "mi'a" | "ma'a" | "do'o" | "ko" => {
                Sumti::ProSumti(cmavo.to_string())
            }
            s if s.starts_with("ko'") && s.len() == 4 => Sumti::ProSumti(cmavo.to_string()),
            "da" | "de" | "di" => Sumti::ProSumti(cmavo.to_string()),
            "ti" | "ta" | "tu" => Sumti::ProSumti(cmavo.to_string()),
            "ri" | "ra" | "ru" => Sumti::ProSumti(cmavo.to_string()),
            "ke'a" => Sumti::ProSumti(cmavo.to_string()),
            "ce'u" => Sumti::ProSumti(cmavo.to_string()),
            "ma" => Sumti::ProSumti(cmavo.to_string()),
            _ => return None,
        };

        self.pos += 1;
        Some(result)
    }

    pub(crate) fn try_parse_rel_clause(&mut self) -> Option<RelClause<'arena>> {
        let kind = match self.peek_cmavo()? {
            "poi" => RelClauseKind::Poi,
            "noi" => RelClauseKind::Noi,
            "voi" => RelClauseKind::Voi,
            _ => return None,
        };

        let saved = self.save();
        self.pos += 1;

        let body = match self.parse_sentence() {
            Ok(bridi) => bridi,
            Err(_) => {
                self.restore(saved);
                return None;
            }
        };

        self.eat_cmavo("ku'o");

        Some(RelClause {
            kind,
            body: self.arena.alloc(body),
        })
    }
}
