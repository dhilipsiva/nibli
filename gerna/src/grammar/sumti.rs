//! Sumti/term parsing: descriptions, names, pro-sumti, connectives, relative clauses.

use super::*;

#[allow(dead_code)]
impl<'a, 'arena> Parser<'a, 'arena> {
    // ─── Terms ────────────────────────────────────────────────

    /// Parse zero or more terms (sumti with optional tags).
    pub(crate) fn parse_terms(&mut self) -> Vec<Sumti<'arena>> {
        let mut terms = Vec::new();
        while let Some(term) = self.try_parse_term() {
            terms.push(term);
        }
        terms
    }

    /// Try to parse a single term: tagged or bare sumti.
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

    /// Try to consume a place tag (fa/fe/fi/fo/fu).
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

    /// Try to consume a BAI modal tag.
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

    /// Try to parse a fio...feu custom modal tag.
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

    /// Try to parse any modal tag (BAI shortcut or fio).
    pub(crate) fn try_parse_modal_tag(&mut self) -> Option<ModalTag<'arena>> {
        if let Some(bai) = self.try_parse_bai_tag() {
            return Some(ModalTag::Fixed(bai));
        }
        self.try_parse_fio_tag()
    }

    // ─── Sumti ────────────────────────────────────────────────

    /// Try to parse a sumti with optional relative clauses and connectives.
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

    /// Try to parse a sumti connective (.e/.a/.o/.u + optional nai).
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

    /// Try to parse a bare sumti (no connective, no rel clause).
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
            let interned = &*self.arena.alloc_str(s);
            self.pos += 1;
            return Some(Sumti::QuotedLiteral(interned));
        }
        if self.peek_is_cmavo("li") {
            return self.try_parse_li_number();
        }

        None
    }

    /// Try to parse a li-number sumti (li + PA digits + optional pi fraction +
    /// elidable lo'o terminator).
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
        // A digit string that overflows f64 (≥ ~309 digits) accumulates to +inf:
        // restore and fail so the sentence is a clean syntax error — never a
        // non-finite `Number` flowing into the pipeline (mirrors the u32
        // quantifier path's fail-closed overflow guard above; downstream
        // NonFinite catches exist, but the parse boundary must not rely on
        // them). The fractional loop below only divides, so it cannot overflow.
        if !value.is_finite() {
            self.restore(saved);
            return None;
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

    /// Try to consume a single PA digit cmavo (no..so = 0..9).
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

    /// Return true if the current token is a PA digit.
    pub(crate) fn peek_is_pa_digit(&self) -> bool {
        matches!(
            self.peek_cmavo(),
            Some("no" | "pa" | "re" | "ci" | "vo" | "mu" | "xa" | "ze" | "bi" | "so")
        )
    }

    /// Try to parse a suho-quantified description (suho lo/le selbri).
    pub(crate) fn try_parse_suho_description(&mut self) -> Option<Sumti<'arena>> {
        if !self.peek_is_cmavo("su'o") {
            return None;
        }
        let saved = self.save();
        self.pos += 1; // consume su'o

        let Some((gadri, selbri)) = self.parse_gadri_body(Gadri::Lo, Gadri::Le) else {
            self.restore(saved);
            return None;
        };

        Some(Sumti::Description {
            gadri,
            inner: selbri,
        })
    }

    /// Try to parse a numerically quantified description (PA lo/le selbri).
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

        let Some((gadri, selbri)) = self.parse_gadri_body(Gadri::Lo, Gadri::Le) else {
            self.restore(saved);
            return None;
        };

        let mut count: u32 = 0;
        for d in &digits {
            count = match count.checked_mul(10).and_then(|c| c.checked_add(*d as u32)) {
                Some(v) => v,
                // A PA quantifier count that overflows u32 (≥ ~10 digits) is rejected:
                // restore and fail so the sentence is a clean syntax error — never a
                // wrapped/fabricated count (release/WASM) or an overflow panic
                // (debug/fuzz). Identical, fail-closed behavior in both profiles.
                None => {
                    self.restore(saved);
                    return None;
                }
            };
        }

        Some(Sumti::QuantifiedDescription {
            count,
            gadri,
            inner: selbri,
        })
    }

    /// Try to parse a universally quantified description (ro lo/le selbri).
    pub(crate) fn try_parse_ro_description(&mut self) -> Option<Sumti<'arena>> {
        if !self.peek_is_cmavo("ro") {
            return None;
        }

        let saved = self.save();
        self.pos += 1; // consume ro

        let Some((gadri, selbri)) = self.parse_gadri_body(Gadri::RoLo, Gadri::RoLe) else {
            self.restore(saved);
            return None;
        };

        Some(Sumti::Description {
            gadri,
            inner: selbri,
        })
    }

    /// Try to parse a la-name or la-description.
    pub(crate) fn try_parse_la_name(&mut self) -> Option<Sumti<'arena>> {
        if !self.peek_is_cmavo("la") {
            return None;
        }

        let saved = self.save();
        self.pos += 1;
        self.eat_pause();

        let mut name_parts: Vec<&str> = Vec::new();
        while self.peek_is_cmevla() {
            if let Some(NormalizedToken::Standard(_, s)) = self.advance() {
                name_parts.push(s);
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

        Some(Sumti::Name(self.arena.alloc_str(&name_parts.join(" "))))
    }

    /// Try to parse a lo/le description.
    pub(crate) fn try_parse_description(&mut self) -> Option<Sumti<'arena>> {
        let saved = self.save();

        let Some((gadri, selbri)) = self.parse_gadri_body(Gadri::Lo, Gadri::Le) else {
            self.restore(saved);
            return None;
        };

        Some(Sumti::Description {
            gadri,
            inner: selbri,
        })
    }

    /// Parse a description body after any quantifier prefix: a `lo`/`le` gadri, a
    /// selbri, and an optional `ku` terminator. `lo_gadri`/`le_gadri` are the AST
    /// `Gadri` variants for this quantifier context (`Lo`/`Le` for plain/su'o/
    /// numeric, `RoLo`/`RoLe` for `ro`). Returns `None` WITHOUT backtracking when
    /// the next token is not `lo`/`le` or the selbri fails to parse — the CALLER
    /// restores to its pre-quantifier checkpoint on `None`.
    fn parse_gadri_body(
        &mut self,
        lo_gadri: Gadri,
        le_gadri: Gadri,
    ) -> Option<(Gadri, &'arena Selbri<'arena>)> {
        let gadri = match self.peek_cmavo() {
            Some("lo") => {
                self.pos += 1;
                lo_gadri
            }
            Some("le") => {
                self.pos += 1;
                le_gadri
            }
            _ => return None,
        };

        let selbri = self.try_parse_selbri_for_description()?;
        self.eat_cmavo("ku");

        Some((gadri, self.arena.alloc(selbri)))
    }

    /// Parse a selbri inside a description (supports na-negation and tanru).
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

    /// Try to parse a pro-sumti (mi, do, da, keha, cehu, ma, etc.).
    pub(crate) fn try_parse_pro_sumti(&mut self) -> Option<Sumti<'arena>> {
        let cmavo = self.peek_cmavo()?;

        let result = match cmavo {
            "zo'e" => Sumti::Unspecified,
            "mi" | "do" | "mi'o" | "mi'a" | "ma'a" | "do'o" | "ko" => {
                Sumti::ProSumti(self.arena.alloc_str(cmavo))
            }
            s if s.starts_with("ko'") && s.len() == 4 => {
                Sumti::ProSumti(self.arena.alloc_str(cmavo))
            }
            "da" | "de" | "di" => Sumti::ProSumti(self.arena.alloc_str(cmavo)),
            "ti" | "ta" | "tu" => Sumti::ProSumti(self.arena.alloc_str(cmavo)),
            "ri" | "ra" | "ru" => Sumti::ProSumti(self.arena.alloc_str(cmavo)),
            "ke'a" => Sumti::ProSumti(self.arena.alloc_str(cmavo)),
            "ce'u" => Sumti::ProSumti(self.arena.alloc_str(cmavo)),
            "ma" => Sumti::ProSumti(self.arena.alloc_str(cmavo)),
            _ => return None,
        };

        self.pos += 1;
        Some(result)
    }

    /// Try to parse a relative clause (poi/noi/voi + sentence + optional kuo).
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
