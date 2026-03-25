use super::*;

#[allow(dead_code)]
impl<'a, 'arena> Parser<'a, 'arena> {
    // ─── Selbri ───────────────────────────────────────────────

    pub(crate) fn try_parse_selbri(&mut self) -> Result<Option<Selbri<'arena>>, ParseError> {
        let negated = self.eat_cmavo("na");

        let selbri = if let Some(s) = self.try_parse_selbri_conn()? {
            s
        } else if negated {
            return Err(self.error("'na' without following selbri"));
        } else {
            return Ok(None);
        };

        if negated {
            Ok(Some(Selbri::Negated(self.arena.alloc(selbri))))
        } else {
            Ok(Some(selbri))
        }
    }

    pub(crate) fn try_parse_selbri_conn(&mut self) -> Result<Option<Selbri<'arena>>, ParseError> {
        let mut left = match self.try_parse_selbri_2() {
            Some(s) => s,
            None => return Ok(None),
        };

        loop {
            let conn = match self.peek_cmavo() {
                Some("je") => Connective::Je,
                Some("ja") => Connective::Ja,
                Some("jo") => Connective::Jo,
                Some("ju") => Connective::Ju,
                _ => break,
            };
            self.pos += 1;

            let neg_right = self.eat_cmavo("na");

            let right_base = self
                .try_parse_selbri_2()
                .ok_or_else(|| self.error("expected selbri after connective"))?;

            let right = if neg_right {
                Selbri::Negated(self.arena.alloc(right_base))
            } else {
                right_base
            };

            left = Selbri::Connected {
                left: self.arena.alloc(left),
                connective: conn,
                right: self.arena.alloc(right),
            };
        }

        Ok(Some(left))
    }

    pub(crate) fn try_parse_selbri_2(&mut self) -> Option<Selbri<'arena>> {
        let saved = self.save();
        let conv = self.try_parse_conversion();

        let tanru = match self.try_parse_tanru() {
            Some(t) => t,
            None => {
                if conv.is_some() {
                    self.restore(saved);
                }
                return None;
            }
        };

        if let Some(conv) = conv {
            Some(Selbri::Converted(conv, self.arena.alloc(tanru)))
        } else {
            Some(tanru)
        }
    }

    pub(crate) fn try_parse_conversion(&mut self) -> Option<Conversion> {
        let conv = match self.peek_cmavo()? {
            "se" => Conversion::Se,
            "te" => Conversion::Te,
            "ve" => Conversion::Ve,
            "xe" => Conversion::Xe,
            _ => return None,
        };
        self.pos += 1;
        Some(conv)
    }

    pub(crate) fn try_parse_tanru(&mut self) -> Option<Selbri<'arena>> {
        let mut units: Vec<Selbri> = Vec::new();

        while let Some(unit) = self.try_parse_tanru_unit() {
            units.push(unit);
        }

        if units.is_empty() {
            return None;
        }

        let mut result = units.pop().unwrap();
        while let Some(modifier) = units.pop() {
            result = Selbri::Tanru(self.arena.alloc(modifier), self.arena.alloc(result));
        }

        Some(result)
    }

    pub(crate) fn try_parse_tanru_unit(&mut self) -> Option<Selbri<'arena>> {
        let mut unit = self.try_parse_tanru_unit_base()?;

        while self.peek_is_cmavo("be") {
            unit = self.parse_be_clause(unit);
        }

        Some(unit)
    }

    pub(crate) fn try_parse_tanru_unit_base(&mut self) -> Option<Selbri<'arena>> {
        if self.peek_is_cmavo("ke") {
            if self.depth >= MAX_DEPTH {
                return None;
            }
            let saved = self.save();
            self.pos += 1;

            self.depth += 1;
            let inner = self.try_parse_tanru();
            self.depth = self.depth.saturating_sub(1);

            match inner {
                Some(selbri) => {
                    self.eat_cmavo("ke'e");
                    return Some(Selbri::Grouped(self.arena.alloc(selbri)));
                }
                None => {
                    self.restore(saved);
                    return None;
                }
            }
        }

        if let Some(kind) = self.try_parse_abstraction_keyword() {
            if self.depth >= MAX_DEPTH {
                return None;
            }
            let saved = self.save();

            self.depth += 1;
            let inner = self.parse_sentence();
            self.depth = self.depth.saturating_sub(1);

            match inner {
                Ok(bridi) => {
                    self.eat_cmavo("kei");
                    return Some(Selbri::Abstraction(kind, self.arena.alloc(bridi)));
                }
                Err(_) => {
                    self.restore(saved);
                    return None;
                }
            }
        }

        if self.peek_is_gismu() {
            if let Some(NormalizedToken::Standard(_, s)) = self.advance() {
                return Some(Selbri::Root(s.to_string()));
            }
        }

        if let Some(NormalizedToken::Glued(parts)) = self.peek() {
            let compound: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
            self.pos += 1;
            return Some(Selbri::Compound(compound));
        }

        if self.peek_is_cmavo("go'i") {
            self.pos += 1;
            return Some(Selbri::Root("go'i".to_string()));
        }

        {
            let saved = self.save();
            if let Some(conv) = self.try_parse_conversion() {
                if let Some(inner) = self.try_parse_tanru_unit_base() {
                    return Some(Selbri::Converted(conv, self.arena.alloc(inner)));
                }
                self.restore(saved);
            }
        }

        None
    }

    pub(crate) fn try_parse_abstraction_keyword(&mut self) -> Option<AbstractionKind> {
        let kind = match self.peek_cmavo()? {
            "nu" => AbstractionKind::Nu,
            "du'u" => AbstractionKind::Duhu,
            "ka" => AbstractionKind::Ka,
            "ni" => AbstractionKind::Ni,
            "si'o" => AbstractionKind::Siho,
            _ => return None,
        };
        self.pos += 1;
        Some(kind)
    }

    pub(crate) fn parse_be_clause(&mut self, core: Selbri<'arena>) -> Selbri<'arena> {
        self.eat_cmavo("be");

        let mut args = Vec::new();

        if let Some(sumti) = self.try_parse_sumti() {
            args.push(sumti);
        }

        while self.eat_cmavo("bei") {
            if let Some(sumti) = self.try_parse_sumti() {
                args.push(sumti);
            }
        }

        self.eat_cmavo("be'o");

        if args.is_empty() {
            core
        } else {
            Selbri::WithArgs {
                core: self.arena.alloc(core),
                args,
            }
        }
    }
}
