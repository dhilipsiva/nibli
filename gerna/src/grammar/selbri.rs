//! Selbri parsing: tanru, connectives, conversion, abstraction, be-clauses.

use super::*;

#[allow(dead_code)]
impl<'a, 'arena> Parser<'a, 'arena> {
    // ─── Selbri ───────────────────────────────────────────────

    /// Try to parse a selbri, including optional na-negation.
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

    /// Parse a selbri connective chain: selbri_2 ((je|ja|jo|ju)[nai] selbri_2)*.
    ///
    /// The `nai`-suffixed forms arrive as single tokens (the lexer's compound-cmavo
    /// merge) and negate the RIGHT operand via `Selbri::Negated` — `jenai` ("and
    /// not") is the official grammar's negated connective. A bare `na` after a
    /// plain connective (`X je na Y`) is NOT official grammar — camxes-std rejects
    /// it — so gerna rejects it too, with a diagnostic pointing at the compound
    /// form (the parse-differential gate pins gerna ⊆ camxes on acceptance).
    pub(crate) fn try_parse_selbri_conn(&mut self) -> Result<Option<Selbri<'arena>>, ParseError> {
        let mut left = match self.try_parse_selbri_2() {
            Some(s) => s,
            None => return Ok(None),
        };

        loop {
            let (conn, nai) = match self.peek_cmavo() {
                Some("je") => (Connective::Je, false),
                Some("ja") => (Connective::Ja, false),
                Some("jo") => (Connective::Jo, false),
                Some("ju") => (Connective::Ju, false),
                Some("jenai") => (Connective::Je, true),
                Some("janai") => (Connective::Ja, true),
                Some("jonai") => (Connective::Jo, true),
                Some("junai") => (Connective::Ju, true),
                _ => break,
            };
            self.pos += 1;

            if !nai && self.peek_cmavo() == Some("na") {
                return Err(self.error(
                    "bare 'na' after a selbri connective is not official grammar: \
                     use the compound negated connective (jenai/janai/jonai/junai)",
                ));
            }
            let neg_right = nai;

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

    /// Parse an optionally converted tanru (SE + tanru).
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

    /// Try to consume a SE-series conversion cmavo (se/te/ve/xe).
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

    /// Parse a tanru (right-grouping sequence of tanru units).
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

    /// Parse a single tanru unit, including any trailing be-clauses.
    pub(crate) fn try_parse_tanru_unit(&mut self) -> Option<Selbri<'arena>> {
        let mut unit = self.try_parse_tanru_unit_base()?;

        while self.peek_is_cmavo("be") {
            unit = self.parse_be_clause(unit);
        }

        Some(unit)
    }

    /// Parse the base of a tanru unit: brivla, ke-group, abstraction, or conversion.
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
            let word = match self.advance() {
                Some(NormalizedToken::Standard(_, s)) => Some(*s),
                _ => None,
            };
            if let Some(word) = word {
                return Some(Selbri::Root(self.arena.alloc_str(word)));
            }
        }

        if let Some(NormalizedToken::Glued(parts)) = self.peek() {
            let arena = self.arena;
            let compound: &'arena [&'arena str] =
                arena.alloc_slice_fill_iter(parts.iter().map(|s| &*arena.alloc_str(s)));
            self.pos += 1;
            return Some(Selbri::Compound(compound));
        }

        if self.peek_is_cmavo("go'i") {
            self.pos += 1;
            return Some(Selbri::Root("go'i"));
        }

        // `du` (identity / GOhA): a content-bearing cmavo selbri, like go'i.
        // Smuni lowers it to a flat 2-arg `du(x1, x2)` predicate (no event
        // decomposition) that feeds logji's union-find equivalence classes.
        if self.peek_is_cmavo("du") {
            self.pos += 1;
            return Some(Selbri::Root("du"));
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

    /// Try to consume a NU-class abstraction keyword (nu/duhu/ka/ni/siho).
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

    /// Parse a be...bei...beo argument-binding clause on a selbri.
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
                args: self.arena.alloc_slice_fill_iter(args),
            }
        }
    }
}
