// parser/src/grammar.rs — Recursive descent parser for Lojban
//
// Operates on the preprocessed NormalizedToken stream.
// Grammar (subset of CLL, expanded incrementally):
//
//   text        → sentence (.i sentence)*
//   sentence    → tense? terms? cu? tense? selbri tail? vau?
//   tail        → terms
//   terms       → term+
//   term        → place_tag sumti | modal_tag sumti | sumti
//   modal_tag   → bai_tag | fi'o selbri fe'u?
//   bai_tag     → ri'a | ni'i | mu'i | ki'u | pi'o | ba'i
//   sumti       → la_name | description | pro_sumti | quoted
//                | sumti rel_clause
//   la_name     → la cmevla+
//   quantified_desc → su'o? PA* (lo|le) selbri ku?
//   description → ro? (lo|le) selbri ku?
//   rel_clause  → (poi|noi) sentence ku'o?
//   selbri      → na? selbri_conn
//   selbri_conn → selbri_2 ((je|ja|jo|ju) selbri_2)*
//   selbri_2    → conversion? tanru
//   tanru       → tanru_unit+   (right-grouping)
//   tanru_unit  → brivla | ke selbri ke'e? | tanru_unit be_clause
//   be_clause   → be sumti (bei sumti)* be'o?
//   brivla      → gismu | lujvo | compound
//   conversion  → se | te | ve | xe
//   place_tag   → fa | fe | fi | fo | fu

use crate::ast::*;
use crate::lexer::LojbanToken;
use crate::preprocessor::NormalizedToken;

/// Maximum recursion depth to prevent stack overflow on pathological input.
const MAX_DEPTH: usize = 64;

/// Parse error with context.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub position: usize,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "parse error at token {}: {}",
            self.position, self.message
        )
    }
}

/// Recursive descent parser over the preprocessed token stream.
pub struct Parser<'a> {
    tokens: &'a [NormalizedToken<'a>],
    pos: usize,
    depth: usize,
}

#[allow(dead_code)]
impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [NormalizedToken<'a>]) -> Self {
        Self {
            tokens,
            pos: 0,
            depth: 0,
        }
    }

    // ─── Depth guard ──────────────────────────────────────────

    fn enter(&mut self) -> Result<(), ParseError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            Err(self.error("maximum nesting depth exceeded"))
        } else {
            Ok(())
        }
    }

    fn leave(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }

    // ─── Token inspection ─────────────────────────────────────

    fn at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn peek(&self) -> Option<&NormalizedToken<'a>> {
        self.tokens.get(self.pos)
    }

    fn peek_cmavo(&self) -> Option<&'a str> {
        match self.peek()? {
            NormalizedToken::Standard(LojbanToken::Cmavo, s) => Some(s),
            _ => None,
        }
    }

    fn peek_is_cmavo(&self, target: &str) -> bool {
        self.peek_cmavo().map_or(false, |s| s == target)
    }

    fn peek_is_any_cmavo(&self, targets: &[&str]) -> bool {
        self.peek_cmavo().map_or(false, |s| targets.contains(&s))
    }

    fn peek_is_gismu(&self) -> bool {
        matches!(
            self.peek(),
            Some(NormalizedToken::Standard(LojbanToken::Gismu, _))
        )
    }

    fn peek_is_cmevla(&self) -> bool {
        matches!(
            self.peek(),
            Some(NormalizedToken::Standard(LojbanToken::Cmevla, _))
        )
    }

    fn advance(&mut self) -> Option<&NormalizedToken<'a>> {
        let t = self.tokens.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    /// Consume a specific cmavo if present. Returns true if consumed.
    fn eat_cmavo(&mut self, target: &str) -> bool {
        if self.peek_is_cmavo(target) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    /// Consume any of the given cmavo. Returns the matched one, or None.
    fn eat_any_cmavo(&mut self, targets: &[&str]) -> Option<String> {
        if let Some(s) = self.peek_cmavo() {
            if targets.contains(&s) {
                let owned = s.to_string();
                self.pos += 1;
                return Some(owned);
            }
        }
        None
    }

    /// Consume a Pause token if present.
    fn eat_pause(&mut self) -> bool {
        if matches!(
            self.peek(),
            Some(NormalizedToken::Standard(LojbanToken::Pause, _))
        ) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    /// Save position for backtracking.
    fn save(&self) -> usize {
        self.pos
    }

    /// Restore position for backtracking.
    fn restore(&mut self, pos: usize) {
        self.pos = pos;
    }

    /// Check if the current position is at a `.i` sentence separator.
    fn at_dot_i(&self) -> bool {
        if self.pos + 1 >= self.tokens.len() {
            return false;
        }
        matches!(
            (&self.tokens[self.pos], &self.tokens[self.pos + 1]),
            (
                NormalizedToken::Standard(LojbanToken::Pause, _),
                NormalizedToken::Standard(LojbanToken::Cmavo, "i")
            )
        )
    }

    /// Consume a `.i` sentence separator if present.
    fn eat_dot_i(&mut self) -> bool {
        if self.at_dot_i() {
            self.pos += 2;
            true
        } else {
            false
        }
    }

    /// Try to parse an afterthought sentence connective: [na] (je|ja|jo|ju) [nai]
    /// Called right after `.i` has been consumed. Returns the SentenceConnective
    /// or None (restoring position) if no connective follows.
    fn try_parse_afterthought_sentence_connective(&mut self) -> Option<SentenceConnective> {
        let saved = self.save();

        // Optional left negation: na
        let left_negated = self.eat_cmavo("na");

        // Try compound forms first (jenai, janai, jonai, junai)
        let (conn, right_negated) = if self.eat_cmavo("jenai") {
            (Connective::Je, true)
        } else if self.eat_cmavo("janai") {
            (Connective::Ja, true)
        } else if self.eat_cmavo("jonai") {
            (Connective::Jo, true)
        } else if self.eat_cmavo("junai") {
            (Connective::Ju, true)
        } else if self.eat_cmavo("je") {
            (Connective::Je, self.eat_cmavo("nai"))
        } else if self.eat_cmavo("ja") {
            (Connective::Ja, self.eat_cmavo("nai"))
        } else if self.eat_cmavo("jo") {
            (Connective::Jo, self.eat_cmavo("nai"))
        } else if self.eat_cmavo("ju") {
            (Connective::Ju, self.eat_cmavo("nai"))
        } else {
            // No connective found; backtrack (may have consumed "na")
            self.restore(saved);
            return None;
        };

        Some(SentenceConnective::Afterthought {
            left_negated,
            connective: conn,
            right_negated,
        })
    }

    /// Check if current token is a sentence boundary.
    fn at_sentence_boundary(&self) -> bool {
        if self.at_end() {
            return true;
        }
        if self.at_dot_i() {
            return true;
        }
        self.peek_is_any_cmavo(&["ku'o", "kei", "vau"])
    }

    // Replace the top-level parse_text method:
    pub fn parse_text(&mut self) -> Result<ParsedText, ParseError> {
        let mut sentences = Vec::new();

        while self.eat_dot_i() || self.eat_pause() {}

        if self.at_end() {
            return Err(self.error("empty input"));
        }

        sentences.push(self.parse_sentence()?);

        loop {
            if !self.eat_dot_i() {
                while self.eat_pause() {}
                if !self.eat_dot_i() {
                    break;
                }
            }

            // Try afterthought sentence connective: .i [na] (je|ja|jo|ju) [nai]
            if let Some(conn) = self.try_parse_afterthought_sentence_connective() {
                while self.eat_pause() {}
                if self.at_end() {
                    return Err(
                        self.error("expected sentence after afterthought connective"),
                    );
                }
                let left = sentences
                    .pop()
                    .ok_or_else(|| self.error("no preceding sentence for connective"))?;
                let right = self.parse_sentence()?;
                sentences.push(Sentence::Connected {
                    connective: conn,
                    left: Box::new(left),
                    right: Box::new(right),
                });
                continue;
            }

            while self.eat_pause() {}
            if self.at_end() {
                break;
            }
            if self.at_dot_i() {
                continue;
            }
            sentences.push(self.parse_sentence()?);
        }

        while self.eat_pause() {}

        if !self.at_end() {
            return Err(self.error("unconsumed tokens remaining"));
        }

        Ok(ParsedText { sentences })
    }

    // ─── Sentence ─────────────────────────────────────────────

    fn parse_sentence(&mut self) -> Result<Sentence, ParseError> {
        self.enter()?;

        // Check for forethought connectives
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
            // Parse the left sentence
            let left = self.parse_sentence()?;

            // Expect the 'gi' separator
            if !self.eat_cmavo("gi") {
                self.leave();
                return Err(
                    self.error("expected 'gi' after forethought connective and first sentence")
                );
            }

            // Parse the right sentence
            let right = self.parse_sentence()?;

            self.leave();
            return Ok(Sentence::Connected {
                connective,
                left: Box::new(left),
                right: Box::new(right),
            });
        }

        // Fallback to standard simple bridi
        let bridi = self.parse_simple_sentence()?;
        self.leave();
        Ok(Sentence::Simple(bridi))
    }

    fn parse_simple_sentence(&mut self) -> Result<Bridi, ParseError> {
        self.enter()?;

        // Tense can appear sentence-initially: "pu mi klama"
        let mut tense = self.try_parse_tense();

        let head_terms = self.parse_terms();
        self.eat_cmavo("cu");

        // Tense can also appear mid-sentence: "mi pu klama" / "mi cu pu klama"
        if tense.is_none() {
            tense = self.try_parse_tense();
        }

        let selbri = if let Some(s) = self.try_parse_selbri()? {
            s
        } else {
            if head_terms.is_empty() {
                self.leave();
                return Err(self.error("expected selbri or terms"));
            }
            self.leave();
            return Err(self.error("observative sentences not yet supported"));
        };

        let (selbri, negated) = match selbri {
            Selbri::Negated(inner) => (*inner, true),
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
        })
    }

    fn looks_like_selbri_na(&self) -> bool {
        if self.pos + 1 >= self.tokens.len() {
            return false;
        }
        match &self.tokens[self.pos + 1] {
            NormalizedToken::Standard(LojbanToken::Gismu, _) => true,
            NormalizedToken::Standard(LojbanToken::Cmavo, s) => {
                matches!(
                    *s,
                    "se" | "te" | "ve" | "xe" | "ke" | "na"
                    | "nu" | "du'u" | "ka" | "ni" | "si'o"
                    | "pu" | "ca" | "ba"
                )
            }
            _ => false,
        }
    }

    // ─── Terms ────────────────────────────────────────────────

    fn parse_terms(&mut self) -> Vec<Sumti> {
        let mut terms = Vec::new();
        while let Some(term) = self.try_parse_term() {
            terms.push(term);
        }
        terms
    }

    fn try_parse_term(&mut self) -> Option<Sumti> {
        let saved = self.save();

        // Place tags first (fa/fe/fi/fo/fu)
        if let Some(tag) = self.try_parse_place_tag() {
            if let Some(sumti) = self.try_parse_sumti() {
                return Some(Sumti::Tagged(tag, Box::new(sumti)));
            }
            self.restore(saved);
            return None;
        }

        // Modal tags (BAI or fi'o)
        if let Some(modal) = self.try_parse_modal_tag() {
            if let Some(sumti) = self.try_parse_sumti() {
                return Some(Sumti::ModalTagged(modal, Box::new(sumti)));
            }
            self.restore(saved);
            return None;
        }

        self.try_parse_sumti()
    }

    fn try_parse_place_tag(&mut self) -> Option<PlaceTag> {
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

    fn try_parse_bai_tag(&mut self) -> Option<BaiTag> {
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

    fn try_parse_fio_tag(&mut self) -> Option<ModalTag> {
        if !self.peek_is_cmavo("fi'o") {
            return None;
        }
        let saved = self.save();
        self.pos += 1; // consume fi'o

        let selbri = match self.try_parse_selbri_for_description() {
            Some(s) => s,
            None => {
                self.restore(saved);
                return None;
            }
        };

        self.eat_cmavo("fe'u"); // optional terminator

        Some(ModalTag::Fio(Box::new(selbri)))
    }

    fn try_parse_modal_tag(&mut self) -> Option<ModalTag> {
        if let Some(bai) = self.try_parse_bai_tag() {
            return Some(ModalTag::Fixed(bai));
        }
        self.try_parse_fio_tag()
    }

    // ─── Sumti ────────────────────────────────────────────────

    fn try_parse_sumti(&mut self) -> Option<Sumti> {
        let mut sumti = self.try_parse_bare_sumti()?;

        while let Some(clause) = self.try_parse_rel_clause() {
            sumti = Sumti::Restricted {
                inner: Box::new(sumti),
                clause,
            };
        }

        // Afterthought sumti connective: .e / .a / .o / .u [nai]
        if let Some((conn, negated)) = self.try_parse_sumti_connective() {
            if let Some(right) = self.try_parse_sumti() {
                sumti = Sumti::Connected {
                    left: Box::new(sumti),
                    connective: conn,
                    right_negated: negated,
                    right: Box::new(right),
                };
            }
        }

        Some(sumti)
    }

    /// Try to parse a sumti connective: Pause + (e|a|o|u) [nai]
    /// Returns (Connective, right_negated) or None.
    fn try_parse_sumti_connective(&mut self) -> Option<(Connective, bool)> {
        // Must see Pause followed by a sumti connective cmavo
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
        self.pos += 2; // consume Pause + connective cmavo

        // Check for optional `nai` suffix
        let negated = self.eat_cmavo("nai");

        // Verify something parseable follows; if not, backtrack
        if self.at_end() || self.at_sentence_boundary() {
            self.restore(saved);
            return None;
        }

        Some((conn, negated))
    }

    fn try_parse_bare_sumti(&mut self) -> Option<Sumti> {
        if self.peek_is_cmavo("la") {
            return self.try_parse_la_name();
        }

        // ── su'o lo/le → plain existential (same as bare lo/le) ──
        if self.peek_is_cmavo("su'o") {
            if let Some(desc) = self.try_parse_suho_description() {
                return Some(desc);
            }
        }

        // ── PA digit(s) + lo/le → numeric quantified description ──
        if self.peek_is_pa_digit() {
            if let Some(desc) = self.try_parse_numeric_quantified_description() {
                return Some(desc);
            }
        }

        // ── Phase 6b: ro lo / ro le (universal quantification) ──
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

    fn try_parse_li_number(&mut self) -> Option<Sumti> {
        if !self.peek_is_cmavo("li") {
            return None;
        }
        let saved = self.save();
        self.pos += 1; // consume li

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

        self.eat_cmavo("lo'o"); // optional terminator

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

    fn try_parse_pa_digit(&mut self) -> Option<u8> {
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

    /// Peek whether the current token is a PA digit (no consuming).
    fn peek_is_pa_digit(&self) -> bool {
        matches!(
            self.peek_cmavo(),
            Some("no" | "pa" | "re" | "ci" | "vo" | "mu" | "xa" | "ze" | "bi" | "so")
        )
    }

    /// su'o (lo|le) selbri ku? — existential ("at least one"), same as bare lo/le.
    /// Backtracks if su'o is not followed by lo/le.
    fn try_parse_suho_description(&mut self) -> Option<Sumti> {
        if !self.peek_is_cmavo("su'o") {
            return None;
        }
        let saved = self.save();
        self.pos += 1; // consume su'o

        // Must be followed by lo or le
        let gadri = match self.peek_cmavo() {
            Some("lo") => { self.pos += 1; Gadri::Lo }
            Some("le") => { self.pos += 1; Gadri::Le }
            _ => { self.restore(saved); return None; }
        };

        let selbri = match self.try_parse_selbri_for_description() {
            Some(s) => s,
            None => { self.restore(saved); return None; }
        };

        self.eat_cmavo("ku");

        // su'o lo X ≡ lo X (existential default)
        Some(Sumti::Description {
            gadri,
            inner: Box::new(selbri),
        })
    }

    /// PA+ (lo|le) selbri ku? — numeric quantified description.
    /// Multi-digit: [pa, no] → 10. Backtracks if digits not followed by gadri.
    fn try_parse_numeric_quantified_description(&mut self) -> Option<Sumti> {
        let saved = self.save();

        // Collect one or more PA digits
        let mut digits: Vec<u8> = Vec::new();
        while let Some(d) = self.try_parse_pa_digit() {
            digits.push(d);
        }

        if digits.is_empty() {
            self.restore(saved);
            return None;
        }

        // Must be followed by lo or le
        let gadri = match self.peek_cmavo() {
            Some("lo") => { self.pos += 1; Gadri::Lo }
            Some("le") => { self.pos += 1; Gadri::Le }
            _ => { self.restore(saved); return None; }
        };

        let selbri = match self.try_parse_selbri_for_description() {
            Some(s) => s,
            None => { self.restore(saved); return None; }
        };

        self.eat_cmavo("ku");

        // Compute multi-digit number: [pa, no] → 10, [re] → 2
        let mut count: u32 = 0;
        for d in &digits {
            count = count * 10 + (*d as u32);
        }

        Some(Sumti::QuantifiedDescription {
            count,
            gadri,
            inner: Box::new(selbri),
        })
    }

    /// ro (lo|le) selbri ku? — universal quantification
    fn try_parse_ro_description(&mut self) -> Option<Sumti> {
        if !self.peek_is_cmavo("ro") {
            return None;
        }

        let saved = self.save();
        self.pos += 1; // consume ro

        // Must be followed by lo or le
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
            inner: Box::new(selbri),
        })
    }

    fn try_parse_la_name(&mut self) -> Option<Sumti> {
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
                    inner: Box::new(selbri),
                });
            }
            self.restore(saved);
            return None;
        }

        Some(Sumti::Name(name_parts.join(" ")))
    }

    /// (lo|le) selbri ku?
    fn try_parse_description(&mut self) -> Option<Sumti> {
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
            inner: Box::new(selbri),
        })
    }

    fn try_parse_selbri_for_description(&mut self) -> Option<Selbri> {
        self.try_parse_tanru()
    }

    fn try_parse_pro_sumti(&mut self) -> Option<Sumti> {
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

    fn try_parse_rel_clause(&mut self) -> Option<RelClause> {
        let kind = match self.peek_cmavo()? {
            "poi" => RelClauseKind::Poi,
            "noi" => RelClauseKind::Noi,
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
            body: Box::new(body),
        })
    }

    // ─── Selbri ───────────────────────────────────────────────

    fn try_parse_selbri(&mut self) -> Result<Option<Selbri>, ParseError> {
        let negated = self.eat_cmavo("na");

        let selbri = if let Some(s) = self.try_parse_selbri_conn()? {
            s
        } else if negated {
            return Err(self.error("'na' without following selbri"));
        } else {
            return Ok(None);
        };

        if negated {
            Ok(Some(Selbri::Negated(Box::new(selbri))))
        } else {
            Ok(Some(selbri))
        }
    }

    fn try_parse_selbri_conn(&mut self) -> Result<Option<Selbri>, ParseError> {
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

            let right = self
                .try_parse_selbri_2()
                .ok_or_else(|| self.error("expected selbri after connective"))?;

            left = Selbri::Connected {
                left: Box::new(left),
                connective: conn,
                right: Box::new(right),
            };
        }

        Ok(Some(left))
    }

    fn try_parse_selbri_2(&mut self) -> Option<Selbri> {
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
            Some(Selbri::Converted(conv, Box::new(tanru)))
        } else {
            Some(tanru)
        }
    }

    fn try_parse_conversion(&mut self) -> Option<Conversion> {
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

    fn try_parse_tanru(&mut self) -> Option<Selbri> {
        let mut units: Vec<Selbri> = Vec::new();

        while let Some(unit) = self.try_parse_tanru_unit() {
            units.push(unit);
        }

        if units.is_empty() {
            return None;
        }

        let mut result = units.pop().unwrap();
        while let Some(modifier) = units.pop() {
            result = Selbri::Tanru(Box::new(modifier), Box::new(result));
        }

        Some(result)
    }

    fn try_parse_tanru_unit(&mut self) -> Option<Selbri> {
        let mut unit = self.try_parse_tanru_unit_base()?;

        while self.peek_is_cmavo("be") {
            unit = self.parse_be_clause(unit);
        }

        Some(unit)
    }

    fn try_parse_tanru_unit_base(&mut self) -> Option<Selbri> {
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
                    return Some(Selbri::Grouped(Box::new(selbri)));
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
                    return Some(Selbri::Abstraction(kind, Box::new(bridi)));
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

        None
    }

    /// Try to parse an abstraction keyword (NU selma'o).
    /// Returns the AbstractionKind and consumes the keyword token.
    fn try_parse_abstraction_keyword(&mut self) -> Option<AbstractionKind> {
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

    fn parse_be_clause(&mut self, core: Selbri) -> Selbri {
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
                core: Box::new(core),
                args,
            }
        }
    }

    // ─── Error helpers ────────────────────────────────────────

    fn error(&self, message: &str) -> ParseError {
        ParseError {
            message: message.to_string(),
            position: self.pos,
        }
    }

    fn try_parse_tense(&mut self) -> Option<Tense> {
        let t = match self.peek_cmavo()? {
            "pu" => Tense::Pu,
            "ca" => Tense::Ca,
            "ba" => Tense::Ba,
            _ => return None,
        };
        self.pos += 1;
        Some(t)
    }
}

// ─── Public entry point ───────────────────────────────────────────

pub fn parse_tokens_to_ast(tokens: &[NormalizedToken<'_>]) -> Result<ParsedText, String> {
    let mut parser = Parser::new(tokens);
    parser.parse_text().map_err(|e| e.to_string())
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ─── Token constructors ───────────────────────────────────

    fn cmavo(text: &'static str) -> NormalizedToken<'static> {
        NormalizedToken::Standard(LojbanToken::Cmavo, text)
    }

    fn gismu(text: &'static str) -> NormalizedToken<'static> {
        NormalizedToken::Standard(LojbanToken::Gismu, text)
    }

    fn pause() -> NormalizedToken<'static> {
        NormalizedToken::Standard(LojbanToken::Pause, ".")
    }

    fn cmevla(text: &'static str) -> NormalizedToken<'static> {
        NormalizedToken::Standard(LojbanToken::Cmevla, text)
    }

    fn quoted(text: &'static str) -> NormalizedToken<'static> {
        NormalizedToken::Quoted(text)
    }

    fn glued(parts: Vec<&'static str>) -> NormalizedToken<'static> {
        NormalizedToken::Glued(parts)
    }

    /// Helper: parse tokens, assert success, return ParsedText
    fn parse_ok(tokens: &[NormalizedToken<'_>]) -> ParsedText {
        parse_tokens_to_ast(tokens).unwrap_or_else(|e| panic!("unexpected parse error: {}", e))
    }

    /// Helper: parse tokens, assert failure, return error string
    fn parse_err(tokens: &[NormalizedToken<'_>]) -> String {
        parse_tokens_to_ast(tokens).unwrap_err()
    }

    /// Helper: extract Bridi from a Sentence::Simple
    fn as_bridi(sentence: &Sentence) -> &Bridi {
        match sentence {
            Sentence::Simple(b) => b,
            other => panic!("expected Sentence::Simple, got {:?}", other),
        }
    }

    // ═══════════════════════════════════════════════════════════
    // 1. BASIC BRIDI STRUCTURE
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_simple_bridi() {
        // mi prami do → head:[mi], selbri:prami, tail:[do]
        let r = parse_ok(&[cmavo("mi"), gismu("prami"), cmavo("do")]);
        assert_eq!(r.sentences.len(), 1);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.selbri, Selbri::Root("prami".into()));
        assert_eq!(s.head_terms.len(), 1);
        assert_eq!(s.tail_terms.len(), 1);
        assert!(!s.negated);
    }

    #[test]
    fn test_selbri_only() {
        // klama → head:[], selbri:klama, tail:[]
        let r = parse_ok(&[gismu("klama")]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.selbri, Selbri::Root("klama".into()));
        assert!(s.head_terms.is_empty());
        assert!(s.tail_terms.is_empty());
    }

    #[test]
    fn test_with_cu() {
        // mi cu prami do — cu separates head from selbri
        let r = parse_ok(&[cmavo("mi"), cmavo("cu"), gismu("prami"), cmavo("do")]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.selbri, Selbri::Root("prami".into()));
        assert_eq!(s.head_terms.len(), 1);
        assert_eq!(s.tail_terms.len(), 1);
    }

    #[test]
    fn test_multiple_head_terms() {
        // mi do prami — two head terms before selbri
        let r = parse_ok(&[cmavo("mi"), cmavo("do"), gismu("prami")]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.head_terms.len(), 2);
        assert!(s.tail_terms.is_empty());
    }

    #[test]
    fn test_multiple_tail_terms() {
        // klama mi do — two tail terms after selbri
        let r = parse_ok(&[gismu("klama"), cmavo("mi"), cmavo("do")]);
        let s = as_bridi(&r.sentences[0]);
        assert!(s.head_terms.is_empty());
        assert_eq!(s.tail_terms.len(), 2);
    }

    #[test]
    fn test_vau_terminator() {
        // mi klama do vau — vau consumed, doesn't appear as unconsumed
        let r = parse_ok(&[cmavo("mi"), gismu("klama"), cmavo("do"), cmavo("vau")]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.tail_terms.len(), 1);
    }

    // ═══════════════════════════════════════════════════════════
    // 2. MULTI-SENTENCE (.i separator)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_multi_sentence() {
        // mi prami do .i do prami mi
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("prami"),
            cmavo("do"),
            pause(),
            cmavo("i"),
            cmavo("do"),
            gismu("prami"),
            cmavo("mi"),
        ]);
        assert_eq!(r.sentences.len(), 2);
    }

    #[test]
    fn test_three_sentences() {
        let r = parse_ok(&[
            gismu("klama"),
            pause(),
            cmavo("i"),
            gismu("prami"),
            pause(),
            cmavo("i"),
            gismu("barda"),
        ]);
        assert_eq!(r.sentences.len(), 3);
    }

    #[test]
    fn test_trailing_dot_i() {
        // mi klama .i (trailing .i with nothing after)
        let r = parse_ok(&[cmavo("mi"), gismu("klama"), pause(), cmavo("i")]);
        assert_eq!(r.sentences.len(), 1);
    }

    #[test]
    fn test_leading_dot_i_skipped() {
        // .i mi klama — leading .i is harmless
        let r = parse_ok(&[pause(), cmavo("i"), cmavo("mi"), gismu("klama")]);
        assert_eq!(r.sentences.len(), 1);
    }

    // ═══════════════════════════════════════════════════════════
    // 2b. AFTERTHOUGHT SENTENCE CONNECTIVES
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_afterthought_sentence_je() {
        // mi klama .i je do prami → Connected(Afterthought(Je), left, right)
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("klama"),
            pause(),
            cmavo("i"),
            cmavo("je"),
            cmavo("do"),
            gismu("prami"),
        ]);
        assert_eq!(r.sentences.len(), 1);
        match &r.sentences[0] {
            Sentence::Connected {
                connective:
                    SentenceConnective::Afterthought {
                        left_negated: false,
                        connective: Connective::Je,
                        right_negated: false,
                    },
                left,
                right,
            } => {
                let lb = as_bridi(left);
                assert_eq!(lb.selbri, Selbri::Root("klama".into()));
                let rb = as_bridi(right);
                assert_eq!(rb.selbri, Selbri::Root("prami".into()));
            }
            other => panic!("expected Connected(.i je), got {:?}", other),
        }
    }

    #[test]
    fn test_afterthought_sentence_ja() {
        // mi klama .i ja do prami
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("klama"),
            pause(),
            cmavo("i"),
            cmavo("ja"),
            cmavo("do"),
            gismu("prami"),
        ]);
        assert_eq!(r.sentences.len(), 1);
        match &r.sentences[0] {
            Sentence::Connected {
                connective:
                    SentenceConnective::Afterthought {
                        left_negated: false,
                        connective: Connective::Ja,
                        right_negated: false,
                    },
                ..
            } => {}
            other => panic!("expected Connected(.i ja), got {:?}", other),
        }
    }

    #[test]
    fn test_afterthought_sentence_jo() {
        // mi klama .i jo do prami
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("klama"),
            pause(),
            cmavo("i"),
            cmavo("jo"),
            cmavo("do"),
            gismu("prami"),
        ]);
        assert_eq!(r.sentences.len(), 1);
        match &r.sentences[0] {
            Sentence::Connected {
                connective:
                    SentenceConnective::Afterthought {
                        left_negated: false,
                        connective: Connective::Jo,
                        right_negated: false,
                    },
                ..
            } => {}
            other => panic!("expected Connected(.i jo), got {:?}", other),
        }
    }

    #[test]
    fn test_afterthought_sentence_ju() {
        // mi klama .i ju do prami
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("klama"),
            pause(),
            cmavo("i"),
            cmavo("ju"),
            cmavo("do"),
            gismu("prami"),
        ]);
        assert_eq!(r.sentences.len(), 1);
        match &r.sentences[0] {
            Sentence::Connected {
                connective:
                    SentenceConnective::Afterthought {
                        left_negated: false,
                        connective: Connective::Ju,
                        right_negated: false,
                    },
                ..
            } => {}
            other => panic!("expected Connected(.i ju), got {:?}", other),
        }
    }

    #[test]
    fn test_afterthought_sentence_naja() {
        // mi klama .i na ja do prami → implies (left negated)
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("klama"),
            pause(),
            cmavo("i"),
            cmavo("na"),
            cmavo("ja"),
            cmavo("do"),
            gismu("prami"),
        ]);
        assert_eq!(r.sentences.len(), 1);
        match &r.sentences[0] {
            Sentence::Connected {
                connective:
                    SentenceConnective::Afterthought {
                        left_negated: true,
                        connective: Connective::Ja,
                        right_negated: false,
                    },
                ..
            } => {}
            other => panic!("expected Connected(.i naja), got {:?}", other),
        }
    }

    #[test]
    fn test_afterthought_sentence_jenai() {
        // mi klama .i jenai do prami → AND with right negation
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("klama"),
            pause(),
            cmavo("i"),
            cmavo("jenai"),
            cmavo("do"),
            gismu("prami"),
        ]);
        assert_eq!(r.sentences.len(), 1);
        match &r.sentences[0] {
            Sentence::Connected {
                connective:
                    SentenceConnective::Afterthought {
                        left_negated: false,
                        connective: Connective::Je,
                        right_negated: true,
                    },
                ..
            } => {}
            other => panic!("expected Connected(.i jenai), got {:?}", other),
        }
    }

    #[test]
    fn test_afterthought_sentence_chain() {
        // A .i je B .i ja C → left-associative: Connected(ja, Connected(je, A, B), C)
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("klama"),
            pause(),
            cmavo("i"),
            cmavo("je"),
            cmavo("do"),
            gismu("prami"),
            pause(),
            cmavo("i"),
            cmavo("ja"),
            cmavo("ti"),
            gismu("barda"),
        ]);
        assert_eq!(r.sentences.len(), 1);
        match &r.sentences[0] {
            Sentence::Connected {
                connective:
                    SentenceConnective::Afterthought {
                        connective: Connective::Ja,
                        ..
                    },
                left,
                right,
            } => {
                // Left should be the .i je connection
                match left.as_ref() {
                    Sentence::Connected {
                        connective:
                            SentenceConnective::Afterthought {
                                connective: Connective::Je,
                                ..
                            },
                        ..
                    } => {}
                    other => panic!("inner should be .i je, got {:?}", other),
                }
                // Right should be simple
                let rb = as_bridi(right);
                assert_eq!(rb.selbri, Selbri::Root("barda".into()));
            }
            other => panic!("expected chained Connected, got {:?}", other),
        }
    }

    #[test]
    fn test_plain_dot_i_still_separates() {
        // mi klama .i do prami → two independent sentences (no connective)
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("klama"),
            pause(),
            cmavo("i"),
            cmavo("do"),
            gismu("prami"),
        ]);
        assert_eq!(r.sentences.len(), 2);
        let b0 = as_bridi(&r.sentences[0]);
        assert_eq!(b0.selbri, Selbri::Root("klama".into()));
        let b1 = as_bridi(&r.sentences[1]);
        assert_eq!(b1.selbri, Selbri::Root("prami".into()));
    }

    // ═══════════════════════════════════════════════════════════
    // 3. NEGATION
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_negation() {
        // mi na prami do → negated bridi
        let r = parse_ok(&[cmavo("mi"), cmavo("na"), gismu("prami"), cmavo("do")]);
        let s = as_bridi(&r.sentences[0]);
        assert!(s.negated);
        assert_eq!(s.selbri, Selbri::Root("prami".into()));
    }

    #[test]
    fn test_negation_with_cu() {
        // mi cu na prami do
        let r = parse_ok(&[
            cmavo("mi"),
            cmavo("cu"),
            cmavo("na"),
            gismu("prami"),
            cmavo("do"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert!(s.negated);
    }

    #[test]
    fn test_na_without_selbri_errors() {
        // na alone — error
        let e = parse_err(&[cmavo("na")]);
        assert!(e.contains("na"), "error should mention 'na': {}", e);
    }

    // ═══════════════════════════════════════════════════════════
    // 4. PLACE TAGS (fa/fe/fi/fo/fu)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_place_tag_fa() {
        let r = parse_ok(&[cmavo("fa"), cmavo("mi"), gismu("prami")]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Tagged(PlaceTag::Fa, inner) => {
                assert_eq!(**inner, Sumti::ProSumti("mi".into()));
            }
            other => panic!("expected Tagged(Fa), got {:?}", other),
        }
    }

    #[test]
    fn test_place_tag_all_five() {
        // fa mi fe do fi ti fo ta fu tu klama
        let r = parse_ok(&[
            cmavo("fa"),
            cmavo("mi"),
            cmavo("fe"),
            cmavo("do"),
            cmavo("fi"),
            cmavo("ti"),
            cmavo("fo"),
            cmavo("ta"),
            cmavo("fu"),
            cmavo("tu"),
            gismu("klama"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.head_terms.len(), 5);
        let tags: Vec<_> = s
            .head_terms
            .iter()
            .map(|t| match t {
                Sumti::Tagged(tag, _) => *tag,
                _ => panic!("expected Tagged"),
            })
            .collect();
        assert_eq!(
            tags,
            vec![
                PlaceTag::Fa,
                PlaceTag::Fe,
                PlaceTag::Fi,
                PlaceTag::Fo,
                PlaceTag::Fu
            ]
        );
    }

    #[test]
    fn test_place_tag_backtrack_at_end() {
        // klama fa — fa with no following sumti
        let e = parse_err(&[gismu("klama"), cmavo("fa")]);
        assert!(e.contains("unconsumed") || e.len() > 0);
    }

    #[test]
    fn test_place_tag_with_description() {
        // fe lo gerku ku klama — ku terminates description
        let r = parse_ok(&[
            cmavo("fe"),
            cmavo("lo"),
            gismu("gerku"),
            cmavo("ku"),
            gismu("klama"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Tagged(PlaceTag::Fe, inner) => {
                assert!(matches!(inner.as_ref(), Sumti::Description { .. }));
            }
            other => panic!("expected Tagged(Fe, Description), got {:?}", other),
        }
    }

    // ═══════════════════════════════════════════════════════════
    // 5. DESCRIPTIONS (lo/le/la gadri)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_lo_description() {
        let r = parse_ok(&[cmavo("mi"), gismu("nelci"), cmavo("lo"), gismu("gerku")]);
        match &as_bridi(&r.sentences[0]).tail_terms[0] {
            Sumti::Description { gadri, inner } => {
                assert_eq!(*gadri, Gadri::Lo);
                assert_eq!(**inner, Selbri::Root("gerku".into()));
            }
            other => panic!("expected Lo description, got {:?}", other),
        }
    }

    #[test]
    fn test_le_description() {
        let r = parse_ok(&[cmavo("mi"), gismu("nelci"), cmavo("le"), gismu("mlatu")]);
        match &as_bridi(&r.sentences[0]).tail_terms[0] {
            Sumti::Description { gadri, .. } => assert_eq!(*gadri, Gadri::Le),
            other => panic!("expected Le description, got {:?}", other),
        }
    }

    #[test]
    fn test_lo_with_ku_terminator() {
        // lo gerku ku barda — ku terminates description, barda is tail
        let r = parse_ok(&[cmavo("lo"), gismu("gerku"), cmavo("ku"), gismu("barda")]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.head_terms.len(), 1);
        assert!(matches!(
            &s.head_terms[0],
            Sumti::Description {
                gadri: Gadri::Lo,
                ..
            }
        ));
        assert_eq!(s.selbri, Selbri::Root("barda".into()));
    }

    #[test]
    fn test_lo_tanru_description() {
        // lo sutra gerku — description with tanru selbri
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("nelci"),
            cmavo("lo"),
            gismu("sutra"),
            gismu("gerku"),
        ]);
        match &as_bridi(&r.sentences[0]).tail_terms[0] {
            Sumti::Description { inner, .. } => {
                assert!(matches!(inner.as_ref(), Selbri::Tanru(_, _)));
            }
            other => panic!("expected tanru description, got {:?}", other),
        }
    }

    #[test]
    fn test_lo_backtrack_without_selbri() {
        let e = parse_err(&[gismu("klama"), cmavo("lo")]);
        assert!(e.contains("unconsumed"));
    }

    // ═══════════════════════════════════════════════════════════
    // 6. NAMES (la + cmevla)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_la_name_single() {
        let r = parse_ok(&[
            cmavo("la"),
            pause(),
            cmevla("djan"),
            pause(),
            cmavo("cu"),
            gismu("klama"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Name(n) => assert_eq!(n, "djan"),
            other => panic!("expected Name, got {:?}", other),
        }
    }

    #[test]
    fn test_la_name_multiple_cmevla() {
        // la .djan. .braun. — multi-part name
        let r = parse_ok(&[
            cmavo("la"),
            pause(),
            cmevla("djan"),
            pause(),
            cmevla("braun"),
            pause(),
            cmavo("cu"),
            gismu("klama"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Name(n) => assert_eq!(n, "djan braun"),
            other => panic!("expected Name, got {:?}", other),
        }
    }

    #[test]
    fn test_la_as_description() {
        // la + selbri (not cmevla) → Description with La gadri
        let r = parse_ok(&[cmavo("la"), gismu("gerku"), cmavo("cu"), gismu("barda")]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Description {
                gadri: Gadri::La, ..
            } => {}
            other => panic!("expected La description, got {:?}", other),
        }
    }

    #[test]
    fn test_la_backtrack_without_name() {
        let e = parse_err(&[gismu("klama"), cmavo("la")]);
        assert!(e.contains("unconsumed"));
    }

    // ═══════════════════════════════════════════════════════════
    // 7. PRO-SUMTI
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_pro_sumti_mi_do() {
        let r = parse_ok(&[cmavo("mi"), gismu("prami"), cmavo("do")]);
        assert_eq!(as_bridi(&r.sentences[0]).head_terms[0], Sumti::ProSumti("mi".into()));
        assert_eq!(as_bridi(&r.sentences[0]).tail_terms[0], Sumti::ProSumti("do".into()));
    }

    #[test]
    fn test_pro_sumti_da_de_di() {
        // da de di are logic variables
        let r = parse_ok(&[cmavo("da"), gismu("prami"), cmavo("de")]);
        assert_eq!(as_bridi(&r.sentences[0]).head_terms[0], Sumti::ProSumti("da".into()));
        assert_eq!(as_bridi(&r.sentences[0]).tail_terms[0], Sumti::ProSumti("de".into()));
    }

    #[test]
    fn test_pro_sumti_demonstratives() {
        // ti ta tu — near/medium/far demonstratives
        for pro in &["ti", "ta", "tu"] {
            let r = parse_ok(&[cmavo(pro), gismu("barda")]);
            assert_eq!(
                as_bridi(&r.sentences[0]).head_terms[0],
                Sumti::ProSumti(pro.to_string())
            );
        }
    }

    #[test]
    fn test_pro_sumti_anaphora() {
        // ri ra ru — anaphoric references
        for pro in &["ri", "ra", "ru"] {
            let r = parse_ok(&[cmavo(pro), gismu("barda")]);
            assert_eq!(
                as_bridi(&r.sentences[0]).head_terms[0],
                Sumti::ProSumti(pro.to_string())
            );
        }
    }

    #[test]
    fn test_pro_sumti_ma_question() {
        let r = parse_ok(&[cmavo("ma"), gismu("klama")]);
        assert_eq!(as_bridi(&r.sentences[0]).head_terms[0], Sumti::ProSumti("ma".into()));
    }

    #[test]
    fn test_zo_e_unspecified() {
        let r = parse_ok(&[cmavo("mi"), gismu("prami"), cmavo("zo'e")]);
        assert_eq!(as_bridi(&r.sentences[0]).tail_terms[0], Sumti::Unspecified);
    }

    // ═══════════════════════════════════════════════════════════
    // 8. QUOTED LITERALS
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_quoted_literal() {
        let r = parse_ok(&[cmavo("mi"), gismu("cusku"), quoted("coi")]);
        match &as_bridi(&r.sentences[0]).tail_terms[0] {
            Sumti::QuotedLiteral(s) => assert_eq!(s, "coi"),
            other => panic!("expected QuotedLiteral, got {:?}", other),
        }
    }

    // ═══════════════════════════════════════════════════════════
    // 9. SE CONVERSIONS (se/te/ve/xe)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_se_conversion() {
        let r = parse_ok(&[cmavo("do"), cmavo("se"), gismu("prami"), cmavo("mi")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Converted(Conversion::Se, inner) => {
                assert_eq!(**inner, Selbri::Root("prami".into()));
            }
            other => panic!("expected Se conversion, got {:?}", other),
        }
    }

    #[test]
    fn test_te_conversion() {
        let r = parse_ok(&[cmavo("te"), gismu("klama")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Converted(Conversion::Te, _) => {}
            other => panic!("expected Te conversion, got {:?}", other),
        }
    }

    #[test]
    fn test_ve_conversion() {
        let r = parse_ok(&[cmavo("ve"), gismu("klama")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Converted(Conversion::Ve, _) => {}
            other => panic!("expected Ve conversion, got {:?}", other),
        }
    }

    #[test]
    fn test_xe_conversion() {
        let r = parse_ok(&[cmavo("xe"), gismu("klama")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Converted(Conversion::Xe, _) => {}
            other => panic!("expected Xe conversion, got {:?}", other),
        }
    }

    #[test]
    fn test_conversion_backtrack_without_tanru() {
        let e = parse_err(&[gismu("klama"), cmavo("se")]);
        assert!(e.contains("unconsumed"));
    }

    // ═══════════════════════════════════════════════════════════
    // 10. TANRU (compound selbri)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_tanru_two_words() {
        // sutra gerku → Tanru(sutra, gerku)
        let r = parse_ok(&[cmavo("mi"), gismu("sutra"), gismu("gerku")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Tanru(m, h) => {
                assert_eq!(**m, Selbri::Root("sutra".into()));
                assert_eq!(**h, Selbri::Root("gerku".into()));
            }
            other => panic!("expected Tanru, got {:?}", other),
        }
    }

    #[test]
    fn test_tanru_three_words_right_grouping() {
        // a b c → Tanru(a, Tanru(b, c)) — right grouping
        let r = parse_ok(&[gismu("barda"), gismu("sutra"), gismu("gerku")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Tanru(a, bc) => {
                assert_eq!(**a, Selbri::Root("barda".into()));
                match bc.as_ref() {
                    Selbri::Tanru(b, c) => {
                        assert_eq!(**b, Selbri::Root("sutra".into()));
                        assert_eq!(**c, Selbri::Root("gerku".into()));
                    }
                    other => panic!("expected inner Tanru, got {:?}", other),
                }
            }
            other => panic!("expected outer Tanru, got {:?}", other),
        }
    }

    // ═══════════════════════════════════════════════════════════
    // 11. KE/KE'E GROUPING
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_ke_grouping() {
        // ke sutra gerku ke'e
        let r = parse_ok(&[
            cmavo("mi"),
            cmavo("ke"),
            gismu("sutra"),
            gismu("gerku"),
            cmavo("ke'e"),
        ]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Grouped(inner) => {
                assert!(matches!(inner.as_ref(), Selbri::Tanru(_, _)));
            }
            other => panic!("expected Grouped, got {:?}", other),
        }
    }

    #[test]
    fn test_ke_without_ke_e() {
        // ke sutra gerku (no ke'e — optional)
        let r = parse_ok(&[cmavo("mi"), cmavo("ke"), gismu("sutra"), gismu("gerku")]);
        assert!(matches!(&as_bridi(&r.sentences[0]).selbri, Selbri::Grouped(_)));
    }

    #[test]
    fn test_ke_nested() {
        // ke ke barda sutra ke'e gerku ke'e
        let r = parse_ok(&[
            cmavo("ke"),
            cmavo("ke"),
            gismu("barda"),
            gismu("sutra"),
            cmavo("ke'e"),
            gismu("gerku"),
            cmavo("ke'e"),
        ]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Grouped(outer) => {
                // outer is Tanru(Grouped(Tanru(barda, sutra)), gerku)
                match outer.as_ref() {
                    Selbri::Tanru(left, right) => {
                        assert!(matches!(left.as_ref(), Selbri::Grouped(_)));
                        assert_eq!(**right, Selbri::Root("gerku".into()));
                    }
                    other => panic!("expected Tanru inside Grouped, got {:?}", other),
                }
            }
            other => panic!("expected Grouped, got {:?}", other),
        }
    }

    #[test]
    fn test_depth_limit_does_not_crash() {
        let mut tokens: Vec<NormalizedToken<'static>> = Vec::new();
        tokens.push(cmavo("mi"));
        for _ in 0..100 {
            tokens.push(cmavo("ke"));
        }
        tokens.push(gismu("klama"));
        for _ in 0..100 {
            tokens.push(cmavo("ke'e"));
        }
        // Should not panic/stack overflow — either parses partially or errors
        let _ = parse_tokens_to_ast(&tokens);
    }

    // ═══════════════════════════════════════════════════════════
    // 12. BE/BEI CLAUSES
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_be_single_arg() {
        // nelci be lo gerku
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("nelci"),
            cmavo("be"),
            cmavo("lo"),
            gismu("gerku"),
        ]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::WithArgs { core, args } => {
                assert_eq!(**core, Selbri::Root("nelci".into()));
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected WithArgs, got {:?}", other),
        }
    }

    #[test]
    fn test_be_bei_multiple_args() {
        // klama be mi bei do bei ti
        let r = parse_ok(&[
            gismu("klama"),
            cmavo("be"),
            cmavo("mi"),
            cmavo("bei"),
            cmavo("do"),
            cmavo("bei"),
            cmavo("ti"),
        ]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::WithArgs { args, .. } => assert_eq!(args.len(), 3),
            other => panic!("expected WithArgs with 3 args, got {:?}", other),
        }
    }

    #[test]
    fn test_be_with_be_o_terminator() {
        // nelci be lo gerku be'o barda
        let r = parse_ok(&[
            gismu("nelci"),
            cmavo("be"),
            cmavo("lo"),
            gismu("gerku"),
            cmavo("be'o"),
            cmavo("mi"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert!(matches!(&s.selbri, Selbri::WithArgs { .. }));
        assert_eq!(s.tail_terms.len(), 1);
    }

    // ═══════════════════════════════════════════════════════════
    // 13. SELBRI CONNECTIVES (je/ja/jo/ju)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_connective_je() {
        let r = parse_ok(&[cmavo("mi"), gismu("barda"), cmavo("je"), gismu("xunre")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Connected {
                connective: Connective::Je,
                ..
            } => {}
            other => panic!("expected Je, got {:?}", other),
        }
    }

    #[test]
    fn test_connective_ja() {
        let r = parse_ok(&[cmavo("mi"), gismu("barda"), cmavo("ja"), gismu("cmalu")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Connected {
                connective: Connective::Ja,
                ..
            } => {}
            other => panic!("expected Ja, got {:?}", other),
        }
    }

    #[test]
    fn test_connective_jo() {
        let r = parse_ok(&[cmavo("mi"), gismu("barda"), cmavo("jo"), gismu("cmalu")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Connected {
                connective: Connective::Jo,
                ..
            } => {}
            other => panic!("expected Jo, got {:?}", other),
        }
    }

    #[test]
    fn test_connective_ju() {
        let r = parse_ok(&[cmavo("mi"), gismu("barda"), cmavo("ju"), gismu("cmalu")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Connected {
                connective: Connective::Ju,
                ..
            } => {}
            other => panic!("expected Ju, got {:?}", other),
        }
    }

    #[test]
    fn test_connective_chained() {
        // barda je sutra je cmalu → left-associative: Connected(Connected(barda,je,sutra),je,cmalu)
        let r = parse_ok(&[
            gismu("barda"),
            cmavo("je"),
            gismu("sutra"),
            cmavo("je"),
            gismu("cmalu"),
        ]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Connected {
                left,
                connective: Connective::Je,
                right,
            } => {
                assert!(matches!(left.as_ref(), Selbri::Connected { .. }));
                assert_eq!(**right, Selbri::Root("cmalu".into()));
            }
            other => panic!("expected chained Connected, got {:?}", other),
        }
    }

    // ═══════════════════════════════════════════════════════════
    // 14. RELATIVE CLAUSES (poi/noi)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_poi_relative_clause() {
        // lo gerku poi barda
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("nelci"),
            cmavo("lo"),
            gismu("gerku"),
            cmavo("poi"),
            gismu("barda"),
        ]);
        match &as_bridi(&r.sentences[0]).tail_terms[0] {
            Sumti::Restricted { clause, .. } => {
                assert_eq!(clause.kind, RelClauseKind::Poi);
            }
            other => panic!("expected Restricted(poi), got {:?}", other),
        }
    }

    #[test]
    fn test_noi_relative_clause() {
        // lo gerku noi sutra
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("nelci"),
            cmavo("lo"),
            gismu("gerku"),
            cmavo("noi"),
            gismu("sutra"),
        ]);
        match &as_bridi(&r.sentences[0]).tail_terms[0] {
            Sumti::Restricted { clause, .. } => {
                assert_eq!(clause.kind, RelClauseKind::Noi);
            }
            other => panic!("expected Restricted(noi), got {:?}", other),
        }
    }

    #[test]
    fn test_relative_clause_with_ku_o() {
        // lo gerku poi barda ku'o klama
        let r = parse_ok(&[
            cmavo("lo"),
            gismu("gerku"),
            cmavo("poi"),
            gismu("barda"),
            cmavo("ku'o"),
            gismu("klama"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert!(matches!(&s.head_terms[0], Sumti::Restricted { .. }));
        assert_eq!(s.selbri, Selbri::Root("klama".into()));
    }

    #[test]
    fn test_relative_clause_with_arguments() {
        // lo gerku poi mi nelci — relative clause with head+selbri
        let r = parse_ok(&[
            cmavo("lo"),
            gismu("gerku"),
            cmavo("poi"),
            cmavo("mi"),
            gismu("nelci"),
            cmavo("ku'o"),
            gismu("barda"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Restricted { clause, .. } => {
                let body_bridi = as_bridi(&clause.body);
                assert_eq!(body_bridi.head_terms.len(), 1);
                assert_eq!(body_bridi.selbri, Selbri::Root("nelci".into()));
            }
            other => panic!("expected Restricted with complex body, got {:?}", other),
        }
    }

    // ═══════════════════════════════════════════════════════════
    // 15. COMPOUND (glued/lujvo)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_compound_selbri() {
        let r = parse_ok(&[cmavo("mi"), glued(vec!["barda", "gerku"])]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Compound(parts) => {
                assert_eq!(parts, &["barda", "gerku"]);
            }
            other => panic!("expected Compound, got {:?}", other),
        }
    }

    // ═══════════════════════════════════════════════════════════
    // 16. UNIVERSAL QUANTIFIER (ro lo / ro le) — Phase 6b
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_ro_lo_description() {
        let r = parse_ok(&[
            cmavo("ro"),
            cmavo("lo"),
            gismu("gerku"),
            cmavo("cu"),
            gismu("barda"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description { gadri, inner } => {
                assert_eq!(*gadri, Gadri::RoLo);
                assert_eq!(**inner, Selbri::Root("gerku".into()));
            }
            other => panic!("expected RoLo, got {:?}", other),
        }
    }

    #[test]
    fn test_ro_le_description() {
        let r = parse_ok(&[
            cmavo("ro"),
            cmavo("le"),
            gismu("mlatu"),
            cmavo("cu"),
            gismu("cmalu"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Description { gadri, .. } => assert_eq!(*gadri, Gadri::RoLe),
            other => panic!("expected RoLe, got {:?}", other),
        }
    }

    #[test]
    fn test_ro_lo_with_ku() {
        let r = parse_ok(&[
            cmavo("ro"),
            cmavo("lo"),
            gismu("gerku"),
            cmavo("ku"),
            gismu("barda"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert!(matches!(
            &s.head_terms[0],
            Sumti::Description {
                gadri: Gadri::RoLo,
                ..
            }
        ));
        assert_eq!(s.selbri, Selbri::Root("barda".into()));
    }

    #[test]
    fn test_ro_lo_tanru() {
        // ro lo sutra gerku cu barda — tanru inside ro lo
        let r = parse_ok(&[
            cmavo("ro"),
            cmavo("lo"),
            gismu("sutra"),
            gismu("gerku"),
            cmavo("cu"),
            gismu("barda"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Description {
                gadri: Gadri::RoLo,
                inner,
            } => {
                assert!(matches!(inner.as_ref(), Selbri::Tanru(_, _)));
            }
            other => panic!("expected RoLo tanru, got {:?}", other),
        }
    }

    #[test]
    fn test_ro_in_tail_position() {
        // mi nelci ro lo gerku — ro lo in tail
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("nelci"),
            cmavo("ro"),
            cmavo("lo"),
            gismu("gerku"),
        ]);
        match &as_bridi(&r.sentences[0]).tail_terms[0] {
            Sumti::Description {
                gadri: Gadri::RoLo, ..
            } => {}
            other => panic!("expected RoLo in tail, got {:?}", other),
        }
    }

    #[test]
    fn test_ro_backtrack_without_gadri() {
        // ro alone (not followed by lo/le) — should error
        let e = parse_err(&[cmavo("ro"), gismu("klama")]);
        assert!(!e.is_empty());
    }

    #[test]
    fn test_ro_lo_with_relative_clause() {
        // ro lo gerku poi barda cu sutra
        let r = parse_ok(&[
            cmavo("ro"),
            cmavo("lo"),
            gismu("gerku"),
            cmavo("poi"),
            gismu("barda"),
            cmavo("ku'o"),
            cmavo("cu"),
            gismu("sutra"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Restricted { inner, clause } => {
                assert_eq!(clause.kind, RelClauseKind::Poi);
                match inner.as_ref() {
                    Sumti::Description {
                        gadri: Gadri::RoLo, ..
                    } => {}
                    other => panic!("expected RoLo inside Restricted, got {:?}", other),
                }
            }
            other => panic!("expected Restricted(RoLo), got {:?}", other),
        }
    }

    // ═══════════════════════════════════════════════════════════
    // 17. COMBINED / COMPLEX STRUCTURES
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_conversion_plus_tanru() {
        // se sutra gerku → Converted(Se, Tanru(sutra, gerku))
        let r = parse_ok(&[cmavo("se"), gismu("sutra"), gismu("gerku")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Converted(Conversion::Se, inner) => {
                assert!(matches!(inner.as_ref(), Selbri::Tanru(_, _)));
            }
            other => panic!("expected Converted(Se, Tanru), got {:?}", other),
        }
    }

    #[test]
    fn test_negation_plus_conversion() {
        // mi na se prami do
        let r = parse_ok(&[
            cmavo("mi"),
            cmavo("na"),
            cmavo("se"),
            gismu("prami"),
            cmavo("do"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert!(s.negated);
        assert!(matches!(&s.selbri, Selbri::Converted(Conversion::Se, _)));
    }

    #[test]
    fn test_description_in_be_clause() {
        // nelci be lo gerku bei lo mlatu
        let r = parse_ok(&[
            gismu("nelci"),
            cmavo("be"),
            cmavo("lo"),
            gismu("gerku"),
            cmavo("bei"),
            cmavo("lo"),
            gismu("mlatu"),
        ]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::WithArgs { args, .. } => {
                assert_eq!(args.len(), 2);
                assert!(matches!(
                    &args[0],
                    Sumti::Description {
                        gadri: Gadri::Lo,
                        ..
                    }
                ));
                assert!(matches!(
                    &args[1],
                    Sumti::Description {
                        gadri: Gadri::Lo,
                        ..
                    }
                ));
            }
            other => panic!("expected WithArgs with 2 descriptions, got {:?}", other),
        }
    }

    #[test]
    fn test_connective_with_conversion() {
        // barda je se prami
        let r = parse_ok(&[gismu("barda"), cmavo("je"), cmavo("se"), gismu("prami")]);
        match &as_bridi(&r.sentences[0]).selbri {
            Selbri::Connected { right, .. } => {
                assert!(matches!(
                    right.as_ref(),
                    Selbri::Converted(Conversion::Se, _)
                ));
            }
            other => panic!("expected Connected with Converted right, got {:?}", other),
        }
    }

    #[test]
    fn test_existential_and_universal_same_sentence() {
        // lo gerku cu nelci ro lo mlatu
        let r = parse_ok(&[
            cmavo("lo"),
            gismu("gerku"),
            cmavo("cu"),
            gismu("nelci"),
            cmavo("ro"),
            cmavo("lo"),
            gismu("mlatu"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description {
                gadri: Gadri::Lo, ..
            } => {}
            other => panic!("expected Lo head, got {:?}", other),
        }
        match &s.tail_terms[0] {
            Sumti::Description {
                gadri: Gadri::RoLo, ..
            } => {}
            other => panic!("expected RoLo tail, got {:?}", other),
        }
    }

    #[test]
    fn test_name_with_connective_selbri() {
        // la .bob. cu barda je sutra
        let r = parse_ok(&[
            cmavo("la"),
            pause(),
            cmevla("bob"),
            pause(),
            cmavo("cu"),
            gismu("barda"),
            cmavo("je"),
            gismu("sutra"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert!(matches!(&s.head_terms[0], Sumti::Name(n) if n == "bob"));
        assert!(matches!(
            &s.selbri,
            Selbri::Connected {
                connective: Connective::Je,
                ..
            }
        ));
    }

    // ═══════════════════════════════════════════════════════════
    // 18. ERROR CONDITIONS
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_empty_input() {
        let e = parse_err(&[]);
        assert!(e.contains("empty"));
    }

    #[test]
    fn test_unconsumed_tokens() {
        // mi klama ku'o — ku'o has no matching poi/noi
        let e = parse_err(&[cmavo("mi"), gismu("klama"), cmavo("ku'o")]);
        assert!(e.contains("unconsumed"));
    }

    #[test]
    fn test_pause_only() {
        let e = parse_err(&[pause()]);
        assert!(e.contains("empty") || e.contains("expected"));
    }

    #[test]
    fn test_connective_without_right_operand() {
        // barda je — missing right selbri
        let e = parse_err(&[gismu("barda"), cmavo("je")]);
        assert!(e.contains("expected") || e.contains("connective"));
    }

    // ═══════════════════════════════════════════════════════════
    // 19. TENSE MARKERS (pu/ca/ba)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_tense_mid_sentence() {
        // mi pu klama — tense between head terms and selbri
        let r = parse_ok(&[cmavo("mi"), cmavo("pu"), gismu("klama")]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.tense, Some(Tense::Pu));
        assert_eq!(s.selbri, Selbri::Root("klama".into()));
        assert_eq!(s.head_terms.len(), 1);
    }

    #[test]
    fn test_tense_after_cu() {
        // mi cu pu klama — tense after cu
        let r = parse_ok(&[cmavo("mi"), cmavo("cu"), cmavo("pu"), gismu("klama")]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.tense, Some(Tense::Pu));
    }

    #[test]
    fn test_tense_sentence_initial() {
        // pu mi klama — tense at start of sentence
        let r = parse_ok(&[cmavo("pu"), cmavo("mi"), gismu("klama")]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.tense, Some(Tense::Pu));
        assert_eq!(s.selbri, Selbri::Root("klama".into()));
        assert_eq!(s.head_terms.len(), 1);
        assert_eq!(s.head_terms[0], Sumti::ProSumti("mi".into()));
    }

    #[test]
    fn test_tense_ca_present() {
        let r = parse_ok(&[cmavo("ca"), cmavo("mi"), gismu("klama")]);
        assert_eq!(as_bridi(&r.sentences[0]).tense, Some(Tense::Ca));
    }

    #[test]
    fn test_tense_ba_future() {
        let r = parse_ok(&[cmavo("ba"), cmavo("do"), gismu("prami"), cmavo("mi")]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.tense, Some(Tense::Ba));
        assert_eq!(s.head_terms[0], Sumti::ProSumti("do".into()));
        assert_eq!(s.tail_terms[0], Sumti::ProSumti("mi".into()));
    }

    #[test]
    fn test_tense_initial_selbri_only() {
        // pu klama — tense + selbri, no terms
        let r = parse_ok(&[cmavo("pu"), gismu("klama")]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.tense, Some(Tense::Pu));
        assert_eq!(s.selbri, Selbri::Root("klama".into()));
        assert!(s.head_terms.is_empty());
    }

    #[test]
    fn test_tense_with_negation() {
        // pu mi na klama — past tense + negation
        let r = parse_ok(&[cmavo("pu"), cmavo("mi"), cmavo("na"), gismu("klama")]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.tense, Some(Tense::Pu));
        assert!(s.negated);
    }

    #[test]
    fn test_no_tense() {
        // mi klama — no tense marker
        let r = parse_ok(&[cmavo("mi"), gismu("klama")]);
        assert_eq!(as_bridi(&r.sentences[0]).tense, None);
    }

    // ═══════════════════════════════════════════════════════════
    // 20. KE'A (relative clause pronoun)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_kea_in_relative_clause() {
        // lo gerku poi mi nelci ke'a ku'o cu barda
        // ke'a as explicit bound variable in relative clause tail
        let r = parse_ok(&[
            cmavo("lo"),
            gismu("gerku"),
            cmavo("poi"),
            cmavo("mi"),
            gismu("nelci"),
            cmavo("ke'a"),
            cmavo("ku'o"),
            cmavo("cu"),
            gismu("barda"),
        ]);
        let bridi = as_bridi(&r.sentences[0]);
        assert_eq!(bridi.selbri, Selbri::Root("barda".into()));
        match &bridi.head_terms[0] {
            Sumti::Restricted { clause, .. } => {
                let body_bridi = as_bridi(&clause.body);
                assert_eq!(body_bridi.tail_terms.len(), 1);
                assert_eq!(body_bridi.tail_terms[0], Sumti::ProSumti("ke'a".into()));
            }
            other => panic!("expected Restricted with ke'a, got {:?}", other),
        }
    }

    #[test]
    fn test_kea_as_head_term() {
        // lo prenu poi ke'a nelci lo mlatu ku'o cu barda
        // ke'a as explicit bound variable in relative clause head
        let r = parse_ok(&[
            cmavo("lo"),
            gismu("prenu"),
            cmavo("poi"),
            cmavo("ke'a"),
            gismu("nelci"),
            cmavo("lo"),
            gismu("mlatu"),
            cmavo("ku'o"),
            cmavo("cu"),
            gismu("barda"),
        ]);
        let bridi = as_bridi(&r.sentences[0]);
        assert_eq!(bridi.selbri, Selbri::Root("barda".into()));
        match &bridi.head_terms[0] {
            Sumti::Restricted { clause, .. } => {
                let body_bridi = match &*clause.body {
                    Sentence::Simple(b) => b,
                    _ => panic!("expected simple bridi"),
                };
                assert_eq!(body_bridi.head_terms[0], Sumti::ProSumti("ke'a".into()));
            }
            other => panic!("expected Restricted with ke'a head, got {:?}", other),
        }
    }

    // ═══════════════════════════════════════════════════════════
    // 21. SUMTI CONNECTIVES (.e/.a/.o/.u + nai)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_sumti_connective_e() {
        // mi .e do klama → head:[Connected(mi, Je, do)], selbri:klama
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("e"),
            cmavo("do"),
            gismu("klama"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Connected {
                left,
                connective,
                right_negated,
                right,
            } => {
                assert_eq!(**left, Sumti::ProSumti("mi".into()));
                assert_eq!(*connective, Connective::Je);
                assert!(!right_negated);
                assert_eq!(**right, Sumti::ProSumti("do".into()));
            }
            other => panic!("expected Connected(.e), got {:?}", other),
        }
        assert_eq!(s.selbri, Selbri::Root("klama".into()));
    }

    #[test]
    fn test_sumti_connective_a() {
        // mi .a do klama
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("a"),
            cmavo("do"),
            gismu("klama"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Ja,
                ..
            } => {}
            other => panic!("expected Connected(.a), got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_o() {
        // mi .o do klama
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("o"),
            cmavo("do"),
            gismu("klama"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Jo,
                ..
            } => {}
            other => panic!("expected Connected(.o), got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_u() {
        // mi .u do klama
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("u"),
            cmavo("do"),
            gismu("klama"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Ju,
                ..
            } => {}
            other => panic!("expected Connected(.u), got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_enai() {
        // mi .e nai do klama → right_negated = true
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("e"),
            cmavo("nai"),
            cmavo("do"),
            gismu("klama"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Je,
                right_negated: true,
                ..
            } => {}
            other => panic!("expected Connected(.enai), got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_anai() {
        // mi .a nai do klama
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("a"),
            cmavo("nai"),
            cmavo("do"),
            gismu("klama"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Ja,
                right_negated: true,
                ..
            } => {}
            other => panic!("expected Connected(.anai), got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_with_descriptions() {
        // lo gerku .e lo mlatu cu barda
        let r = parse_ok(&[
            cmavo("lo"),
            gismu("gerku"),
            pause(),
            cmavo("e"),
            cmavo("lo"),
            gismu("mlatu"),
            cmavo("cu"),
            gismu("barda"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Connected {
                left,
                connective: Connective::Je,
                right,
                ..
            } => {
                assert!(matches!(left.as_ref(), Sumti::Description { gadri: Gadri::Lo, .. }));
                assert!(matches!(right.as_ref(), Sumti::Description { gadri: Gadri::Lo, .. }));
            }
            other => panic!("expected Connected descriptions, got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_in_tail() {
        // mi nelci lo gerku .e lo mlatu
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("nelci"),
            cmavo("lo"),
            gismu("gerku"),
            pause(),
            cmavo("e"),
            cmavo("lo"),
            gismu("mlatu"),
        ]);
        match &as_bridi(&r.sentences[0]).tail_terms[0] {
            Sumti::Connected {
                connective: Connective::Je,
                ..
            } => {}
            other => panic!("expected Connected in tail, got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_does_not_eat_dot_i() {
        // mi klama .i do prami — .i is NOT a sumti connective
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("klama"),
            pause(),
            cmavo("i"),
            cmavo("do"),
            gismu("prami"),
        ]);
        assert_eq!(r.sentences.len(), 2);
    }

    #[test]
    fn test_sumti_connective_onai() {
        // mi .o nai do klama → right_negated = true, connective = Jo
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("o"),
            cmavo("nai"),
            cmavo("do"),
            gismu("klama"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Jo,
                right_negated: true,
                ..
            } => {}
            other => panic!("expected Connected(.onai), got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_unai() {
        // mi .u nai do klama → right_negated = true, connective = Ju
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("u"),
            cmavo("nai"),
            cmavo("do"),
            gismu("klama"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Ju,
                right_negated: true,
                ..
            } => {}
            other => panic!("expected Connected(.unai), got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_chained() {
        // mi .e do .e di klama → right-associative (recursive try_parse_sumti):
        //   Connected(mi, Je, Connected(do, Je, di))
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("e"),
            cmavo("do"),
            pause(),
            cmavo("e"),
            cmavo("di"),
            gismu("klama"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Connected {
                left,
                connective: Connective::Je,
                right_negated: false,
                right,
            } => {
                // Left is mi
                assert_eq!(**left, Sumti::ProSumti("mi".into()));
                // Right is Connected(do, Je, di)
                match right.as_ref() {
                    Sumti::Connected {
                        left: inner_left,
                        connective: Connective::Je,
                        right_negated: false,
                        right: inner_right,
                    } => {
                        assert_eq!(**inner_left, Sumti::ProSumti("do".into()));
                        assert_eq!(**inner_right, Sumti::ProSumti("di".into()));
                    }
                    other => panic!("expected inner Connected, got {:?}", other),
                }
            }
            other => panic!("expected outer Connected, got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_with_cu() {
        // mi .e do cu klama → Connected in head, selbri after cu
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("e"),
            cmavo("do"),
            cmavo("cu"),
            gismu("klama"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert!(matches!(&s.head_terms[0], Sumti::Connected { .. }));
        assert_eq!(s.selbri, Selbri::Root("klama".into()));
    }

    #[test]
    fn test_sumti_connective_with_names() {
        // la .djan. .e la .meris. cu klama
        let r = parse_ok(&[
            cmavo("la"),
            pause(),
            cmevla("djan"),
            pause(),
            pause(),
            cmavo("e"),
            cmavo("la"),
            pause(),
            cmevla("meris"),
            pause(),
            cmavo("cu"),
            gismu("klama"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Connected {
                left,
                connective: Connective::Je,
                right,
                ..
            } => {
                assert!(matches!(left.as_ref(), Sumti::Name(_)));
                assert!(matches!(right.as_ref(), Sumti::Name(_)));
            }
            other => panic!("expected Connected names, got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_with_place_tags() {
        // fe mi .e do fa lo gerku cu klama
        // fe applies to the entire Connected sumti
        let r = parse_ok(&[
            cmavo("fe"),
            cmavo("mi"),
            pause(),
            cmavo("e"),
            cmavo("do"),
            cmavo("fa"),
            cmavo("lo"),
            gismu("gerku"),
            cmavo("cu"),
            gismu("klama"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        // First head term: fe (mi .e do) — Tagged wraps Connected
        match &s.head_terms[0] {
            Sumti::Tagged(PlaceTag::Fe, inner) => {
                assert!(matches!(inner.as_ref(), Sumti::Connected { .. }));
            }
            other => panic!("expected Tagged(Fe, Connected), got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_with_se_conversion() {
        // mi .e do se prami lo gerku → Connected in head, se conversion selbri
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("e"),
            cmavo("do"),
            cmavo("se"),
            gismu("prami"),
            cmavo("lo"),
            gismu("gerku"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert!(matches!(&s.head_terms[0], Sumti::Connected { .. }));
        assert!(matches!(&s.selbri, Selbri::Converted(Conversion::Se, _)));
    }

    #[test]
    fn test_sumti_connective_mixed_types() {
        // mi .a lo gerku ku klama → Connected(ProSumti, Ja, Description)
        // ku terminates the description so klama becomes the selbri
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("a"),
            cmavo("lo"),
            gismu("gerku"),
            cmavo("ku"),
            gismu("klama"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Connected {
                left,
                connective: Connective::Ja,
                right,
                ..
            } => {
                assert!(matches!(left.as_ref(), Sumti::ProSumti(_)));
                assert!(matches!(right.as_ref(), Sumti::Description { .. }));
            }
            other => panic!("expected Connected(ProSumti, Ja, Description), got {:?}", other),
        }
        assert_eq!(s.selbri, Selbri::Root("klama".into()));
    }

    #[test]
    fn test_sumti_connective_both_head_and_tail() {
        // mi .e do prami lo gerku .a lo mlatu
        // head: Connected(mi, Je, do), tail: Connected(lo gerku, Ja, lo mlatu)
        let r = parse_ok(&[
            cmavo("mi"),
            pause(),
            cmavo("e"),
            cmavo("do"),
            gismu("prami"),
            cmavo("lo"),
            gismu("gerku"),
            pause(),
            cmavo("a"),
            cmavo("lo"),
            gismu("mlatu"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert!(matches!(&s.head_terms[0], Sumti::Connected { connective: Connective::Je, .. }));
        assert!(matches!(&s.tail_terms[0], Sumti::Connected { connective: Connective::Ja, .. }));
    }

    // ─── §22 Abstraction types (du'u, ka, ni, si'o) ─────────────────────

    #[test]
    fn test_duhu_abstraction_parses() {
        // lo du'u mi klama kei cu barda
        let s = parse_ok(&[
            cmavo("lo"), cmavo("du'u"), cmavo("mi"), gismu("klama"), cmavo("kei"),
            cmavo("cu"), gismu("barda"),
        ]);
        let bridi = as_bridi(&s.sentences[0]);
        assert_eq!(bridi.selbri, Selbri::Root("barda".into()));
        match &bridi.head_terms[0] {
            Sumti::Description { gadri: Gadri::Lo, inner } => {
                match inner.as_ref() {
                    Selbri::Abstraction(AbstractionKind::Duhu, _) => {}
                    other => panic!("expected Abstraction(Duhu, ..), got {:?}", other),
                }
            }
            other => panic!("expected Description, got {:?}", other),
        }
    }

    #[test]
    fn test_ka_abstraction_parses() {
        // lo ka ce'u melbi kei cu barda
        let s = parse_ok(&[
            cmavo("lo"), cmavo("ka"), cmavo("ce'u"), gismu("melbi"), cmavo("kei"),
            cmavo("cu"), gismu("barda"),
        ]);
        let bridi = as_bridi(&s.sentences[0]);
        match &bridi.head_terms[0] {
            Sumti::Description { inner, .. } => {
                match inner.as_ref() {
                    Selbri::Abstraction(AbstractionKind::Ka, body) => {
                        // The inner sentence should have ce'u as head term
                        match body.as_ref() {
                            Sentence::Simple(inner_bridi) => {
                                assert_eq!(inner_bridi.head_terms[0], Sumti::ProSumti("ce'u".into()));
                            }
                            other => panic!("expected Simple sentence, got {:?}", other),
                        }
                    }
                    other => panic!("expected Abstraction(Ka, ..), got {:?}", other),
                }
            }
            other => panic!("expected Description, got {:?}", other),
        }
    }

    #[test]
    fn test_ka_without_ceu_parses() {
        // lo ka melbi kei cu barda
        let s = parse_ok(&[
            cmavo("lo"), cmavo("ka"), gismu("melbi"), cmavo("kei"),
            cmavo("cu"), gismu("barda"),
        ]);
        let bridi = as_bridi(&s.sentences[0]);
        match &bridi.head_terms[0] {
            Sumti::Description { inner, .. } => {
                match inner.as_ref() {
                    Selbri::Abstraction(AbstractionKind::Ka, _) => {}
                    other => panic!("expected Abstraction(Ka, ..), got {:?}", other),
                }
            }
            other => panic!("expected Description, got {:?}", other),
        }
    }

    #[test]
    fn test_ni_abstraction_parses() {
        // lo ni mi gleki kei cu barda
        let s = parse_ok(&[
            cmavo("lo"), cmavo("ni"), cmavo("mi"), gismu("gleki"), cmavo("kei"),
            cmavo("cu"), gismu("barda"),
        ]);
        let bridi = as_bridi(&s.sentences[0]);
        match &bridi.head_terms[0] {
            Sumti::Description { inner, .. } => {
                match inner.as_ref() {
                    Selbri::Abstraction(AbstractionKind::Ni, _) => {}
                    other => panic!("expected Abstraction(Ni, ..), got {:?}", other),
                }
            }
            other => panic!("expected Description, got {:?}", other),
        }
    }

    #[test]
    fn test_siho_abstraction_parses() {
        // lo si'o mi klama kei cu barda
        let s = parse_ok(&[
            cmavo("lo"), cmavo("si'o"), cmavo("mi"), gismu("klama"), cmavo("kei"),
            cmavo("cu"), gismu("barda"),
        ]);
        let bridi = as_bridi(&s.sentences[0]);
        match &bridi.head_terms[0] {
            Sumti::Description { inner, .. } => {
                match inner.as_ref() {
                    Selbri::Abstraction(AbstractionKind::Siho, _) => {}
                    other => panic!("expected Abstraction(Siho, ..), got {:?}", other),
                }
            }
            other => panic!("expected Description, got {:?}", other),
        }
    }

    #[test]
    fn test_nu_still_parses_with_kind() {
        // lo nu mi klama kei cu barda — ensure existing nu still works
        let s = parse_ok(&[
            cmavo("lo"), cmavo("nu"), cmavo("mi"), gismu("klama"), cmavo("kei"),
            cmavo("cu"), gismu("barda"),
        ]);
        let bridi = as_bridi(&s.sentences[0]);
        match &bridi.head_terms[0] {
            Sumti::Description { inner, .. } => {
                match inner.as_ref() {
                    Selbri::Abstraction(AbstractionKind::Nu, _) => {}
                    other => panic!("expected Abstraction(Nu, ..), got {:?}", other),
                }
            }
            other => panic!("expected Description, got {:?}", other),
        }
    }

    #[test]
    fn test_ceu_as_pro_sumti() {
        // ce'u melbi → head: [ProSumti("ce'u")], selbri: melbi
        let s = parse_ok(&[cmavo("ce'u"), gismu("melbi")]);
        let bridi = as_bridi(&s.sentences[0]);
        assert_eq!(bridi.head_terms[0], Sumti::ProSumti("ce'u".into()));
    }

    #[test]
    fn test_abstraction_without_kei() {
        // lo du'u mi klama cu barda — kei is optional
        let s = parse_ok(&[
            cmavo("lo"), cmavo("du'u"), cmavo("mi"), gismu("klama"),
            cmavo("cu"), gismu("barda"),
        ]);
        let bridi = as_bridi(&s.sentences[0]);
        // With optional kei, the inner sentence is "mi klama" and cu+barda is outer
        assert_eq!(bridi.selbri, Selbri::Root("barda".into()));
    }

    #[test]
    fn test_nested_abstractions() {
        // lo nu lo ka ce'u melbi kei cu barda kei cu xamgu
        // outer: nu(ka(ce'u melbi) cu barda), selbri: xamgu
        let s = parse_ok(&[
            cmavo("lo"), cmavo("nu"),
            cmavo("lo"), cmavo("ka"), cmavo("ce'u"), gismu("melbi"), cmavo("kei"),
            cmavo("cu"), gismu("barda"),
            cmavo("kei"),
            cmavo("cu"), gismu("xamgu"),
        ]);
        let bridi = as_bridi(&s.sentences[0]);
        assert_eq!(bridi.selbri, Selbri::Root("xamgu".into()));
        match &bridi.head_terms[0] {
            Sumti::Description { inner, .. } => {
                match inner.as_ref() {
                    Selbri::Abstraction(AbstractionKind::Nu, inner_sentence) => {
                        // Inner: lo ka ce'u melbi cu barda
                        match inner_sentence.as_ref() {
                            Sentence::Simple(inner_bridi) => {
                                assert_eq!(inner_bridi.selbri, Selbri::Root("barda".into()));
                            }
                            other => panic!("expected Simple inner, got {:?}", other),
                        }
                    }
                    other => panic!("expected Abstraction(Nu), got {:?}", other),
                }
            }
            other => panic!("expected Description, got {:?}", other),
        }
    }

    #[test]
    fn test_sumti_connective_at_end_errors() {
        // mi klama .e → trailing .e with nothing after it
        // The parser backtracks the connective but can't consume the
        // remaining Pause+Cmavo tokens → "unconsumed tokens" error
        let err = parse_err(&[
            cmavo("mi"),
            gismu("klama"),
            pause(),
            cmavo("e"),
        ]);
        assert!(err.contains("unconsumed"), "expected unconsumed error, got: {}", err);
    }

    #[test]
    fn test_sumti_connective_trailing_in_tail_errors() {
        // mi klama .e do prami → after "mi klama", the tail position sees
        // Pause(".") which is not a valid bare sumti start, so the .e is not
        // consumed, resulting in "unconsumed tokens" error
        let err = parse_err(&[
            cmavo("mi"),
            gismu("klama"),
            pause(),
            cmavo("e"),
            cmavo("do"),
            gismu("prami"),
        ]);
        assert!(err.contains("unconsumed"), "expected unconsumed error, got: {}", err);
    }

    // ═══════════════════════════════════════════════════════════
    // BAI MODAL TAGS
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_bai_tag_ria() {
        // ri'a lo nu brife → ModalTagged(Fixed(Ria), Description(Lo, "brife"))
        let r = parse_ok(&[
            gismu("klama"),
            cmavo("ri'a"),
            cmavo("lo"),
            cmavo("nu"),
            gismu("brife"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.tail_terms.len(), 1);
        match &s.tail_terms[0] {
            Sumti::ModalTagged(ModalTag::Fixed(BaiTag::Ria), inner) => {
                assert!(matches!(inner.as_ref(), Sumti::Description { .. }));
            }
            other => panic!("expected ModalTagged(Ria, Description), got {:?}", other),
        }
    }

    #[test]
    fn test_bai_in_tail_terms() {
        // mi klama ri'a lo nu brife → head:[mi], tail:[ModalTagged(Ria, ...)]
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("klama"),
            cmavo("ri'a"),
            cmavo("lo"),
            cmavo("nu"),
            gismu("brife"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.head_terms.len(), 1);
        assert_eq!(s.tail_terms.len(), 1);
        assert!(matches!(
            &s.tail_terms[0],
            Sumti::ModalTagged(ModalTag::Fixed(BaiTag::Ria), _)
        ));
    }

    #[test]
    fn test_bai_all_six() {
        // Test each BAI tag parses correctly
        for (cmavo_str, expected_tag) in [
            ("ri'a", BaiTag::Ria),
            ("ni'i", BaiTag::Nii),
            ("mu'i", BaiTag::Mui),
            ("ki'u", BaiTag::Kiu),
            ("pi'o", BaiTag::Pio),
            ("ba'i", BaiTag::Bai),
        ] {
            let r = parse_ok(&[gismu("klama"), cmavo(cmavo_str), cmavo("mi")]);
            let s = as_bridi(&r.sentences[0]);
            match &s.tail_terms[0] {
                Sumti::ModalTagged(ModalTag::Fixed(tag), inner) => {
                    assert_eq!(*tag, expected_tag, "BAI mismatch for {}", cmavo_str);
                    assert_eq!(**inner, Sumti::ProSumti("mi".into()));
                }
                other => panic!("expected ModalTagged for {}, got {:?}", cmavo_str, other),
            }
        }
    }

    #[test]
    fn test_fio_with_selbri() {
        // fi'o klama fe'u mi → ModalTagged(Fio(Root("klama")), ProSumti("mi"))
        let r = parse_ok(&[
            gismu("barda"),
            cmavo("fi'o"),
            gismu("klama"),
            cmavo("fe'u"),
            cmavo("mi"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.tail_terms.len(), 1);
        match &s.tail_terms[0] {
            Sumti::ModalTagged(ModalTag::Fio(selbri), inner) => {
                assert_eq!(**selbri, Selbri::Root("klama".into()));
                assert_eq!(**inner, Sumti::ProSumti("mi".into()));
            }
            other => panic!("expected ModalTagged(Fio(klama), mi), got {:?}", other),
        }
    }

    #[test]
    fn test_fio_without_feu() {
        // fi'o klama mi → ModalTagged(Fio(Root("klama")), ProSumti("mi"))
        let r = parse_ok(&[
            gismu("barda"),
            cmavo("fi'o"),
            gismu("klama"),
            cmavo("mi"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.tail_terms.len(), 1);
        match &s.tail_terms[0] {
            Sumti::ModalTagged(ModalTag::Fio(selbri), inner) => {
                assert_eq!(**selbri, Selbri::Root("klama".into()));
                assert_eq!(**inner, Sumti::ProSumti("mi".into()));
            }
            other => panic!("expected ModalTagged(Fio(klama), mi), got {:?}", other),
        }
    }

    #[test]
    fn test_bai_with_place_tags() {
        // fa mi klama ri'a lo nu brife — mix of place and modal tags
        let r = parse_ok(&[
            cmavo("fa"),
            cmavo("mi"),
            gismu("klama"),
            cmavo("ri'a"),
            cmavo("lo"),
            cmavo("nu"),
            gismu("brife"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.head_terms.len(), 1);
        assert!(matches!(
            &s.head_terms[0],
            Sumti::Tagged(PlaceTag::Fa, _)
        ));
        assert_eq!(s.tail_terms.len(), 1);
        assert!(matches!(
            &s.tail_terms[0],
            Sumti::ModalTagged(ModalTag::Fixed(BaiTag::Ria), _)
        ));
    }

    #[test]
    fn test_multiple_bai_tags() {
        // mi klama ri'a do pi'o lo tanxe — two BAI tags
        let r = parse_ok(&[
            cmavo("mi"),
            gismu("klama"),
            cmavo("ri'a"),
            cmavo("do"),
            cmavo("pi'o"),
            cmavo("lo"),
            gismu("tanxe"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        assert_eq!(s.tail_terms.len(), 2);
        assert!(matches!(
            &s.tail_terms[0],
            Sumti::ModalTagged(ModalTag::Fixed(BaiTag::Ria), _)
        ));
        assert!(matches!(
            &s.tail_terms[1],
            Sumti::ModalTagged(ModalTag::Fixed(BaiTag::Pio), _)
        ));
    }

    #[test]
    fn test_bai_tag_backtrack_at_end() {
        // klama ri'a — ri'a with no following sumti should error
        let e = parse_err(&[gismu("klama"), cmavo("ri'a")]);
        assert!(e.contains("unconsumed") || e.len() > 0);
    }

    // ═══════════════════════════════════════════════════════════
    // NUMERIC QUANTIFIERS (PA lo/le)
    // ═══════════════════════════════════════════════════════════

    #[test]
    fn test_re_lo_description() {
        // re lo gerku cu barda → QuantifiedDescription { count: 2, Lo, gerku }
        let r = parse_ok(&[
            cmavo("re"), cmavo("lo"), gismu("gerku"), cmavo("cu"), gismu("barda"),
        ]);
        let s = as_bridi(&r.sentences[0]);
        match &s.head_terms[0] {
            Sumti::QuantifiedDescription { count, gadri, inner } => {
                assert_eq!(*count, 2);
                assert_eq!(*gadri, Gadri::Lo);
                assert_eq!(**inner, Selbri::Root("gerku".into()));
            }
            other => panic!("expected QuantifiedDescription, got {:?}", other),
        }
        assert_eq!(s.selbri, Selbri::Root("barda".into()));
    }

    #[test]
    fn test_ci_lo_description() {
        // ci lo mlatu cu barda → count: 3
        let r = parse_ok(&[
            cmavo("ci"), cmavo("lo"), gismu("mlatu"), cmavo("cu"), gismu("barda"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::QuantifiedDescription { count, .. } => assert_eq!(*count, 3),
            other => panic!("expected QuantifiedDescription, got {:?}", other),
        }
    }

    #[test]
    fn test_no_lo_description() {
        // no lo gerku cu barda → count: 0
        let r = parse_ok(&[
            cmavo("no"), cmavo("lo"), gismu("gerku"), cmavo("cu"), gismu("barda"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::QuantifiedDescription { count, .. } => assert_eq!(*count, 0),
            other => panic!("expected QuantifiedDescription, got {:?}", other),
        }
    }

    #[test]
    fn test_pa_lo_description() {
        // pa lo gerku cu barda → count: 1
        let r = parse_ok(&[
            cmavo("pa"), cmavo("lo"), gismu("gerku"), cmavo("cu"), gismu("barda"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::QuantifiedDescription { count, .. } => assert_eq!(*count, 1),
            other => panic!("expected QuantifiedDescription, got {:?}", other),
        }
    }

    #[test]
    fn test_multi_digit_pa_no() {
        // pa no lo gerku cu barda → count: 10
        let r = parse_ok(&[
            cmavo("pa"), cmavo("no"), cmavo("lo"), gismu("gerku"), cmavo("cu"), gismu("barda"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::QuantifiedDescription { count, .. } => assert_eq!(*count, 10),
            other => panic!("expected QuantifiedDescription with count 10, got {:?}", other),
        }
    }

    #[test]
    fn test_suho_lo_is_plain_existential() {
        // su'o lo gerku cu barda → plain Description(Lo) (existential)
        let r = parse_ok(&[
            cmavo("su'o"), cmavo("lo"), gismu("gerku"), cmavo("cu"), gismu("barda"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Description { gadri: Gadri::Lo, inner } => {
                assert_eq!(**inner, Selbri::Root("gerku".into()));
            }
            other => panic!("expected plain Description(Lo), got {:?}", other),
        }
    }

    #[test]
    fn test_ro_lo_still_universal() {
        // Regression: ro lo gerku cu barda → RoLo (not affected by new code)
        let r = parse_ok(&[
            cmavo("ro"), cmavo("lo"), gismu("gerku"), cmavo("cu"), gismu("barda"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::Description { gadri: Gadri::RoLo, .. } => {}
            other => panic!("expected Description(RoLo), got {:?}", other),
        }
    }

    #[test]
    fn test_re_le_description() {
        // re le gerku cu barda → QuantifiedDescription with Le gadri
        let r = parse_ok(&[
            cmavo("re"), cmavo("le"), gismu("gerku"), cmavo("cu"), gismu("barda"),
        ]);
        match &as_bridi(&r.sentences[0]).head_terms[0] {
            Sumti::QuantifiedDescription { count, gadri, .. } => {
                assert_eq!(*count, 2);
                assert_eq!(*gadri, Gadri::Le);
            }
            other => panic!("expected QuantifiedDescription(Le), got {:?}", other),
        }
    }
}
