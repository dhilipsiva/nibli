// parser/src/grammar.rs — Recursive descent parser for Lojban
//
// Operates on the preprocessed NormalizedToken stream.
// Grammar (subset of CLL, expanded incrementally):
//
//   text        → sentence (.i sentence)*
//   sentence    → terms? cu? selbri tail? vau?
//   tail        → terms
//   terms       → term+
//   term        → place_tag? sumti
//   sumti       → la_name | description | pro_sumti | quoted
//                | sumti rel_clause
//   la_name     → la cmevla+
//   description → (lo|le) selbri ku?
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
    /// Lojban `.i` is lexed as two tokens: Pause(".") + Cmavo("i").
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

    /// Consume a `.i` sentence separator if present. Returns true if consumed.
    fn eat_dot_i(&mut self) -> bool {
        if self.at_dot_i() {
            self.pos += 2; // consume both Pause and Cmavo("i")
            true
        } else {
            false
        }
    }

    /// Check if current token is a sentence boundary (for rel clause scoping).
    fn at_sentence_boundary(&self) -> bool {
        if self.at_end() {
            return true;
        }
        if self.at_dot_i() {
            return true;
        }
        self.peek_is_any_cmavo(&["ku'o", "kei", "vau"])
    }

    // ─── Top-level entry point ────────────────────────────────

    /// Parse a complete text: sentence (.i sentence)*
    pub fn parse_text(&mut self) -> Result<ParsedText, ParseError> {
        let mut sentences = Vec::new();

        // Skip leading .i separators and pauses
        while self.eat_dot_i() || self.eat_pause() {}

        if self.at_end() {
            return Err(self.error("empty input"));
        }

        // Parse first sentence
        sentences.push(self.parse_sentence()?);

        // Parse subsequent .i-separated sentences
        loop {
            if !self.eat_dot_i() {
                while self.eat_pause() {}
                if !self.eat_dot_i() {
                    break;
                }
            }

            while self.eat_pause() {}

            if self.at_end() {
                break; // trailing .i is fine
            }

            if self.at_dot_i() {
                continue; // doubled .i, skip
            }

            sentences.push(self.parse_sentence()?);
        }

        // Skip trailing pauses
        while self.eat_pause() {}

        // ── FIX #5: Detect unconsumed tokens ──
        if !self.at_end() {
            let remaining = self.tokens.len() - self.pos;
            let next_desc = match self.peek() {
                Some(NormalizedToken::Standard(kind, text)) => {
                    format!("{:?}(\"{}\")", kind, text)
                }
                Some(NormalizedToken::Quoted(text)) => format!("Quoted(\"{}\")", text),
                Some(NormalizedToken::Glued(parts)) => format!("Glued({:?})", parts),
                None => "???".to_string(),
            };
            return Err(ParseError {
                message: format!(
                    "{} unconsumed token(s) starting with {} at position {}",
                    remaining, next_desc, self.pos
                ),
                position: self.pos,
            });
        }

        Ok(ParsedText { sentences })
    }

    // ─── Sentence ─────────────────────────────────────────────

    /// sentence → terms? cu? selbri tail? vau?
    fn parse_sentence(&mut self) -> Result<Bridi, ParseError> {
        self.enter()?;

        let head_terms = self.parse_terms();

        // cu separator (optional)
        self.eat_cmavo("cu");

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

        // Optional vau terminator
        self.eat_cmavo("vau");

        self.leave();
        Ok(Bridi {
            selbri,
            head_terms,
            tail_terms,
            negated,
        })
    }

    fn looks_like_selbri_na(&self) -> bool {
        if self.pos + 1 >= self.tokens.len() {
            return false;
        }
        match &self.tokens[self.pos + 1] {
            NormalizedToken::Standard(LojbanToken::Gismu, _) => true,
            NormalizedToken::Standard(LojbanToken::Cmavo, s) => {
                matches!(*s, "se" | "te" | "ve" | "xe" | "ke" | "na" | "nu")
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

    /// term → place_tag? sumti
    fn try_parse_term(&mut self) -> Option<Sumti> {
        // ── FIX #1: Save before consuming place tag ──
        let saved = self.save();

        if let Some(tag) = self.try_parse_place_tag() {
            if let Some(sumti) = self.try_parse_sumti() {
                return Some(Sumti::Tagged(tag, Box::new(sumti)));
            }
            // Tag consumed but no sumti — restore
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

    // ─── Sumti ────────────────────────────────────────────────

    fn try_parse_sumti(&mut self) -> Option<Sumti> {
        let mut sumti = self.try_parse_bare_sumti()?;

        while let Some(clause) = self.try_parse_rel_clause() {
            sumti = Sumti::Restricted {
                inner: Box::new(sumti),
                clause,
            };
        }

        Some(sumti)
    }

    fn try_parse_bare_sumti(&mut self) -> Option<Sumti> {
        if self.peek_is_cmavo("la") {
            return self.try_parse_la_name();
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

        None
    }

    /// la + cmevla+
    fn try_parse_la_name(&mut self) -> Option<Sumti> {
        if !self.peek_is_cmavo("la") {
            return None;
        }

        // ── FIX #2: Save before consuming `la` ──
        let saved = self.save();
        self.pos += 1; // consume la

        self.eat_pause();

        let mut name_parts = Vec::new();
        while self.peek_is_cmevla() {
            if let Some(NormalizedToken::Standard(_, s)) = self.advance() {
                name_parts.push(s.to_string());
            }
            self.eat_pause();
        }

        if name_parts.is_empty() {
            // la + selbri variant
            if let Some(selbri) = self.try_parse_selbri_for_description() {
                self.eat_cmavo("ku");
                return Some(Sumti::Description {
                    gadri: Gadri::La,
                    inner: Box::new(selbri),
                });
            }
            // Total failure — restore
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

        // ── FIX #3: Save before consuming gadri ──
        let saved = self.save();
        self.pos += 1; // consume gadri

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
            "ma" => Sumti::ProSumti(cmavo.to_string()),
            _ => return None,
        };

        self.pos += 1;
        Some(result)
    }

    /// rel_clause → (poi|noi) sentence ku'o?
    fn try_parse_rel_clause(&mut self) -> Option<RelClause> {
        let kind = match self.peek_cmavo()? {
            "poi" => RelClauseKind::Poi,
            "noi" => RelClauseKind::Noi,
            _ => return None,
        };

        // ── FIX #6: Save before consuming poi/noi ──
        let saved = self.save();
        self.pos += 1; // consume poi/noi

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
        // ── FIX: Save before conversion in case tanru fails ──
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
        // ke ... ke'e (explicit grouping)
        if self.peek_is_cmavo("ke") {
            // ── FIX #4: Depth guard on ke recursion ──
            if self.depth >= MAX_DEPTH {
                return None;
            }
            let saved = self.save();
            self.pos += 1; // consume ke

            self.depth += 1;
            let inner = self.try_parse_tanru();
            self.depth = self.depth.saturating_sub(1);

            match inner {
                Some(selbri) => {
                    self.eat_cmavo("ke'e");
                    return Some(Selbri::Grouped(Box::new(selbri)));
                }
                None => {
                    // Restore on failed ke-group
                    self.restore(saved);
                    return None;
                }
            }
        }

        // Gismu (root word)
        if self.peek_is_gismu() {
            if let Some(NormalizedToken::Standard(_, s)) = self.advance() {
                return Some(Selbri::Root(s.to_string()));
            }
        }

        // Glued compound (from zei preprocessing)
        if let Some(NormalizedToken::Glued(parts)) = self.peek() {
            let compound: Vec<String> = parts.iter().map(|s| s.to_string()).collect();
            self.pos += 1;
            return Some(Selbri::Compound(compound));
        }

        None
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
}

// ─── Public entry point ───────────────────────────────────────────

/// Parse a preprocessed token stream into a structured AST.
pub fn parse_tokens_to_ast(tokens: &[NormalizedToken<'_>]) -> Result<ParsedText, String> {
    let mut parser = Parser::new(tokens);
    parser.parse_text().map_err(|e| e.to_string())
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn std_tok(kind: LojbanToken, text: &str) -> NormalizedToken<'_> {
        NormalizedToken::Standard(kind, text)
    }

    fn cmavo(text: &'static str) -> NormalizedToken<'static> {
        std_tok(LojbanToken::Cmavo, text)
    }

    fn gismu(text: &'static str) -> NormalizedToken<'static> {
        std_tok(LojbanToken::Gismu, text)
    }

    fn pause() -> NormalizedToken<'static> {
        std_tok(LojbanToken::Pause, ".")
    }

    fn cmevla(text: &'static str) -> NormalizedToken<'static> {
        std_tok(LojbanToken::Cmevla, text)
    }

    // ─── Original regression tests ────────────────────────────

    #[test]
    fn test_simple_bridi() {
        let tokens = [cmavo("mi"), gismu("prami"), cmavo("do")];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        assert_eq!(result.sentences.len(), 1);
        let s = &result.sentences[0];
        assert_eq!(s.selbri, Selbri::Root("prami".into()));
        assert_eq!(s.head_terms.len(), 1);
        assert_eq!(s.tail_terms.len(), 1);
    }

    #[test]
    fn test_with_cu() {
        let tokens = [cmavo("mi"), cmavo("cu"), gismu("prami"), cmavo("do")];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        assert_eq!(s.selbri, Selbri::Root("prami".into()));
    }

    #[test]
    fn test_lo_description() {
        let tokens = [cmavo("mi"), gismu("nelci"), cmavo("lo"), gismu("gerku")];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        match &s.tail_terms[0] {
            Sumti::Description { gadri, inner } => {
                assert_eq!(*gadri, Gadri::Lo);
                assert_eq!(**inner, Selbri::Root("gerku".into()));
            }
            other => panic!("expected Description, got {:?}", other),
        }
    }

    #[test]
    fn test_multi_sentence() {
        let tokens = [
            cmavo("mi"),
            gismu("prami"),
            cmavo("do"),
            pause(),
            cmavo("i"),
            cmavo("do"),
            gismu("prami"),
            cmavo("mi"),
        ];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        assert_eq!(result.sentences.len(), 2);
    }

    #[test]
    fn test_negation() {
        let tokens = [cmavo("mi"), cmavo("na"), gismu("prami"), cmavo("do")];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        assert!(s.negated);
        assert_eq!(s.selbri, Selbri::Root("prami".into()));
    }

    #[test]
    fn test_place_tags() {
        let tokens = [
            cmavo("fa"),
            cmavo("mi"),
            cmavo("fe"),
            cmavo("do"),
            gismu("prami"),
        ];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        assert_eq!(s.head_terms.len(), 2);
        match &s.head_terms[0] {
            Sumti::Tagged(PlaceTag::Fa, inner) => {
                assert_eq!(**inner, Sumti::ProSumti("mi".into()));
            }
            other => panic!("expected Tagged(Fa, ...), got {:?}", other),
        }
    }

    #[test]
    fn test_se_conversion() {
        let tokens = [cmavo("do"), cmavo("se"), gismu("prami"), cmavo("mi")];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        match &s.selbri {
            Selbri::Converted(Conversion::Se, inner) => {
                assert_eq!(**inner, Selbri::Root("prami".into()));
            }
            other => panic!("expected Converted(Se, ...), got {:?}", other),
        }
    }

    #[test]
    fn test_tanru() {
        let tokens = [cmavo("mi"), gismu("sutra"), gismu("gerku")];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        match &s.selbri {
            Selbri::Tanru(modifier, head) => {
                assert_eq!(**modifier, Selbri::Root("sutra".into()));
                assert_eq!(**head, Selbri::Root("gerku".into()));
            }
            other => panic!("expected Tanru, got {:?}", other),
        }
    }

    #[test]
    fn test_be_clause() {
        let tokens = [
            cmavo("mi"),
            gismu("nelci"),
            cmavo("be"),
            cmavo("lo"),
            gismu("gerku"),
        ];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        match &s.selbri {
            Selbri::WithArgs { core, args } => {
                assert_eq!(**core, Selbri::Root("nelci".into()));
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected WithArgs, got {:?}", other),
        }
    }

    #[test]
    fn test_selbri_connective() {
        let tokens = [cmavo("mi"), gismu("barda"), cmavo("je"), gismu("xunre")];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        match &s.selbri {
            Selbri::Connected {
                left,
                connective,
                right,
            } => {
                assert_eq!(**left, Selbri::Root("barda".into()));
                assert_eq!(*connective, Connective::Je);
                assert_eq!(**right, Selbri::Root("xunre".into()));
            }
            other => panic!("expected Connected, got {:?}", other),
        }
    }

    #[test]
    fn test_la_name() {
        let tokens = [
            cmavo("la"),
            pause(),
            cmevla("djan"),
            pause(),
            cmavo("cu"),
            gismu("klama"),
        ];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        match &s.head_terms[0] {
            Sumti::Name(n) => assert_eq!(n, "djan"),
            other => panic!("expected Name, got {:?}", other),
        }
    }

    #[test]
    fn test_relative_clause() {
        let tokens = [
            cmavo("mi"),
            gismu("nelci"),
            cmavo("lo"),
            gismu("gerku"),
            cmavo("poi"),
            gismu("barda"),
        ];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        match &s.tail_terms[0] {
            Sumti::Restricted { inner, clause } => {
                assert_eq!(clause.kind, RelClauseKind::Poi);
                match inner.as_ref() {
                    Sumti::Description { gadri, .. } => assert_eq!(*gadri, Gadri::Lo),
                    other => panic!("expected Description, got {:?}", other),
                }
            }
            other => panic!("expected Restricted, got {:?}", other),
        }
    }

    #[test]
    fn test_ke_grouping() {
        let tokens = [
            cmavo("mi"),
            cmavo("ke"),
            gismu("sutra"),
            gismu("gerku"),
            cmavo("ke'e"),
        ];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        match &s.selbri {
            Selbri::Grouped(inner) => {
                assert!(matches!(inner.as_ref(), Selbri::Tanru(_, _)));
            }
            other => panic!("expected Grouped, got {:?}", other),
        }
    }

    #[test]
    fn test_zo_e_unspecified() {
        let tokens = [cmavo("mi"), gismu("prami"), cmavo("zo'e")];
        let result = parse_tokens_to_ast(&tokens).unwrap();
        let s = &result.sentences[0];
        assert_eq!(s.tail_terms[0], Sumti::Unspecified);
    }

    // ─── Phase 5: hardening-specific tests ────────────────────

    #[test]
    fn test_unconsumed_tokens_detected() {
        // "klama" is selbri, ku'o is a stray terminator → unconsumed
        let tokens = [cmavo("mi"), gismu("klama"), cmavo("ku'o")];
        let result = parse_tokens_to_ast(&tokens);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("unconsumed"));
    }

    #[test]
    fn test_backtrack_place_tag_at_end() {
        // "fa" at end — tag consumed but no sumti → should restore and error
        let tokens = [gismu("klama"), cmavo("fa")];
        let result = parse_tokens_to_ast(&tokens);
        assert!(result.is_err());
    }

    #[test]
    fn test_backtrack_lo_without_selbri() {
        // "lo" at end — gadri consumed but no selbri → should restore
        let tokens = [gismu("klama"), cmavo("lo")];
        let result = parse_tokens_to_ast(&tokens);
        assert!(result.is_err());
    }

    #[test]
    fn test_backtrack_la_without_name() {
        // "la" at end — consumed but no cmevla → should restore
        let tokens = [gismu("klama"), cmavo("la")];
        let result = parse_tokens_to_ast(&tokens);
        assert!(result.is_err());
    }

    #[test]
    fn test_depth_limit_does_not_crash() {
        // 100 nested ke's — should hit depth limit, not stack overflow
        let mut tokens: Vec<NormalizedToken<'static>> = Vec::new();
        tokens.push(cmavo("mi"));
        for _ in 0..100 {
            tokens.push(cmavo("ke"));
        }
        tokens.push(gismu("klama"));
        for _ in 0..100 {
            tokens.push(cmavo("ke'e"));
        }
        let result = parse_tokens_to_ast(&tokens);
        // Must not panic/crash — error or degraded parse are both acceptable
        let _ = result;
    }

    #[test]
    fn test_backtrack_conversion_without_tanru() {
        // "se" at end — conversion consumed but no tanru → should restore
        let tokens = [gismu("klama"), cmavo("se")];
        let result = parse_tokens_to_ast(&tokens);
        assert!(result.is_err());
    }
}
