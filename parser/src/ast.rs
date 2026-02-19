use crate::lexer::LojbanToken;
use crate::preprocessor::NormalizedToken;
use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;

#[derive(Debug, PartialEq)]
pub enum Sumti<'a> {
    ProSumti(&'a str),
    Description(Box<Selbri<'a>>),
    Name(&'a str),
    QuotedLiteral(&'a str),
}

#[derive(Debug, PartialEq)]
pub enum Selbri<'a> {
    Root(&'a str),
    Compound(BumpVec<'a, &'a str>),
    Tanru(Box<Selbri<'a>>, Box<Selbri<'a>>),
}

#[derive(Debug, PartialEq)]
pub struct Bridi<'a> {
    pub selbri: Selbri<'a>,
    pub terms: BumpVec<'a, Sumti<'a>>,
}

struct TokenCursor<'a> {
    tokens: &'a [NormalizedToken<'a>],
    pos: usize,
}

impl<'a> TokenCursor<'a> {
    fn peek(&self) -> Option<&'a NormalizedToken<'a>> {
        self.tokens.get(self.pos)
    }

    fn next(&mut self) -> Option<&'a NormalizedToken<'a>> {
        let t = self.tokens.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
}

pub fn parse_tokens_to_ast<'a>(
    tokens: &'a [NormalizedToken<'a>],
    arena: &'a Bump,
) -> Result<BumpVec<'a, Bridi<'a>>, String> {
    let mut cursor = TokenCursor { tokens, pos: 0 };
    let mut bridi_list = BumpVec::new_in(arena);

    // Sentence structure: [Sumti]* [cu]? [Selbri] [Sumti]*
    let mut terms = BumpVec::new_in(arena);
    let mut selbri = None;

    while let Some(token) = cursor.peek() {
        match token {
            NormalizedToken::Standard(LojbanToken::Cmavo, "lo") => {
                cursor.next(); // consume 'lo'
                if let Some(NormalizedToken::Standard(LojbanToken::Gismu, s)) = cursor.next() {
                    terms.push(Sumti::Description(Box::new(Selbri::Root(s))));
                }
            }
            NormalizedToken::Standard(LojbanToken::Cmavo, s) if *s == "mi" || *s == "do" => {
                cursor.next();
                terms.push(Sumti::ProSumti(s));
            }
            NormalizedToken::Standard(LojbanToken::Cmavo, "cu") => {
                cursor.next(); // consume 'cu' separator
            }
            NormalizedToken::Standard(LojbanToken::Gismu, s) => {
                cursor.next();
                selbri = Some(Selbri::Root(s));
            }
            _ => {
                cursor.next();
            } // Skip unknown for MVP
        }
    }

    if let Some(s) = selbri {
        bridi_list.push(Bridi { selbri: s, terms });
        Ok(bridi_list)
    } else {
        Err("No selbri found in token stream".to_string())
    }
}
