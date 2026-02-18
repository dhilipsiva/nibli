use pest::Parser;
use pest::iterators::Pair;
use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;

#[derive(pest_derive::Parser)]
#[grammar = "lojban.pest"]
pub struct LojbanParser;

// --------------------------------------------------
// AST Node Definitions (Arena Allocated)
// --------------------------------------------------

#[derive(Debug, PartialEq)]
pub enum Sumti<'a> {
    ProSumti(&'a str),                 // "mi", "do", "da" (Variables/Constants)
    Description(Box<Selbri<'a>>),      // "lo gerku" (Entities satisfying a predicate)
    Name(&'a str),                     // "la .alis."
    QuotedLiteral(&'a str),            // Output of zo/zoi
}

#[derive(Debug, PartialEq)]
pub enum Selbri<'a> {
    Root(&'a str),                     // Gismu (e.g., "klama")
    Compound(BumpVec<'a, &'a str>),    // Lujvo components
    Tanru(Box<Selbri<'a>>, Box<Selbri<'a>>), // Metaphorical modification (Modifier, Head)
}

#[derive(Debug, PartialEq)]
pub struct Bridi<'a> {
    pub selbri: Selbri<'a>,
    pub terms: BumpVec<'a, Sumti<'a>>,
}

// --------------------------------------------------
// AST Construction
// --------------------------------------------------

/// Parses a sanitized Lojban string into an arena-allocated AST.
pub fn parse_to_ast<'a>(input: &'a str, arena: &'a Bump) -> Result<BumpVec<'a, Bridi<'a>>, pest::error::Error<Rule>> {
    let mut ast = BumpVec::new_in(arena);
    let pairs = LojbanParser::parse(Rule::text, input)?;

    for pair in pairs {
        if pair.as_rule() == Rule::sentence {
            ast.push(build_bridi(pair, arena));
        }
    }

    Ok(ast)
}

fn build_bridi<'a>(pair: Pair<'a, Rule>, arena: &'a Bump) -> Bridi<'a> {
    let mut terms = BumpVec::new_in(arena);
    let mut selbri = None;

    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::sumti_list => {
                for sumti_pair in inner.into_inner() {
                    terms.push(build_sumti(sumti_pair, arena));
                }
            }
            Rule::bridi_tail => {
                for tail_inner in inner.into_inner() {
                    match tail_inner.as_rule() {
                        Rule::selbri => selbri = Some(build_selbri(tail_inner, arena)),
                        Rule::sumti_list => {
                            for sumti_pair in tail_inner.into_inner() {
                                terms.push(build_sumti(sumti_pair, arena));
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    Bridi {
        selbri: selbri.expect("A valid sentence must contain a selbri"),
        terms,
    }
}

fn build_selbri<'a>(pair: Pair<'a, Rule>, _arena: &'a Bump) -> Selbri<'a> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::simple_selbri => Selbri::Root(inner.as_str()),
        Rule::tanru => {
            // Simplified tanru parsing for MVP: treats the first as modifier, rest as head.
            let mut parts = inner.into_inner();
            let modifier = parts.next().unwrap().as_str();
            let head = parts.next().unwrap().as_str();
            Selbri::Tanru(
                Box::new(Selbri::Root(modifier)),
                Box::new(Selbri::Root(head))
            )
        }
        _ => unreachable!(),
    }
}

fn build_sumti<'a>(pair: Pair<'a, Rule>, arena: &'a Bump) -> Sumti<'a> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::pron_clause => Sumti::ProSumti(inner.as_str()),
        Rule::lo_clause => {
            let selbri_pair = inner.into_inner().next().unwrap();
            Sumti::Description(Box::new(build_selbri(selbri_pair, arena)))
        }
        Rule::name_clause => Sumti::Name(inner.as_str()),
        _ => Sumti::QuotedLiteral(inner.as_str()),
    }
}
