//! Minimal RDF Turtle parser.
//!
//! Supports the subset needed for practical KB import:
//! - `<IRI> <IRI> <IRI> .` — URI triples
//! - `<IRI> <IRI> "literal" .` — String literals
//! - `<IRI> <IRI> "42"^^<xsd:integer> .` — Typed numeric literals
//! - `@prefix ex: <http://example.org/> .` — Prefix declarations
//! - `# comment` lines
//!
//! Complex features (blank nodes, collections, multi-line literals) not supported.

use std::collections::HashMap;

/// A parsed RDF triple.
#[derive(Clone, Debug, PartialEq)]
pub struct Triple {
    pub subject: Term,
    pub predicate: Term,
    pub object: Term,
}

/// An RDF term (IRI, literal, or typed literal).
#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    /// Full IRI: `<http://example.org/Dog>`
    Iri(String),
    /// String literal: `"hello"`
    StringLiteral(String),
    /// Numeric literal (parsed to f64).
    NumericLiteral(f64),
}

impl Term {
    /// Extract the local name from an IRI (part after last `/` or `#`).
    pub fn local_name(&self) -> &str {
        match self {
            Term::Iri(iri) => {
                if let Some(pos) = iri.rfind('#') {
                    &iri[pos + 1..]
                } else if let Some(pos) = iri.rfind('/') {
                    &iri[pos + 1..]
                } else {
                    iri
                }
            }
            Term::StringLiteral(s) => s,
            Term::NumericLiteral(_) => "",
        }
    }
}

/// Parse RDF Turtle text into triples.
pub fn parse_turtle(text: &str) -> Result<Vec<Triple>, String> {
    let mut prefixes: HashMap<String, String> = HashMap::new();
    let mut triples = Vec::new();

    for (line_num, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        // Prefix declaration: @prefix ex: <http://example.org/> .
        if line.starts_with("@prefix") {
            let rest = line.trim_start_matches("@prefix").trim();
            let colon_pos = rest
                .find(':')
                .ok_or_else(|| format!("line {}: invalid @prefix", line_num + 1))?;
            let prefix = rest[..colon_pos].trim().to_string();
            let rest = rest[colon_pos + 1..].trim();
            let iri = parse_iri_token(rest)
                .ok_or_else(|| format!("line {}: invalid IRI in @prefix", line_num + 1))?;
            prefixes.insert(prefix, iri);
            continue;
        }

        // Triple: subject predicate object .
        let parts = tokenize_triple(line, &prefixes);
        match parts {
            Ok((s, p, o)) => triples.push(Triple {
                subject: s,
                predicate: p,
                object: o,
            }),
            Err(e) => return Err(format!("line {}: {}", line_num + 1, e)),
        }
    }

    Ok(triples)
}

/// Extract an IRI from `<...>` notation.
fn parse_iri_token(s: &str) -> Option<String> {
    let s = s.trim();
    if s.starts_with('<') {
        let end = s.find('>')?;
        Some(s[1..end].to_string())
    } else {
        None
    }
}

/// Tokenize a triple line into (subject, predicate, object).
fn tokenize_triple(
    line: &str,
    prefixes: &HashMap<String, String>,
) -> Result<(Term, Term, Term), String> {
    let line = line.trim().trim_end_matches('.');
    let mut tokens = Vec::new();
    let mut chars = line.chars().peekable();

    while chars.peek().is_some() {
        skip_whitespace(&mut chars);
        if chars.peek().is_none() {
            break;
        }

        match chars.peek() {
            Some('<') => {
                // IRI
                chars.next(); // consume <
                let mut iri = String::new();
                for ch in chars.by_ref() {
                    if ch == '>' {
                        break;
                    }
                    iri.push(ch);
                }
                tokens.push(Term::Iri(iri));
            }
            Some('"') => {
                // Literal
                chars.next(); // consume opening "
                let mut lit = String::new();
                loop {
                    match chars.next() {
                        Some('"') => break,
                        Some('\\') => {
                            if let Some(escaped) = chars.next() {
                                lit.push(escaped);
                            }
                        }
                        Some(ch) => lit.push(ch),
                        None => break,
                    }
                }
                // Check for type annotation ^^<...>
                let mut is_numeric = false;
                if chars.peek() == Some(&'^') {
                    chars.next(); // first ^
                    if chars.peek() == Some(&'^') {
                        chars.next(); // second ^
                        if chars.peek() == Some(&'<') {
                            chars.next();
                            let mut type_iri = String::new();
                            loop {
                                match chars.next() {
                                    Some('>') => break,
                                    Some(ch) => type_iri.push(ch),
                                    None => break,
                                }
                            }
                            if type_iri.contains("integer") || type_iri.contains("decimal") || type_iri.contains("double") || type_iri.contains("float") {
                                if let Ok(n) = lit.parse::<f64>() {
                                    tokens.push(Term::NumericLiteral(n));
                                    is_numeric = true;
                                }
                            }
                        }
                    }
                }
                if !is_numeric {
                    tokens.push(Term::StringLiteral(lit));
                }
            }
            _ => {
                // Prefixed name or bare word
                let mut word = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch.is_whitespace() || ch == '.' {
                        break;
                    }
                    word.push(ch);
                    chars.next();
                }
                // Check for prefix:local
                if let Some(colon_pos) = word.find(':') {
                    let prefix = &word[..colon_pos];
                    let local = &word[colon_pos + 1..];
                    if let Some(base) = prefixes.get(prefix) {
                        tokens.push(Term::Iri(format!("{}{}", base, local)));
                        continue;
                    }
                }
                // Bare numeric
                if let Ok(n) = word.parse::<f64>() {
                    tokens.push(Term::NumericLiteral(n));
                } else if !word.is_empty() {
                    tokens.push(Term::Iri(word));
                }
            }
        }
    }

    if tokens.len() < 3 {
        return Err(format!(
            "expected 3 terms, got {} in: {}",
            tokens.len(),
            line.trim()
        ));
    }

    Ok((tokens[0].clone(), tokens[1].clone(), tokens[2].clone()))
}

fn skip_whitespace(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    while let Some(&ch) = chars.peek() {
        if ch.is_whitespace() {
            chars.next();
        } else {
            break;
        }
    }
}
