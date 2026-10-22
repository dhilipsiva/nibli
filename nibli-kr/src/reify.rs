//! Lossless, syntax-only export of the KR tree to ordinary Nibli base facts.
//!
//! This module deliberately does not call the validating emitter, semantic
//! compiler, or reasoner. Unknown words and ill-placed arguments are data, not
//! exporter errors. All payloads are constants: source variables never become
//! variables in the exported program. The catalog is the projection of the
//! committed lexicon onto spellings present in the input (including literals).

use crate::ast::*;
use std::collections::BTreeSet;
use std::fmt::{self, Write};

pub const SCHEMA_VERSION: &str = "nibli-ast-v1";
pub const PROGRAM: &str = "program:0";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InputIntent {
    Assertion,
    Query,
}

/// An emitted fact contains string constants only; the relation is fixed by the
/// schema, never taken from source text. Useful to native embedding consumers
/// that already provide a ground-fact ingress.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstFact {
    pub relation: &'static str,
    pub arguments: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AstFacts {
    pub facts: Vec<AstFact>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReifyError(pub String);

impl fmt::Display for ReifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ReifyError {}

impl AstFacts {
    pub fn to_nibli(&self) -> String {
        let mut out = format!("# {SCHEMA_VERSION}; syntax facts, not executable subject code.\n");
        for fact in &self.facts {
            write!(out, "{}(", fact.relation).unwrap();
            for (i, arg) in fact.arguments.iter().enumerate() {
                if i != 0 {
                    out.push_str(", ");
                }
                out.push('"');
                for c in arg.chars() {
                    if c == '\\' || c == '"' {
                        out.push('\\');
                    }
                    out.push(c);
                }
                out.push('"');
            }
            out.push_str(").\n");
        }
        out
    }
}

/// Injective UTF-8 encoding shared by every textual payload and catalog key.
pub fn text_constant(text: &str) -> String {
    let mut out = String::from("text:");
    for byte in text.bytes() {
        write!(out, "{byte:02x}").unwrap();
    }
    out
}

pub fn ast_to_nibli(statements: &[Statement], intent: InputIntent) -> Result<String, ReifyError> {
    Ok(reify(statements, intent)?.to_nibli())
}

pub fn reify(statements: &[Statement], intent: InputIntent) -> Result<AstFacts, ReifyError> {
    let mut e = Exporter::default();
    e.fact("ast_program", &[PROGRAM, SCHEMA_VERSION]);
    for (i, statement) in statements.iter().enumerate() {
        let id = format!("statement:{i}");
        let root = e.claim(&statement.claim)?;
        e.fact(
            "ast_statement",
            &[
                &id,
                &root,
                match intent {
                    InputIntent::Assertion => "assertion",
                    InputIntent::Query => "query",
                },
            ],
        );
        e.span(&id, &statement.span);
        if i > 0 {
            e.fact(
                "ast_next_statement",
                &[&format!("statement:{}", i - 1), &id],
            );
        }
    }
    e.catalog();
    e.texts();
    for i in 0..e.max_index {
        e.fact("ast_index_next", &[&i.to_string(), &(i + 1).to_string()]);
    }
    Ok(AstFacts { facts: e.facts })
}

#[derive(Default)]
struct Exporter {
    facts: Vec<AstFact>,
    next_node: usize,
    max_index: usize,
    strings: BTreeSet<String>,
}

impl Exporter {
    fn fact(&mut self, relation: &'static str, args: &[&str]) {
        self.facts.push(AstFact {
            relation,
            arguments: args.iter().map(|a| (*a).to_owned()).collect(),
        });
    }

    fn node(&mut self, kind: &str) -> String {
        let id = format!("node:{}", self.next_node);
        self.next_node += 1;
        self.fact("ast_node", &[&id, kind]);
        id
    }

    fn value(&mut self, node: &str, field: &str, kind: &str, value: &str) {
        self.fact("ast_value", &[node, field, kind, value]);
    }

    fn text(&mut self, node: &str, field: &str, value: &str) {
        self.strings.insert(value.to_owned());
        self.value(node, field, "text", &text_constant(value));
    }

    fn length(&mut self, node: &str, field: &str, len: usize) {
        self.max_index = self.max_index.max(len);
        self.fact("ast_length", &[node, field, &len.to_string()]);
    }

    fn child(&mut self, node: &str, field: &str, i: usize, child: &str) {
        self.max_index = self.max_index.max(i + 1);
        self.fact("ast_child", &[node, field, &i.to_string(), child]);
    }

    fn span(&mut self, node: &str, span: &std::ops::Range<usize>) {
        self.fact(
            "ast_span",
            &[node, &span.start.to_string(), &span.end.to_string()],
        );
    }

    fn claim(&mut self, claim: &Claim) -> Result<String, ReifyError> {
        let kind = match claim {
            Claim::Prenex { .. } => "prenex",
            Claim::DetBlock { .. } => "det_block",
            Claim::Impl(..) => "impl",
            Claim::Iff(..) => "iff",
            Claim::Xor(..) => "xor",
            Claim::Or(..) => "or",
            Claim::And(..) => "and",
            Claim::Not(..) => "not",
            Claim::Prefixed { .. } => "prefixed",
            Claim::Equality(..) => "equality",
            Claim::Predication(_) => "predication",
        };
        let node = self.node(kind);
        match claim {
            Claim::Prenex { vars, body } => {
                self.length(&node, "vars", vars.len());
                for (i, var) in vars.iter().enumerate() {
                    let child = self.node("binder");
                    self.text(&child, "name", var);
                    self.child(&node, "vars", i, &child);
                }
                let child = self.claim(body)?;
                self.child(&node, "body", 0, &child);
            }
            Claim::DetBlock {
                det,
                restr,
                var,
                body,
            } => {
                self.determiner(&node, *det);
                self.text(&node, "var", var);
                let child = self.restr(restr)?;
                self.child(&node, "restrictor", 0, &child);
                let child = self.claim(body)?;
                self.child(&node, "body", 0, &child);
            }
            Claim::Impl(a, b)
            | Claim::Iff(a, b)
            | Claim::Xor(a, b)
            | Claim::Or(a, b)
            | Claim::And(a, b) => {
                let child = self.claim(a)?;
                self.child(&node, "left", 0, &child);
                let child = self.claim(b)?;
                self.child(&node, "right", 0, &child);
            }
            Claim::Not(body) => {
                let child = self.claim(body)?;
                self.child(&node, "body", 0, &child);
            }
            Claim::Prefixed {
                deontic,
                tense,
                atom,
            } => {
                self.value(
                    &node,
                    "tense",
                    "tag",
                    match tense {
                        None => "none",
                        Some(Tense::Past) => "past",
                        Some(Tense::Now) => "now",
                        Some(Tense::Future) => "future",
                    },
                );
                self.value(
                    &node,
                    "deontic",
                    "tag",
                    match deontic {
                        None => "none",
                        Some(DeonticMood::Obligation) => "must",
                        Some(DeonticMood::Permission) => "may",
                    },
                );
                let child = self.claim(atom)?;
                self.child(&node, "body", 0, &child);
            }
            Claim::Equality(a, b) => {
                let child = self.term(a)?;
                self.child(&node, "left", 0, &child);
                let child = self.term(b)?;
                self.child(&node, "right", 0, &child);
            }
            Claim::Predication(p) => {
                self.span(&node, &p.span);
                let child = self.seq(&p.seq)?;
                self.child(&node, "sequence", 0, &child);
                self.args(&node, &p.args)?;
                self.length(&node, "tags", p.tags.len());
                for (i, tag) in p.tags.iter().enumerate() {
                    let child = self.node("tag");
                    self.span(&child, &tag.span);
                    self.word(&child, &tag.pred);
                    let term = self.term(&tag.term)?;
                    self.child(&child, "term", 0, &term);
                    self.child(&node, "tags", i, &child);
                }
            }
        }
        Ok(node)
    }

    fn word(&mut self, node: &str, parts: &[String]) {
        self.length(node, "parts", parts.len());
        // Joining lexical compound parts is spelling, not name resolution.
        self.text(node, "spelling", &parts.join("+"));
        for (i, part) in parts.iter().enumerate() {
            let child = self.node("word_part");
            self.text(&child, "name", part);
            self.child(node, "parts", i, &child);
        }
    }

    fn seq(&mut self, seq: &PredSeq) -> Result<String, ReifyError> {
        if seq.0.is_empty() {
            return Err(ReifyError(
                "a parsed predicate sequence cannot be empty".into(),
            ));
        }
        let node = self.node("sequence");
        self.length(&node, "units", seq.0.len());
        for (i, unit) in seq.0.iter().enumerate() {
            let child = match unit {
                PredUnit::Word(parts) => {
                    let child = self.node("word");
                    self.word(&child, parts);
                    child
                }
                PredUnit::Group(seq) => {
                    let child = self.node("group");
                    let inner = self.seq(seq)?;
                    self.child(&child, "sequence", 0, &inner);
                    child
                }
            };
            self.child(&node, "units", i, &child);
        }
        Ok(node)
    }

    fn args(&mut self, node: &str, args: &[Arg]) -> Result<(), ReifyError> {
        self.length(node, "args", args.len());
        for (i, arg) in args.iter().enumerate() {
            let child = self.node("argument");
            self.span(&child, &arg.span);
            if let Some(label) = &arg.label {
                self.text(&child, "label", label);
            } else {
                self.value(&child, "label", "tag", "positional");
            }
            let term = self.term(&arg.term)?;
            self.child(&child, "term", 0, &term);
            self.child(node, "args", i, &child);
        }
        Ok(())
    }

    fn term(&mut self, term: &Term) -> Result<String, ReifyError> {
        let kind = match term {
            Term::Unspecified => "unspecified",
            Term::Witness => "witness",
            Term::Number(_) => "number",
            Term::Str(_) => "string",
            Term::Var(_) => "variable",
            Term::Key(_) => "key",
            Term::Name { .. } => "name",
            Term::Abstraction { .. } => "abstraction",
            Term::Det { .. } => "description",
        };
        let node = self.node(kind);
        match term {
            Term::Unspecified | Term::Witness => {}
            Term::Number(n) => {
                if !n.is_finite() {
                    return Err(ReifyError("non-finite number in AST".into()));
                }
                self.value(&node, "number", "f64", &format!("{:016x}", n.to_bits()));
            }
            Term::Str(s) => self.text(&node, "text", s),
            Term::Var(s) => self.text(&node, "name", s),
            Term::Key(key) => self.value(
                &node,
                "key",
                "tag",
                match key {
                    KeyTerm::Me => "me",
                    KeyTerm::You => "you",
                    KeyTerm::We => "we",
                    KeyTerm::WeAll => "we_all",
                    KeyTerm::WeOthers => "we_others",
                    KeyTerm::YouAll => "you_all",
                    KeyTerm::This => "this",
                    KeyTerm::That => "that",
                    KeyTerm::Yonder => "yonder",
                    KeyTerm::ItA => "it_a",
                    KeyTerm::ItE => "it_e",
                    KeyTerm::ItI => "it_i",
                    KeyTerm::ItO => "it_o",
                    KeyTerm::ItU => "it_u",
                    KeyTerm::It => "it",
                    KeyTerm::Slot => "slot",
                },
            ),
            Term::Name { name, rel_clauses } => {
                self.text(&node, "name", name);
                self.clauses(&node, rel_clauses)?;
            }
            Term::Abstraction { kind, body } => {
                self.value(
                    &node,
                    "abstraction",
                    "tag",
                    match kind {
                        AbsKind::Event => "event",
                        AbsKind::Fact => "fact",
                        AbsKind::Property => "property",
                        AbsKind::Amount => "amount",
                        AbsKind::Concept => "concept",
                    },
                );
                let child = self.claim(body)?;
                self.child(&node, "body", 0, &child);
            }
            Term::Det { det, restr } => {
                self.determiner(&node, *det);
                let child = self.restr(restr)?;
                self.child(&node, "restrictor", 0, &child);
            }
        }
        Ok(node)
    }

    fn determiner(&mut self, node: &str, det: Det) {
        self.value(
            node,
            "determiner",
            "tag",
            match det {
                Det::Some => "some",
                Det::The => "the",
                Det::Every => "every",
                Det::EveryThe => "every_the",
                Det::Exactly(_) => "exactly",
                Det::ExactlyThe(_) => "exactly_the",
            },
        );
        if let Det::Exactly(n) | Det::ExactlyThe(n) = det {
            self.value(node, "count", "u32", &n.to_string());
        }
    }

    fn restr(&mut self, restr: &Restr) -> Result<String, ReifyError> {
        let node = self.node(match restr.kind {
            RestrKind::Seq { .. } => "restrictor",
            RestrKind::Selected { .. } => "selected",
        });
        self.span(&node, &restr.span);
        self.value(
            &node,
            "negated",
            "bool",
            if restr.negated { "true" } else { "false" },
        );
        match &restr.kind {
            RestrKind::Seq { seq, linked_args } => {
                let child = self.seq(seq)?;
                self.child(&node, "sequence", 0, &child);
                self.args(&node, linked_args)?;
            }
            RestrKind::Selected { pred, label } => {
                self.text(&node, "spelling", pred);
                self.text(&node, "selector", label);
            }
        }
        self.clauses(&node, &restr.rel_clauses)?;
        Ok(node)
    }

    fn clauses(&mut self, node: &str, clauses: &[RelClause]) -> Result<(), ReifyError> {
        self.length(node, "clauses", clauses.len());
        for (i, clause) in clauses.iter().enumerate() {
            let child = self.node("clause");
            self.span(&child, &clause.span);
            self.value(
                &child,
                "clause",
                "tag",
                match clause.kind {
                    RelKind::Where => "where",
                    RelKind::Also => "also",
                },
            );
            match &clause.body {
                ClauseBody::Bare { negated, seq } => {
                    self.value(
                        &child,
                        "negated",
                        "bool",
                        if *negated { "true" } else { "false" },
                    );
                    let inner = self.seq(seq)?;
                    self.child(&child, "sequence", 0, &inner);
                }
                ClauseBody::Full(claim) => {
                    let inner = self.claim(claim)?;
                    self.child(&child, "body", 0, &inner);
                }
            }
            self.child(node, "clauses", i, &child);
        }
        Ok(())
    }

    fn catalog(&mut self) {
        let requested = self.strings.clone();
        for entry in nibli_lexicon::corpus::corpus_entries() {
            if requested.contains(entry.name) {
                let canonical = entry.swap.map_or(entry.name, |s| s.base);
                self.catalog_entry(
                    entry.name,
                    canonical,
                    entry.places,
                    entry.swap.map(|s| s.with),
                );
            }
        }
        for entry in nibli_lexicon::corpus::corpus_compounds() {
            if requested.contains(entry.name) {
                self.catalog_entry(entry.name, entry.relation, entry.places, None);
            }
        }
        for (relation, kind) in [
            ("admits", "admits"),
            ("derived_only", "derived_only"),
            ("equals", "identity"),
            ("product", "compute"),
            ("sum", "compute"),
            ("quotient", "compute"),
            ("exponential", "external_compute"),
            ("logarithm", "external_compute"),
            ("greater", "comparison"),
            ("less", "comparison"),
            ("num_equal", "comparison"),
        ] {
            self.strings.insert(relation.into());
            self.fact("lex_builtin", &[&text_constant(relation), kind]);
        }
        for pronoun in nibli_types::ast::Pronoun::ALL {
            let name = pronoun.as_str();
            self.strings.insert(name.into());
            self.fact("lex_pronoun", &[name, &text_constant(name)]);
        }
        // Byte-wise rigid-name normalization is specified by the checker, not
        // performed on AST names here. These are the ASCII alphabet's facts.
        for byte in 0u8..=127 {
            let folded = if byte == b'_' {
                b' '
            } else {
                byte.to_ascii_lowercase()
            };
            self.fact("lex_name_byte", &[&byte.to_string(), &folded.to_string()]);
        }
    }

    fn catalog_entry(&mut self, name: &str, canonical: &str, places: &[&str], swap: Option<u8>) {
        self.strings.insert(name.into());
        self.strings.insert(canonical.into());
        let name = text_constant(name);
        self.fact(
            "lex_pred",
            &[&name, &text_constant(canonical), &places.len().to_string()],
        );
        let domain = format!("the_domain_{canonical}");
        self.strings.insert(domain.clone());
        self.fact(
            "lex_domain",
            &[&text_constant(canonical), &text_constant(&domain)],
        );
        for i in 1..=places.len() {
            let role = format!("{canonical}_x{i}");
            self.strings.insert(role.clone());
            self.fact(
                "lex_role",
                &[
                    &text_constant(canonical),
                    &i.to_string(),
                    &text_constant(&role),
                ],
            );
        }
        self.max_index = self.max_index.max(places.len());
        for (i, label) in places.iter().enumerate() {
            let surface = i + 1;
            let canonical = match swap {
                Some(other) if surface == 1 => other as usize,
                Some(other) if surface == other as usize => 1,
                _ => surface,
            };
            for label in [(*label).to_string(), format!("x{surface}")] {
                self.strings.insert(label.clone());
                self.fact(
                    "lex_place",
                    &[
                        &name,
                        &text_constant(&label),
                        &surface.to_string(),
                        &canonical.to_string(),
                    ],
                );
            }
        }
    }

    fn texts(&mut self) {
        for text in self.strings.clone() {
            let id = text_constant(&text);
            self.fact("ast_text_end", &[&id, &text.len().to_string()]);
            self.max_index = self.max_index.max(text.len());
            for (i, byte) in text.bytes().enumerate() {
                self.fact("ast_text_byte", &[&id, &i.to_string(), &byte.to_string()]);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_statements;

    #[test]
    fn deterministic_and_inert_even_for_invalid_subjects() {
        let source = r#"all $x: person($x) & ~unregistered_probe($x) -> prisoner($x).
name("a\". prisoner(Zed). # \\ λ", Zed)."#;
        let ast = parse_statements(source).unwrap();
        assert!(crate::parse_checked(source).is_err());
        let first = reify(&ast, InputIntent::Assertion).unwrap();
        assert_eq!(first, reify(&ast, InputIntent::Assertion).unwrap());
        let text = first.to_nibli();
        crate::parse_checked(&text).expect("every export is legal admitted-base-fact syntax");
        for statement in parse_statements(&text).unwrap() {
            let Claim::Predication(predication) = statement.claim else {
                panic!("subject code escaped into the metadata program");
            };
            assert!(
                predication
                    .args
                    .iter()
                    .all(|a| matches!(a.term, Term::Str(_)))
            );
        }
        assert!(!text.contains("unregistered_probe"));
        assert!(!text.contains("prisoner(Zed)"));
        assert!(text.contains(&text_constant("unregistered_probe")));
    }

    #[test]
    fn text_encoding_is_injective_and_numbers_keep_their_bits() {
        assert_ne!(text_constant("A_b"), text_constant("a b"));
        assert_ne!(text_constant("λ"), text_constant("cebb"));
        assert_eq!(text_constant("λ"), "text:cebb");
        let tree = parse_statements("quantity(Zed, 0.1).").unwrap();
        let facts = reify(&tree, InputIntent::Query).unwrap();
        assert!(facts.facts.iter().any(|f| f.relation == "ast_value"
            && f.arguments[2] == "f64"
            && f.arguments[3] == format!("{:016x}", 0.1f64.to_bits())));
        assert!(
            facts
                .facts
                .iter()
                .any(|f| f.relation == "ast_statement" && f.arguments[2] == "query")
        );
    }

    #[test]
    fn ordered_syntax_and_alias_spelling_survive() {
        let tree = parse_statements("owned(x2: Adam, x1: House). person(Adam).").unwrap();
        let facts = reify(&tree, InputIntent::Assertion).unwrap();
        assert!(
            facts
                .facts
                .iter()
                .any(|f| f.relation == "ast_next_statement"
                    && f.arguments == ["statement:0", "statement:1"])
        );
        assert!(facts.facts.iter().any(|f| f.relation == "ast_value"
            && f.arguments[1] == "spelling"
            && f.arguments[3] == text_constant("owned")));
        assert!(facts.facts.iter().any(|f| f.relation == "lex_pred"
            && f.arguments[..2] == [text_constant("owned"), text_constant("owns")]));
        assert!(
            facts
                .facts
                .iter()
                .any(|f| f.relation == "ast_span" && f.arguments == ["statement:0", "0", "27"])
        );
    }

    #[test]
    fn committed_export_snapshot() {
        let source = include_str!("../tests/fixtures/reify_subject.nibli");
        let tree = parse_statements(source).unwrap();
        assert_eq!(
            ast_to_nibli(&tree, InputIntent::Assertion).unwrap(),
            include_str!("../tests/fixtures/reify_subject.ast.nibli")
        );
    }
}
