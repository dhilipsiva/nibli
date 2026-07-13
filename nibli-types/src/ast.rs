//! AST types produced by the gerna parser.
//!
//! Flat index-based representation: `AstBuffer` contains parallel arrays of
//! `Predicate`, `Argument`, and `Sentence` nodes, referenced by `u32` indices.

/// Index into the `predicates` array of an `AstBuffer`.
pub type PredicateId = u32;
/// Index into the `arguments` array of an `AstBuffer`.
pub type ArgumentId = u32;

/// Modal tag: a custom modal built from a predicate reference (the `via:` tag).
#[derive(Clone, Copy, Debug)]
pub enum ModalTag {
    /// `via` + predicate: user-defined modal via a predicate reference.
    Custom(PredicateId),
}

/// SE-series conversion: permutes the x1 place with another.
/// se=x1↔x2, te=x1↔x3, ve=x1↔x4, xe=x1↔x5.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Conversion {
    Swap12,
    Swap13,
    Swap14,
    Swap15,
}

/// Logical connective shared by selbri and sumti connectives.
/// je=AND(∧), ja=OR(∨), jo=IFF(↔), ju=XOR(⊕).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Connective {
    And,
    Or,
    Iff,
    Whether,
}

/// Determiner (article/descriptor): determines how a description term binds.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Determiner {
    /// Indefinite description (at least one entity satisfying the predicate).
    Indefinite,
    /// Definite description (an opaque rigid designator).
    Definite,
    /// Universal over an indefinite description.
    UniversalIndefinite,
    /// Universal over a definite description.
    UniversalDefinite,
}

/// Abstraction kind: wraps a sub-sentence into a sumti.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AbstractionKind {
    /// Event abstraction.
    Event,
    /// Propositional (fact) abstraction.
    Fact,
    /// Property abstraction.
    Property,
    /// Quantity/amount abstraction.
    Amount,
    /// Concept abstraction.
    Concept,
}

/// Relative clause kind: restrictive or non-restrictive (incidental).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RelClauseKind {
    /// Restrictive relative clause.
    Restrictive,
    /// Non-restrictive (incidental) relative clause.
    Incidental,
}

/// A relative clause attached to a sumti.
#[derive(Clone, Debug)]
pub struct RelClause {
    pub kind: RelClauseKind,
    /// Index into the `sentences` array of the containing `AstBuffer`.
    pub body_sentence: u32,
}

/// A sumti (argument term) in the AST.
#[derive(Clone, Debug)]
pub enum Argument {
    /// Pro-sumti: mi, do, da, de, di, ti, ta, tu, ke'a, ma, ko, etc.
    Pronoun(String),
    /// Determiner description: `lo/le` + selbri. Fields: (gadri, selbri-id).
    Description((Determiner, PredicateId)),
    /// Named entity: `la` + cmevla.
    Name(String),
    /// Quoted literal: `lu ... li'u`.
    QuotedLiteral(String),
    /// Unspecified placeholder (zo'e or implicit).
    Unspecified,
    /// Place-tagged sumti: (zero-based place index 0..=4, inner-sumti-id).
    Tagged((u8, ArgumentId)),
    /// Modal-tagged sumti: (modal-tag, inner-sumti-id).
    ModalTagged((ModalTag, ArgumentId)),
    /// Argument with a relative clause: (inner-sumti-id, relative-clause).
    Restricted((ArgumentId, RelClause)),
    /// Number sumti: `li` + PA.
    Number(f64),
    /// Quantified description: PA lo/le selbri. Fields: (count, gadri, selbri-id).
    QuantifiedDescription((u32, Determiner, PredicateId)),
}

/// A selbri (predicate relation) in the AST.
#[derive(Clone, Debug)]
pub enum Predicate {
    /// Root brivla (gismu, lujvo, or fu'ivla).
    Root(String),
    /// Compound word from zei-gluing. Payload: list of component strings.
    Compound(Vec<String>),
    /// Modifier+head pair (a compound predicate). Fields: (modifier-id, head-id).
    Pair((PredicateId, PredicateId)),
    /// SE-converted selbri. Fields: (conversion, inner-id).
    Converted((Conversion, PredicateId)),
    /// Negated selbri (`na`). Payload: inner-id.
    Negated(PredicateId),
    /// Grouped selbri (`ke ... ke'e`). Payload: inner-id.
    Grouped(PredicateId),
    /// Predicate with be/bei arguments. Fields: (core-id, argument-sumti-ids).
    WithArgs((PredicateId, Vec<ArgumentId>)),
    /// Abstraction: nu/du'u/ka/ni/si'o + sentence. Fields: (kind, sentence-id).
    Abstraction((AbstractionKind, u32)),
}

/// Tense marker: past (pu), present (ca), future (ba).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Tense {
    Past,
    Now,
    Future,
}

/// Deontic deontic: ei (obligation/should), e'e (competence/permission/may).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DeonticMood {
    Obligation,
    Permission,
}

/// A bridi (predication): selbri + head terms + tail terms + modifiers.
#[derive(Clone, Debug)]
pub struct Proposition {
    pub relation: PredicateId,
    pub head_terms: Vec<ArgumentId>,
    pub tail_terms: Vec<ArgumentId>,
    pub negated: bool,
    pub tense: Option<Tense>,
    pub deontic: Option<DeonticMood>,
}

/// Sentence connective for sentence-level connection.
#[derive(Clone, Debug)]
pub enum SentenceConnective {
    /// Conditional (implication) sentence connective.
    Implies,
    /// Conjunctive (and) sentence connective.
    And,
    /// Afterthought connective between two sentences.
    Afterthought(Connective),
}

/// A sentence: a simple bridi, two connected sentences, or a prenex-quantified body.
#[derive(Clone, Debug)]
pub enum Sentence {
    /// Simple predication.
    Simple(Proposition),
    /// Connected sentences. Fields: (connective, left-sentence-id, right-sentence-id).
    Connected((SentenceConnective, u32, u32)),
    /// Prenex `ro da [ro de ...] zo'u <body>`: a sequence of universally
    /// quantified logic variables (`da`/`de`/`di`) scoping a body sentence.
    /// Fields: (variable names in prenex order, body-sentence-id). Lowers to
    /// nested `∀` over the body in smuni.
    Prenex((Vec<String>, u32)),
}

/// Flat AST buffer: parallel arrays indexed by u32 IDs.
#[derive(Clone, Debug)]
pub struct AstBuffer {
    pub predicates: Vec<Predicate>,
    pub arguments: Vec<Argument>,
    pub sentences: Vec<Sentence>,
    /// Root sentence indices (top-level sentences to compile).
    pub roots: Vec<u32>,
}

/// A per-sentence parse error with location context.
#[derive(Clone, Debug)]
pub struct ParseError {
    pub message: String,
    pub line: u32,
    pub column: u32,
}

/// Result of parsing: partial AST buffer + per-sentence errors.
#[derive(Clone, Debug)]
pub struct ParseResult {
    pub buffer: AstBuffer,
    pub errors: Vec<ParseError>,
}
