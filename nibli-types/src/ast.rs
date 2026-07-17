//! AST types produced by the nibli-kr emitter.
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

/// Logical connective shared by predicate and argument connectives.
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

/// Abstraction kind: wraps a sub-sentence into a argument.
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

/// A relative clause attached to a argument.
#[derive(Clone, Debug)]
pub struct RelClause {
    pub kind: RelClauseKind,
    /// Index into the `sentences` array of the containing `AstBuffer`.
    pub body_sentence: u32,
}

/// A argument (argument term) in the AST.
#[derive(Clone, Debug)]
pub enum Argument {
    /// Pro-argument: me, you, this, that, yonder, it_a…it_u, `$vars`, plus the
    /// markers `it` (bound entity), `slot` (open place), and `?` (witness).
    Pronoun(String),
    /// Determiner description: `lo/le` + predicate. Fields: (determiner, predicate-id).
    Description((Determiner, PredicateId)),
    /// Named entity: a capitalized rigid Name.
    Name(String),
    /// Quoted literal: `lu ... li'u`.
    QuotedLiteral(String),
    /// Unspecified placeholder (zo'e or implicit).
    Unspecified,
    /// Place-tagged argument: (zero-based place index 0..=4, inner-argument-id).
    Tagged((u8, ArgumentId)),
    /// Modal-tagged argument: (modal-tag, inner-argument-id).
    ModalTagged((ModalTag, ArgumentId)),
    /// Argument with a relative clause: (inner-argument-id, relative-clause).
    Restricted((ArgumentId, RelClause)),
    /// Number argument: `li` + PA.
    Number(f64),
    /// Quantified description: PA lo/le predicate. Fields: (count, determiner, predicate-id).
    QuantifiedDescription((u32, Determiner, PredicateId)),
}

/// A predicate (predicate relation) in the AST.
#[derive(Clone, Debug)]
pub enum Predicate {
    /// Root relation: an atomic corpus name, or a compound entry's relation
    /// ident (`computer_user`) — compounds resolve to their entry BEFORE
    /// emission, so no compound structure survives into the AST.
    Root(String),
    /// Modifier+head pair (a compound predicate). Fields: (modifier-id, head-id).
    Pair((PredicateId, PredicateId)),
    /// SE-converted predicate. Fields: (conversion, inner-id).
    Converted((Conversion, PredicateId)),
    /// Negated predicate (`na`). Payload: inner-id.
    Negated(PredicateId),
    /// Grouped predicate (`ke ... ke'e`). Payload: inner-id.
    Grouped(PredicateId),
    /// Predicate with be/bei arguments. Fields: (core-id, argument-argument-ids).
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

/// A proposition (predication): predicate + head terms + tail terms + modifiers.
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

/// A sentence: a simple proposition, two connected sentences, or a prenex-quantified body.
#[derive(Clone, Debug)]
pub enum Sentence {
    /// Simple predication.
    Simple(Proposition),
    /// Connected sentences. Fields: (connective, left-sentence-id, right-sentence-id).
    Connected((SentenceConnective, u32, u32)),
    /// Prenex `ro da [ro de ...] zo'u <body>`: a sequence of universally
    /// quantified logic variables (`da`/`de`/`di`) scoping a body sentence.
    /// Fields: (variable names in prenex order, body-sentence-id). Lowers to
    /// nested `∀` over the body in nibli-semantics.
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
