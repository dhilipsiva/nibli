//! AST types produced by the nibli-kr emitter — the INTERNAL interchange
//! between the front-end and the semantic compiler, NOT a WIT boundary.
//!
//! `AstBuffer` is produced by nibli-kr's validating emit walk and consumed by
//! `nibli_semantics::compile_from_ast` over a plain Rust function call; only
//! `logic.rs`'s `LogicBuffer` crosses the WASM component boundary. The type
//! lives HERE (not in nibli-kr) for three reasons:
//! - dependency direction: nibli-semantics must not depend on nibli-kr;
//! - it is render's INPUT: `nibli_kr::render` spells buffers back to KR text
//!   (the fixpoint / round-trip layer);
//! - it is the validated PROGRAMMATIC-BUILD target: hand-built buffers enter
//!   compilation through `validate_ast_buffer` (index-bounds + acyclicity —
//!   the "corrupt AST buffer" reject), so tools may construct ASTs directly.
//!
//! The flat shape — parallel `Predicate`/`Argument`/`Sentence` arrays with
//! `u32` child indices — is a WIT-era inheritance KEPT for properties that
//! are load-bearing today: `parse_text`'s per-statement recovery rolls a
//! failed statement back by truncating the four Vecs, and structural
//! validation is an iterative index-walk (no recursion to overflow on
//! adversarially deep inputs).

/// Index into the `predicates` array of an `AstBuffer`.
pub type PredicateId = u32;
/// Index into the `arguments` array of an `AstBuffer`.
pub type ArgumentId = u32;

/// Modal tag: a modal built from a predicate reference (the `via` tag) —
/// a newtype over the tagged predicate's id.
#[derive(Clone, Copy, Debug)]
pub struct ModalTag(pub PredicateId);

/// Place conversion: permutes the x1 place with another.
/// Swap12=x1↔x2, Swap13=x1↔x3, Swap14=x1↔x4, Swap15=x1↔x5.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Conversion {
    Swap12,
    Swap13,
    Swap14,
    Swap15,
}

/// Logical connective: AND(∧), OR(∨), IFF(↔), XOR(⊕).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Connective {
    And,
    Or,
    Iff,
    Xor,
}

/// Determiner (article/descriptor): determines how a description term binds.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Determiner {
    /// Indefinite description (at least one entity satisfying the predicate).
    Indefinite,
    /// Definite description (an opaque rigid designator).
    Definite,
    /// Universal over an indefinite description (`every X`).
    Every,
    /// Universal over a definite description (`every the X`).
    EveryThe,
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

/// A positional marker: not a constant — nibli-semantics consumes each as a
/// binding signal (`it` → the enclosing rel-clause's bound entity, `slot` →
/// the enclosing `property { … }`'s open place, `?` → a fresh witness
/// variable).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Marker {
    /// The relativized entity of a where/also clause body (`it`).
    It,
    /// The open place of a `property { … }` body (`slot`).
    Slot,
    /// The witness marker (`?`): binds a fresh variable per occurrence.
    Witness,
}

/// The fixed pronoun inventory — the closed set of pro-argument constants.
/// [`Pronoun::as_str`] is the SINGLE spelling authority (the emit walk
/// constructs from these spellings' keywords, render prints them, and
/// nibli-semantics interns them as constants); a conformance test pins every
/// spelling against nibli-lexicon's reserved-word list and the surface
/// round-trip.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Pronoun {
    Me,
    You,
    We,
    WeAll,
    WeOthers,
    YouAll,
    This,
    That,
    Yonder,
    ItA,
    ItE,
    ItI,
    ItO,
    ItU,
}

impl Pronoun {
    /// The canonical KR spelling — also the interned constant's identity.
    pub fn as_str(&self) -> &'static str {
        match self {
            Pronoun::Me => "me",
            Pronoun::You => "you",
            Pronoun::We => "we",
            Pronoun::WeAll => "we_all",
            Pronoun::WeOthers => "we_others",
            Pronoun::YouAll => "you_all",
            Pronoun::This => "this",
            Pronoun::That => "that",
            Pronoun::Yonder => "yonder",
            Pronoun::ItA => "it_a",
            Pronoun::ItE => "it_e",
            Pronoun::ItI => "it_i",
            Pronoun::ItO => "it_o",
            Pronoun::ItU => "it_u",
        }
    }

    /// Every variant, for conformance sweeps.
    pub const ALL: [Pronoun; 14] = [
        Pronoun::Me,
        Pronoun::You,
        Pronoun::We,
        Pronoun::WeAll,
        Pronoun::WeOthers,
        Pronoun::YouAll,
        Pronoun::This,
        Pronoun::That,
        Pronoun::Yonder,
        Pronoun::ItA,
        Pronoun::ItE,
        Pronoun::ItI,
        Pronoun::ItO,
        Pronoun::ItU,
    ];
}

/// A argument (argument term) in the AST.
#[derive(Clone, Debug)]
pub enum Argument {
    /// A `$`-sigiled logic variable, preserved VERBATIM (the sigil IS the
    /// variable signal all the way through the IR — the interner and the
    /// free-variable/scope passes key on the `$`-prefixed string, and proof
    /// traces display it). INVARIANT: the payload starts with `$`;
    /// `validate_ast_buffer` rejects a sigil-less payload as corrupt (a bare
    /// name here would silently become a free, never-closed IR variable).
    Variable(String),
    /// A positional marker consumed by nibli-semantics (never a constant):
    /// `it` (bound entity), `slot` (open place), `?` (witness).
    Marker(Marker),
    /// A fixed pronoun constant (me, you, we, we_all, …, it_u); lowers to an
    /// interned constant of its [`Pronoun::as_str`] spelling.
    Pronoun(Pronoun),
    /// Determiner description: `some`/`the` + predicate. Fields: (determiner, predicate-id).
    Description((Determiner, PredicateId)),
    /// Named entity: a capitalized rigid Name.
    Name(String),
    /// Quoted string literal: `"any text"`.
    QuotedLiteral(String),
    /// Unspecified placeholder (`_` or an omitted place).
    Unspecified,
    /// Place-tagged argument: (zero-based place index 0..=4, inner-argument-id).
    Tagged((u8, ArgumentId)),
    /// Modal-tagged argument: (modal-tag, inner-argument-id).
    ModalTagged((ModalTag, ArgumentId)),
    /// Argument with a relative clause: (inner-argument-id, relative-clause).
    Restricted((ArgumentId, RelClause)),
    /// Numeric literal argument.
    Number(f64),
    /// Quantified description: `exactly N` + determiner + predicate.
    /// Fields: (count, determiner, predicate-id).
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
    /// Grouped predicate (`[ ... ]` bracket group). Payload: inner-id.
    Grouped(PredicateId),
    /// Predicate with linked arguments. Fields: (core-id, argument-ids).
    WithArgs((PredicateId, Vec<ArgumentId>)),
    /// Abstraction: `event`/`fact`/`property`/`amount`/`concept` block.
    /// Fields: (kind, sentence-id).
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

/// A proposition (predication): predicate + argument terms + modifiers.
#[derive(Clone, Debug)]
pub struct Proposition {
    pub relation: PredicateId,
    /// All argument ids in EMISSION order: the explicit-x1 positional (when
    /// present) FIRST, then the remaining positionals/tagged/modal args.
    /// Consumers' place counters and surface-ordered scope markers depend on
    /// this order (the old head/tail split's chained order).
    pub terms: Vec<ArgumentId>,
    /// Whether an explicit untagged x1 positional was written — when true it
    /// is `terms[0]`. False ⇒ x1 is implicit: the rel-clause bound-entity
    /// injection point in nibli-semantics, and render's bare-sugar /
    /// inject-`it` spelling.
    pub x1_present: bool,
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

/// The quantifier kind of a [`Sentence::Quantified`] block.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BlockQuant {
    /// `exactly N X $v:` — exact-count over the indefinite restrictor.
    ExactCount(u32),
    /// `exactly N the X $v:` — exact-count over the opaque definite domain.
    ExactCountDefinite(u32),
    /// `every the X $v:` — universal over the opaque definite domain.
    UniversalDefinite,
}

/// A sentence: a simple proposition, two connected sentences, a
/// prenex-quantified body, or a quantified binder block.
#[derive(Clone, Debug)]
pub enum Sentence {
    /// Simple predication.
    Simple(Proposition),
    /// Connected sentences. Fields: (connective, left-sentence-id, right-sentence-id).
    Connected((SentenceConnective, u32, u32)),
    /// Prenex `all $x, $y: <body>`: a sequence of universally quantified
    /// logic variables scoping a body sentence. Fields: (variable names in
    /// prenex order, body-sentence-id). Lowers to nested `∀` over the body
    /// in nibli-semantics.
    Prenex((Vec<String>, u32)),
    /// Quantified binder block: `exactly N [the] X $v: body` / `every the X
    /// $v: body`. Fields: (kind, variable particle `$v`,
    /// restrictor-predicate-id, optional where-clause-sentence-id folded on
    /// the DOMAIN side, body-sentence-id). The variable binds by name across
    /// the whole block (the prenex mechanism); lowers to `Count{v, N,
    /// And(domain, body)}` / `ForAll(v, Or(Not(domain), body))` in
    /// nibli-semantics, where the definite kinds' domain is the opaque
    /// `the_domain_<head>` restrictor. (`the X $v:` blocks never reach the
    /// AST — they desugar by substitution at emission.)
    Quantified((BlockQuant, String, PredicateId, Option<u32>, u32)),
}

/// Flat AST buffer: parallel arrays indexed by u32 IDs — the
/// nibli-kr→nibli-semantics interchange and render's input (see the module
/// doc; never crosses WASM). Hand-built buffers are validated at the compile
/// boundary by `validate_ast_buffer`.
#[derive(Clone, Debug)]
pub struct AstBuffer {
    pub predicates: Vec<Predicate>,
    pub arguments: Vec<Argument>,
    pub sentences: Vec<Sentence>,
    /// Root sentence indices — one top-level sentence per statement.
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
