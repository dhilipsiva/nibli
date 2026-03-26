//! AST types produced by the gerna parser.
//!
//! Flat index-based representation: `AstBuffer` contains parallel arrays of
//! `Selbri`, `Sumti`, and `Sentence` nodes, referenced by `u32` indices.

/// Index into the `selbris` array of an `AstBuffer`.
pub type SelbriId = u32;
/// Index into the `sumtis` array of an `AstBuffer`.
pub type SumtiId = u32;

/// Explicit argument-place tag (FA selma'o): fa=x1, fe=x2, fi=x3, fo=x4, fu=x5.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PlaceTag {
    Fa,
    Fe,
    Fi,
    Fo,
    Fu,
}

/// BAI modal tag — each maps to an underlying gismu:
/// ri'a=rinka (cause), ni'i=nibli (entailment), mu'i=mukti (motivation),
/// ki'u=krinu (reason), pi'o=pilno (tool), ba'i=basti (replace).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BaiTag {
    Ria,
    Nii,
    Mui,
    Kiu,
    Pio,
    Bai,
}

/// Modal tag: either a fixed BAI shortcut or a fi'o custom modal.
#[derive(Clone, Copy, Debug)]
pub enum ModalTag {
    /// One of the six built-in BAI cmavo.
    Fixed(BaiTag),
    /// fi'o + selbri [+ fe'u]: user-defined modal via a selbri reference.
    Fio(SelbriId),
}

/// SE-series conversion: permutes the x1 place with another.
/// se=x1↔x2, te=x1↔x3, ve=x1↔x4, xe=x1↔x5.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Conversion {
    Se,
    Te,
    Ve,
    Xe,
}

/// Logical connective shared by selbri and sumti connectives.
/// je=AND(∧), ja=OR(∨), jo=IFF(↔), ju=XOR(⊕).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Connective {
    Je,
    Ja,
    Jo,
    Ju,
}

/// Gadri (article/descriptor): determines how a description term binds.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Gadri {
    /// `lo` — veridical description (at least one entity satisfying the selbri).
    Lo,
    /// `le` — non-veridical description (opaque rigid designator).
    Le,
    /// `la` — name gadri (proper name).
    La,
    /// `lo` in a universal scope (`ro lo`).
    LoUniversal,
    /// `le` in a universal scope (`ro le`).
    LeUniversal,
}

/// Abstraction kind: wraps a sub-sentence into a sumti.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AbstractionKind {
    /// `nu` — event abstraction.
    Nu,
    /// `du'u` — propositional abstraction.
    Duhu,
    /// `ka` — property abstraction (with ce'u).
    Ka,
    /// `ni` — quantity/amount abstraction.
    Ni,
    /// `si'o` — concept abstraction.
    Siho,
}

/// Relative clause kind: restrictive, non-restrictive, or voi.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RelClauseKind {
    /// `poi` — restrictive relative clause.
    Poi,
    /// `noi` — non-restrictive (incidental) relative clause.
    Noi,
    /// `voi` — restrictive relative clause (designating).
    Voi,
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
pub enum Sumti {
    /// Pro-sumti: mi, do, da, de, di, ti, ta, tu, ke'a, ma, ko, etc.
    ProSumti(String),
    /// Gadri description: `lo/le` + selbri. Fields: (gadri, selbri-id).
    Description((Gadri, SelbriId)),
    /// Named entity: `la` + cmevla.
    Name(String),
    /// Quoted literal: `lu ... li'u`.
    QuotedLiteral(String),
    /// Unspecified placeholder (zo'e or implicit).
    Unspecified,
    /// Place-tagged sumti: (tag, inner-sumti-id).
    Tagged((PlaceTag, SumtiId)),
    /// Modal-tagged sumti: (modal-tag, inner-sumti-id).
    ModalTagged((ModalTag, SumtiId)),
    /// Sumti with a relative clause: (inner-sumti-id, relative-clause).
    Restricted((SumtiId, RelClause)),
    /// Number sumti: `li` + PA.
    Number(f64),
    /// Connected sumti: left .e/.a/.o/.u [nai] right.
    /// Fields: (left-id, connective, nai-flag, right-id).
    Connected((SumtiId, Connective, bool, SumtiId)),
    /// Quantified description: PA lo/le selbri. Fields: (count, gadri, selbri-id).
    QuantifiedDescription((u32, Gadri, SelbriId)),
}

/// A selbri (predicate relation) in the AST.
#[derive(Clone, Debug)]
pub enum Selbri {
    /// Root brivla (gismu, lujvo, or fu'ivla).
    Root(String),
    /// Compound brivla (zei-lujvo).
    Compound(String),
    /// Tanru: modifier + head. Fields: (modifier-id, head-id).
    Tanru((SelbriId, SelbriId)),
    /// SE-converted selbri. Fields: (conversion, inner-id).
    Converted((Conversion, SelbriId)),
    /// Negated selbri (`na`). Payload: inner-id.
    Negated(SelbriId),
    /// Grouped selbri (`ke ... ke'e`). Payload: inner-id.
    Grouped(SelbriId),
    /// Selbri with be/bei arguments. Fields: (core-id, argument-sumti-ids).
    WithArgs((SelbriId, Vec<SumtiId>)),
    /// Connected selbri: left je/ja/jo/ju right. Fields: (left-id, connective, right-id).
    Connected((SelbriId, Connective, SelbriId)),
    /// Abstraction: nu/du'u/ka/ni/si'o + sentence. Fields: (kind, sentence-id).
    Abstraction((AbstractionKind, u32)),
}

/// Tense marker: past (pu), present (ca), future (ba).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Tense {
    Pu,
    Ca,
    Ba,
}

/// Deontic attitudinal: ei (obligation/should), e'e (competence/permission/may).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Attitudinal {
    Ei,
    Ehe,
}

/// A bridi (predication): selbri + head terms + tail terms + modifiers.
#[derive(Clone, Debug)]
pub struct Bridi {
    pub relation: SelbriId,
    pub head_terms: Vec<SumtiId>,
    pub tail_terms: Vec<SumtiId>,
    pub negated: bool,
    pub tense: Option<Tense>,
    pub attitudinal: Option<Attitudinal>,
}

/// Sentence connective for forethought/afterthought sentence-level connection.
#[derive(Clone, Debug)]
pub enum SentenceConnective {
    /// `ganai ... gi` — conditional.
    GanaiGi,
    /// `ge ... gi` — conjunctive (and).
    GeGi,
    /// `ga ... gi` — disjunctive (or).
    GaGi,
    /// `.i` + afterthought connective: (connective, na-flag, nai-flag).
    Afterthought((Connective, bool, bool)),
}

/// A sentence: either a simple bridi or two connected sentences.
#[derive(Clone, Debug)]
pub enum Sentence {
    /// Simple predication.
    Simple(Bridi),
    /// Connected sentences. Fields: (connective, left-sentence-id, right-sentence-id).
    Connected((SentenceConnective, u32, u32)),
}

/// Flat AST buffer: parallel arrays indexed by u32 IDs.
#[derive(Clone, Debug)]
pub struct AstBuffer {
    pub selbris: Vec<Selbri>,
    pub sumtis: Vec<Sumti>,
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
