// parser/src/ast.rs — Lojban AST types
//
// Covers I6 constructs:
//   1. .i sentence separator
//   2. fa/fe/fi/fo/fu place tags
//   3. na/naku negation
//   4. poi/noi relative clauses
//   5. be/bei sumti raising
//   6. ke/ke'e tanru grouping
//   7. je/ja/jo/ju connectives
//   8. ku/vau/ku'o/kei terminators
// Plus: se/te/ve/xe conversion, lo/le/la gadri, ro quantifier, extended pro-sumti

// ─── Enums for grammatical markers ───────────────────────────────

/// Place-tag cmavo: explicit argument position
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlaceTag {
    Fa, // x1
    Fe, // x2
    Fi, // x3
    Fo, // x4
    Fu, // x5
}

impl PlaceTag {
    pub fn to_index(self) -> usize {
        match self {
            PlaceTag::Fa => 0,
            PlaceTag::Fe => 1,
            PlaceTag::Fi => 2,
            PlaceTag::Fo => 3,
            PlaceTag::Fu => 4,
        }
    }
}

/// SE-series conversion: permutes argument places
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Conversion {
    Se, // swap x1 ↔ x2
    Te, // swap x1 ↔ x3
    Ve, // swap x1 ↔ x4
    Xe, // swap x1 ↔ x5
}

/// Logical connective between selbri or sumti
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Connective {
    Je, // AND (∧)
    Ja, // OR  (∨)
    Jo, // IFF (↔)
    Ju, // XOR (⊕)
}

/// Gadri (descriptor) type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Gadri {
    Lo,   // veridical description (∃ in FOL)
    Le,   // non-veridical reference (specific referent)
    La,   // named entity (proper name)
    RoLo, // universal veridical (∀ in FOL): ro lo
    RoLe, // universal referential (∀ over specific set): ro le
}

/// Relative clause type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelClauseKind {
    Poi, // restrictive (intersective)
    Noi, // non-restrictive (appositive)
}

// ─── Core AST nodes ──────────────────────────────────────────────

/// A term (argument slot) in a bridi.
#[derive(Debug, Clone, PartialEq)]
pub enum Sumti {
    /// Pro-sumti: mi, do, ko'a..ko'u, da/de/di, ti/ta/tu, ri/ra/ru, etc.
    ProSumti(String),

    /// Gadri-description: lo/le/la/ro lo/ro le + selbri [+ ku]
    Description { gadri: Gadri, inner: Box<Selbri> },

    /// la + cmevla name(s)
    Name(String),

    /// Quoted literal (from zo/zoi)
    QuotedLiteral(String),

    /// Explicit unspecified: zo'e
    Unspecified,

    /// Place-tagged sumti: fa/fe/fi/fo/fu + sumti
    Tagged(PlaceTag, Box<Sumti>),

    /// Sumti with relative clause: sumti + (poi|noi) sentence [ku'o]
    Restricted {
        inner: Box<Sumti>,
        clause: RelClause,
    },
}

/// A relative clause attached to a sumti.
#[derive(Debug, Clone, PartialEq)]
pub struct RelClause {
    pub kind: RelClauseKind,
    pub body: Box<Bridi>,
}

/// The main predicate/relation in a bridi.
#[derive(Debug, Clone, PartialEq)]
pub enum Selbri {
    /// Single root word (gismu or lujvo)
    Root(String),

    /// Compound (lujvo rafsi sequence from zei-gluing)
    Compound(Vec<String>),

    /// Tanru: modifier + head (right-grouping)
    /// e.g., "sutra gerku" → Tanru(Root("sutra"), Root("gerku"))
    Tanru(Box<Selbri>, Box<Selbri>),

    /// SE-conversion: se/te/ve/xe + selbri
    Converted(Conversion, Box<Selbri>),

    /// Bridi negation: na + selbri
    Negated(Box<Selbri>),

    /// Explicit grouping: ke + selbri + [ke'e]
    Grouped(Box<Selbri>),

    /// Selbri with bound arguments: selbri + be sumti (bei sumti)* [be'o]
    WithArgs { core: Box<Selbri>, args: Vec<Sumti> },

    /// Selbri connective: selbri + (je|ja|jo|ju) + selbri
    Connected {
        left: Box<Selbri>,
        connective: Connective,
        right: Box<Selbri>,
    },

    /// Abstraction: nu + bridi [+ kei]
    /// Reifies a proposition/event as a 1-place selbri (x1 is the event).
    Abstraction(Box<Bridi>),
}

/// Tense marker (PU selma'o)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tense {
    Pu, // past
    Ca, // present
    Ba, // future
}

/// A single bridi (predication).
#[derive(Debug, Clone, PartialEq)]
pub struct Bridi {
    pub selbri: Selbri,
    pub head_terms: Vec<Sumti>, // terms before selbri (cu-separated)
    pub tail_terms: Vec<Sumti>, // terms after selbri
    pub negated: bool,          // sentence-level na (before all terms)
    pub tense: Option<Tense>,
}

/// A complete parsed text: one or more sentences.
#[derive(Debug, Clone, PartialEq)]
pub struct ParsedText {
    pub sentences: Vec<Bridi>,
}
