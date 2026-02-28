//! Lojban abstract syntax tree types.
//!
//! Arena-allocated (`bumpalo`) AST nodes produced by the recursive-descent parser.
//! All tree references use `&'arena T` instead of `Box<T>`, batching allocations
//! into contiguous arena chunks and freeing them in one shot after flattening.
//!
//! Covers Lojban constructs:
//!   - `.i` sentence separator, `fa`/`fe`/`fi`/`fo`/`fu` place tags
//!   - `na`/`naku` negation, `poi`/`noi`/`voi` relative clauses
//!   - `be`/`bei` sumti raising, `ke`/`ke'e` tanru grouping
//!   - `je`/`ja`/`jo`/`ju` connectives, `se`/`te`/`ve`/`xe` conversion
//!   - `lo`/`le`/`la` gadri, `ro` universal quantifier, numeric quantifiers
//!   - Abstractions (`nu`/`du'u`/`ka`/`ni`/`si'o`), tense (`pu`/`ca`/`ba`)
//!   - Deontic attitudinals (`ei`/`e'e`), quoted literals, number sumti

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

/// BAI cmavo: modal tags derived from underlying gismu
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BaiTag {
    Ria, // ri'a → rinka (cause)
    Nii, // ni'i → nibli (logical entailment)
    Mui, // mu'i → mukti (motivation)
    Kiu, // ki'u → krinu (reason)
    Pio, // pi'o → pilno (tool/use)
    Bai, // ba'i → basti (replace)
}

/// Modal tag: either a fixed BAI shortcut or a fi'o-based custom tag
#[derive(Debug, Clone, PartialEq)]
pub enum ModalTag<'a> {
    /// Fixed BAI cmavo (ri'a, ni'i, etc.)
    Fixed(BaiTag),
    /// Generic modal: fi'o + selbri [+ fe'u]
    Fio(&'a Selbri<'a>),
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
    Voi, // non-veridical restrictive
}

/// Abstraction type: which NU-class cmavo introduced this abstraction
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbstractionKind {
    Nu,   // event/state
    Duhu, // proposition (du'u)
    Ka,   // property (ka) — may contain ce'u
    Ni,   // quantity/amount
    Siho, // concept/idea (si'o)
}

// ─── Core AST nodes ──────────────────────────────────────────────

/// A term (argument slot) in a bridi.
#[derive(Debug, Clone, PartialEq)]
pub enum Sumti<'a> {
    /// Pro-sumti: mi, do, ko'a..ko'u, da/de/di, ti/ta/tu, ri/ra/ru, etc.
    ProSumti(String),

    /// Gadri-description: lo/le/la/ro lo/ro le + selbri [+ ku]
    Description { gadri: Gadri, inner: &'a Selbri<'a> },

    /// la + cmevla name(s)
    Name(String),

    /// Quoted literal (from zo/zoi)
    QuotedLiteral(String),

    /// Explicit unspecified: zo'e
    Unspecified,

    /// Place-tagged sumti: fa/fe/fi/fo/fu + sumti
    Tagged(PlaceTag, &'a Sumti<'a>),

    /// Modal-tagged sumti: BAI tag or fi'o + sumti
    /// Creates a conjoined modal predication rather than filling a place
    ModalTagged(ModalTag<'a>, &'a Sumti<'a>),

    /// Sumti with relative clause: sumti + (poi|noi) sentence [ku'o]
    Restricted {
        inner: &'a Sumti<'a>,
        clause: RelClause<'a>,
    },
    /// Numeric literal: li + PA digits
    Number(f64),

    /// Sumti connective: sumti + (.e|.a|.o|.u)[nai] + sumti
    /// Maps: .e→Je (∧), .a→Ja (∨), .o→Jo (↔), .u→Ju (⊕)
    Connected {
        left: &'a Sumti<'a>,
        connective: Connective,
        /// If true, the RIGHT operand is negated (the `nai` suffix)
        right_negated: bool,
        right: &'a Sumti<'a>,
    },

    /// Numeric quantifier + description: <PA> lo/le selbri [ku]
    /// "re lo gerku" = exactly 2 dogs
    QuantifiedDescription {
        count: u32,
        gadri: Gadri,
        inner: &'a Selbri<'a>,
    },
}

/// A relative clause attached to a sumti.
#[derive(Debug, Clone, PartialEq)]
pub struct RelClause<'a> {
    pub kind: RelClauseKind,
    pub body: &'a Sentence<'a>,
}

/// The main predicate/relation in a bridi.
#[derive(Debug, Clone, PartialEq)]
pub enum Selbri<'a> {
    /// Single root word (gismu or lujvo)
    Root(String),

    /// Compound (lujvo rafsi sequence from zei-gluing)
    Compound(Vec<String>),

    /// Tanru: modifier + head (right-grouping)
    /// e.g., "sutra gerku" → Tanru(Root("sutra"), Root("gerku"))
    Tanru(&'a Selbri<'a>, &'a Selbri<'a>),

    /// SE-conversion: se/te/ve/xe + selbri
    Converted(Conversion, &'a Selbri<'a>),

    /// Bridi negation: na + selbri
    Negated(&'a Selbri<'a>),

    /// Explicit grouping: ke + selbri + [ke'e]
    Grouped(&'a Selbri<'a>),

    /// Selbri with bound arguments: selbri + be sumti (bei sumti)* [be'o]
    WithArgs { core: &'a Selbri<'a>, args: Vec<Sumti<'a>> },

    /// Selbri connective: selbri + (je|ja|jo|ju) + selbri
    Connected {
        left: &'a Selbri<'a>,
        connective: Connective,
        right: &'a Selbri<'a>,
    },

    /// Abstraction: (nu|du'u|ka|ni|si'o) + bridi [+ kei]
    /// Reifies a proposition/event/property/quantity/concept as a 1-place selbri.
    Abstraction(AbstractionKind, &'a Sentence<'a>),
}

/// Tense marker (PU selma'o)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tense {
    Pu, // past
    Ca, // present
    Ba, // future
}

/// Deontic attitudinal marker (UI selma'o subset)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Attitudinal {
    Ei,  // obligation (should)
    Ehe, // competence/permission (may)
}

/// A single bridi (predication).
#[derive(Debug, Clone, PartialEq)]
pub struct Bridi<'a> {
    pub selbri: Selbri<'a>,
    pub head_terms: Vec<Sumti<'a>>, // terms before selbri (cu-separated)
    pub tail_terms: Vec<Sumti<'a>>, // terms after selbri
    pub negated: bool,              // sentence-level na (before all terms)
    pub tense: Option<Tense>,
    pub attitudinal: Option<Attitudinal>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Sentence<'a> {
    /// A single, simple predicate relationship
    Simple(Bridi<'a>),
    /// Forethought connection: (Connective, Left Sentence, Right Sentence)
    /// Example: ganai A gi B -> Connected(Implies, A, B)
    Connected {
        connective: SentenceConnective, // New enum for gi'i, ganai, etc.
        left: &'a Sentence<'a>,
        right: &'a Sentence<'a>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SentenceConnective {
    GanaiGi, // Implication: ganai ... gi ...
    GeGi,    // Conjunction: ge ... gi ... (AND)
    GaGi,    // Disjunction: ga ... gi ... (OR)
    /// Afterthought: .i [na] (je|ja|jo|ju) [nai]
    Afterthought {
        left_negated: bool,
        connective: Connective,
        right_negated: bool,
    },
}

// Update ParsedText to hold recursive Sentences, not flat Bridis
#[derive(Debug)]
pub struct ParsedText<'a> {
    pub sentences: Vec<Sentence<'a>>,
}
