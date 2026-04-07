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
    /// First argument place (x1).
    Fa,
    /// Second argument place (x2).
    Fe,
    /// Third argument place (x3).
    Fi,
    /// Fourth argument place (x4).
    Fo,
    /// Fifth argument place (x5).
    Fu,
}

impl PlaceTag {
    /// Convert this place tag to a zero-based argument index (fa=0, fe=1, ...).
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
    /// ri'a: causal tag (from gismu rinka).
    Ria,
    /// ni'i: logical entailment tag (from gismu nibli).
    Nii,
    /// mu'i: motivation tag (from gismu mukti).
    Mui,
    /// ki'u: reason tag (from gismu krinu).
    Kiu,
    /// pi'o: instrument tag (from gismu pilno).
    Pio,
    /// ba'i: replacement tag (from gismu basti).
    Bai,
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
    /// Swap x1 and x2.
    Se,
    /// Swap x1 and x3.
    Te,
    /// Swap x1 and x4.
    Ve,
    /// Swap x1 and x5.
    Xe,
}

/// Logical connective between selbri or sumti
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Connective {
    /// Logical AND (conjunction).
    Je,
    /// Logical OR (disjunction).
    Ja,
    /// Logical IFF (biconditional).
    Jo,
    /// Logical XOR (exclusive or).
    Ju,
}

/// Gadri (descriptor) type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Gadri {
    /// Veridical existential description (lo).
    Lo,
    /// Non-veridical opaque reference (le).
    Le,
    /// Named entity / proper name (la).
    La,
    /// Universal veridical quantifier (ro lo).
    RoLo,
    /// Universal referential quantifier (ro le).
    RoLe,
}

/// Relative clause type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelClauseKind {
    /// Restrictive (intersective) relative clause.
    Poi,
    /// Non-restrictive (appositive) relative clause.
    Noi,
    /// Non-veridical restrictive relative clause.
    Voi,
}

/// Abstraction type: which NU-class cmavo introduced this abstraction
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbstractionKind {
    /// Event or state abstraction (nu).
    Nu,
    /// Propositional abstraction (du'u).
    Duhu,
    /// Property abstraction (ka), may contain ce'u.
    Ka,
    /// Quantity or amount abstraction (ni).
    Ni,
    /// Concept or idea abstraction (si'o).
    Siho,
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
    /// Whether this is a poi, noi, or voi clause.
    pub kind: RelClauseKind,
    /// The sentence forming the body of the relative clause.
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
    WithArgs {
        core: &'a Selbri<'a>,
        args: Vec<Sumti<'a>>,
    },

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
    /// Past tense.
    Pu,
    /// Present tense.
    Ca,
    /// Future tense.
    Ba,
}

/// Deontic attitudinal marker (UI selma'o subset)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Attitudinal {
    /// Obligation (should).
    Ei,
    /// Competence or permission (may).
    Ehe,
}

/// A single bridi (predication).
#[derive(Debug, Clone, PartialEq)]
pub struct Bridi<'a> {
    /// The main predicate relation of this bridi.
    pub selbri: Selbri<'a>,
    /// Terms appearing before the selbri (separated by `cu`).
    pub head_terms: Vec<Sumti<'a>>,
    /// Terms appearing after the selbri.
    pub tail_terms: Vec<Sumti<'a>>,
    /// Whether sentence-level `na` negation is present.
    pub negated: bool,
    /// Optional tense marker (pu/ca/ba).
    pub tense: Option<Tense>,
    /// Optional deontic attitudinal (ei/e'e).
    pub attitudinal: Option<Attitudinal>,
}

#[derive(Debug, Clone, PartialEq)]
/// A parsed Lojban sentence: either a simple bridi or two sentences joined by a connective.
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
/// Connective joining two sentences (forethought or afterthought).
pub enum SentenceConnective {
    /// Forethought implication: ganai ... gi ...
    GanaiGi,
    /// Forethought conjunction: ge ... gi ... (AND)
    GeGi,
    /// Forethought disjunction: ga ... gi ... (OR)
    GaGi,
    /// Afterthought: .i [na] (je|ja|jo|ju) [nai]
    Afterthought {
        left_negated: bool,
        connective: Connective,
        right_negated: bool,
    },
}

// Update ParsedText to hold recursive Sentences, not flat Bridis
#[derive(Debug)]
/// Top-level parse result: the list of sentences produced by the parser.
pub struct ParsedText<'a> {
    /// The sequence of top-level sentences parsed from the input text.
    pub sentences: Vec<Sentence<'a>>,
}
