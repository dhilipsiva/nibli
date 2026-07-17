//! nibli KR tree AST — the parser's output, lowered to
//! `nibli_types::ast::AstBuffer` by the emitter (`emit.rs`).
//!
//! Owned `Box`/`Vec` nodes, deliberately NOT gerna's bumpalo arena: nibli KR
//! statements are small, and gerna's arena exists for its leak-free-by-invariant
//! fuzz discipline and whole-corpus REPL throughput — constraints that don't
//! bind here. If fuzzing ever shows allocation pressure, swapping the backing
//! store is internal to this crate.
//!
//! Shape invariants the parser guarantees (NIBLI_KR §6 + the 2026-07-12
//! errata):
//! - [`Claim::Prefixed`] exists only when at least one prefix is present, and
//!   its `atom` is a `Predication`, an `Equality`, or `Not` of one of those
//!   (`must past ~P` ≡ `Obligatory(Past(Not(P)))` — negation innermost,
//!   matching smuni's verified wrapper-emission order).
//! - [`Claim::Not`] wraps only a `Predication` or `Equality` (never another
//!   `Not`, never a prefixed or compound claim — those spellings are
//!   grammar-level rejects).
//! - [`Claim::Equality`] is binary by construction (n-ary `du` is
//!   inexpressible, not an error case).
//! - A `Full` relative-clause body contains at least one [`KeyTerm::It`]
//!   (mandatory-`it`, §7 — the implicit-ke'a ambiguity firewall as syntax).
//! - A [`RestrKind::Selected`] restrictor carries no linked args and its
//!   selector was written with no whitespace around the dot (O8 — keeps the
//!   place selector from colliding with the statement terminator).

use std::ops::Range;

/// One `.`-terminated statement — one independent fact (the bare-`.i` split).
#[derive(Debug, Clone, PartialEq)]
pub struct Statement {
    pub claim: Claim,
    /// Byte span from the first token to the terminating `.`.
    pub span: Range<usize>,
}

/// A claim tree. Operator chains associate as the parser builds them:
/// `&`/`|`/`^`/`<->` left-fold, `->` right-recursive.
#[derive(Debug, Clone, PartialEq)]
pub enum Claim {
    /// `all $x, $y: C` — prenex universals; ForAll wraps the body DIRECTLY
    /// (the non-rule shape, distinct from `every`).
    Prenex { vars: Vec<String>, body: Box<Claim> },
    /// `every dog $d: C` — named-binder block determiner (emission shape is
    /// spec issue O7, pinned at the emitter).
    DetBlock {
        det: Det,
        restr: Restr,
        var: String,
        body: Box<Claim>,
    },
    /// `A -> B` — material implication (`ganai…gi` / `.inaja`).
    Impl(Box<Claim>, Box<Claim>),
    /// `A <-> B` — biconditional (`jo`).
    Iff(Box<Claim>, Box<Claim>),
    /// `A ^ B` — exclusive or (`ju`).
    Xor(Box<Claim>, Box<Claim>),
    /// `A | B` — disjunction (`ja`).
    Or(Box<Claim>, Box<Claim>),
    /// `A & B` — conjunction (`je`).
    And(Box<Claim>, Box<Claim>),
    /// `~A` — negation (`na`). Operand is a `Predication`/`Equality` only.
    Not(Box<Claim>),
    /// Tense/deontic prefixes (`must past P`). Present only when at least one
    /// prefix is set; `atom` is `Predication`/`Equality`, optionally under
    /// `Not` (`past ~P`).
    Prefixed {
        deontic: Option<Deontic>,
        tense: Option<Tense>,
        atom: Box<Claim>,
    },
    /// `a = b` — du identity (union-find), binary only.
    Equality(Term, Term),
    /// `pred(args…) via tag(t)…`.
    Predication(Predication),
}

/// `must` (`.ei` → Obligatory) / `may` (`.e'e` → Permitted).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Deontic {
    Must,
    May,
}

/// `past`/`now`/`future` (`pu`/`ca`/`ba`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tense {
    Past,
    Now,
    Future,
}

/// A predicate application. The head is a [`PredSeq`] (a single word, or a
/// pair of 2+ units whose LAST unit is the head); resolution against
/// nibli-lexicon happens in the resolve pass.
#[derive(Debug, Clone, PartialEq)]
pub struct Predication {
    pub seq: PredSeq,
    pub args: Vec<Arg>,
    /// `via` modal tags (BAI/fi'o — NIBLI_KR §5), in surface order.
    pub tags: Vec<Tag>,
    pub span: Range<usize>,
}

/// A pair: one or more units, right-grouping, LAST unit is the head
/// (arity/name source).
#[derive(Debug, Clone, PartialEq)]
pub struct PredSeq(pub Vec<PredUnit>);

/// One pair unit: a (possibly compound `a+b`) word, or a bracket group.
#[derive(Debug, Clone, PartialEq)]
pub enum PredUnit {
    /// `a` or `a+b+c` — compound parts in order. Multi-part spellings resolve
    /// ONLY via a committed corpus CompoundEntry (NIBLI_KR §5) — resolve/emit
    /// join the parts with `+`, never compile under the last part.
    Word(Vec<String>),
    /// `[ big fast ]` — explicit grouping (ke…ke'e).
    Group(PredSeq),
}

impl PredSeq {
    /// The last SINGLE word of the head unit, descending through bracket
    /// groups — a display convenience (lint messages). NOT the resolution
    /// head for multi-part units: those resolve as compound entries
    /// (resolve's `seq` / emit's `resolved_head`).
    pub fn head_word(&self) -> &str {
        match self.0.last().expect("pred_seq is non-empty") {
            PredUnit::Word(parts) => parts.last().expect("pred_name is non-empty"),
            PredUnit::Group(inner) => inner.head_word(),
        }
    }
}

/// `via pred(term)` — a modal tag.
#[derive(Debug, Clone, PartialEq)]
pub struct Tag {
    /// The modal predicate (compound parts, like a [`PredUnit::Word`]).
    pub pred: Vec<String>,
    pub term: Term,
    pub span: Range<usize>,
}

/// One argument: positional (`label: None`) or named. The parser enforces
/// positionals-before-named; label→place resolution is the resolve pass.
#[derive(Debug, Clone, PartialEq)]
pub struct Arg {
    pub label: Option<String>,
    pub term: Term,
    pub span: Range<usize>,
}

/// A term (NIBLI_KR §3).
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// `_` — explicit unspecified place (zo'e).
    Unspecified,
    /// `?` — anonymous independent witness (ma).
    Witness,
    Number(f64),
    Str(String),
    /// `$x` — logic variable (name without the sigil).
    Var(String),
    /// Reserved pro-term (`me`, `you`, `it`, `slot`, …). `it`/`slot` position
    /// checks happen in the resolve pass.
    Key(KeyTerm),
    /// Capitalized rigid name (la), with optional relative clauses
    /// (`Adam where dog`). Lowercasing/`_`→space happens at emission.
    Name {
        name: String,
        rel_clauses: Vec<RelClause>,
    },
    /// `event { … }` / `fact { … }` / `property { … }` / `amount { … }` /
    /// `concept { … }` — opaque abstraction (implicit-`some` description).
    Abstraction {
        kind: AbsKind,
        body: Box<Claim>,
    },
    /// Determiner phrase: `some dog`, `every the market`, `exactly 2 red`.
    Det {
        det: Det,
        restr: Restr,
    },
}

/// `nu` / `du'u` / `ka` / `ni` / `si'o`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbsKind {
    Event,
    Fact,
    Property,
    Amount,
    Concept,
}

/// The reserved pro-terms (NIBLI_KR §3 table).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeyTerm {
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
    /// `it` — the relativized entity (ke'a): legal only inside rel-clause
    /// bodies and as a NAMED bound-place marker in restr linked args.
    It,
    /// `slot` — the ka open place (ce'u): legal only inside `property { }`.
    Slot,
}

/// The determiner taxonomy (NIBLI_KR §4) — five gadri shapes plus the
/// `no` = exactly-0 sugar, resolved at parse time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Det {
    /// `some` — lo, veridical ∃.
    Some,
    /// `the` — le, opaque rigid designator (NO quantifier).
    The,
    /// `every` — ro lo, the rule shape.
    Every,
    /// `every the` — ro le.
    EveryThe,
    /// `exactly N` — PA lo, CountNode (`no X` parses as `Exactly(0)`).
    Exactly(u32),
    /// `exactly N the` — PA le.
    ExactlyThe(u32),
}

/// A restrictor (NIBLI_KR §4).
#[derive(Debug, Clone, PartialEq)]
pub struct Restr {
    /// `~` before the restrictor — description-inner negation (`lo na broda`).
    pub negated: bool,
    pub kind: RestrKind,
    /// `where` (restrictive) / `also` (incidental) clauses, in surface order.
    pub rel_clauses: Vec<RelClause>,
    pub span: Range<usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RestrKind {
    /// A pair restrictor, optionally with linked args (`carer(of: some data)`
    /// — be/bei; the bound variable takes x1 unless a named `it` marks its
    /// place).
    Seq { seq: PredSeq, linked_args: Vec<Arg> },
    /// `loves.loved` — place selector: the bound variable sits at the place
    /// named by `label` (the se-family). Single word, dot-adjacent, no linked
    /// args (O8).
    Selected { pred: String, label: String },
}

/// `where <body>` (poi — domain side) / `also <body>` (noi — matrix side).
#[derive(Debug, Clone, PartialEq)]
pub struct RelClause {
    pub kind: RelKind,
    pub body: ClauseBody,
    pub span: Range<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelKind {
    Where,
    Also,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ClauseBody {
    /// Bare-predicate sugar: `where consents` ≡ `where consents(it)`;
    /// `where ~cat` ≡ `where ~cat(it)`. A bare pair is ONE shared-event
    /// predicate on `it` (`where big fast` — lint L2 territory).
    Bare { negated: bool, seq: PredSeq },
    /// A full claim; must contain `it` (mandatory-`it`, enforced at parse).
    Full(Box<Claim>),
}
