//! Klaro tree AST — the parser's output, later lowered to
//! `nibli_types::ast::AstBuffer` by the emitter (a subsequent KLARO_TODO
//! bullet).
//!
//! Owned `Box`/`Vec` nodes, deliberately NOT gerna's bumpalo arena: Klaro
//! statements are small, and gerna's arena exists for its leak-free-by-invariant
//! fuzz discipline and whole-corpus REPL throughput — constraints that don't
//! bind here. If fuzzing ever shows allocation pressure, swapping the backing
//! store is internal to this crate.
//!
//! Shape invariants the parser guarantees (SURFACE_SYNTAX §6 + the 2026-07-12
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
    /// `pred(args…)`.
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

/// A predicate application. `pred` is the surface name (alias or gismu —
/// resolution against klaro-dictionary is the resolve pass, a later bullet).
#[derive(Debug, Clone, PartialEq)]
pub struct Predication {
    pub pred: String,
    pub args: Vec<Arg>,
    pub span: Range<usize>,
}

/// One argument: positional (`label: None`) or named. The parser enforces
/// positionals-before-named; label→place resolution is the resolve pass.
#[derive(Debug, Clone, PartialEq)]
pub struct Arg {
    pub label: Option<String>,
    pub term: Term,
}

/// A term (SURFACE_SYNTAX §3).
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
    /// checks happen in the resolve pass, not here.
    Key(KeyTerm),
    /// Capitalized rigid name (la): stored verbatim; lowercasing/`_`→space
    /// happens at emission.
    Name(String),
    /// Determiner phrase: `some dog`, `every the market`, `exactly 2 red`.
    Det {
        det: Det,
        restr: Restr,
    },
}

/// The reserved pro-terms (SURFACE_SYNTAX §3 table).
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
    /// `it` — the relativized entity (ke'a); clause-body-only (resolve pass).
    It,
    /// `slot` — the ka open place (ce'u); `property{}`-only (resolve pass).
    Slot,
}

/// The determiner taxonomy (SURFACE_SYNTAX §4) — five gadri shapes plus the
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

/// A restrictor. Core profile: a single predicate word; the completion bullet
/// extends this struct with tanru units, place selectors, linked args, and
/// relative clauses.
#[derive(Debug, Clone, PartialEq)]
pub struct Restr {
    pub pred: String,
    pub span: Range<usize>,
}
