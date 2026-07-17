//! First-Order Logic intermediate representation.
//!
//! Defines [`IrTerm`] (atomic terms) and [`IrForm`] (well-formed formulas)
//! that the semantic compiler produces from the `AstBuffer` the nibli-kr
//! emitter builds. The reasoning engine consumes these via the flattener in
//! `lib.rs`.
//!
//! INTERN-THEN-RESOLVE BOUNDARY: every name in this IR is a [`lasso::Spur`]
//! key into the compiler's per-compilation `Rodeo` — Spurs NEVER survive into
//! `LogicBuffer`. `flatten_form` (lib.rs) resolves each Spur to an owned
//! `String` at the flattening boundary, so nibli-reason and everything
//! downstream see only strings. Variable identity is the `$`-prefixed
//! interned string — the sigil survives interning, and the free-variable and
//! scope-marker passes key on it.

use lasso::Spur;

/// The atomic arguments of a predicate.
#[derive(Debug, PartialEq, Clone)]
pub enum IrTerm {
    /// A bound logic variable (a `$`-prefixed name, e.g. `$x`)
    Variable(Spur),
    /// A named constant entity (a Name like `Adam`, or a pronoun constant)
    Constant(Spur),
    /// An entity described by a predicate (`some dog` / `the dog`)
    Description(Spur),
    /// An explicitly unspecified argument (`_` or an omitted place)
    Unspecified,
    /// Numeric literal.
    Number(f64),
}

/// The Well-Formed Formulas (WFFs) of our First-Order Logic engine.
#[derive(Debug, PartialEq, Clone)]
pub enum IrForm {
    /// An n-ary predicate: P(t1, t2, ..., tn)
    Predicate { relation: Spur, args: Vec<IrTerm> },
    /// Universal quantification: ∀x. P(x)
    ForAll(Spur, Box<IrForm>),
    /// Existential quantification: ∃x. P(x)
    Exists(Spur, Box<IrForm>),
    /// Logical Conjunction: A ∧ B
    And(Box<IrForm>, Box<IrForm>),
    /// Logical Disjunction: A ∨ B
    Or(Box<IrForm>, Box<IrForm>),
    /// Logical Negation: ¬A
    Not(Box<IrForm>),
    /// Past tense wrapper (`past P`): P was true.
    Past(Box<IrForm>),
    /// Present tense wrapper (`now P`): P is true now.
    Present(Box<IrForm>),
    /// Future tense wrapper (`future P`): P will be true.
    Future(Box<IrForm>),
    /// Deontic obligation (`must P`): P ought to be true.
    Obligatory(Box<IrForm>),
    /// Deontic permission (`may P`): P is permitted.
    Permitted(Box<IrForm>),
    /// Exactly `count` distinct x satisfy `body`.
    /// Count(var, count, body)
    Count {
        var: Spur,
        count: u32,
        body: Box<IrForm>,
    },
    /// Biconditional: A ↔ B  (expanded at flattening to And(Or(Not(A), B), Or(Not(B), A)))
    Biconditional(Box<IrForm>, Box<IrForm>),
    /// Exclusive or: A ⊕ B  (expanded at flattening to And(Or(A, B), Not(And(A, B))))
    Xor(Box<IrForm>, Box<IrForm>),
}
