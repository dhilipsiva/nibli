//! First-Order Logic intermediate representation.
//!
//! Defines [`IrTerm`] (atomic terms) and [`IrForm`] (well-formed formulas)
//! that the semantic compiler produces from the parser's AST. The reasoning engine
//! consumes these via the WIT flattener in `lib.rs`.
//!
//! String interning uses [`lasso::Spur`] keys — resolved to `String` only at the
//! WIT boundary during flattening.

use lasso::Spur;

/// The atomic arguments of a predicate.
#[derive(Debug, PartialEq, Clone)]
pub enum IrTerm {
    /// A bounded logic variable (e.g., 'da', 'de', 'di')
    Variable(Spur),
    /// A named constant entity (e.g., 'la .alis.')
    Constant(Spur),
    /// An entity described by a predicate (e.g., 'lo gerku' -> the dog)
    Description(Spur),
    /// An explicitly unspecified argument (zo'e)
    Unspecified,
    /// Numeric literal (from `li` + PA).
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
    /// Past tense wrapper (pu): P was true.
    Past(Box<IrForm>),
    /// Present tense wrapper (ca): P is true now.
    Present(Box<IrForm>),
    /// Future tense wrapper (ba): P will be true.
    Future(Box<IrForm>),
    /// Deontic obligation (ei/bilga): P ought to be true.
    Obligatory(Box<IrForm>),
    /// Deontic permission (e'e/curmi): P is permitted.
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
