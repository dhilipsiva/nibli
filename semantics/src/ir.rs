use lasso::Spur;

/// The atomic arguments of a predicate.
#[derive(Debug, PartialEq, Clone)]
pub enum LogicalTerm {
    /// A bounded logic variable (e.g., 'da', 'de', 'di')
    Variable(Spur),
    /// A named constant entity (e.g., 'la .alis.')
    Constant(Spur),
    /// An entity described by a predicate (e.g., 'lo gerku' -> the dog)
    Description(Spur),
    /// An explicitly unspecified argument (zo'e)
    Unspecified,
}

/// The Well-Formed Formulas (WFFs) of our First-Order Logic engine.
#[derive(Debug, PartialEq, Clone)]
pub enum LogicalForm {
    /// An n-ary predicate: P(t1, t2, ..., tn)
    Predicate {
        relation: Spur,
        args: Vec<LogicalTerm>,
    },
    /// Universal quantification: ∀x. P(x)
    ForAll(Spur, Box<LogicalForm>),
    /// Existential quantification: ∃x. P(x)
    Exists(Spur, Box<LogicalForm>),
    /// Logical Conjunction: A ∧ B
    And(Box<LogicalForm>, Box<LogicalForm>),
    /// Logical Disjunction: A ∨ B
    Or(Box<LogicalForm>, Box<LogicalForm>),
    /// Logical Negation: ¬A
    Not(Box<LogicalForm>),
    Past(Box<LogicalForm>),    // ← NEW
    Present(Box<LogicalForm>), // ← NEW
    Future(Box<LogicalForm>),  // ← NEW
}
