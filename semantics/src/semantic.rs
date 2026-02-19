use crate::ast::{Bridi, Selbri, Sumti};
use crate::dictionary::JbovlasteSchema;
use crate::ir::{LogicalForm, LogicalTerm};
use lasso::Rodeo;

pub struct SemanticCompiler {
    pub interner: Rodeo,
    pub schema: JbovlasteSchema,
}

impl SemanticCompiler {
    pub fn new(schema: JbovlasteSchema) -> Self {
        Self {
            interner: Rodeo::new(),
            schema,
        }
    }

    /// Compiles a parsed Bridi AST into an explicit First-Order Logic formula.
    pub fn compile_bridi(&mut self, bridi: &Bridi) -> LogicalForm {
        // 1. Resolve the Selbri (Relation)
        let (relation_str, target_arity): (&str, usize) = match &bridi.selbri {
            Selbri::Root(gismu) => (gismu, self.schema.get_arity(gismu)),
            Selbri::Tanru(_modifier, head) => {
                let head_str: &str = match head.as_ref() {
                    Selbri::Root(h) => h,
                    _ => "unknown",
                };
                (head_str, self.schema.get_arity(head_str))
            }
            Selbri::Compound(parts) => {
                // Very crude fallback for V1 lujvo handling
                let head_str = parts.last().unwrap_or(&"unknown");
                (head_str, self.schema.get_arity(head_str))
            }
        };
        let relation_id = self.interner.get_or_intern(relation_str);

        // 2. Map Sumti to Logical Terms
        let mut args: Vec<LogicalTerm> = Vec::with_capacity(target_arity);

        for term in bridi.terms.iter() {
            let logical_term = match term {
                Sumti::ProSumti(p) => {
                    let p_str: &str = p;
                    if p_str == "da" || p_str == "de" || p_str == "di" {
                        LogicalTerm::Variable(self.interner.get_or_intern(p_str))
                    } else {
                        LogicalTerm::Constant(self.interner.get_or_intern(p_str))
                    }
                }
                Sumti::Name(n) => {
                    let n_str: &str = n;
                    LogicalTerm::Constant(self.interner.get_or_intern(n_str))
                }
                Sumti::Description(selbri) => {
                    let desc_str: &str = match selbri.as_ref() {
                        Selbri::Root(r) => r,
                        _ => "entity",
                    };
                    LogicalTerm::Description(self.interner.get_or_intern(desc_str))
                }
                Sumti::QuotedLiteral(_) => LogicalTerm::Unspecified,
            };
            args.push(logical_term);
        }

        // 3. Arity Normalization (Padding with zo'e)
        while args.len() < target_arity {
            args.push(LogicalTerm::Unspecified);
        }

        // 4. Truncation (Safety rail against bad parsing)
        if args.len() > target_arity {
            args.truncate(target_arity);
        }

        LogicalForm::Predicate {
            relation: relation_id,
            args,
        }
    }

    /// Converts the LIR into an egglog S-Expression by resolving interner IDs.
    pub fn to_sexp(&self, form: &LogicalForm) -> String {
        match form {
            LogicalForm::Predicate { relation, args } => {
                let raw_rel = self.interner.resolve(relation);
                let rel_str = Self::sanitize_name(raw_rel);

                let args_str: Vec<String> = args
                    .iter()
                    .map(|arg| match arg {
                        LogicalTerm::Variable(v) => {
                            format!("(Var \"{}\")", self.interner.resolve(v))
                        }
                        LogicalTerm::Constant(c) => {
                            format!("(Const \"{}\")", self.interner.resolve(c))
                        }
                        LogicalTerm::Description(d) => {
                            format!("(Desc \"{}\")", self.interner.resolve(d))
                        }
                        LogicalTerm::Unspecified => "(Zoe)".to_string(),
                    })
                    .collect();

                format!("({} {})", rel_str, args_str.join(" "))
            }
            LogicalForm::And(left, right) => {
                format!("(And {} {})", self.to_sexp(left), self.to_sexp(right))
            }
            _ => unimplemented!("Other forms deferred for V1 MVP"),
        }
    }

    /// egglog datatypes must be capitalized and avoid special characters.
    pub fn sanitize_name(word: &str) -> String {
        let mut s = word.replace('\'', "_").replace('.', "");
        if let Some(r) = s.get_mut(0..1) {
            r.make_ascii_uppercase();
        }
        s
    }
}
