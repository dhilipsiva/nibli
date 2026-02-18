use crate::ast::{Bridi, Selbri, Sumti};
use crate::ir::{LogicalForm, LogicalTerm};
use lasso::Rodeo;

/// A mock dictionary schema defining the exact arity of Lojban gismu.
/// In production, this is generated from the jbovlaste XML exports.
fn get_gismu_arity(predicate: &str) -> usize {
    match predicate {
        "klama" => 5, // agent, destination, origin, route, vehicle
        "prami" => 2, // lover, loved
        "gerku" => 1, // dog
        "dunda" => 3, // donor, gift, recipient
        _ => 2,       // Fallback for unknown tanru/lujvo in V1
    }
}

pub struct SemanticCompiler {
    pub interner: Rodeo,
}

impl SemanticCompiler {
    pub fn new() -> Self {
        Self {
            interner: Rodeo::new(),
        }
    }

    /// Compiles a parsed Bridi AST into an explicit First-Order Logic formula.
    pub fn compile_bridi(&mut self, bridi: &Bridi) -> LogicalForm {
        // 1. Resolve the Selbri (Relation)
        let (relation_str, target_arity): (&str, usize) = match &bridi.selbri {
            Selbri::Root(gismu) => (gismu, get_gismu_arity(gismu)),
            Selbri::Tanru(_modifier, head) => {
                let head_str: &str = match head.as_ref() {
                    Selbri::Root(h) => h,
                    _ => "unknown",
                };
                (head_str, get_gismu_arity(head_str))
            }
            Selbri::Compound(_) => ("lujvo", 2),
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
                Sumti::QuotedLiteral(_) => {
                    LogicalTerm::Unspecified 
                }
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
}
