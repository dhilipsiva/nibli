use crate::bindings::lojban::nesy::ast_types::{Bridi, Selbri, Sumti};
use crate::dictionary::JbovlasteSchema;
use crate::ir::{LogicalForm, LogicalTerm};
use lasso::Rodeo;

pub struct SemanticCompiler {
    pub interner: Rodeo,
}

impl SemanticCompiler {
    pub fn new() -> Self {
        Self {
            interner: Rodeo::new(),
        }
    }

    /// Compiles a flattened WASM Bridi AST into an explicit First-Order Logic formula.
    pub fn compile_bridi(
        &mut self,
        bridi: &Bridi,
        selbris: &[Selbri],
        sumtis: &[Sumti],
    ) -> LogicalForm {
        // 1. Resolve the Selbri (Relation) using the flat array index
        let selbri_node = &selbris[bridi.relation as usize];

        let (relation_str, target_arity): (&str, usize) = match selbri_node {
            Selbri::Root(gismu) => (gismu, JbovlasteSchema::get_arity_or_default(gismu)),
            Selbri::Tanru((modifier_id, head_id)) => {
                let head_node = &selbris[*head_id as usize];
                let head_str: &str = match head_node {
                    Selbri::Root(h) => h,
                    _ => "unknown",
                };
                (head_str, JbovlasteSchema::get_arity_or_default(head_str))
            }
            Selbri::Compound(parts) => {
                let head_str = parts.last().map(|s| s.as_str()).unwrap_or("unknown");
                (head_str, JbovlasteSchema::get_arity_or_default(head_str))
            }
            // Fallback for exhaustive matching on unhandled permutations
            _ => ("unknown", 2),
        };
        let relation_id = self.interner.get_or_intern(relation_str);

        // 2. Map Sumti to Logical Terms
        let mut args: Vec<LogicalTerm> = Vec::with_capacity(target_arity);

        // FIX: Chain head_terms and tail_terms sequentially to reconstruct the logical argument list
        for &term_id in bridi.head_terms.iter().chain(bridi.tail_terms.iter()) {
            let term_node = &sumtis[term_id as usize];
            let logical_term = match term_node {
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
                // FIX: Destructure the tuple to extract the valid memory offset ID
                Sumti::Description((_gadri, desc_selbri_id)) => {
                    let desc_selbri_node = &selbris[*desc_selbri_id as usize];
                    let desc_str: &str = match desc_selbri_node {
                        Selbri::Root(r) => r,
                        _ => "entity",
                    };
                    LogicalTerm::Description(self.interner.get_or_intern(desc_str))
                }
                Sumti::QuotedLiteral(_) | Sumti::Unspecified => LogicalTerm::Unspecified,
                // Ensure exhaustive match for remaining wit-bindgen variants
                _ => LogicalTerm::Unspecified,
            };
            args.push(logical_term);
        }

        // 3. Arity Normalization (Padding with zo'e)
        while args.len() < target_arity {
            args.push(LogicalTerm::Unspecified);
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

                let arity = args.len().clamp(1, 5);
                format!("(Pred{} \"{}\" {})", arity, raw_rel, args_str.join(" "))
            }
            LogicalForm::And(left, right) => {
                format!("(And {} {})", self.to_sexp(left), self.to_sexp(right))
            }
            // FIX: Prevent WASM traps by implementing basic serialization for quantifiers
            LogicalForm::ForAll(var, body) => {
                format!(
                    "(ForAll \"{}\" {})",
                    self.interner.resolve(var),
                    self.to_sexp(body)
                )
            }
            LogicalForm::Exists(var, body) => {
                format!(
                    "(Exists \"{}\" {})",
                    self.interner.resolve(var),
                    self.to_sexp(body)
                )
            }
        }
    }
}
