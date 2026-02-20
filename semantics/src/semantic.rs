use crate::bindings::lojban::nesy::ast_types::{Bridi, Conversion, Gadri, Selbri, Sumti};
use crate::dictionary::JbovlasteSchema;
use crate::ir::{LogicalForm, LogicalTerm};
use lasso::Rodeo;

pub struct SemanticCompiler {
    pub interner: Rodeo,
    pub var_counter: usize,
}

impl SemanticCompiler {
    pub fn new() -> Self {
        Self {
            interner: Rodeo::new(),
            var_counter: 0,
        }
    }

    fn fresh_var(&mut self) -> lasso::Spur {
        let v = format!("_v{}", self.var_counter);
        self.var_counter += 1;
        self.interner.get_or_intern(&v)
    }

    pub fn compile_bridi(
        &mut self,
        bridi: &Bridi,
        selbris: &[Selbri],
        sumtis: &[Sumti],
    ) -> LogicalForm {
        let selbri_node = &selbris[bridi.relation as usize];
        let mut conversion_mod = None;

        // 1. Resolve Relation & Track Conversions
        let (relation_str, target_arity) = match selbri_node {
            Selbri::Root(gismu) => (gismu.as_str(), JbovlasteSchema::get_arity_or_default(gismu)),
            Selbri::Converted((conv, inner_id)) => {
                conversion_mod = Some(*conv);
                let inner_node = &selbris[*inner_id as usize];
                match inner_node {
                    Selbri::Root(r) => (r.as_str(), JbovlasteSchema::get_arity_or_default(r)),
                    _ => ("unknown", 2),
                }
            }
            Selbri::Tanru((_, head_id)) => match &selbris[*head_id as usize] {
                Selbri::Root(h) => (h.as_str(), JbovlasteSchema::get_arity_or_default(h)),
                _ => ("unknown", 2),
            },
            Selbri::Compound(parts) => {
                let head = parts.last().map(|s| s.as_str()).unwrap_or("unknown");
                (head, JbovlasteSchema::get_arity_or_default(head))
            }
            _ => ("unknown", 2),
        };

        let relation_id = self.interner.get_or_intern(relation_str);

        // 2. Map Sumti to Logical Terms and Extract Quantifiers
        let mut args: Vec<LogicalTerm> = Vec::with_capacity(target_arity);
        let mut quantifiers = Vec::new(); // Stores (variable_spur, restrictor_relation_str)

        for &term_id in bridi.head_terms.iter().chain(bridi.tail_terms.iter()) {
            let logical_term = match &sumtis[term_id as usize] {
                Sumti::ProSumti(p) => {
                    if p == "da" || p == "de" || p == "di" {
                        LogicalTerm::Variable(self.interner.get_or_intern(p.as_str()))
                    } else {
                        LogicalTerm::Constant(self.interner.get_or_intern(p.as_str()))
                    }
                }
                Sumti::Name(n) => LogicalTerm::Constant(self.interner.get_or_intern(n.as_str())),
                Sumti::Description((gadri, desc_id)) => {
                    let desc_str = match &selbris[*desc_id as usize] {
                        Selbri::Root(r) => r.as_str(),
                        _ => "entity",
                    };

                    // Core Fix: Map 'lo' to Existential Variables
                    if matches!(gadri, Gadri::Lo) {
                        let var = self.fresh_var();
                        quantifiers.push((var, desc_str));
                        LogicalTerm::Variable(var)
                    } else {
                        LogicalTerm::Description(self.interner.get_or_intern(desc_str))
                    }
                }
                _ => LogicalTerm::Unspecified,
            };
            args.push(logical_term);
        }

        // 3. Arity Normalization
        while args.len() < target_arity {
            args.push(LogicalTerm::Unspecified);
        }

        // 4. Mathematical Place Permutation (se/te/ve/xe)
        if let Some(conv) = conversion_mod {
            match conv {
                Conversion::Se if args.len() >= 2 => args.swap(0, 1),
                Conversion::Te if args.len() >= 3 => args.swap(0, 2),
                Conversion::Ve if args.len() >= 4 => args.swap(0, 3),
                Conversion::Xe if args.len() >= 5 => args.swap(0, 4),
                _ => {}
            }
        }

        // 5. Construct Base Predicate
        let mut final_form = LogicalForm::Predicate {
            relation: relation_id,
            args,
        };

        // 6. Wrap in Quantifiers (Outer-to-Inner)
        for (var, desc_str) in quantifiers.into_iter().rev() {
            let desc_rel = self.interner.get_or_intern(desc_str);
            let target_arity = JbovlasteSchema::get_arity_or_default(desc_str);

            let mut restrictor_args = Vec::with_capacity(target_arity);
            restrictor_args.push(LogicalTerm::Variable(var));
            while restrictor_args.len() < target_arity {
                restrictor_args.push(LogicalTerm::Unspecified);
            }

            let restrictor = LogicalForm::Predicate {
                relation: desc_rel,
                args: restrictor_args,
            };

            final_form = LogicalForm::Exists(
                var,
                Box::new(LogicalForm::And(Box::new(restrictor), Box::new(final_form))),
            );
        }

        final_form
    }

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
            LogicalForm::ForAll(v, b) => format!(
                "(ForAll \"{}\" {})",
                self.interner.resolve(v),
                self.to_sexp(b)
            ),
            LogicalForm::Exists(v, b) => format!(
                "(Exists \"{}\" {})",
                self.interner.resolve(v),
                self.to_sexp(b)
            ),
        }
    }
}
