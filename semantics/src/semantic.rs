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

    /// Recursively extracts the arity of the structural head of the relation
    fn get_selbri_arity(&self, selbri_id: u32, selbris: &[Selbri]) -> usize {
        match &selbris[selbri_id as usize] {
            Selbri::Root(g) => JbovlasteSchema::get_arity_or_default(g.as_str()),
            Selbri::Tanru((_, head_id)) => self.get_selbri_arity(*head_id, selbris),
            Selbri::Converted((_, inner_id)) => self.get_selbri_arity(*inner_id, selbris),
            Selbri::Compound(parts) => parts
                .last()
                .map(|s| JbovlasteSchema::get_arity_or_default(s.as_str()))
                .unwrap_or(2),
            _ => 2,
        }
    }

    /// Extracts the string name of the head for non-quantified descriptions
    fn get_selbri_head_name<'a>(&self, selbri_id: u32, selbris: &'a [Selbri]) -> &'a str {
        match &selbris[selbri_id as usize] {
            Selbri::Root(r) => r.as_str(),
            Selbri::Tanru((_, head_id)) => self.get_selbri_head_name(*head_id, selbris),
            Selbri::Converted((_, inner_id)) => self.get_selbri_head_name(*inner_id, selbris),
            Selbri::Compound(parts) => parts.last().map(|s| s.as_str()).unwrap_or("entity"),
            _ => "entity",
        }
    }

    /// Recursively instantiates a Selbri against a set of arguments, correctly mapping
    /// intersective Tanru and argument-swapping conversions across the binary tree.
    fn apply_selbri(
        &mut self,
        selbri_id: u32,
        args: &[LogicalTerm],
        selbris: &[Selbri],
    ) -> LogicalForm {
        match &selbris[selbri_id as usize] {
            Selbri::Root(g) => LogicalForm::Predicate {
                relation: self.interner.get_or_intern(g.as_str()),
                args: args.to_vec(),
            },
            // The Core Fix: Map Tanru to Intersective Conjunction
            Selbri::Tanru((mod_id, head_id)) => {
                let left = self.apply_selbri(*mod_id, args, selbris);
                let right = self.apply_selbri(*head_id, args, selbris);
                LogicalForm::And(Box::new(left), Box::new(right))
            }
            // Delegate argument permutation directly into the recursion
            Selbri::Converted((conv, inner_id)) => {
                let mut permuted = args.to_vec();
                match conv {
                    Conversion::Se if permuted.len() >= 2 => permuted.swap(0, 1),
                    Conversion::Te if permuted.len() >= 3 => permuted.swap(0, 2),
                    Conversion::Ve if permuted.len() >= 4 => permuted.swap(0, 3),
                    Conversion::Xe if permuted.len() >= 5 => permuted.swap(0, 4),
                    _ => {}
                }
                self.apply_selbri(*inner_id, &permuted, selbris)
            }
            Selbri::Compound(parts) => {
                let head = parts.last().map(|s| s.as_str()).unwrap_or("unknown");
                LogicalForm::Predicate {
                    relation: self.interner.get_or_intern(head),
                    args: args.to_vec(),
                }
            }
            _ => LogicalForm::Predicate {
                relation: self.interner.get_or_intern("unknown"),
                args: args.to_vec(),
            },
        }
    }

    pub fn compile_bridi(
        &mut self,
        bridi: &Bridi,
        selbris: &[Selbri],
        sumtis: &[Sumti],
    ) -> LogicalForm {
        let target_arity = self.get_selbri_arity(bridi.relation, selbris);

        let mut args: Vec<LogicalTerm> = Vec::with_capacity(target_arity);
        let mut quantifiers = Vec::new(); // Tracks (variable, description_selbri_id)

        // 1. Map Sumti and intercept existential quantifiers
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
                    if matches!(gadri, Gadri::Lo) {
                        let var = self.fresh_var();
                        quantifiers.push((var, *desc_id));
                        LogicalTerm::Variable(var)
                    } else {
                        let desc_str = self.get_selbri_head_name(*desc_id, selbris);
                        LogicalTerm::Description(self.interner.get_or_intern(desc_str))
                    }
                }
                _ => LogicalTerm::Unspecified,
            };
            args.push(logical_term);
        }

        // 2. Pad to target arity
        while args.len() < target_arity {
            args.push(LogicalTerm::Unspecified);
        }

        // 3. Construct the main relation via tree traversal
        let mut final_form = self.apply_selbri(bridi.relation, &args, selbris);

        // 4. Wrap with Restrictors (Inner-to-Outer)
        for (var, desc_id) in quantifiers.into_iter().rev() {
            let desc_arity = self.get_selbri_arity(desc_id, selbris);

            let mut restrictor_args = Vec::with_capacity(desc_arity);
            restrictor_args.push(LogicalTerm::Variable(var));
            while restrictor_args.len() < desc_arity {
                restrictor_args.push(LogicalTerm::Unspecified);
            }

            // Description selbris map structurally just like the main relation
            let restrictor = self.apply_selbri(desc_id, &restrictor_args, selbris);

            final_form = LogicalForm::Exists(
                var,
                Box::new(LogicalForm::And(Box::new(restrictor), Box::new(final_form))),
            );
        }

        final_form
    }
}
