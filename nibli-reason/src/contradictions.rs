// SPDX-License-Identifier: MIT OR Apache-2.0

//! Contradiction scans over the engine's represented constraints. A completed
//! scan is not an unrestricted first-order consistency proof.

use super::*;
use std::fmt;

/// Findings and checks that could not be decided. Only an empty result in BOTH
/// fields establishes that this scan completed without finding a contradiction.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ContradictionReport {
    pub violations: Vec<String>,
    pub unresolved: Vec<ContradictionGap>,
}

impl ContradictionReport {
    pub fn is_clean(&self) -> bool {
        self.violations.is_empty() && self.unresolved.is_empty()
    }

    fn gap(&mut self, context: String, reason: ContradictionGapReason) {
        self.unresolved.push(ContradictionGap { context, reason });
    }

    fn finish(mut self) -> Self {
        self.violations.sort();
        self.violations.dedup();
        self.unresolved.sort_by_cached_key(ToString::to_string);
        self.unresolved.dedup();
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContradictionGap {
    pub context: String,
    pub reason: ContradictionGapReason,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContradictionGapReason {
    Unknown(UnknownReason),
    ResourceExceeded(ResourceKind),
    Unsupported(String),
    EvaluationError(String),
}

impl fmt::Display for ContradictionGap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: ", self.context)?;
        match &self.reason {
            ContradictionGapReason::Unknown(reason) => write!(f, "UNKNOWN ({reason:?})"),
            ContradictionGapReason::ResourceExceeded(kind) => {
                write!(f, "RESOURCE_EXCEEDED ({kind:?})")
            }
            ContradictionGapReason::Unsupported(reason) => write!(f, "unsupported: {reason}"),
            ContradictionGapReason::EvaluationError(error) => {
                write!(f, "evaluation error: {error}")
            }
        }
    }
}

impl KnowledgeBase {
    /// Compatibility result containing findings only. Call
    /// [`Self::check_contradictions_report`] when the absence of findings is
    /// used as a gate: this legacy return type cannot disclose incomplete checks.
    pub fn check_contradictions(&self) -> Vec<String> {
        if let Err(error) = self.ensure_ready() {
            return vec![error.to_string()];
        }
        self.check_contradictions_report().violations
    }

    /// Check stored arity/equality conflicts, explicit negatives and registered
    /// integrity/disjunctive constraints, including derived positive counterparts
    /// and antecedents. Reuses ordinary entailment and witness evaluation.
    ///
    /// Unknown results, exhausted bounds, unsupported assertion shapes and
    /// evaluation failures are retained separately from proven violations.
    /// Negative rule premises remain NAF; opaque abstraction bodies remain quoted
    /// content. This scans the represented model, not all classical consequences.
    pub fn check_contradictions_report(&self) -> ContradictionReport {
        let mut report = ContradictionReport::default();
        if let Err(error) = self.ensure_ready() {
            report.gap(
                "contradiction scan".into(),
                ContradictionGapReason::EvaluationError(error.to_string()),
            );
            return report;
        }
        let (integrity, negatives, disjunctions) = {
            let inner = self.inner.borrow();
            if inner
                .cancel
                .as_ref()
                .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
            {
                report.gap(
                    "contradiction scan".into(),
                    ContradictionGapReason::EvaluationError("execution cancelled".into()),
                );
                return report;
            }
            for id in &inner.negative_scan_gaps {
                let context = inner
                    .fact_registry
                    .get(id)
                    .map(|record| format!("assertion #{id} ({})", record.label))
                    .unwrap_or_else(|| format!("assertion #{id}"));
                report.gap(
                    context,
                    ContradictionGapReason::Unsupported(
                        "explicit negation is not a conjunction of positive facts".into(),
                    ),
                );
            }
            let integrity: Vec<_> = inner
                .integrity_constraints
                .iter()
                .filter(|constraint| {
                    !constraint
                        .conjuncts
                        .iter()
                        .all(|fact| inner.fact_store.contains(fact))
                })
                .cloned()
                .collect();
            let negatives: Vec<_> = inner
                .negative_facts
                .iter()
                .filter(|group| {
                    // Bare equality negatives have a complete union-find check.
                    !matches!(group.as_slice(), [StoredFact::Bare(fact)]
                        if fact.relation == "equals" && fact.args.len() == 2)
                        && !negative_group_holds(group, &*inner.fact_store)
                })
                .cloned()
                .collect();
            (integrity, negatives, inner.disjunctive_constraints.clone())
        };
        report.violations = self.check_contradictions_stored();

        for constraint in integrity {
            let context = format!("integrity constraint '{}'", constraint.label);
            if self.scan_positive_group(&constraint.conjuncts, context, &mut report) {
                report.violations.push(format!(
                    "Integrity violation '{}': {} all hold (including derivation)",
                    constraint.label,
                    display_group(&constraint.conjuncts)
                ));
            }
        }
        for group in negatives {
            let facts = display_group(&group);
            if self.scan_positive_group(
                &group,
                format!("positive counterpart of ¬({facts})"),
                &mut report,
            ) {
                report.violations.push(format!(
                    "Negation contradiction: ¬({facts}) was asserted, but the positive \
                     counterpart is derivable"
                ));
            }
        }
        for constraint in disjunctions {
            // A disjunction cannot conflict unless every branch has an explicit
            // denial. With no negatives there is no enumeration work to do.
            if self.inner.borrow().negative_facts.is_empty() {
                break;
            }
            let context = format!("disjunctive constraint '{}'", constraint.label);
            let Some(query) = negative_group_to_query_buffer(&constraint.conditions) else {
                report.gap(context, unsupported_group());
                continue;
            };
            // Keep typed generated identities. Public find witnesses deliberately
            // expose display strings and must never be fed back into matching.
            let result = self.query_find_ground(query);
            self.inner.borrow_mut().find_enumeration = false;
            match result {
                Ok(bindings) => {
                    let inner = self.inner.borrow();
                    let violated = bindings.into_iter().any(|bindings| {
                        let bindings: HashMap<_, _> = bindings
                            .into_iter()
                            .map(|(name, value)| (restore_template_query_variable(name), value))
                            .collect();
                        constraint.disjuncts.iter().all(|disjunct| {
                            let facts: Vec<_> = disjunct
                                .iter()
                                .map(|fact| substitute_fact(fact, &bindings))
                                .collect();
                            disjunct_explicitly_denied(&facts, &inner.negative_facts)
                        })
                    });
                    if violated {
                        report.violations.push(format!(
                            "Disjunctive constraint violated '{}': the antecedent holds but every \
                             disjunct is explicitly denied (na)",
                            constraint.label
                        ));
                    }
                }
                Err(error) => {
                    report.gap(context, ContradictionGapReason::EvaluationError(error));
                }
            }
        }
        report.finish()
    }

    fn scan_positive_group(
        &self,
        group: &[StoredFact],
        context: String,
        report: &mut ContradictionReport,
    ) -> bool {
        let Some(query) = negative_group_to_query_buffer(group) else {
            report.gap(context, unsupported_group());
            return false;
        };
        match self.query_entailment_inner(query) {
            Ok(QueryResult::True) => return true,
            Ok(QueryResult::False) => {}
            Ok(QueryResult::Unknown(reason)) => {
                report.gap(context, ContradictionGapReason::Unknown(reason));
            }
            Ok(QueryResult::ResourceExceeded(kind)) => {
                report.gap(context, ContradictionGapReason::ResourceExceeded(kind));
            }
            Err(error) => report.gap(context, ContradictionGapReason::EvaluationError(error)),
        }
        false
    }
}

fn display_group(group: &[StoredFact]) -> String {
    group
        .iter()
        .map(StoredFact::to_display_string)
        .collect::<Vec<_>>()
        .join(" ∧ ")
}

fn unsupported_group() -> ContradictionGapReason {
    ContradictionGapReason::Unsupported(
        "constraint contains an empty group or an unrepresentable generated term".into(),
    )
}
