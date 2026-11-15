// SPDX-License-Identifier: MIT OR Apache-2.0

//! What the engine may reason from. Statements that are each acceptable alone can refuse to
//! load together, or contradict each other, once two replicas have merged. The statements
//! involved are found here and kept out, all of them, with no winner among them.

use crate::op::{Op, OpId};
use crate::state::{State, Status};
use nibli_engine::NibliEngine;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Reasoned {
    /// The statements the engine reasons from, by id.
    pub statements: Vec<(OpId, String)>,
    /// Active statements kept out because together they break a constraint.
    pub flagged: BTreeSet<OpId>,
    /// What the engine said was broken, in the order it was found.
    pub problems: Vec<String>,
    /// Checks the engine could not decide on the statements it reasons from. Not a refusal.
    pub undecided: Vec<String>,
}

impl Reasoned {
    pub fn of(ops: &BTreeMap<OpId, Op>, state: &State) -> Reasoned {
        let mut keep: Vec<(OpId, String)> = state
            .statements(ops)
            .filter_map(|(id, status)| match status {
                Status::Active { text, .. } => Some((id, text)),
                _ => None,
            })
            .collect();
        let mut out = Reasoned::default();
        loop {
            let (broken, undecided) = check(keep.iter().map(|(_, t)| t.as_str()));
            if broken.is_empty() {
                out.undecided = undecided;
                break;
            }
            // A statement is involved if the trouble changes when its text is left out.
            // Statements with the same text stand or fall together, so that a second copy
            // of one side does not make it the winner.
            let texts: BTreeSet<&str> = keep.iter().map(|(_, t)| t.as_str()).collect();
            let mut involved: BTreeSet<OpId> = BTreeSet::new();
            for text in texts {
                let without = keep.iter().map(|(_, t)| t.as_str()).filter(|t| *t != text);
                if check(without).0 != broken {
                    involved.extend(keep.iter().filter(|(_, t)| t == text).map(|(id, _)| *id));
                }
            }
            if involved.is_empty() {
                // trouble no single statement accounts for: reason from nothing
                involved.extend(keep.iter().map(|(id, _)| *id));
            }
            out.problems.extend(broken);
            keep.retain(|(id, _)| !involved.contains(id));
            out.flagged.extend(involved);
        }
        out.statements = keep;
        out
    }

    /// The statements as nibli-kr text, one to a line, in id order.
    pub fn snapshot(&self) -> String {
        let mut text = String::new();
        for (_, statement) in &self.statements {
            text.push_str(statement);
            text.push('\n');
        }
        text
    }

    /// A fresh engine holding exactly the snapshot.
    pub fn engine(&self) -> Result<NibliEngine, String> {
        let texts: Vec<&str> = self.statements.iter().map(|(_, t)| t.as_str()).collect();
        NibliEngine::from_text_batch(&texts).map_err(|e| e.to_string())
    }
}

/// Load the statements in order and ask the engine what is broken: a refusal to load, or the
/// contradictions it finds. The second list is what it could not decide.
fn check<'a>(texts: impl Iterator<Item = &'a str>) -> (Vec<String>, Vec<String>) {
    let texts: Vec<&str> = texts.collect();
    match NibliEngine::from_text_batch(&texts) {
        Err(e) => (
            vec![format!("the statements do not load together: {e}")],
            vec![],
        ),
        Ok(engine) => {
            let report = engine.check_contradictions_report();
            let undecided = report
                .unresolved
                .iter()
                .map(|gap| format!("{gap:?}"))
                .collect();
            let mut broken = report.violations;
            broken.sort();
            (broken, undecided)
        }
    }
}
