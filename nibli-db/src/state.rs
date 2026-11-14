// SPDX-License-Identifier: MIT OR Apache-2.0

//! The projection: what a set of operations says, as a pure function of the set. No order of
//! arrival, no clock and no storage enters here, which is why replicas holding the same
//! operations hold the same state.

use crate::op::{ActorId, Batch, Change, Op, OpId};
use std::collections::{BTreeMap, BTreeSet};

/// Why an operation the database keeps is not part of its state.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Held {
    /// Other operations of its transaction have not arrived.
    Incomplete,
    /// An operation its transaction builds on has not arrived, or is itself held.
    Waiting(OpId),
    /// Its transaction can never apply: a parent is about another statement, or a
    /// restoration follows something other than a retraction.
    Misfit(OpId),
}

/// One statement, as the operations on it leave it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Status {
    Active {
        by: OpId,
        text: String,
    },
    Withdrawn {
        by: OpId,
    },
    /// Concurrent changes nobody has resolved. All are kept; none is reasoned from.
    Conflict {
        heads: Vec<OpId>,
    },
}

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct State {
    /// The operations that count.
    pub applied: BTreeSet<OpId>,
    /// For each statement, the applied operations on it that no other names as a parent.
    pub heads: BTreeMap<OpId, Vec<OpId>>,
    /// The operations that are kept and do not count, with the reason.
    pub held: BTreeMap<OpId, Held>,
}

impl State {
    pub fn of(ops: &BTreeMap<OpId, Op>) -> State {
        let mut batches: BTreeMap<(ActorId, Batch), Vec<&Op>> = BTreeMap::new();
        for op in ops.values() {
            batches.entry((op.id.actor, op.batch)).or_default().push(op);
        }
        let mut state = State::default();
        let mut waiting: Vec<(&(ActorId, Batch), &Vec<&Op>)> = vec![];
        for (key, members) in &batches {
            if members.len() == key.1.len as usize {
                waiting.push((key, members));
            } else {
                for op in members {
                    state.held.insert(op.id, Held::Incomplete);
                }
            }
        }
        // a transaction applies once everything it builds on has; repeat until none more can
        loop {
            let before = waiting.len();
            let mut still = vec![];
            for (key, members) in waiting {
                if members
                    .iter()
                    .all(|op| fit(ops, &state.applied, key, op).is_ok())
                {
                    state.applied.extend(members.iter().map(|op| op.id));
                } else {
                    still.push((key, members));
                }
            }
            waiting = still;
            if waiting.len() == before {
                break;
            }
        }
        for (key, members) in waiting {
            let why = members
                .iter()
                .find_map(|op| fit(ops, &state.applied, key, op).err())
                .expect("a transaction left waiting has an operation that does not fit");
            for op in members {
                state.held.insert(op.id, why);
            }
        }
        let mut named: BTreeSet<OpId> = BTreeSet::new();
        for id in &state.applied {
            named.extend(ops[id].parents.iter().copied());
        }
        for id in &state.applied {
            if !named.contains(id) {
                state.heads.entry(ops[id].target).or_default().push(*id);
            }
        }
        state
    }

    /// The statements, by id, each with what its operations leave of it.
    pub fn statements<'a>(
        &'a self,
        ops: &'a BTreeMap<OpId, Op>,
    ) -> impl Iterator<Item = (OpId, Status)> + 'a {
        self.heads
            .iter()
            .map(|(target, heads)| (*target, status(ops, heads)))
    }
}

/// Does this operation of a complete transaction stand on applied ground?
fn fit(
    ops: &BTreeMap<OpId, Op>,
    applied: &BTreeSet<OpId>,
    key: &(ActorId, Batch),
    op: &Op,
) -> Result<(), Held> {
    for p in &op.parents {
        let Some(parent) = ops.get(p) else {
            return Err(Held::Waiting(*p));
        };
        if parent.target != op.target
            || (op.change == Change::Restore && parent.change != Change::Retract)
        {
            return Err(Held::Misfit(*p));
        }
        let beside = p.actor == key.0
            && p.counter >= key.1.first
            && p.counter - key.1.first < u64::from(key.1.len);
        if !beside && !applied.contains(p) {
            return Err(Held::Waiting(*p));
        }
    }
    Ok(())
}

#[cfg(not(nibli_db_broken = "lww"))]
fn status(ops: &BTreeMap<OpId, Op>, heads: &[OpId]) -> Status {
    match heads {
        [one] => settled(&ops[one]),
        many => Status::Conflict {
            heads: many.to_vec(),
        },
    }
}

/// The deliberately broken build of roadmap/DB1.md, Anti-fake: the latest by the writer's
/// clock wins, and nothing is ever a conflict.
#[cfg(nibli_db_broken = "lww")]
fn status(ops: &BTreeMap<OpId, Op>, heads: &[OpId]) -> Status {
    let latest = heads
        .iter()
        .max_by_key(|id| (ops[*id].provenance.time, **id))
        .expect("a statement has a head");
    settled(&ops[latest])
}

fn settled(op: &Op) -> Status {
    match &op.payload {
        Some(text) => Status::Active {
            by: op.id,
            text: text.clone(),
        },
        None => Status::Withdrawn { by: op.id },
    }
}
