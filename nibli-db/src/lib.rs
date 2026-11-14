// SPDX-License-Identifier: MIT OR Apache-2.0

//! A nibli-kr-native database: ACID on each replica, CRDT between replicas.
//!
//! **There is no transaction across replicas.** A transaction is atomic, consistent,
//! isolated and durable on the replica that commits it. Between replicas the promise is
//! convergence: replicas holding the same operations hold the same state, whatever order
//! the operations arrived in. Two replicas can both commit while apart, and what they
//! committed can disagree once merged. Disagreement is kept and shown, never settled by a
//! clock: see [`Database::conflicts`] and [`Database::constraint_conflicts`].
//!
//! The database is a set of signed operations ([`Op`]), each carrying one nibli-kr
//! statement. Everything else is derived from that set: which statements are active, the
//! snapshot the engine reasons from, and what is in conflict.
//!
//! ```
//! use nibli_db::{Database, Provenance};
//!
//! let mut db = Database::in_memory(&[7; 32], "example").unwrap();
//! let mut tx = db.begin(Provenance::default());
//! let rex = tx.assert("dog(Rex).");
//! tx.commit().unwrap();
//! assert_eq!(db.snapshot(), "dog(Rex).\n");
//!
//! let mut tx = db.begin(Provenance::default());
//! tx.retract(rex).unwrap();
//! tx.commit().unwrap();
//! assert_eq!(db.snapshot(), "");
//! ```
//!
//! A retraction is not an erasure: the retracted operation stays in the set, and in every
//! replica that has it.
//!
//! This is slice DB1 of `roadmap/DB1.md`: no network, and the whole state is recomputed
//! after every change, so it is correct before it is fast.

mod db;
mod op;
mod reason;
mod state;

pub use db::{Conflict, Database, Error, Have, Merged, Peer, Refusal, Synced, Transaction, sync};
pub use op::{ActorId, Batch, Change, Malformed, Op, OpId, Provenance};
pub use state::{Held, State, Status};
