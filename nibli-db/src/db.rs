// SPDX-License-Identifier: MIT OR Apache-2.0

//! One replica: the operations it keeps in redb, and the state they project to.

use crate::op::{ActorId, Batch, Change, Malformed, Op, OpId, Provenance, one_statement};
use crate::reason::Reasoned;
use crate::state::{Held, State, Status};
use ed25519_dalek::SigningKey;
use nibli_engine::NibliEngine;
use redb::{ReadableTable, TableDefinition};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::Path;

/// Operations by id and variant. Variant 0 is the operation; a variant 1 exists only when
/// its actor signed two contents under one id, and then neither counts.
const OPS: TableDefinition<&[u8], &[u8]> = TableDefinition::new("operations");
const ACTORS: TableDefinition<&[u8], ()> = TableDefinition::new("actors");
const META: TableDefinition<&str, &[u8]> = TableDefinition::new("meta");
const FORMAT: &[u8] = b"nibli-db-1";

#[derive(Debug)]
pub enum Error {
    Storage(String),
    /// The file is not a database of this format, scope or actor history.
    Open(String),
    /// A statement in the transaction is not one nibli-kr statement.
    Statement(Malformed),
    /// The transaction asks for a change the statement's state does not allow.
    Change(String),
    /// The transaction would leave statements the engine cannot hold together.
    Inconsistent(Vec<String>),
    /// The other side keeps another scope.
    Scope {
        ours: String,
        theirs: String,
    },
    /// The Git transport could not do its work. Only with the `git` feature.
    #[cfg(feature = "git")]
    Git(crate::git::Failure),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Storage(e) => write!(f, "storage: {e}"),
            Error::Open(e) => write!(f, "this is not a database I can open: {e}"),
            Error::Statement(e) => write!(f, "refused: {e}"),
            Error::Change(e) => write!(f, "refused: {e}"),
            Error::Inconsistent(problems) => {
                write!(
                    f,
                    "refused, the statements would not hold together: {}",
                    problems.join("; ")
                )
            }
            Error::Scope { ours, theirs } => {
                write!(
                    f,
                    "refused: this database keeps scope {ours:?} and the other {theirs:?}"
                )
            }
            #[cfg(feature = "git")]
            Error::Git(e) => write!(f, "git: {e}"),
        }
    }
}

impl std::error::Error for Error {}

fn storage(e: impl fmt::Display) -> Error {
    Error::Storage(e.to_string())
}

/// Why a delivered operation was not kept.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Refusal {
    Malformed(Malformed),
    /// Its actor's key is not enrolled here.
    Unenrolled(ActorId),
    /// It belongs to another scope.
    Scope(String),
}

/// What a delivery did.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Merged {
    /// Newly kept.
    pub kept: Vec<OpId>,
    /// Already here, byte for byte.
    pub known: usize,
    /// Ids now known to name two contents. Neither content counts from here on.
    pub disowned: Vec<OpId>,
    pub refused: Vec<Refusal>,
}

/// A statement whose concurrent changes nobody has resolved, with every one of them.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Conflict {
    pub statement: OpId,
    pub heads: Vec<(OpId, Change, Option<String>)>,
}

/// Which operation, in which of its contents. Two replicas compare these to see what the
/// other lacks.
pub type Have = (OpId, [u8; 64]);

/// Another replica, however it is reached. `Database` is one; a Git remote is another, as
/// `git::GitPeer` (with the `git` feature).
pub trait Peer {
    fn scope(&self) -> String;
    fn have(&self) -> Result<BTreeSet<Have>, Error>;
    fn fetch(&self, want: &BTreeSet<Have>) -> Result<Vec<Vec<u8>>, Error>;
    fn send(&mut self, operations: &[Vec<u8>]) -> Result<Merged, Error>;
}

pub struct Database {
    file: redb::Database,
    seed: [u8; 32],
    actor: ActorId,
    scope: String,
    actors: BTreeSet<ActorId>,
    ops: BTreeMap<OpId, Op>,
    /// Ids signed twice with different contents: both, kept as evidence, neither counted.
    disowned: BTreeMap<OpId, (Op, Op)>,
    state: State,
    reasoned: Reasoned,
    next: u64,
}

impl Database {
    /// Open or create the database at `path`. `seed` is this replica's Ed25519 secret key;
    /// keep it out of the database's directory, and keep the Git transport's clone
    /// (`git::GitPeer`) beside the file, never inside that directory either.
    pub fn open(path: &Path, seed: &[u8; 32], scope: &str) -> Result<Self, Error> {
        Self::load(redb::Database::create(path).map_err(storage)?, seed, scope)
    }

    /// A database that lives and dies with the process. For tests and scratch work.
    pub fn in_memory(seed: &[u8; 32], scope: &str) -> Result<Self, Error> {
        let file = redb::Database::builder()
            .create_with_backend(redb::backends::InMemoryBackend::new())
            .map_err(storage)?;
        Self::load(file, seed, scope)
    }

    fn load(file: redb::Database, seed: &[u8; 32], scope: &str) -> Result<Self, Error> {
        let actor = SigningKey::from_bytes(seed).verifying_key().to_bytes();
        let tx = file.begin_write().map_err(storage)?;
        let (actors, stored) = {
            let mut meta = tx.open_table(META).map_err(storage)?;
            let found = |name: &str, meta: &redb::Table<&str, &[u8]>| {
                meta.get(name)
                    .map(|v| v.map(|v| v.value().to_vec()))
                    .map_err(storage)
            };
            match (found("format", &meta)?, found("scope", &meta)?) {
                (None, None) => {
                    meta.insert("format", FORMAT).map_err(storage)?;
                    meta.insert("scope", scope.as_bytes()).map_err(storage)?;
                }
                (Some(format), Some(kept)) => {
                    if format != FORMAT {
                        return Err(Error::Open("another format".into()));
                    }
                    if kept != scope.as_bytes() {
                        return Err(Error::Open(format!(
                            "it keeps scope {:?}",
                            String::from_utf8_lossy(&kept)
                        )));
                    }
                }
                _ => return Err(Error::Open("half a header".into())),
            }
            let mut table = tx.open_table(ACTORS).map_err(storage)?;
            table.insert(actor.as_slice(), ()).map_err(storage)?;
            let mut actors = BTreeSet::new();
            for row in table.iter().map_err(storage)? {
                let (k, _) = row.map_err(storage)?;
                let k: ActorId = k
                    .value()
                    .try_into()
                    .map_err(|_| Error::Open("an actor key of the wrong length".into()))?;
                actors.insert(k);
            }
            let table = tx.open_table(OPS).map_err(storage)?;
            let mut stored = vec![];
            for row in table.iter().map_err(storage)? {
                let (_, v) = row.map_err(storage)?;
                stored.push(v.value().to_vec());
            }
            (actors, stored)
        };
        tx.commit().map_err(storage)?;
        let mut db = Database {
            file,
            seed: *seed,
            actor,
            scope: scope.into(),
            actors,
            ops: BTreeMap::new(),
            disowned: BTreeMap::new(),
            state: State::default(),
            reasoned: Reasoned::default(),
            next: 0,
        };
        // what is on disk is checked like anything delivered: a file is not trusted for being mine
        for bytes in stored {
            let op =
                Op::decode(&bytes).map_err(|e| Error::Open(format!("a stored operation: {e}")))?;
            if op.scope != db.scope || !db.actors.contains(&op.id.actor) {
                return Err(Error::Open(
                    "a stored operation of another scope or actor".into(),
                ));
            }
            db.place(op);
        }
        db.next = db
            .ops
            .keys()
            .chain(db.disowned.keys())
            .filter(|id| id.actor == db.actor)
            .map(|id| id.counter + 1)
            .max()
            .unwrap_or(0);
        db.project();
        Ok(db)
    }

    /// Put a checked operation where it belongs in memory. True if it changed anything.
    fn place(&mut self, op: Op) -> Placed {
        if let Some((a, b)) = self.disowned.get(&op.id) {
            return if *a == op || *b == op {
                Placed::Known
            } else {
                Placed::Ignored
            };
        }
        match self.ops.get(&op.id) {
            None => {
                self.ops.insert(op.id, op);
                Placed::Kept
            }
            Some(known) if *known == op => Placed::Known,
            Some(_) => {
                let first = self.ops.remove(&op.id).expect("it was just found");
                self.disowned.insert(op.id, (first, op));
                Placed::Disowned
            }
        }
    }

    fn project(&mut self) {
        self.state = State::of(&self.ops);
        self.reasoned = Reasoned::of(&self.ops, &self.state);
    }

    pub fn actor(&self) -> ActorId {
        self.actor
    }

    /// Accept operations signed by this key from now on.
    pub fn enroll(&mut self, actor: ActorId) -> Result<(), Error> {
        let tx = self.file.begin_write().map_err(storage)?;
        tx.open_table(ACTORS)
            .map_err(storage)?
            .insert(actor.as_slice(), ())
            .map_err(storage)?;
        tx.commit().map_err(storage)?;
        self.actors.insert(actor);
        Ok(())
    }

    /// Begin a transaction. Nothing is written until it commits, and then all of it is.
    pub fn begin(&mut self, provenance: Provenance) -> Transaction<'_> {
        Transaction {
            heads: BTreeMap::new(),
            drafts: vec![],
            provenance,
            db: self,
        }
    }

    /// The statements the engine reasons from, as nibli-kr text, in id order.
    pub fn snapshot(&self) -> String {
        self.reasoned.snapshot()
    }

    /// The statements the engine reasons from, with their ids.
    pub fn statements(&self) -> &[(OpId, String)] {
        &self.reasoned.statements
    }

    /// A fresh engine holding exactly the snapshot.
    pub fn engine(&self) -> Result<NibliEngine, Error> {
        self.reasoned.engine().map_err(Error::Open)
    }

    /// Every statement, by id, with what its operations leave of it.
    pub fn all(&self) -> Vec<(OpId, Status)> {
        self.state.statements(&self.ops).collect()
    }

    /// One statement, with what its operations leave of it.
    pub fn status(&self, statement: OpId) -> Option<Status> {
        self.state
            .statements(&self.ops)
            .find(|(id, _)| *id == statement)
            .map(|(_, s)| s)
    }

    /// Statements whose concurrent changes nobody has resolved.
    pub fn conflicts(&self) -> Vec<Conflict> {
        self.state
            .statements(&self.ops)
            .filter_map(|(statement, status)| match status {
                Status::Conflict { heads } => Some(Conflict {
                    statement,
                    heads: heads
                        .iter()
                        .map(|h| (*h, self.ops[h].change, self.ops[h].payload.clone()))
                        .collect(),
                }),
                _ => None,
            })
            .collect()
    }

    /// Active statements kept out of reasoning because together they break a constraint,
    /// and what the engine said was broken.
    pub fn constraint_conflicts(&self) -> (&BTreeSet<OpId>, &[String]) {
        (&self.reasoned.flagged, &self.reasoned.problems)
    }

    /// Checks the engine could not decide on the snapshot.
    pub fn undecided(&self) -> &[String] {
        &self.reasoned.undecided
    }

    /// Operations kept but not counted, with the reason.
    pub fn held(&self) -> &BTreeMap<OpId, Held> {
        &self.state.held
    }

    /// Ids whose actor signed two contents. Neither counts.
    pub fn disowned(&self) -> Vec<OpId> {
        self.disowned.keys().copied().collect()
    }

    /// Every operation kept here, in its byte form.
    pub fn operations(&self) -> Vec<Vec<u8>> {
        let mut all: Vec<Vec<u8>> = self.ops.values().map(Op::encode).collect();
        for (a, b) in self.disowned.values() {
            all.push(a.encode());
            all.push(b.encode());
        }
        all
    }

    /// Take in delivered operations. Each is checked alone; what passes is written in one
    /// redb transaction. A delivery can arrive in any order, in parts, and more than once.
    pub fn merge(&mut self, delivered: &[Vec<u8>]) -> Result<Merged, Error> {
        let mut report = Merged::default();
        let mut fresh: Vec<Op> = vec![];
        for bytes in delivered {
            let op = match Op::decode(bytes) {
                Ok(op) => op,
                Err(e) => {
                    report.refused.push(Refusal::Malformed(e));
                    continue;
                }
            };
            if op.scope != self.scope {
                report.refused.push(Refusal::Scope(op.scope));
            } else if !self.actors.contains(&op.id.actor) {
                report.refused.push(Refusal::Unenrolled(op.id.actor));
            } else {
                fresh.push(op);
            }
        }
        // decide in memory first, on a copy of what an operation can touch, then write once
        let mut writes: Vec<(Vec<u8>, Vec<u8>)> = vec![];
        let (ops, disowned) = (self.ops.clone(), self.disowned.clone());
        for op in fresh {
            let (id, bytes) = (op.id, op.encode());
            match self.place(op) {
                Placed::Kept => {
                    writes.push((variant(&id, 0), bytes));
                    report.kept.push(id);
                }
                Placed::Disowned => {
                    writes.push((variant(&id, 1), bytes));
                    report.disowned.push(id);
                }
                Placed::Known => report.known += 1,
                Placed::Ignored => {}
            }
        }
        if writes.is_empty() {
            return Ok(report);
        }
        if let Err(e) = self.write(&writes) {
            self.ops = ops;
            self.disowned = disowned;
            return Err(e);
        }
        self.next = self.next.max(
            report
                .kept
                .iter()
                .chain(&report.disowned)
                .filter(|id| id.actor == self.actor)
                .map(|id| id.counter + 1)
                .max()
                .unwrap_or(0),
        );
        self.project();
        Ok(report)
    }

    #[cfg(not(nibli_db_broken = "nonatomic"))]
    fn write(&self, rows: &[(Vec<u8>, Vec<u8>)]) -> Result<(), Error> {
        let tx = self.file.begin_write().map_err(storage)?;
        {
            let mut table = tx.open_table(OPS).map_err(storage)?;
            for (k, v) in rows {
                table.insert(k.as_slice(), v.as_slice()).map_err(storage)?;
            }
        }
        tx.commit().map_err(storage)
    }

    /// The deliberately broken build of roadmap/DB1.md, Anti-fake: every operation is
    /// written in a transaction of its own.
    #[cfg(nibli_db_broken = "nonatomic")]
    fn write(&self, rows: &[(Vec<u8>, Vec<u8>)]) -> Result<(), Error> {
        for (k, v) in rows {
            let tx = self.file.begin_write().map_err(storage)?;
            tx.open_table(OPS)
                .map_err(storage)?
                .insert(k.as_slice(), v.as_slice())
                .map_err(storage)?;
            tx.commit().map_err(storage)?;
        }
        Ok(())
    }
}

enum Placed {
    Kept,
    Known,
    Disowned,
    /// A third content for an id already disowned: nothing more to learn from it.
    Ignored,
}

fn variant(id: &OpId, n: u8) -> Vec<u8> {
    let mut k = id.key().to_vec();
    k.push(n);
    k
}

impl Peer for Database {
    fn scope(&self) -> String {
        self.scope.clone()
    }
    fn have(&self) -> Result<BTreeSet<Have>, Error> {
        let mut have: BTreeSet<Have> = self.ops.values().map(|op| (op.id, op.signature)).collect();
        for (a, b) in self.disowned.values() {
            have.insert((a.id, a.signature));
            have.insert((b.id, b.signature));
        }
        Ok(have)
    }
    fn fetch(&self, want: &BTreeSet<Have>) -> Result<Vec<Vec<u8>>, Error> {
        let mut out = vec![];
        for (id, signature) in want {
            let both = self.disowned.get(id);
            let found = self
                .ops
                .get(id)
                .into_iter()
                .chain(both.map(|(a, _)| a))
                .chain(both.map(|(_, b)| b))
                .find(|op| op.signature == *signature);
            if let Some(op) = found {
                out.push(op.encode());
            }
        }
        Ok(out)
    }
    fn send(&mut self, operations: &[Vec<u8>]) -> Result<Merged, Error> {
        self.merge(operations)
    }
}

/// What a sync moved: what came in, and what went out.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Synced {
    pub received: Merged,
    pub sent: Merged,
}

/// Bring two replicas of one scope to the same set of operations. A peer of another scope
/// is refused before anything is asked of it or sent to it.
pub fn sync(local: &mut Database, remote: &mut dyn Peer) -> Result<Synced, Error> {
    let theirs = remote.scope();
    if theirs != local.scope {
        return Err(Error::Scope {
            ours: local.scope.clone(),
            theirs,
        });
    }
    let (mine, yours) = (local.have()?, remote.have()?);
    let wanted: BTreeSet<Have> = yours.difference(&mine).copied().collect();
    let owed: BTreeSet<Have> = mine.difference(&yours).copied().collect();
    let received = local.merge(&remote.fetch(&wanted)?)?;
    let sent = remote.send(&local.fetch(&owed)?)?;
    Ok(Synced { received, sent })
}

struct Draft {
    target: Option<OpId>,
    parents: Vec<OpId>,
    change: Change,
    payload: Option<String>,
}

/// A transaction on one replica. Dropping it without `commit` leaves the database as it was.
pub struct Transaction<'a> {
    db: &'a mut Database,
    /// Heads of the statements this transaction has touched, as it leaves them.
    heads: BTreeMap<OpId, Vec<OpId>>,
    drafts: Vec<Draft>,
    provenance: Provenance,
}

impl Transaction<'_> {
    fn next_id(&self) -> OpId {
        OpId {
            actor: self.db.actor,
            counter: self.db.next + self.drafts.len() as u64,
        }
    }

    fn heads_of(&self, statement: OpId) -> Result<Vec<OpId>, Error> {
        self.heads
            .get(&statement)
            .or_else(|| self.db.state.heads.get(&statement))
            .cloned()
            .ok_or_else(|| Error::Change(format!("there is no statement {statement}")))
    }

    fn is_retraction(&self, id: &OpId) -> bool {
        match self.db.ops.get(id) {
            Some(op) => op.change == Change::Retract,
            None => self.drafts[(id.counter - self.db.next) as usize].change == Change::Retract,
        }
    }

    fn push(
        &mut self,
        statement: Option<OpId>,
        parents: Vec<OpId>,
        change: Change,
        text: Option<&str>,
    ) -> OpId {
        let id = self.next_id();
        self.heads.insert(statement.unwrap_or(id), vec![id]);
        self.drafts.push(Draft {
            target: statement,
            parents,
            change,
            payload: text.map(str::to_owned),
        });
        id
    }

    /// A new statement. The id returned is the statement's from now on.
    pub fn assert(&mut self, text: &str) -> OpId {
        self.push(None, vec![], Change::Assert, Some(text))
    }

    /// New text for a statement. On a statement in conflict this resolves it: the new
    /// operation follows every one of the conflicting changes.
    pub fn correct(&mut self, statement: OpId, text: &str) -> Result<OpId, Error> {
        let parents = self.heads_of(statement)?;
        Ok(self.push(Some(statement), parents, Change::Correct, Some(text)))
    }

    /// Withdraw a statement. On a statement in conflict this resolves it.
    pub fn retract(&mut self, statement: OpId) -> Result<OpId, Error> {
        let parents = self.heads_of(statement)?;
        Ok(self.push(Some(statement), parents, Change::Retract, None))
    }

    /// Make a withdrawn statement active again, with the text given.
    pub fn restore(&mut self, statement: OpId, text: &str) -> Result<OpId, Error> {
        let parents = self.heads_of(statement)?;
        if !parents.iter().all(|p| self.is_retraction(p)) {
            return Err(Error::Change(format!(
                "statement {statement} is not withdrawn"
            )));
        }
        Ok(self.push(Some(statement), parents, Change::Restore, Some(text)))
    }

    /// Commit: every operation of this transaction, or none. Refused, and the file left
    /// untouched, if a statement is not one nibli-kr statement or if the engine could not
    /// hold the resulting statements together.
    pub fn commit(self) -> Result<Vec<OpId>, Error> {
        let Transaction {
            db,
            drafts,
            provenance,
            ..
        } = self;
        if drafts.is_empty() {
            return Ok(vec![]);
        }
        let batch = Batch {
            first: db.next,
            len: drafts.len() as u32,
        };
        let mut candidate = db.ops.clone();
        let mut rows = vec![];
        let mut ids = vec![];
        for (i, draft) in drafts.into_iter().enumerate() {
            if let Some(text) = &draft.payload {
                one_statement(text).map_err(Error::Statement)?;
            }
            let id = OpId {
                actor: db.actor,
                counter: batch.first + i as u64,
            };
            let mut parents = draft.parents;
            parents.sort();
            let op = Op {
                id,
                scope: db.scope.clone(),
                target: draft.target.unwrap_or(id),
                parents,
                change: draft.change,
                payload: draft.payload,
                provenance: provenance.clone(),
                batch,
                signature: [0; 64],
            }
            .sign(&db.seed);
            rows.push((variant(&id, 0), op.encode()));
            ids.push(id);
            candidate.insert(id, op);
        }
        let state = State::of(&candidate);
        if let Some(why) = ids.iter().find_map(|id| state.held.get(id)) {
            return Err(Error::Change(format!(
                "the transaction does not apply: {why:?}"
            )));
        }
        let reasoned = Reasoned::of(&candidate, &state);
        if !reasoned.flagged.is_subset(&db.reasoned.flagged) {
            return Err(Error::Inconsistent(reasoned.problems));
        }
        db.write(&rows)?;
        db.ops = candidate;
        db.state = state;
        db.reasoned = reasoned;
        db.next = batch.first + u64::from(batch.len);
        Ok(ids)
    }
}
