// SPDX-License-Identifier: MIT OR Apache-2.0

//! One signed operation: the only thing a database stores and the only thing replicas exchange.

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use std::fmt;

/// An actor is its Ed25519 public key.
pub type ActorId = [u8; 32];

/// What an operation's bytes are signed under. A change of layout is a change of tag.
const TAG: &[u8] = b"nibli-db-op-v1\0";

/// An operation's identity: who made it, and that actor's count. Never names two contents.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OpId {
    pub actor: ActorId,
    pub counter: u64,
}

impl OpId {
    pub(crate) fn key(&self) -> [u8; 40] {
        let mut k = [0u8; 40];
        k[..32].copy_from_slice(&self.actor);
        k[32..].copy_from_slice(&self.counter.to_be_bytes());
        k
    }
}

impl fmt::Display for OpId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in self.actor {
            write!(f, "{b:02x}")?;
        }
        write!(f, ":{}", self.counter)
    }
}

impl fmt::Debug for OpId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in &self.actor[..4] {
            write!(f, "{b:02x}")?;
        }
        write!(f, "…:{}", self.counter)
    }
}

/// What an operation does to its target statement.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Change {
    /// A new statement. Its target is its own id.
    Assert,
    /// New text for a statement.
    Correct,
    /// The statement is withdrawn. The operations before it stay in the set.
    Retract,
    /// A withdrawn statement is active again, with the text given.
    Restore,
}

impl Change {
    fn byte(self) -> u8 {
        match self {
            Change::Assert => 0,
            Change::Correct => 1,
            Change::Retract => 2,
            Change::Restore => 3,
        }
    }
    fn from_byte(b: u8) -> Option<Self> {
        Some(match b {
            0 => Change::Assert,
            1 => Change::Correct,
            2 => Change::Retract,
            3 => Change::Restore,
            _ => return None,
        })
    }
}

/// The transaction an operation was committed in: `len` operations of one actor, counted from
/// `first`. A replica applies all of them or none.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Batch {
    pub first: u64,
    pub len: u32,
}

/// Who said it, and when, as the writer gave them. Kept and never used to order anything.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Provenance {
    pub source: String,
    pub time: u64,
}

/// A signed operation.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Op {
    pub id: OpId,
    pub scope: String,
    pub target: OpId,
    /// The operations on the same target this one has seen, ascending. The only ordering used.
    pub parents: Vec<OpId>,
    pub change: Change,
    /// The exact nibli-kr source of one statement; absent on a retraction.
    pub payload: Option<String>,
    pub provenance: Provenance,
    pub batch: Batch,
    pub signature: [u8; 64],
}

/// Why bytes are not an operation this database will keep.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Malformed {
    /// Not the layout of an operation, or bytes left over.
    Layout(&'static str),
    /// The signature does not verify under the actor's key.
    Signature,
    /// The fields contradict each other.
    Shape(&'static str),
    /// The payload is not exactly one nibli-kr statement.
    Statement(String),
}

impl fmt::Display for Malformed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Malformed::Layout(what) => write!(f, "not an operation: {what}"),
            Malformed::Signature => write!(f, "the signature does not verify"),
            Malformed::Shape(what) => write!(f, "the operation contradicts itself: {what}"),
            Malformed::Statement(why) => write!(f, "the payload is not one statement: {why}"),
        }
    }
}

/// The payload must be exactly one statement the front end accepts.
pub fn one_statement(text: &str) -> Result<(), Malformed> {
    match nibli_kr::parse_checked(text) {
        Ok(ast) if ast.roots.len() == 1 => Ok(()),
        Ok(ast) => Err(Malformed::Statement(format!(
            "{} statements where one is wanted",
            ast.roots.len()
        ))),
        Err(e) => Err(Malformed::Statement(format!("{e:?}"))),
    }
}

impl Op {
    /// Everything the signature covers.
    fn body(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(160 + self.payload.as_ref().map_or(0, String::len));
        out.extend_from_slice(TAG);
        out.extend_from_slice(&self.id.key());
        put_bytes(&mut out, self.scope.as_bytes());
        out.extend_from_slice(&self.target.key());
        out.extend_from_slice(&(self.parents.len() as u32).to_be_bytes());
        for p in &self.parents {
            out.extend_from_slice(&p.key());
        }
        out.push(self.change.byte());
        match &self.payload {
            None => out.push(0),
            Some(text) => {
                out.push(1);
                put_bytes(&mut out, text.as_bytes());
            }
        }
        put_bytes(&mut out, self.provenance.source.as_bytes());
        out.extend_from_slice(&self.provenance.time.to_be_bytes());
        out.extend_from_slice(&self.batch.first.to_be_bytes());
        out.extend_from_slice(&self.batch.len.to_be_bytes());
        out
    }

    /// The one byte form of this operation: its body, then its signature.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = self.body();
        out.extend_from_slice(&self.signature);
        out
    }

    /// Sign this operation with an actor's secret key, replacing whatever signature it had.
    /// The database signs its own; this is for other writers of the format, and for tests.
    pub fn sign(mut self, seed: &[u8; 32]) -> Self {
        self.signature = SigningKey::from_bytes(seed).sign(&self.body()).to_bytes();
        self
    }

    /// Read an operation and check everything that can be checked from its own bytes: the
    /// layout, the signature, the shape, and that the payload is one statement. Whether its
    /// actor is enrolled and its parents fit is the database's to decide.
    pub fn decode(bytes: &[u8]) -> Result<Self, Malformed> {
        let mut r = Reader(bytes);
        if r.take(TAG.len())? != TAG {
            return Err(Malformed::Layout("the tag"));
        }
        let id = r.id()?;
        let scope = r.string()?;
        let target = r.id()?;
        let count = r.u32()? as usize;
        if count > r.0.len() / 40 {
            return Err(Malformed::Layout("more parents than bytes"));
        }
        let mut parents = Vec::with_capacity(count);
        for _ in 0..count {
            parents.push(r.id()?);
        }
        let change = Change::from_byte(r.u8()?).ok_or(Malformed::Layout("the change"))?;
        let payload = match r.u8()? {
            0 => None,
            1 => Some(r.string()?),
            _ => return Err(Malformed::Layout("the payload mark")),
        };
        let provenance = Provenance {
            source: r.string()?,
            time: r.u64()?,
        };
        let batch = Batch {
            first: r.u64()?,
            len: r.u32()?,
        };
        let signature: [u8; 64] = r.take(64)?.try_into().expect("64 bytes were taken");
        if !r.0.is_empty() {
            return Err(Malformed::Layout("bytes after the signature"));
        }
        let op = Op {
            id,
            scope,
            target,
            parents,
            change,
            payload,
            provenance,
            batch,
            signature,
        };
        op.verify()?;
        op.shape()?;
        if let Some(text) = &op.payload {
            one_statement(text)?;
        }
        Ok(op)
    }

    #[cfg(not(nibli_db_broken = "nosig"))]
    fn verify(&self) -> Result<(), Malformed> {
        let key = VerifyingKey::from_bytes(&self.id.actor).map_err(|_| Malformed::Signature)?;
        key.verify_strict(&self.body(), &Signature::from_bytes(&self.signature))
            .map_err(|_| Malformed::Signature)
    }

    /// The deliberately broken build of roadmap/DB1.md, Anti-fake: no signature is checked.
    #[cfg(nibli_db_broken = "nosig")]
    fn verify(&self) -> Result<(), Malformed> {
        let _ = (
            VerifyingKey::from_bytes(&self.id.actor),
            Signature::from_bytes(&self.signature),
        );
        Ok(())
    }

    fn shape(&self) -> Result<(), Malformed> {
        let end = self
            .batch
            .first
            .checked_add(u64::from(self.batch.len))
            .ok_or(Malformed::Shape("the batch runs past the last counter"))?;
        if self.batch.len == 0 || self.id.counter < self.batch.first || self.id.counter >= end {
            return Err(Malformed::Shape("the counter is outside its batch"));
        }
        if self.parents.windows(2).any(|w| w[0] >= w[1]) {
            return Err(Malformed::Shape("the parents are not in ascending order"));
        }
        if self
            .parents
            .iter()
            .any(|p| p.actor == self.id.actor && p.counter >= self.id.counter)
        {
            return Err(Malformed::Shape("a parent that its own actor made later"));
        }
        match self.change {
            Change::Assert => {
                if self.target != self.id || !self.parents.is_empty() {
                    return Err(Malformed::Shape(
                        "an assertion with another target or a parent",
                    ));
                }
            }
            _ => {
                if self.target == self.id || self.parents.is_empty() {
                    return Err(Malformed::Shape("a change with no statement before it"));
                }
            }
        }
        if self.payload.is_some() == (self.change == Change::Retract) {
            return Err(Malformed::Shape(
                "a retraction with text, or another change without",
            ));
        }
        Ok(())
    }
}

fn put_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
    out.extend_from_slice(bytes);
}

struct Reader<'a>(&'a [u8]);

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], Malformed> {
        if self.0.len() < n {
            return Err(Malformed::Layout("too short"));
        }
        let (head, rest) = self.0.split_at(n);
        self.0 = rest;
        Ok(head)
    }
    fn u8(&mut self) -> Result<u8, Malformed> {
        Ok(self.take(1)?[0])
    }
    fn u32(&mut self) -> Result<u32, Malformed> {
        Ok(u32::from_be_bytes(
            self.take(4)?.try_into().expect("4 bytes"),
        ))
    }
    fn u64(&mut self) -> Result<u64, Malformed> {
        Ok(u64::from_be_bytes(
            self.take(8)?.try_into().expect("8 bytes"),
        ))
    }
    fn id(&mut self) -> Result<OpId, Malformed> {
        Ok(OpId {
            actor: self.take(32)?.try_into().expect("32 bytes"),
            counter: self.u64()?,
        })
    }
    fn string(&mut self) -> Result<String, Malformed> {
        let n = self.u32()? as usize;
        String::from_utf8(self.take(n)?.to_vec()).map_err(|_| Malformed::Layout("text not UTF-8"))
    }
}
