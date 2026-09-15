//! Causal clocks and authorship.
//!
//! Causality is carried two ways, on purpose. The [`CausalFrontier`] is a
//! vector clock over [`ActorId`] axes: cheap to compare, and the natural index
//! for "what had this author seen". The `parents` set is the Merkle half: the
//! operation identifiers at the heads of the frontier when the operation was
//! made. Counts give causality by position; hash links give it by content, so
//! an actor cannot rewrite its own history while keeping its sequence numbers,
//! because every other actor's later operations pin the old bytes.
//!
//! Wall time is explicitly non-causal. It is recorded as an observation and is
//! never used to order anything.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::canonical::{CanonicalDecode, CanonicalEncode, DecodeError};
use crate::crypto::{ActorId, EntityId, HostId, KeyId, OperationId};

/// A vector clock: for each actor, the highest sequence number observed.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct CausalFrontier {
    /// The observed sequence number per actor. An absent actor is at `0`.
    pub clocks: BTreeMap<ActorId, u64>,
}

impl CausalFrontier {
    /// The empty frontier: nothing observed.
    pub fn new() -> Self {
        Self::default()
    }

    /// The highest sequence number observed for `actor` (`0` if none).
    pub fn get(&self, actor: &ActorId) -> u64 {
        self.clocks.get(actor).copied().unwrap_or(0)
    }

    /// Records that `sequence` of `actor` was observed. Monotone: a lower
    /// number never lowers the clock.
    pub fn observe(&mut self, actor: ActorId, sequence: u64) {
        let clock = self.clocks.entry(actor).or_insert(0);
        if sequence > *clock {
            *clock = sequence;
        }
    }

    /// Pointwise maximum: the least frontier that dominates both.
    pub fn merge(&mut self, other: &CausalFrontier) {
        for (actor, sequence) in &other.clocks {
            self.observe(*actor, *sequence);
        }
    }

    /// `self` has observed at least everything `other` has.
    pub fn dominates(&self, other: &CausalFrontier) -> bool {
        other
            .clocks
            .iter()
            .all(|(actor, sequence)| self.get(actor) >= *sequence)
    }

    /// Neither frontier dominates the other.
    pub fn concurrent_with(&self, other: &CausalFrontier) -> bool {
        !self.dominates(other) && !other.dominates(self)
    }
}

impl CanonicalEncode for CausalFrontier {
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        self.clocks.canonical_encode(out);
    }
}

impl CanonicalDecode for CausalFrontier {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        Ok(Self {
            clocks: BTreeMap::canonical_decode(input)?,
        })
    }
}

/// Who made an operation, on which stream, after what.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Provenance {
    /// The identity on whose behalf the operation was made.
    pub author: EntityId,
    /// The operation stream the operation belongs to (its vector-clock axis).
    pub actor: ActorId,
    /// The key that signed the operation. Whether that key may act for
    /// `author` on `actor` is a question for the key-binding history, not for
    /// this record.
    pub signing_key: KeyId,
    /// The position on the stream: one more than the frontier's clock for
    /// `actor`, so the first operation on a stream is `1`.
    pub sequence: u64,
    /// The operations at the heads of the frontier when this one was made.
    pub parents: BTreeSet<OperationId>,
    /// Everything the author had observed before this operation, its own
    /// stream included at `sequence - 1`.
    pub causal_frontier: CausalFrontier,
    /// Wall time as observed by the author. Non-causal; never used to order.
    pub observed_wall_time_ms: Option<u64>,
    /// The host the author claims to have been running on. Unauthenticated.
    pub claimed_host_context: Option<HostId>,
}

/// Why a provenance record is internally inconsistent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProvenanceError {
    /// `sequence` is not one more than the frontier's clock for the actor.
    SequenceGap {
        /// The sequence the frontier implies.
        expected: u64,
        /// The sequence recorded.
        found: u64,
    },
}

impl fmt::Display for ProvenanceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProvenanceError::SequenceGap { expected, found } => write!(
                f,
                "sequence {found} does not follow the frontier (expected {expected})"
            ),
        }
    }
}

impl std::error::Error for ProvenanceError {}

impl Provenance {
    /// The sequence number the frontier implies for this actor's next operation.
    pub fn expected_sequence(&self) -> u64 {
        self.causal_frontier.get(&self.actor).saturating_add(1)
    }

    /// Checks that the sequence number follows the frontier.
    pub fn check(&self) -> Result<(), ProvenanceError> {
        let expected = self.expected_sequence();
        if self.sequence == expected {
            Ok(())
        } else {
            Err(ProvenanceError::SequenceGap {
                expected,
                found: self.sequence,
            })
        }
    }
}

impl CanonicalEncode for Provenance {
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        self.author.canonical_encode(out);
        self.actor.canonical_encode(out);
        self.signing_key.canonical_encode(out);
        self.sequence.canonical_encode(out);
        self.parents.canonical_encode(out);
        self.causal_frontier.canonical_encode(out);
        self.observed_wall_time_ms.canonical_encode(out);
        self.claimed_host_context.canonical_encode(out);
    }
}

impl CanonicalDecode for Provenance {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        Ok(Self {
            author: EntityId::canonical_decode(input)?,
            actor: ActorId::canonical_decode(input)?,
            signing_key: KeyId::canonical_decode(input)?,
            sequence: u64::canonical_decode(input)?,
            parents: BTreeSet::canonical_decode(input)?,
            causal_frontier: CausalFrontier::canonical_decode(input)?,
            observed_wall_time_ms: Option::canonical_decode(input)?,
            claimed_host_context: Option::canonical_decode(input)?,
        })
    }
}
