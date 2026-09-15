//! The epistemic layer: what is claimed, on what modality, with what evidence,
//! and, as first-class durable state, what is not known and why.
//!
//! Three things are kept apart here. A [`Proposition`] is the formal object.
//! A [`ClaimModality`] says how the claim relates to the world (seen, told,
//! derived, supposed). A [`DurableUncertainty`] is not the absence of a claim
//! but a record: this proposition was considered against this evidence, as of
//! this frontier, and could not be settled for this reason. Ignorance that is
//! written down can be synced, revisited, and resolved; ignorance that is
//! merely the gap between claims cannot.

use std::collections::BTreeSet;

use crate::canonical::{
    CanonicalDecode, CanonicalEncode, DecodeError, read_len, read_u8, write_u8,
};
use crate::crypto::{Blake3Hash, EntityId, EvidenceId, SymbolId, VariableId};
use crate::provenance::CausalFrontier;

/// The deepest term nesting the decoder accepts. Encoding has no limit; the
/// limit protects the decoder's stack from hostile input.
pub const MAX_TERM_DEPTH: usize = 64;

/// A term of the formal language.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    /// A persistent identity.
    Entity(EntityId),
    /// A symbol (a constant of the vocabulary).
    Symbol(SymbolId),
    /// A signed integer.
    Integer(i64),
    /// Text, held as UTF-8 exactly as given.
    Text(String),
    /// A logic variable.
    Variable(VariableId),
    /// A compound term: a functor applied to arguments.
    Compound {
        /// The functor symbol.
        functor: SymbolId,
        /// The arguments, in order.
        args: Vec<Term>,
    },
}

impl CanonicalEncode for Term {
    /// Tags: `0` Entity, `1` Symbol, `2` Integer, `3` Text, `4` Variable,
    /// `5` Compound (functor, then argument count, then arguments).
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        match self {
            Term::Entity(id) => {
                write_u8(out, 0);
                id.canonical_encode(out);
            }
            Term::Symbol(id) => {
                write_u8(out, 1);
                id.canonical_encode(out);
            }
            Term::Integer(value) => {
                write_u8(out, 2);
                value.canonical_encode(out);
            }
            Term::Text(text) => {
                write_u8(out, 3);
                text.canonical_encode(out);
            }
            Term::Variable(id) => {
                write_u8(out, 4);
                id.canonical_encode(out);
            }
            Term::Compound { functor, args } => {
                write_u8(out, 5);
                functor.canonical_encode(out);
                args.canonical_encode(out);
            }
        }
    }
}

impl Term {
    fn decode_at_depth(input: &mut &[u8], depth: usize) -> Result<Self, DecodeError> {
        if depth > MAX_TERM_DEPTH {
            return Err(DecodeError::Invalid(
                "term nested deeper than MAX_TERM_DEPTH",
            ));
        }
        match read_u8(input)? {
            0 => Ok(Term::Entity(EntityId::canonical_decode(input)?)),
            1 => Ok(Term::Symbol(SymbolId::canonical_decode(input)?)),
            2 => Ok(Term::Integer(i64::canonical_decode(input)?)),
            3 => Ok(Term::Text(String::canonical_decode(input)?)),
            4 => Ok(Term::Variable(VariableId::canonical_decode(input)?)),
            5 => {
                let functor = SymbolId::canonical_decode(input)?;
                let count = read_len(input)?;
                let mut args = Vec::new();
                for _ in 0..count {
                    args.push(Term::decode_at_depth(input, depth + 1)?);
                }
                Ok(Term::Compound { functor, args })
            }
            tag => Err(DecodeError::InvalidTag {
                type_name: "Term",
                tag,
            }),
        }
    }
}

impl CanonicalDecode for Term {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        Term::decode_at_depth(input, 0)
    }
}

/// A predicate applied to arguments.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Proposition {
    /// The predicate symbol.
    pub predicate: SymbolId,
    /// The arguments, in order.
    pub args: Vec<Term>,
}

impl CanonicalEncode for Proposition {
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        self.predicate.canonical_encode(out);
        self.args.canonical_encode(out);
    }
}

impl CanonicalDecode for Proposition {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        Ok(Self {
            predicate: SymbolId::canonical_decode(input)?,
            args: Vec::canonical_decode(input)?,
        })
    }
}

/// How a claim relates to the world.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClaimModality {
    /// Directly observed by the author.
    Observed,
    /// Told by `source`, whose reliability is a separate question.
    Reported {
        /// Who reported it.
        source: EntityId,
    },
    /// Derived by inference; the evidence should include the derivation.
    Derived,
    /// Entertained, not asserted.
    Hypothetical,
    /// Known to be contrary to fact, entertained for reasoning.
    Counterfactual,
    /// Taken as a premise without evidence.
    Assumed,
}

impl CanonicalEncode for ClaimModality {
    /// Tags: `0` Observed, `1` Reported (then source), `2` Derived,
    /// `3` Hypothetical, `4` Counterfactual, `5` Assumed.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        match self {
            ClaimModality::Observed => write_u8(out, 0),
            ClaimModality::Reported { source } => {
                write_u8(out, 1);
                source.canonical_encode(out);
            }
            ClaimModality::Derived => write_u8(out, 2),
            ClaimModality::Hypothetical => write_u8(out, 3),
            ClaimModality::Counterfactual => write_u8(out, 4),
            ClaimModality::Assumed => write_u8(out, 5),
        }
    }
}

impl CanonicalDecode for ClaimModality {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        match read_u8(input)? {
            0 => Ok(ClaimModality::Observed),
            1 => Ok(ClaimModality::Reported {
                source: EntityId::canonical_decode(input)?,
            }),
            2 => Ok(ClaimModality::Derived),
            3 => Ok(ClaimModality::Hypothetical),
            4 => Ok(ClaimModality::Counterfactual),
            5 => Ok(ClaimModality::Assumed),
            tag => Err(DecodeError::InvalidTag {
                type_name: "ClaimModality",
                tag,
            }),
        }
    }
}

/// A proposition, held on a modality, with its evidence.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct EpistemicClaim {
    /// The proposition claimed.
    pub proposition: Proposition,
    /// How the claim relates to the world.
    pub modality: ClaimModality,
    /// The evidence the claim rests on.
    pub evidence: BTreeSet<EvidenceId>,
}

impl CanonicalEncode for EpistemicClaim {
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        self.proposition.canonical_encode(out);
        self.modality.canonical_encode(out);
        self.evidence.canonical_encode(out);
    }
}

impl CanonicalDecode for EpistemicClaim {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        Ok(Self {
            proposition: Proposition::canonical_decode(input)?,
            modality: ClaimModality::canonical_decode(input)?,
            evidence: BTreeSet::canonical_decode(input)?,
        })
    }
}

/// Why a proposition could not be settled.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum UncertaintyReason {
    /// Every active copy of the relevant state was lost.
    TotalActiveLoss,
    /// The evidence considered does not decide it.
    InsufficientEvidence,
    /// The evidence considered points both ways.
    ConflictingEvidence,
    /// A memory this depends on is missing; its digest is known.
    MissingMemory(Blake3Hash),
    /// Concurrent operations disagree and no rule ranks them.
    UnresolvableFork,
    /// The source of the relevant evidence is unknown.
    UnknownSource,
    /// The source of the relevant evidence is not trusted.
    UntrustedSource,
    /// The relevant evidence exists but is not available here.
    UnavailableEvidence,
    /// The relevant evidence is encrypted and the key is not available here.
    EncryptedEvidenceUnavailable,
    /// Replication of the relevant state has not completed.
    ReplicationIncomplete,
    /// The relevant state is outside this replica's scope.
    OutsideReplicationScope,
    /// It is not settled which entity is meant.
    AmbiguousIdentity,
    /// It is not settled whether two records are the same continuing thing.
    AmbiguousContinuity,
    /// The inference needed is not one the reasoner supports.
    UnsupportedInference,
}

impl CanonicalEncode for UncertaintyReason {
    /// Tags `0` through `13` in declaration order; `3` (MissingMemory) is
    /// followed by the digest.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        match self {
            UncertaintyReason::TotalActiveLoss => write_u8(out, 0),
            UncertaintyReason::InsufficientEvidence => write_u8(out, 1),
            UncertaintyReason::ConflictingEvidence => write_u8(out, 2),
            UncertaintyReason::MissingMemory(hash) => {
                write_u8(out, 3);
                hash.canonical_encode(out);
            }
            UncertaintyReason::UnresolvableFork => write_u8(out, 4),
            UncertaintyReason::UnknownSource => write_u8(out, 5),
            UncertaintyReason::UntrustedSource => write_u8(out, 6),
            UncertaintyReason::UnavailableEvidence => write_u8(out, 7),
            UncertaintyReason::EncryptedEvidenceUnavailable => write_u8(out, 8),
            UncertaintyReason::ReplicationIncomplete => write_u8(out, 9),
            UncertaintyReason::OutsideReplicationScope => write_u8(out, 10),
            UncertaintyReason::AmbiguousIdentity => write_u8(out, 11),
            UncertaintyReason::AmbiguousContinuity => write_u8(out, 12),
            UncertaintyReason::UnsupportedInference => write_u8(out, 13),
        }
    }
}

impl CanonicalDecode for UncertaintyReason {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        Ok(match read_u8(input)? {
            0 => UncertaintyReason::TotalActiveLoss,
            1 => UncertaintyReason::InsufficientEvidence,
            2 => UncertaintyReason::ConflictingEvidence,
            3 => UncertaintyReason::MissingMemory(Blake3Hash::canonical_decode(input)?),
            4 => UncertaintyReason::UnresolvableFork,
            5 => UncertaintyReason::UnknownSource,
            6 => UncertaintyReason::UntrustedSource,
            7 => UncertaintyReason::UnavailableEvidence,
            8 => UncertaintyReason::EncryptedEvidenceUnavailable,
            9 => UncertaintyReason::ReplicationIncomplete,
            10 => UncertaintyReason::OutsideReplicationScope,
            11 => UncertaintyReason::AmbiguousIdentity,
            12 => UncertaintyReason::AmbiguousContinuity,
            13 => UncertaintyReason::UnsupportedInference,
            tag => {
                return Err(DecodeError::InvalidTag {
                    type_name: "UncertaintyReason",
                    tag,
                });
            }
        })
    }
}

/// Ignorance, written down: a proposition considered and not settled.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DurableUncertainty {
    /// The proposition that could not be settled.
    pub proposition: Proposition,
    /// Why not.
    pub reason: UncertaintyReason,
    /// The frontier of evidence as of which this was decided.
    pub evidence_frontier: CausalFrontier,
    /// The evidence actually considered.
    pub considered_evidence: BTreeSet<EvidenceId>,
    /// The event that opened this uncertainty.
    pub since_event: EvidenceId,
}

impl CanonicalEncode for DurableUncertainty {
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        self.proposition.canonical_encode(out);
        self.reason.canonical_encode(out);
        self.evidence_frontier.canonical_encode(out);
        self.considered_evidence.canonical_encode(out);
        self.since_event.canonical_encode(out);
    }
}

impl CanonicalDecode for DurableUncertainty {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        Ok(Self {
            proposition: Proposition::canonical_decode(input)?,
            reason: UncertaintyReason::canonical_decode(input)?,
            evidence_frontier: CausalFrontier::canonical_decode(input)?,
            considered_evidence: BTreeSet::canonical_decode(input)?,
            since_event: EvidenceId::canonical_decode(input)?,
        })
    }
}

/// Where a proposition stands after consideration.
///
/// `Rejected` and `Withdrawn` are kept apart on purpose: the first says the
/// evidence stands against the claim, the second only that the claim is no
/// longer held. Collapsing them would repeat the mistake of reading "not
/// derivable" as "false".
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum EpistemicDisposition {
    /// The claim is held.
    Supported(EpistemicClaim),
    /// The claim is held to be false, on these grounds.
    Rejected {
        /// The claim rejected.
        claim: EpistemicClaim,
        /// The evidence against it.
        grounds: BTreeSet<EvidenceId>,
    },
    /// The claim is no longer held; nothing is said about its truth.
    Withdrawn(EpistemicClaim),
    /// The proposition could not be settled.
    Uncertain(DurableUncertainty),
}

impl CanonicalEncode for EpistemicDisposition {
    /// Tags: `0` Supported, `1` Rejected (claim, then grounds), `2` Withdrawn,
    /// `3` Uncertain.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        match self {
            EpistemicDisposition::Supported(claim) => {
                write_u8(out, 0);
                claim.canonical_encode(out);
            }
            EpistemicDisposition::Rejected { claim, grounds } => {
                write_u8(out, 1);
                claim.canonical_encode(out);
                grounds.canonical_encode(out);
            }
            EpistemicDisposition::Withdrawn(claim) => {
                write_u8(out, 2);
                claim.canonical_encode(out);
            }
            EpistemicDisposition::Uncertain(uncertainty) => {
                write_u8(out, 3);
                uncertainty.canonical_encode(out);
            }
        }
    }
}

impl CanonicalDecode for EpistemicDisposition {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        match read_u8(input)? {
            0 => Ok(EpistemicDisposition::Supported(
                EpistemicClaim::canonical_decode(input)?,
            )),
            1 => Ok(EpistemicDisposition::Rejected {
                claim: EpistemicClaim::canonical_decode(input)?,
                grounds: BTreeSet::canonical_decode(input)?,
            }),
            2 => Ok(EpistemicDisposition::Withdrawn(
                EpistemicClaim::canonical_decode(input)?,
            )),
            3 => Ok(EpistemicDisposition::Uncertain(
                DurableUncertainty::canonical_decode(input)?,
            )),
            tag => Err(DecodeError::InvalidTag {
                type_name: "EpistemicDisposition",
                tag,
            }),
        }
    }
}
