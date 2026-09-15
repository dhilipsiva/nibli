//! Lucy D, Phase 1: the core types of a persistent epistemic identity.
//!
//! Lucy is an entity whose memory is a signed, append-only log of operations,
//! replicated across hosts, that survives the eviction of any one copy and
//! records what it does not know as durable state rather than as a gap. This
//! crate holds only the data structures and their normative encoding. It does
//! not store, replicate, reason, or authenticate anything beyond a signature
//! over bytes; those are later phases.
//!
//! Four commitments hold throughout:
//!
//! - **Fixed-width, domain-separated identifiers** ([`crypto`]). Every id is its
//!   own type over a fixed byte array, hashed under its own BLAKE3 derivation
//!   context, and can only be built from content or from explicitly unverified
//!   bytes.
//! - **One byte representation per value** ([`canonical`]). Hand-written
//!   encoders, a decoder that rejects anything non-canonical, and the round
//!   trip `decode(encode(v)) == v` as the injectivity argument.
//! - **Causality by content and by count** ([`provenance`]). Parent hash links
//!   plus a vector clock; wall time is an observation, never an order.
//! - **Claims apart from transport, and ignorance as state** ([`epistemic`],
//!   [`operation`]). A claim carries its modality and evidence; an uncertainty
//!   carries its reason, frontier and considered evidence; a reconsideration
//!   amends history without deleting it.
//!
//! # Departures from the Phase 1 handoff
//!
//! The type names of the handoff are kept. Where its shapes could not express
//! what they promised, they were changed, and each change is deliberate:
//!
//! - `Provenance` gained `parents` (the Merkle links a DAG needs) and
//!   `signing_key` (a verifier must know which key to check).
//! - `canonical_encode` is infallible and lengths are `u64`; failure lives in
//!   `canonical_decode`, which the handoff lacked.
//! - The identifier newtypes keep their bytes private; `from_bytes` exists for
//!   deserialization and says nothing about derivation.
//! - `ClaimModality::Reported` names its source, or the source-based
//!   uncertainty reasons could never be computed.
//! - `EpistemicDisposition` separates `Rejected` (evidence against) from
//!   `Withdrawn` (no longer held).
//! - `HostAction` gained `Resume` (dormancy is not a terminus) and
//!   `RevokeCapabilities` names what it revokes.
//! - `OperationPayload::KeyEvent` records key registration and revocation, the
//!   minimum for delegated execution to be representable.
//! - Evidence and capability collections are ordered sets, so their encoding
//!   has one order.
//!
//! # The seam with nibli
//!
//! Lucy is the multi-actor, signed belief base; nibli is the deterministic
//! reasoner over a materialized view of it. A `Derived` claim's evidence is
//! meant to reference a nibli proof envelope by [`EvidenceId`], `Reconsider`
//! maps onto nibli's retract-and-rebuild, and `UnsupportedInference` is where a
//! nibli `UNKNOWN` lands. That mapping is documented here and built later; this
//! crate depends on no nibli crate.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod canonical;
pub mod crypto;
pub mod epistemic;
pub mod operation;
pub mod provenance;

pub use canonical::{CanonicalDecode, CanonicalEncode, DecodeError};
pub use crypto::{
    ActorId, Blake3Hash, CapsuleId, Ed25519PublicKey, Ed25519Signature, Ed25519SigningKey,
    EntityId, EvidenceId, ExpertId, HostId, KeyId, OperationId, SignatureError, SymbolId,
    VariableId,
};
pub use epistemic::{
    ClaimModality, DurableUncertainty, EpistemicClaim, EpistemicDisposition, Proposition, Term,
    UncertaintyReason,
};
pub use operation::{
    AuthenticatedOperation, Capability, HostAction, KeyAction, OperationPayload, PeerScope,
    SignError, VerifyError,
};
pub use provenance::{CausalFrontier, Provenance, ProvenanceError};

#[cfg(test)]
mod tests;
