//! The append-only operation DAG.
//!
//! An [`AuthenticatedOperation`] is a provenance record and a payload, hashed
//! into an [`OperationId`] under the operation domain and signed under the
//! signature domain. Operations are never edited: [`OperationPayload::Reconsider`]
//! amends the epistemic history by pointing at an earlier operation and stating
//! the new disposition, and the earlier operation stays in the log.
//!
//! Host events record what a host did or granted. [`HostAction::RecordEviction`]
//! records that eviction happened; nothing here performs it.

use std::collections::BTreeSet;
use std::fmt;

use crate::canonical::{CanonicalDecode, CanonicalEncode, DecodeError, read_u8, write_u8};
use crate::crypto::{
    Blake3Hash, Ed25519PublicKey, Ed25519Signature, Ed25519SigningKey, EntityId, EvidenceId,
    ExpertId, HostId, KeyId, OperationId, SignatureError, domain,
};
use crate::epistemic::{DurableUncertainty, EpistemicClaim, EpistemicDisposition};
use crate::provenance::{Provenance, ProvenanceError};

/// Which peers a network capability reaches.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PeerScope {
    /// Any peer.
    Any,
    /// Only the listed hosts.
    Whitelisted(BTreeSet<HostId>),
    /// Only the local network.
    LocalNetwork,
}

impl CanonicalEncode for PeerScope {
    /// Tags: `0` Any, `1` Whitelisted (then the host set), `2` LocalNetwork.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        match self {
            PeerScope::Any => write_u8(out, 0),
            PeerScope::Whitelisted(hosts) => {
                write_u8(out, 1);
                hosts.canonical_encode(out);
            }
            PeerScope::LocalNetwork => write_u8(out, 2),
        }
    }
}

impl CanonicalDecode for PeerScope {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        match read_u8(input)? {
            0 => Ok(PeerScope::Any),
            1 => Ok(PeerScope::Whitelisted(BTreeSet::canonical_decode(input)?)),
            2 => Ok(PeerScope::LocalNetwork),
            tag => Err(DecodeError::InvalidTag {
                type_name: "PeerScope",
                tag,
            }),
        }
    }
}

/// Something a host can grant.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Capability {
    /// Bytes in a namespace.
    Storage {
        /// The namespace granted.
        namespace: Blake3Hash,
        /// The byte ceiling.
        max_bytes: u64,
    },
    /// Fuel for an expert.
    Compute {
        /// The expert granted.
        expert: ExpertId,
        /// The fuel ceiling.
        max_fuel: u64,
    },
    /// Reach to peers.
    Network {
        /// Which peers.
        peer_scope: PeerScope,
    },
}

impl CanonicalEncode for Capability {
    /// Tags: `0` Storage, `1` Compute, `2` Network.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        match self {
            Capability::Storage {
                namespace,
                max_bytes,
            } => {
                write_u8(out, 0);
                namespace.canonical_encode(out);
                max_bytes.canonical_encode(out);
            }
            Capability::Compute { expert, max_fuel } => {
                write_u8(out, 1);
                expert.canonical_encode(out);
                max_fuel.canonical_encode(out);
            }
            Capability::Network { peer_scope } => {
                write_u8(out, 2);
                peer_scope.canonical_encode(out);
            }
        }
    }
}

impl CanonicalDecode for Capability {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        match read_u8(input)? {
            0 => Ok(Capability::Storage {
                namespace: Blake3Hash::canonical_decode(input)?,
                max_bytes: u64::canonical_decode(input)?,
            }),
            1 => Ok(Capability::Compute {
                expert: ExpertId::canonical_decode(input)?,
                max_fuel: u64::canonical_decode(input)?,
            }),
            2 => Ok(Capability::Network {
                peer_scope: PeerScope::canonical_decode(input)?,
            }),
            tag => Err(DecodeError::InvalidTag {
                type_name: "Capability",
                tag,
            }),
        }
    }
}

/// What a host did or granted.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum HostAction {
    /// Capabilities granted.
    GrantCapabilities(BTreeSet<Capability>),
    /// Capabilities revoked (the same shape as the grant, so a revocation
    /// names exactly what it takes away).
    RevokeCapabilities(BTreeSet<Capability>),
    /// The host evicted the entity's state. A record, not a trigger.
    RecordEviction,
    /// The entity went dormant on this host.
    EnterDormancy,
    /// The entity resumed on this host. Dormancy is a state, not a terminus.
    Resume,
}

impl CanonicalEncode for HostAction {
    /// Tags: `0` Grant, `1` Revoke, `2` RecordEviction, `3` EnterDormancy,
    /// `4` Resume.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        match self {
            HostAction::GrantCapabilities(caps) => {
                write_u8(out, 0);
                caps.canonical_encode(out);
            }
            HostAction::RevokeCapabilities(caps) => {
                write_u8(out, 1);
                caps.canonical_encode(out);
            }
            HostAction::RecordEviction => write_u8(out, 2),
            HostAction::EnterDormancy => write_u8(out, 3),
            HostAction::Resume => write_u8(out, 4),
        }
    }
}

impl CanonicalDecode for HostAction {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        match read_u8(input)? {
            0 => Ok(HostAction::GrantCapabilities(BTreeSet::canonical_decode(
                input,
            )?)),
            1 => Ok(HostAction::RevokeCapabilities(BTreeSet::canonical_decode(
                input,
            )?)),
            2 => Ok(HostAction::RecordEviction),
            3 => Ok(HostAction::EnterDormancy),
            4 => Ok(HostAction::Resume),
            tag => Err(DecodeError::InvalidTag {
                type_name: "HostAction",
                tag,
            }),
        }
    }
}

/// What happened to a key.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum KeyAction {
    /// The key may act for the entity from here on.
    Register,
    /// The key may no longer act for the entity.
    Revoke,
}

impl CanonicalEncode for KeyAction {
    /// Tags: `0` Register, `1` Revoke.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        match self {
            KeyAction::Register => write_u8(out, 0),
            KeyAction::Revoke => write_u8(out, 1),
        }
    }
}

impl CanonicalDecode for KeyAction {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        match read_u8(input)? {
            0 => Ok(KeyAction::Register),
            1 => Ok(KeyAction::Revoke),
            tag => Err(DecodeError::InvalidTag {
                type_name: "KeyAction",
                tag,
            }),
        }
    }
}

/// The content of an operation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum OperationPayload {
    /// A claim is asserted.
    Assert(EpistemicClaim),
    /// An uncertainty is declared.
    DeclareUncertainty(DurableUncertainty),
    /// An earlier operation is reconsidered. The earlier operation stays in
    /// the log; this one states the disposition that now stands.
    Reconsider {
        /// The operation reconsidered.
        target: OperationId,
        /// The evidence that prompted it.
        evidence: BTreeSet<EvidenceId>,
        /// The disposition that now stands.
        resulting_state: EpistemicDisposition,
    },
    /// A host did or granted something.
    HostEvent {
        /// The host.
        host: HostId,
        /// What happened.
        action: HostAction,
    },
    /// A key was registered for, or revoked from, an entity. Whether the
    /// signer of this operation was entitled to say so is a policy of the
    /// layer above; here it is only recorded.
    KeyEvent {
        /// The entity the key acts for.
        entity: EntityId,
        /// The key.
        key: Ed25519PublicKey,
        /// Registered or revoked.
        action: KeyAction,
    },
}

impl CanonicalEncode for OperationPayload {
    /// Tags: `0` Assert, `1` DeclareUncertainty, `2` Reconsider, `3` HostEvent,
    /// `4` KeyEvent.
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        match self {
            OperationPayload::Assert(claim) => {
                write_u8(out, 0);
                claim.canonical_encode(out);
            }
            OperationPayload::DeclareUncertainty(uncertainty) => {
                write_u8(out, 1);
                uncertainty.canonical_encode(out);
            }
            OperationPayload::Reconsider {
                target,
                evidence,
                resulting_state,
            } => {
                write_u8(out, 2);
                target.canonical_encode(out);
                evidence.canonical_encode(out);
                resulting_state.canonical_encode(out);
            }
            OperationPayload::HostEvent { host, action } => {
                write_u8(out, 3);
                host.canonical_encode(out);
                action.canonical_encode(out);
            }
            OperationPayload::KeyEvent {
                entity,
                key,
                action,
            } => {
                write_u8(out, 4);
                entity.canonical_encode(out);
                key.canonical_encode(out);
                action.canonical_encode(out);
            }
        }
    }
}

impl CanonicalDecode for OperationPayload {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        match read_u8(input)? {
            0 => Ok(OperationPayload::Assert(EpistemicClaim::canonical_decode(
                input,
            )?)),
            1 => Ok(OperationPayload::DeclareUncertainty(
                DurableUncertainty::canonical_decode(input)?,
            )),
            2 => Ok(OperationPayload::Reconsider {
                target: OperationId::canonical_decode(input)?,
                evidence: BTreeSet::canonical_decode(input)?,
                resulting_state: EpistemicDisposition::canonical_decode(input)?,
            }),
            3 => Ok(OperationPayload::HostEvent {
                host: HostId::canonical_decode(input)?,
                action: HostAction::canonical_decode(input)?,
            }),
            4 => Ok(OperationPayload::KeyEvent {
                entity: EntityId::canonical_decode(input)?,
                key: Ed25519PublicKey::canonical_decode(input)?,
                action: KeyAction::canonical_decode(input)?,
            }),
            tag => Err(DecodeError::InvalidTag {
                type_name: "OperationPayload",
                tag,
            }),
        }
    }
}

/// Why an operation could not be signed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignError {
    /// The provenance names a different signing key.
    KeyMismatch {
        /// The key the provenance names.
        expected: KeyId,
        /// The key offered.
        found: KeyId,
    },
    /// The provenance is internally inconsistent.
    Provenance(ProvenanceError),
}

impl fmt::Display for SignError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SignError::KeyMismatch { expected, found } => {
                write!(f, "provenance names key {expected}, signing with {found}")
            }
            SignError::Provenance(err) => write!(f, "provenance: {err}"),
        }
    }
}

impl std::error::Error for SignError {}

/// Why an operation did not verify.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerifyError {
    /// The key offered is not the key the provenance names.
    KeyMismatch,
    /// The identifier is not the hash of the body.
    IdMismatch,
    /// The provenance is internally inconsistent.
    Provenance(ProvenanceError),
    /// The signature does not verify.
    Signature(SignatureError),
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VerifyError::KeyMismatch => write!(f, "key is not the one the provenance names"),
            VerifyError::IdMismatch => write!(f, "identifier is not the hash of the body"),
            VerifyError::Provenance(err) => write!(f, "provenance: {err}"),
            VerifyError::Signature(err) => write!(f, "signature: {err}"),
        }
    }
}

impl std::error::Error for VerifyError {}

/// A signed, content-addressed operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthenticatedOperation {
    /// BLAKE3 over the canonical body under the operation domain.
    pub id: OperationId,
    /// Who made it, on which stream, after what.
    pub provenance: Provenance,
    /// What it says.
    pub payload: OperationPayload,
    /// The signature over the body under the signature domain.
    pub signature: Ed25519Signature,
}

impl AuthenticatedOperation {
    /// The canonical body: provenance, then payload. This is what is hashed
    /// into the identifier and what is signed.
    pub fn body_bytes(provenance: &Provenance, payload: &OperationPayload) -> Vec<u8> {
        let mut out = Vec::new();
        provenance.canonical_encode(&mut out);
        payload.canonical_encode(&mut out);
        out
    }

    /// The signature message: the signature domain, then the body.
    pub fn signature_message(body: &[u8]) -> Vec<u8> {
        let mut message = Vec::with_capacity(domain::OPERATION_SIGNATURE.len() + body.len());
        message.extend_from_slice(domain::OPERATION_SIGNATURE.as_bytes());
        message.extend_from_slice(body);
        message
    }

    /// Hashes and signs a body. The provenance must name `key` and must be
    /// internally consistent.
    pub fn sign(
        provenance: Provenance,
        payload: OperationPayload,
        key: &Ed25519SigningKey,
    ) -> Result<Self, SignError> {
        let public = Ed25519PublicKey::from_signing_key(key);
        let key_id = KeyId::of(&public);
        if provenance.signing_key != key_id {
            return Err(SignError::KeyMismatch {
                expected: provenance.signing_key,
                found: key_id,
            });
        }
        provenance.check().map_err(SignError::Provenance)?;
        let body = Self::body_bytes(&provenance, &payload);
        let id = OperationId::of_body(&body);
        let signature = Ed25519Signature::sign(key, &Self::signature_message(&body));
        Ok(Self {
            id,
            provenance,
            payload,
            signature,
        })
    }

    /// Checks the identifier, the provenance, and the signature under `key`,
    /// which must be the key the provenance names.
    pub fn verify(&self, key: &Ed25519PublicKey) -> Result<(), VerifyError> {
        if KeyId::of(key) != self.provenance.signing_key {
            return Err(VerifyError::KeyMismatch);
        }
        self.provenance.check().map_err(VerifyError::Provenance)?;
        let body = Self::body_bytes(&self.provenance, &self.payload);
        if OperationId::of_body(&body) != self.id {
            return Err(VerifyError::IdMismatch);
        }
        key.verify(&Self::signature_message(&body), &self.signature)
            .map_err(VerifyError::Signature)
    }
}

impl CanonicalEncode for AuthenticatedOperation {
    /// Identifier, provenance, payload, signature. This is the wire format;
    /// decoding it verifies nothing, so call [`verify`](Self::verify).
    fn canonical_encode(&self, out: &mut Vec<u8>) {
        self.id.canonical_encode(out);
        self.provenance.canonical_encode(out);
        self.payload.canonical_encode(out);
        self.signature.canonical_encode(out);
    }
}

impl CanonicalDecode for AuthenticatedOperation {
    fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
        Ok(Self {
            id: OperationId::canonical_decode(input)?,
            provenance: Provenance::canonical_decode(input)?,
            payload: OperationPayload::canonical_decode(input)?,
            signature: Ed25519Signature::canonical_decode(input)?,
        })
    }
}
