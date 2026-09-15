//! Fixed-width cryptographic primitives and domain-separated identifiers.
//!
//! Every identifier is a distinct newtype over a fixed-width byte array, so the
//! type system refuses to pass an [`ActorId`] where an [`EntityId`] is expected
//! even though both are 32-byte hashes. The inner bytes are private: an
//! identifier that names content can only be produced by hashing that content
//! under its own domain context ([`domain`]), and the one way to build one from
//! raw bytes, [`from_bytes`](EntityId::from_bytes), is for deserialization and
//! says nothing about whether the bytes were derived correctly.
//!
//! Domain separation uses BLAKE3's key-derivation mode: the context string is
//! bound into the hash, so the same bytes hashed as an operation and as a
//! capsule yield unrelated identifiers, and a signature over one domain can
//! never be replayed in another.

use std::fmt;

use ed25519_dalek::{Signature, SigningKey, VerifyingKey};

use crate::canonical::{CanonicalDecode, CanonicalEncode, DecodeError, read_array};

/// Lower-case hex of a byte string.
pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The domain contexts. Each identifier kind hashes under its own context, and
/// the operation signature has one of its own.
pub mod domain {
    /// Persistent identity, derived from an entity's root public key.
    pub const ENTITY: &str = "lucy-d/v1/entity-id";
    /// A specific signing key, derived from its public bytes.
    pub const KEY: &str = "lucy-d/v1/key-id";
    /// An authorized operation stream (one vector-clock axis).
    pub const ACTOR: &str = "lucy-d/v1/actor-id";
    /// A physical or logical resource provider, derived from its public key.
    pub const HOST: &str = "lucy-d/v1/host-id";
    /// A computational capability, derived from its declared name.
    pub const EXPERT: &str = "lucy-d/v1/expert-id";
    /// An operation, derived from its canonical body (provenance and payload).
    pub const OPERATION: &str = "lucy-d/v1/operation-id";
    /// A capsule, derived from its canonical bytes.
    pub const CAPSULE: &str = "lucy-d/v1/capsule-id";
    /// An evidence item, derived from its canonical bytes.
    pub const EVIDENCE: &str = "lucy-d/v1/evidence-id";
    /// A predicate or functor symbol, derived from its name.
    pub const SYMBOL: &str = "lucy-d/v1/symbol-id";
    /// A logic variable, derived from its name.
    pub const VARIABLE: &str = "lucy-d/v1/variable-id";
    /// The message domain of an operation signature.
    pub const OPERATION_SIGNATURE: &str = "lucy-d/v1/operation-signature";
}

/// BLAKE3 key derivation: `context` is bound into the hash of `material`.
pub fn derive(context: &str, material: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(context);
    hasher.update(material);
    *hasher.finalize().as_bytes()
}

macro_rules! define_id {
    ($(#[$meta:meta])* $name:ident, $len:expr) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name([u8; $len]);

        impl $name {
            /// The width in bytes.
            pub const LEN: usize = $len;

            /// Wraps raw bytes. This asserts nothing about how they were
            /// derived; it exists for deserialization and test fixtures.
            pub const fn from_bytes(bytes: [u8; $len]) -> Self {
                Self(bytes)
            }

            /// The raw bytes.
            pub const fn as_bytes(&self) -> &[u8; $len] {
                &self.0
            }

            /// Lower-case hex.
            pub fn to_hex(&self) -> String {
                hex(&self.0)
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}({})", stringify!($name), self.to_hex())
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&self.to_hex())
            }
        }

        impl AsRef<[u8]> for $name {
            fn as_ref(&self) -> &[u8] {
                &self.0
            }
        }

        impl CanonicalEncode for $name {
            /// The raw bytes, no length prefix: the width is fixed by the type.
            fn canonical_encode(&self, out: &mut Vec<u8>) {
                out.extend_from_slice(&self.0);
            }
        }

        impl CanonicalDecode for $name {
            fn canonical_decode(input: &mut &[u8]) -> Result<Self, DecodeError> {
                read_array::<$len>(input).map(Self)
            }
        }
    };
}

// ── cryptographic primitives ──

define_id!(
    /// A plain BLAKE3 hash, used where content is referenced by digest without
    /// a domain of its own (for example a missing memory).
    Blake3Hash,
    32
);
define_id!(
    /// An Ed25519 public key.
    Ed25519PublicKey,
    32
);
define_id!(
    /// An Ed25519 signature.
    Ed25519Signature,
    64
);

// ── infrastructure identities ──

define_id!(
    /// A persistent identity (Lucy herself, a person, a host operator).
    EntityId,
    32
);
define_id!(
    /// A specific cryptographic key.
    KeyId,
    32
);
define_id!(
    /// An authorized operation stream: one axis of the causal frontier.
    ActorId,
    32
);
define_id!(
    /// A physical or logical resource provider.
    HostId,
    32
);
define_id!(
    /// A computational capability.
    ExpertId,
    32
);

// ── domain-separated object identifiers ──

define_id!(
    /// The identity of an operation: BLAKE3 over its canonical body under the
    /// operation domain.
    OperationId,
    32
);
define_id!(
    /// The identity of a capsule.
    CapsuleId,
    32
);
define_id!(
    /// The identity of an evidence item.
    EvidenceId,
    32
);
define_id!(
    /// The identity of a predicate or functor symbol.
    SymbolId,
    32
);
define_id!(
    /// The identity of a logic variable.
    VariableId,
    32
);

impl Blake3Hash {
    /// The plain (undomained) BLAKE3 hash of `bytes`.
    pub fn of(bytes: &[u8]) -> Self {
        Self(*blake3::hash(bytes).as_bytes())
    }
}

impl EntityId {
    /// The identity rooted in `root_key`.
    pub fn derive(root_key: &Ed25519PublicKey) -> Self {
        Self(derive(domain::ENTITY, root_key.as_bytes()))
    }
}

impl KeyId {
    /// The identifier of a public key.
    pub fn of(key: &Ed25519PublicKey) -> Self {
        Self(derive(domain::KEY, key.as_bytes()))
    }
}

impl ActorId {
    /// The stream `stream` of `entity`. Different stream labels give one entity
    /// independent causal axes, which is what lets it delegate execution
    /// without sharing a key.
    pub fn derive(entity: &EntityId, stream: &[u8]) -> Self {
        let mut material = Vec::with_capacity(EntityId::LEN + stream.len());
        material.extend_from_slice(entity.as_bytes());
        material.extend_from_slice(stream);
        Self(derive(domain::ACTOR, &material))
    }
}

impl HostId {
    /// The host identified by `key`.
    pub fn derive(key: &Ed25519PublicKey) -> Self {
        Self(derive(domain::HOST, key.as_bytes()))
    }
}

impl ExpertId {
    /// The capability named `name`.
    pub fn of_name(name: &str) -> Self {
        Self(derive(domain::EXPERT, name.as_bytes()))
    }
}

impl OperationId {
    /// The identity of the operation whose canonical body is `body`.
    pub fn of_body(body: &[u8]) -> Self {
        Self(derive(domain::OPERATION, body))
    }
}

impl CapsuleId {
    /// The identity of the capsule whose canonical bytes are `bytes`.
    pub fn of_bytes(bytes: &[u8]) -> Self {
        Self(derive(domain::CAPSULE, bytes))
    }
}

impl EvidenceId {
    /// The identity of the evidence whose canonical bytes are `bytes`.
    pub fn of_bytes(bytes: &[u8]) -> Self {
        Self(derive(domain::EVIDENCE, bytes))
    }
}

impl SymbolId {
    /// The symbol named `name`. Names are hashed as their UTF-8 bytes; the
    /// vocabulary they must belong to is a policy of the layer above.
    pub fn of_name(name: &str) -> Self {
        Self(derive(domain::SYMBOL, name.as_bytes()))
    }
}

impl VariableId {
    /// The variable named `name`.
    pub fn of_name(name: &str) -> Self {
        Self(derive(domain::VARIABLE, name.as_bytes()))
    }
}

/// Why a signature did not verify.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignatureError {
    /// The public key bytes are not a valid Ed25519 point.
    InvalidPublicKey,
    /// The signature is not valid for the message under the key.
    Invalid,
}

impl fmt::Display for SignatureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SignatureError::InvalidPublicKey => write!(f, "invalid Ed25519 public key"),
            SignatureError::Invalid => write!(f, "signature does not verify"),
        }
    }
}

impl std::error::Error for SignatureError {}

impl Ed25519PublicKey {
    /// The public half of a signing key.
    pub fn from_signing_key(key: &SigningKey) -> Self {
        Self(key.verifying_key().to_bytes())
    }

    /// Verifies `signature` over `message` under this key, with the strict
    /// (non-malleable) verification rules.
    pub fn verify(
        &self,
        message: &[u8],
        signature: &Ed25519Signature,
    ) -> Result<(), SignatureError> {
        let key =
            VerifyingKey::from_bytes(&self.0).map_err(|_| SignatureError::InvalidPublicKey)?;
        let signature = Signature::from_bytes(&signature.0);
        key.verify_strict(message, &signature)
            .map_err(|_| SignatureError::Invalid)
    }
}

impl Ed25519Signature {
    /// Signs `message` with `key`. Ed25519 is deterministic: the same key and
    /// message always yield the same signature.
    pub fn sign(key: &SigningKey, message: &[u8]) -> Self {
        use ed25519_dalek::Signer;
        Self(key.sign(message).to_bytes())
    }
}

/// Verifies a signature under a key given only as bytes; used by the tests'
/// tamper checks. Re-exported dalek types are the signing-side API.
pub use ed25519_dalek::SigningKey as Ed25519SigningKey;
