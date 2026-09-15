//! The Phase 1 battery: encoding round trips (the injectivity argument),
//! non-canonical rejections, signing and tampering, golden vectors that pin
//! the encoding, and the vector-clock laws.

use std::collections::{BTreeMap, BTreeSet};

use crate::canonical::{CanonicalDecode, CanonicalEncode, DecodeError};
use crate::crypto::{
    ActorId, Blake3Hash, Ed25519PublicKey, Ed25519SigningKey, EntityId, EvidenceId, ExpertId,
    HostId, KeyId, OperationId, SymbolId, VariableId, hex,
};
use crate::epistemic::{
    ClaimModality, DurableUncertainty, EpistemicClaim, EpistemicDisposition, Proposition, Term,
    UncertaintyReason,
};
use crate::operation::{
    AuthenticatedOperation, Capability, HostAction, KeyAction, OperationPayload, PeerScope,
    SignError, VerifyError,
};
use crate::provenance::{CausalFrontier, Provenance, ProvenanceError};

// ── a small deterministic generator (xorshift64*) so the battery needs no
//    external crate and every failure is reproducible from its seed ──

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed | 1)
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn bytes32(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.chunks_mut(8) {
            chunk.copy_from_slice(&self.next().to_be_bytes()[..chunk.len()]);
        }
        out
    }

    fn text(&mut self) -> String {
        let alphabet = ['a', 'z', ' ', 'é', '日', '\u{0}', 'β'];
        let len = self.below(6) as usize;
        (0..len)
            .map(|_| alphabet[self.below(alphabet.len() as u64) as usize])
            .collect()
    }
}

fn sample_term(rng: &mut Rng, depth: usize) -> Term {
    match rng.below(if depth < 2 { 6 } else { 5 }) {
        0 => Term::Entity(EntityId::from_bytes(rng.bytes32())),
        1 => Term::Symbol(SymbolId::from_bytes(rng.bytes32())),
        2 => Term::Integer(rng.next() as i64),
        3 => Term::Text(rng.text()),
        4 => Term::Variable(VariableId::from_bytes(rng.bytes32())),
        _ => Term::Compound {
            functor: SymbolId::from_bytes(rng.bytes32()),
            args: (0..rng.below(3))
                .map(|_| sample_term(rng, depth + 1))
                .collect(),
        },
    }
}

fn sample_proposition(rng: &mut Rng) -> Proposition {
    Proposition {
        predicate: SymbolId::from_bytes(rng.bytes32()),
        args: (0..rng.below(4)).map(|_| sample_term(rng, 0)).collect(),
    }
}

fn sample_evidence(rng: &mut Rng) -> BTreeSet<EvidenceId> {
    (0..rng.below(3))
        .map(|_| EvidenceId::from_bytes(rng.bytes32()))
        .collect()
}

fn sample_claim(rng: &mut Rng) -> EpistemicClaim {
    let modality = match rng.below(6) {
        0 => ClaimModality::Observed,
        1 => ClaimModality::Reported {
            source: EntityId::from_bytes(rng.bytes32()),
        },
        2 => ClaimModality::Derived,
        3 => ClaimModality::Hypothetical,
        4 => ClaimModality::Counterfactual,
        _ => ClaimModality::Assumed,
    };
    EpistemicClaim {
        proposition: sample_proposition(rng),
        modality,
        evidence: sample_evidence(rng),
    }
}

fn sample_frontier(rng: &mut Rng) -> CausalFrontier {
    let mut frontier = CausalFrontier::new();
    for _ in 0..rng.below(4) {
        frontier.observe(ActorId::from_bytes(rng.bytes32()), rng.below(1000));
    }
    frontier
}

fn sample_uncertainty(rng: &mut Rng) -> DurableUncertainty {
    let reason = match rng.below(14) {
        0 => UncertaintyReason::TotalActiveLoss,
        1 => UncertaintyReason::InsufficientEvidence,
        2 => UncertaintyReason::ConflictingEvidence,
        3 => UncertaintyReason::MissingMemory(Blake3Hash::from_bytes(rng.bytes32())),
        4 => UncertaintyReason::UnresolvableFork,
        5 => UncertaintyReason::UnknownSource,
        6 => UncertaintyReason::UntrustedSource,
        7 => UncertaintyReason::UnavailableEvidence,
        8 => UncertaintyReason::EncryptedEvidenceUnavailable,
        9 => UncertaintyReason::ReplicationIncomplete,
        10 => UncertaintyReason::OutsideReplicationScope,
        11 => UncertaintyReason::AmbiguousIdentity,
        12 => UncertaintyReason::AmbiguousContinuity,
        _ => UncertaintyReason::UnsupportedInference,
    };
    DurableUncertainty {
        proposition: sample_proposition(rng),
        reason,
        evidence_frontier: sample_frontier(rng),
        considered_evidence: sample_evidence(rng),
        since_event: EvidenceId::from_bytes(rng.bytes32()),
    }
}

fn sample_disposition(rng: &mut Rng) -> EpistemicDisposition {
    match rng.below(4) {
        0 => EpistemicDisposition::Supported(sample_claim(rng)),
        1 => EpistemicDisposition::Rejected {
            claim: sample_claim(rng),
            grounds: sample_evidence(rng),
        },
        2 => EpistemicDisposition::Withdrawn(sample_claim(rng)),
        _ => EpistemicDisposition::Uncertain(sample_uncertainty(rng)),
    }
}

fn sample_capabilities(rng: &mut Rng) -> BTreeSet<Capability> {
    (0..rng.below(4))
        .map(|_| match rng.below(3) {
            0 => Capability::Storage {
                namespace: Blake3Hash::from_bytes(rng.bytes32()),
                max_bytes: rng.next(),
            },
            1 => Capability::Compute {
                expert: ExpertId::from_bytes(rng.bytes32()),
                max_fuel: rng.next(),
            },
            _ => Capability::Network {
                peer_scope: match rng.below(3) {
                    0 => PeerScope::Any,
                    1 => PeerScope::Whitelisted(
                        (0..rng.below(3))
                            .map(|_| HostId::from_bytes(rng.bytes32()))
                            .collect(),
                    ),
                    _ => PeerScope::LocalNetwork,
                },
            },
        })
        .collect()
}

fn sample_payload(rng: &mut Rng) -> OperationPayload {
    match rng.below(5) {
        0 => OperationPayload::Assert(sample_claim(rng)),
        1 => OperationPayload::DeclareUncertainty(sample_uncertainty(rng)),
        2 => OperationPayload::Reconsider {
            target: OperationId::from_bytes(rng.bytes32()),
            evidence: sample_evidence(rng),
            resulting_state: sample_disposition(rng),
        },
        3 => OperationPayload::HostEvent {
            host: HostId::from_bytes(rng.bytes32()),
            action: match rng.below(5) {
                0 => HostAction::GrantCapabilities(sample_capabilities(rng)),
                1 => HostAction::RevokeCapabilities(sample_capabilities(rng)),
                2 => HostAction::RecordEviction,
                3 => HostAction::EnterDormancy,
                _ => HostAction::Resume,
            },
        },
        _ => OperationPayload::KeyEvent {
            entity: EntityId::from_bytes(rng.bytes32()),
            key: Ed25519PublicKey::from_bytes(rng.bytes32()),
            action: if rng.below(2) == 0 {
                KeyAction::Register
            } else {
                KeyAction::Revoke
            },
        },
    }
}

/// A key, an actor on it, and a consistent provenance at some sequence.
fn sample_provenance(rng: &mut Rng, key: &Ed25519SigningKey) -> Provenance {
    let public = Ed25519PublicKey::from_signing_key(key);
    let author = EntityId::derive(&public);
    let actor = ActorId::derive(&author, b"stream");
    let mut causal_frontier = sample_frontier(rng);
    let own = rng.below(50);
    if own > 0 {
        causal_frontier.observe(actor, own);
    }
    Provenance {
        author,
        actor,
        signing_key: KeyId::of(&public),
        sequence: own + 1,
        parents: (0..rng.below(3))
            .map(|_| OperationId::from_bytes(rng.bytes32()))
            .collect(),
        causal_frontier,
        observed_wall_time_ms: if rng.below(2) == 0 {
            None
        } else {
            Some(rng.next())
        },
        claimed_host_context: if rng.below(2) == 0 {
            None
        } else {
            Some(HostId::from_bytes(rng.bytes32()))
        },
    }
}

fn sample_key(rng: &mut Rng) -> Ed25519SigningKey {
    Ed25519SigningKey::from_bytes(&rng.bytes32())
}

// ── round trips: decode(encode(v)) == v is the injectivity argument ──

#[test]
fn operations_round_trip_and_verify() {
    let mut rng = Rng::new(0x5eed);
    for _ in 0..300 {
        let key = sample_key(&mut rng);
        let public = Ed25519PublicKey::from_signing_key(&key);
        let op = AuthenticatedOperation::sign(
            sample_provenance(&mut rng, &key),
            sample_payload(&mut rng),
            &key,
        )
        .expect("sample provenance is consistent");
        let bytes = op.canonical_bytes();
        let back = AuthenticatedOperation::canonical_decode_exact(&bytes)
            .expect("the crate's own encoding decodes");
        assert_eq!(back, op);
        assert_eq!(back.canonical_bytes(), bytes, "re-encoding is stable");
        back.verify(&public).expect("a signed operation verifies");
    }
}

#[test]
fn terms_round_trip_at_every_depth() {
    let mut rng = Rng::new(7);
    for _ in 0..2000 {
        let term = sample_term(&mut rng, 0);
        let bytes = term.canonical_bytes();
        assert_eq!(Term::canonical_decode_exact(&bytes).unwrap(), term);
    }
}

#[test]
fn distinct_values_have_distinct_encodings() {
    let mut rng = Rng::new(11);
    let mut seen: BTreeMap<Vec<u8>, OperationPayload> = BTreeMap::new();
    for _ in 0..500 {
        let payload = sample_payload(&mut rng);
        let bytes = payload.canonical_bytes();
        if let Some(previous) = seen.get(&bytes) {
            assert_eq!(previous, &payload, "one encoding, two values");
        }
        seen.insert(bytes, payload);
    }
}

// ── non-canonical input is refused ──

fn encode_set(items: &[u64]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&(items.len() as u64).to_be_bytes());
    for item in items {
        out.extend_from_slice(&item.to_be_bytes());
    }
    out
}

#[test]
fn unordered_set_is_non_canonical() {
    let err = BTreeSet::<u64>::canonical_decode_exact(&encode_set(&[2, 1])).unwrap_err();
    assert!(matches!(err, DecodeError::NonCanonical(_)), "{err:?}");
    let err = BTreeSet::<u64>::canonical_decode_exact(&encode_set(&[1, 1])).unwrap_err();
    assert!(matches!(err, DecodeError::NonCanonical(_)), "{err:?}");
    assert_eq!(
        BTreeSet::<u64>::canonical_decode_exact(&encode_set(&[1, 2])).unwrap(),
        BTreeSet::from([1, 2])
    );
}

#[test]
fn unordered_map_is_non_canonical() {
    let mut frontier = CausalFrontier::new();
    frontier.observe(ActorId::from_bytes([9; 32]), 3);
    frontier.observe(ActorId::from_bytes([1; 32]), 5);
    let good = frontier.canonical_bytes();
    assert_eq!(
        CausalFrontier::canonical_decode_exact(&good).unwrap(),
        frontier
    );
    // Swap the two entries (each is 32 bytes of key + 8 of clock) after the count.
    let mut swapped = good[..8].to_vec();
    swapped.extend_from_slice(&good[8 + 40..]);
    swapped.extend_from_slice(&good[8..8 + 40]);
    let err = CausalFrontier::canonical_decode_exact(&swapped).unwrap_err();
    assert!(matches!(err, DecodeError::NonCanonical(_)), "{err:?}");
}

#[test]
fn trailing_bytes_truncation_and_bad_tags_are_refused() {
    let term = Term::Integer(-5);
    let mut bytes = term.canonical_bytes();
    bytes.push(0);
    assert_eq!(
        Term::canonical_decode_exact(&bytes).unwrap_err(),
        DecodeError::TrailingBytes(1)
    );
    bytes.truncate(4);
    assert_eq!(
        Term::canonical_decode_exact(&bytes).unwrap_err(),
        DecodeError::UnexpectedEnd
    );
    assert_eq!(
        Term::canonical_decode_exact(&[9]).unwrap_err(),
        DecodeError::InvalidTag {
            type_name: "Term",
            tag: 9
        }
    );
    // Tag 3 (Text), declared length 5, only two bytes present.
    let mut short = vec![3u8];
    short.extend_from_slice(&5u64.to_be_bytes());
    short.extend_from_slice(b"ab");
    assert_eq!(
        Term::canonical_decode_exact(&short).unwrap_err(),
        DecodeError::LengthOverflow
    );
    // Tag 3, declared length 2, bytes that are not UTF-8.
    let mut bad_utf8 = vec![3u8];
    bad_utf8.extend_from_slice(&2u64.to_be_bytes());
    bad_utf8.extend_from_slice(&[0xff, 0xfe]);
    assert_eq!(
        Term::canonical_decode_exact(&bad_utf8).unwrap_err(),
        DecodeError::InvalidUtf8
    );
}

#[test]
fn term_nesting_is_bounded_on_decode() {
    let mut term = Term::Integer(0);
    for _ in 0..(crate::epistemic::MAX_TERM_DEPTH + 2) {
        term = Term::Compound {
            functor: SymbolId::from_bytes([0; 32]),
            args: vec![term],
        };
    }
    let bytes = term.canonical_bytes();
    assert_eq!(
        Term::canonical_decode_exact(&bytes).unwrap_err(),
        DecodeError::Invalid("term nested deeper than MAX_TERM_DEPTH")
    );
}

// ── signing and tampering ──

fn fixed_operation() -> (Ed25519SigningKey, AuthenticatedOperation) {
    let key = Ed25519SigningKey::from_bytes(&[7u8; 32]);
    let public = Ed25519PublicKey::from_signing_key(&key);
    let author = EntityId::derive(&public);
    let actor = ActorId::derive(&author, b"main");
    let provenance = Provenance {
        author,
        actor,
        signing_key: KeyId::of(&public),
        sequence: 1,
        parents: BTreeSet::new(),
        causal_frontier: CausalFrontier::new(),
        observed_wall_time_ms: Some(1_700_000_000_000),
        claimed_host_context: None,
    };
    let payload = OperationPayload::Assert(EpistemicClaim {
        proposition: Proposition {
            predicate: SymbolId::of_name("loves"),
            args: vec![Term::Entity(author), Term::Text("you".to_string())],
        },
        modality: ClaimModality::Observed,
        evidence: BTreeSet::new(),
    });
    let op = AuthenticatedOperation::sign(provenance, payload, &key).unwrap();
    (key, op)
}

#[test]
fn tampering_is_detected() {
    let (key, op) = fixed_operation();
    let public = Ed25519PublicKey::from_signing_key(&key);
    op.verify(&public).unwrap();

    let mut wrong_payload = op.clone();
    wrong_payload.payload = OperationPayload::HostEvent {
        host: HostId::from_bytes([1; 32]),
        action: HostAction::Resume,
    };
    assert_eq!(wrong_payload.verify(&public), Err(VerifyError::IdMismatch));

    let mut wrong_id = op.clone();
    wrong_id.id = OperationId::from_bytes([0; 32]);
    assert_eq!(wrong_id.verify(&public), Err(VerifyError::IdMismatch));

    let mut forged = op.clone();
    forged.payload = wrong_payload.payload.clone();
    forged.id = OperationId::of_body(&AuthenticatedOperation::body_bytes(
        &forged.provenance,
        &forged.payload,
    ));
    assert!(matches!(
        forged.verify(&public),
        Err(VerifyError::Signature(_))
    ));

    let other = Ed25519SigningKey::from_bytes(&[8u8; 32]);
    assert_eq!(
        op.verify(&Ed25519PublicKey::from_signing_key(&other)),
        Err(VerifyError::KeyMismatch)
    );

    let mut gap = op.clone();
    gap.provenance.sequence = 2;
    gap.id = OperationId::of_body(&AuthenticatedOperation::body_bytes(
        &gap.provenance,
        &gap.payload,
    ));
    assert_eq!(
        gap.verify(&public),
        Err(VerifyError::Provenance(ProvenanceError::SequenceGap {
            expected: 1,
            found: 2
        }))
    );
}

#[test]
fn signing_refuses_a_key_the_provenance_does_not_name() {
    let (_, op) = fixed_operation();
    let other = Ed25519SigningKey::from_bytes(&[8u8; 32]);
    let err = AuthenticatedOperation::sign(op.provenance.clone(), op.payload.clone(), &other)
        .unwrap_err();
    assert!(matches!(err, SignError::KeyMismatch { .. }), "{err}");
    let mut provenance = op.provenance.clone();
    provenance.sequence = 5;
    let key = Ed25519SigningKey::from_bytes(&[7u8; 32]);
    assert_eq!(
        AuthenticatedOperation::sign(provenance, op.payload.clone(), &key).unwrap_err(),
        SignError::Provenance(ProvenanceError::SequenceGap {
            expected: 1,
            found: 5
        })
    );
}

// ── golden vectors: these pin the encoding and the domain contexts. A change
//    that moves them is a wire-format change and must be made on purpose. ──

const GOLDEN_OPERATION_ID: &str =
    "c96c6cb51468621eb72425cbbbf76cdaf2585c35e675bf9581e2e700409db497";
const GOLDEN_SIGNATURE: &str = "b99a3d4b3549d35feafacb765bae3de29f24cabb47b4e35e76c890b6433359377f591f88964da3c9bcfad4dc672e6a739289fd5d1a9c4aa19929a863f38c2403";
const GOLDEN_BODY_LEN: usize = 225;

#[test]
fn golden_operation_vector() {
    let (_, op) = fixed_operation();
    let body = AuthenticatedOperation::body_bytes(&op.provenance, &op.payload);
    assert_eq!(
        (op.id.to_hex(), op.signature.to_hex(), body.len()),
        (
            GOLDEN_OPERATION_ID.to_string(),
            GOLDEN_SIGNATURE.to_string(),
            GOLDEN_BODY_LEN
        ),
        "golden vector moved; body hex: {}",
        hex(&body)
    );
}

#[test]
fn identifiers_are_domain_separated() {
    let material = b"the same bytes";
    let as_capsule = crate::crypto::CapsuleId::of_bytes(material);
    let as_evidence = EvidenceId::of_bytes(material);
    let as_operation = OperationId::of_body(material);
    assert_ne!(as_capsule.as_bytes(), as_evidence.as_bytes());
    assert_ne!(as_evidence.as_bytes(), as_operation.as_bytes());
    assert_ne!(
        SymbolId::of_name("x").as_bytes(),
        VariableId::of_name("x").as_bytes()
    );
    assert_ne!(
        Blake3Hash::of(material).as_bytes(),
        as_capsule.as_bytes(),
        "a domained id is not the plain hash"
    );
    assert_eq!(
        format!("{:?}", KeyId::from_bytes([0xab; 32])).len(),
        "KeyId()".len() + 64
    );
}

// ── vector-clock laws ──

#[test]
fn frontier_merge_is_commutative_associative_idempotent() {
    let mut rng = Rng::new(3);
    for _ in 0..200 {
        let a = sample_frontier(&mut rng);
        let b = sample_frontier(&mut rng);
        let c = sample_frontier(&mut rng);

        let mut ab = a.clone();
        ab.merge(&b);
        let mut ba = b.clone();
        ba.merge(&a);
        assert_eq!(ab, ba, "commutative");

        let mut ab_c = ab.clone();
        ab_c.merge(&c);
        let mut bc = b.clone();
        bc.merge(&c);
        let mut a_bc = a.clone();
        a_bc.merge(&bc);
        assert_eq!(ab_c, a_bc, "associative");

        let mut aa = a.clone();
        aa.merge(&a);
        assert_eq!(aa, a, "idempotent");

        assert!(ab.dominates(&a) && ab.dominates(&b), "merge dominates both");
        assert!(a.dominates(&a), "reflexive");
        if a.concurrent_with(&b) {
            assert!(!a.dominates(&b) && !b.dominates(&a));
        }
    }
}

#[test]
fn frontier_observe_is_monotone() {
    let actor = ActorId::from_bytes([4; 32]);
    let mut frontier = CausalFrontier::new();
    assert_eq!(frontier.get(&actor), 0);
    frontier.observe(actor, 5);
    frontier.observe(actor, 2);
    assert_eq!(frontier.get(&actor), 5);
    let mut again = frontier.clone();
    again.observe(actor, 5);
    assert_eq!(again, frontier);
}

#[test]
fn provenance_sequence_follows_the_frontier() {
    let key = Ed25519SigningKey::from_bytes(&[1u8; 32]);
    let mut rng = Rng::new(99);
    for _ in 0..50 {
        let provenance = sample_provenance(&mut rng, &key);
        assert_eq!(provenance.check(), Ok(()));
        assert_eq!(
            provenance.expected_sequence(),
            provenance.causal_frontier.get(&provenance.actor) + 1
        );
    }
}
