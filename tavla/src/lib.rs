//! tavla — nibli gossip library
//!
//! lo tavla — lo fatri ke logji ciste
//!
//! Core gossip types and GossipNode: wraps a nibli engine with
//! envelope creation, ingestion, and vector clock synchronization.

use std::collections::HashMap;

use nibli_engine::NibliEngine;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

// ─── Types ───────────────────────────────────────────────────────

pub type AgentId = String;
pub type EnvelopeId = String;

/// Vector clock — sparse map of agent-id → logical counter.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct VectorClock {
    pub entries: HashMap<AgentId, u64>,
}

impl VectorClock {
    pub fn new() -> Self {
        Self::default()
    }

    /// Increment this agent's counter and return the new value.
    pub fn tick(&mut self, agent: &str) -> u64 {
        let counter = self.entries.entry(agent.to_string()).or_insert(0);
        *counter += 1;
        *counter
    }

    /// Merge another clock into this one (component-wise max).
    pub fn merge(&mut self, other: &VectorClock) {
        for (agent, &counter) in &other.entries {
            let local = self.entries.entry(agent.clone()).or_insert(0);
            if counter > *local {
                *local = counter;
            }
        }
    }
}

/// The kind of gossip operation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum GossipOp {
    /// Assert a Lojban sentence as fact.
    AssertLojban(String),
    /// Assert a ground fact directly (relation, args).
    AssertDirect { relation: String, args: Vec<String> },
    /// Retract a previously asserted envelope by its ID.
    Retract(EnvelopeId),
}

/// Epistemic confidence — maps to Lojban evidentials.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum EpistemicStance {
    /// ja'o — deduced from evidence (highest confidence).
    Deduced,
    /// ba'a — expected based on experience.
    Expected,
    /// pe'i — opinion.
    Opinion,
    /// ti'e — hearsay (relayed from another agent).
    Hearsay,
}

/// A signed gossip envelope — the atomic unit of federation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Envelope {
    /// Content-addressed ID (SHA-256 hex of canonical form).
    pub id: EnvelopeId,
    /// The agent that authored this message.
    pub author: AgentId,
    /// Vector clock at time of authoring.
    pub clock: VectorClock,
    /// The operation (assert, retract).
    pub op: GossipOp,
    /// Epistemic stance.
    pub stance: EpistemicStance,
    /// Topic tags (Lojban selbri roots) for routing/filtering.
    pub topics: Vec<String>,
    /// Wall-clock timestamp (ISO 8601, informational).
    pub timestamp: String,
    /// Signature placeholder (not verified in Prompt 1).
    pub sig: Vec<u8>,
}

impl Envelope {
    /// Compute content-addressed ID from canonical fields.
    fn compute_id(
        author: &str,
        clock: &VectorClock,
        op: &GossipOp,
        stance: &EpistemicStance,
        topics: &[String],
        timestamp: &str,
    ) -> EnvelopeId {
        let canonical = serde_json::json!({
            "author": author,
            "clock": clock,
            "op": op,
            "stance": stance,
            "topics": topics,
            "timestamp": timestamp,
        });
        let bytes = serde_json::to_vec(&canonical).unwrap();
        let hash = Sha256::digest(&bytes);
        hex_encode(hash)
    }
}

/// Result of ingesting an envelope.
#[derive(Debug)]
pub struct IngestResult {
    pub envelope_id: EnvelopeId,
    pub fact_id: Option<u64>,
}

/// Extract topic tags from Lojban text.
/// Picks words that look like gismu (5+ chars, all lowercase ascii).
fn extract_topics(text: &str) -> Vec<String> {
    let mut topics = Vec::new();
    for word in text.split_whitespace() {
        let clean = word.trim_matches('.');
        if clean.len() >= 5
            && clean.chars().all(|c| c.is_ascii_lowercase() || c == '\'')
        {
            topics.push(clean.to_string());
        }
    }
    topics
}

// ─── GossipNode ──────────────────────────────────────────────────

/// A gossip-capable nibli node.
///
/// Wraps a NibliEngine with:
/// - Agent identity
/// - CRDT append-only log (Vec<Envelope> for now)
/// - Vector clock for causal ordering
/// - Envelope creation and ingestion
pub struct GossipNode {
    /// This node's agent identity.
    pub agent_id: AgentId,
    /// The reasoning engine.
    engine: NibliEngine,
    /// Local vector clock.
    clock: VectorClock,
    /// Append-only log of all envelopes (local + ingested).
    log: Vec<Envelope>,
    /// Set of known envelope IDs (for dedup).
    known_ids: std::collections::HashSet<EnvelopeId>,
}

impl GossipNode {
    /// Create a new gossip node with the given agent identity.
    pub fn new(agent_id: impl Into<String>) -> Self {
        GossipNode {
            agent_id: agent_id.into(),
            engine: NibliEngine::new(),
            clock: VectorClock::new(),
            log: Vec::new(),
            known_ids: std::collections::HashSet::new(),
        }
    }

    /// Assert Lojban text locally. Creates a signed envelope,
    /// appends to the local log, and asserts into the local KB.
    /// Returns the envelope.
    pub fn assert_local(&mut self, lojban: &str) -> Result<Envelope, String> {
        // Assert into engine first — if gerna rejects, we fail before creating an envelope.
        let fact_id = self.engine.assert_text(lojban)?;

        // Tick the vector clock.
        self.clock.tick(&self.agent_id);

        // Extract topics from the Lojban text.
        let topics = extract_topics(lojban);
        let timestamp = chrono::Utc::now().to_rfc3339();
        let stance = EpistemicStance::Deduced;
        let op = GossipOp::AssertLojban(lojban.to_string());

        let id = Envelope::compute_id(
            &self.agent_id,
            &self.clock,
            &op,
            &stance,
            &topics,
            &timestamp,
        );

        let envelope = Envelope {
            id: id.clone(),
            author: self.agent_id.clone(),
            clock: self.clock.clone(),
            op,
            stance,
            topics,
            timestamp,
            sig: Vec::new(),
        };

        self.log.push(envelope.clone());
        self.known_ids.insert(id.clone());

        println!(
            "[tavla] {} asserted: {:?} (fact #{}, envelope {}...)",
            self.agent_id,
            lojban,
            fact_id,
            &id[..12]
        );

        Ok(envelope)
    }

    /// Ingest an envelope from a peer.
    ///
    /// 1. Dedup — skip if already known
    /// 2. Merge vector clock
    /// 3. Parse and compile via gerna → smuni → logji
    /// 4. Assert into local KB
    /// 5. Append to local log
    pub fn ingest(&mut self, envelope: Envelope) -> Result<IngestResult, String> {
        // Dedup.
        if self.known_ids.contains(&envelope.id) {
            return Ok(IngestResult {
                envelope_id: envelope.id,
                fact_id: None,
            });
        }

        // Merge vector clock.
        self.clock.merge(&envelope.clock);

        // Process the operation.
        let fact_id = match &envelope.op {
            GossipOp::AssertLojban(text) => {
                let fid = self.engine.assert_text(text)?;
                println!(
                    "[tavla] {} ← {}: {:?} (accepted, fact #{})",
                    self.agent_id, envelope.author, text, fid
                );
                Some(fid)
            }
            GossipOp::AssertDirect { relation, args } => {
                println!(
                    "[tavla] {} ← {}: direct assert {}({}) (skipped — not yet supported)",
                    self.agent_id,
                    envelope.author,
                    relation,
                    args.join(", ")
                );
                None
            }
            GossipOp::Retract(target_id) => {
                println!(
                    "[tavla] {} ← {}: retract {} (not yet supported)",
                    self.agent_id, envelope.author, target_id
                );
                None
            }
        };

        // Append to log and mark as known.
        let id = envelope.id.clone();
        self.log.push(envelope);
        self.known_ids.insert(id.clone());

        Ok(IngestResult {
            envelope_id: id,
            fact_id,
        })
    }

    /// Query the local KB with proof trace.
    /// Returns (holds, formatted_proof, json_proof).
    pub fn query_with_proof(&self, lojban: &str) -> Result<(bool, String, String), String> {
        self.engine.query_text_with_proof(lojban)
    }

    /// Get the current vector clock.
    pub fn get_clock(&self) -> &VectorClock {
        &self.clock
    }

    /// Get the number of envelopes in the log.
    pub fn log_size(&self) -> usize {
        self.log.len()
    }

    /// Get the log.
    pub fn log(&self) -> &[Envelope] {
        &self.log
    }

    /// Reset the engine KB.
    pub fn reset(&mut self) {
        self.engine.reset();
    }
}

// ─── Wire Protocol ───────────────────────────────────────────────

/// JSON Lines wire message for TCP/WebRTC transport.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum WireMessage {
    /// Gossip envelope (assertion, retraction).
    #[serde(rename = "envelope")]
    Envelope(Envelope),
    /// Sync request: send your vector clock so I can compute the diff.
    #[serde(rename = "sync_request")]
    SyncRequest { clock: VectorClock },
    /// Sync response: here are the envelopes you're missing.
    #[serde(rename = "sync_response")]
    SyncResponse { envelopes: Vec<Envelope> },
}

// ─── Hex encoding (inline, no extra dep) ─────────────────────────

const HEX_CHARS: &[u8; 16] = b"0123456789abcdef";

fn hex_encode(bytes: impl AsRef<[u8]>) -> String {
    let bytes = bytes.as_ref();
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(HEX_CHARS[(b >> 4) as usize] as char);
        s.push(HEX_CHARS[(b & 0x0f) as usize] as char);
    }
    s
}
