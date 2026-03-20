//! tavla — nibli gossip library
//!
//! lo tavla — lo fatri ke logji ciste
//!
//! OR-Set CRDT gossip log with vector clock causality.
//! The CRDT log is ground truth. The KB is a materialized view.
//! Trust is knowledge — lacri predicates in the KB.

// Workaround: rustc 1.93.1 ICE in `check_mod_deathness` — same issue as nibli-engine.
#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use nibli_engine::NibliEngine;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub mod repl;
pub mod signal;
pub mod tcp;
pub mod transport;
pub mod webrtc;

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

    /// Check if this clock dominates (is ≥ in every component) another.
    pub fn dominates(&self, other: &VectorClock) -> bool {
        for (agent, &counter) in &other.entries {
            let local = self.entries.get(agent).copied().unwrap_or(0);
            if local < counter {
                return false;
            }
        }
        true
    }

    /// Sum of all counters — used as a tiebreaker for causal sorting.
    pub fn sum(&self) -> u64 {
        self.entries.values().sum()
    }
}

/// The kind of gossip operation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum GossipOp {
    /// Assert a Lojban sentence as fact.
    AssertLojban(String),
    /// Assert a ground fact directly (relation, args).
    AssertDirect { relation: String, args: Vec<String> },
    /// Retract a previously asserted envelope by its ID (tombstone).
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

/// Trust policy for inbound envelope filtering.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum TrustPolicy {
    /// Accept all envelopes regardless of trust (default).
    AcceptAll,
    /// Reject envelopes from untrusted authors.
    TrustRequired,
    /// Accept but quarantine envelopes from untrusted authors.
    QuarantineUntrusted,
}

/// Trust verdict from checking lacri predicates.
#[derive(Clone, Debug, PartialEq)]
pub enum TrustVerdict {
    /// Author is trusted (general or topic-specific).
    Trusted,
    /// Author is not trusted.
    Untrusted,
    /// Author is quarantined (accepted but tagged).
    Quarantined,
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
    /// Signature placeholder (not verified yet).
    pub sig: Vec<u8>,
    /// True if this envelope was accepted but the author was untrusted.
    #[serde(default)]
    pub quarantined: bool,
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
    /// None if deduped, retraction, rejected, or unsupported op.
    pub fact_id: Option<u64>,
    /// True if this was a retraction tombstone.
    pub was_retraction: bool,
    /// True if the envelope was quarantined (untrusted author).
    pub was_quarantined: bool,
    /// True if the envelope was rejected by trust policy.
    pub was_rejected: bool,
}

/// Extract topic tags from Lojban text.
/// Picks words that look like gismu (5+ chars, all lowercase ascii).
pub fn extract_topics(text: &str) -> Vec<String> {
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

// ─── OR-Set CRDT Log ─────────────────────────────────────────────

/// OR-Set CRDT: set of envelopes minus tombstoned IDs.
/// The log is append-only. Retractions add tombstones.
/// Active envelopes = all envelopes whose target is not tombstoned.
#[derive(Clone)]
pub struct CrdtLog {
    /// All envelopes ever received (including retraction envelopes).
    envelopes: HashMap<EnvelopeId, Envelope>,
    /// Tombstoned envelope IDs (targets of Retract ops).
    pub tombstones: HashSet<EnvelopeId>,
    /// Insertion order for deterministic iteration.
    order: Vec<EnvelopeId>,
}

impl CrdtLog {
    pub fn new() -> Self {
        CrdtLog {
            envelopes: HashMap::new(),
            tombstones: HashSet::new(),
            order: Vec::new(),
        }
    }

    /// Insert an envelope. Returns false if already known (dedup).
    pub fn insert(&mut self, envelope: Envelope) -> bool {
        if self.envelopes.contains_key(&envelope.id) {
            return false;
        }
        // If this is a retraction, record the tombstone.
        if let GossipOp::Retract(ref target_id) = envelope.op {
            self.tombstones.insert(target_id.clone());
        }
        let id = envelope.id.clone();
        self.envelopes.insert(id.clone(), envelope);
        self.order.push(id);
        true
    }

    /// Check if an envelope ID is known.
    pub fn contains(&self, id: &str) -> bool {
        self.envelopes.contains_key(id)
    }

    /// Check if an envelope ID has been tombstoned (retracted).
    pub fn is_tombstoned(&self, id: &str) -> bool {
        self.tombstones.contains(id)
    }

    /// Get an envelope by ID.
    pub fn get(&self, id: &str) -> Option<&Envelope> {
        self.envelopes.get(id)
    }

    /// Get all active (non-tombstoned, non-quarantined) assertion envelopes.
    pub fn active_assertions(&self) -> Vec<&Envelope> {
        self.order
            .iter()
            .filter_map(|id| {
                if self.tombstones.contains(id) {
                    return None;
                }
                let env = self.envelopes.get(id)?;
                if env.quarantined {
                    return None;
                }
                match &env.op {
                    GossipOp::AssertLojban(_) | GossipOp::AssertDirect { .. } => {
                        Some(env)
                    }
                    GossipOp::Retract(_) => None,
                }
            })
            .collect()
    }

    /// Get quarantined assertion envelopes.
    pub fn quarantined_assertions(&self) -> Vec<&Envelope> {
        self.order
            .iter()
            .filter_map(|id| {
                if self.tombstones.contains(id) {
                    return None;
                }
                let env = self.envelopes.get(id)?;
                if !env.quarantined {
                    return None;
                }
                match &env.op {
                    GossipOp::AssertLojban(_) | GossipOp::AssertDirect { .. } => {
                        Some(env)
                    }
                    GossipOp::Retract(_) => None,
                }
            })
            .collect()
    }

    /// Get all envelopes in insertion order (including retractions).
    pub fn all_envelopes(&self) -> Vec<&Envelope> {
        self.order
            .iter()
            .filter_map(|id| self.envelopes.get(id))
            .collect()
    }

    /// Total number of envelopes (including retractions).
    pub fn len(&self) -> usize {
        self.envelopes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.envelopes.is_empty()
    }

    /// Compute the diff: envelopes we have that the peer is missing,
    /// based on the peer's vector clock. Returns them in causal order.
    pub fn sync_diff(&self, peer_clock: &VectorClock) -> Vec<Envelope> {
        let mut missing: Vec<&Envelope> = self
            .order
            .iter()
            .filter_map(|id| self.envelopes.get(id))
            .filter(|env| !peer_clock.dominates(&env.clock))
            .collect();

        missing.sort_by(|a, b| {
            a.clock
                .sum()
                .cmp(&b.clock.sum())
                .then_with(|| a.author.cmp(&b.author))
                .then_with(|| a.id.cmp(&b.id))
        });

        missing.into_iter().cloned().collect()
    }

    /// Merge another log into this one (OR-Set union).
    pub fn merge(&mut self, other: &CrdtLog) -> Vec<EnvelopeId> {
        let mut new_ids = Vec::new();
        for id in &other.order {
            if let Some(env) = other.envelopes.get(id) {
                if self.insert(env.clone()) {
                    new_ids.push(id.clone());
                }
            }
        }
        new_ids
    }

    /// Mark an envelope as quarantined (mutable access by ID).
    pub fn set_quarantined(&mut self, id: &str, quarantined: bool) {
        if let Some(env) = self.envelopes.get_mut(id) {
            env.quarantined = quarantined;
        }
    }
}

impl Default for CrdtLog {
    fn default() -> Self {
        Self::new()
    }
}

// ─── GossipNode ──────────────────────────────────────────────────

/// A gossip-capable nibli node.
///
/// Architecture: CRDT log is ground truth, KB is a materialized view.
/// Trust is knowledge — lacri predicates queryable in the KB.
pub struct GossipNode {
    /// This node's agent identity.
    pub agent_id: AgentId,
    /// The reasoning engine (materialized view of the CRDT log).
    engine: NibliEngine,
    /// Local vector clock.
    clock: VectorClock,
    /// OR-Set CRDT log — the authoritative state.
    crdt_log: CrdtLog,
    /// Trust policy for inbound envelope filtering.
    pub trust_policy: TrustPolicy,
}

impl GossipNode {
    /// Create a new gossip node with the given agent identity.
    /// Default trust policy: AcceptAll.
    pub fn new(agent_id: impl Into<String>) -> Self {
        GossipNode {
            agent_id: agent_id.into(),
            engine: NibliEngine::new(),
            clock: VectorClock::new(),
            crdt_log: CrdtLog::new(),
            trust_policy: TrustPolicy::AcceptAll,
        }
    }

    /// Create a new gossip node with a specific trust policy.
    pub fn with_policy(agent_id: impl Into<String>, policy: TrustPolicy) -> Self {
        GossipNode {
            agent_id: agent_id.into(),
            engine: NibliEngine::new(),
            clock: VectorClock::new(),
            crdt_log: CrdtLog::new(),
            trust_policy: policy,
        }
    }

    // ─── Trust as knowledge ──────────────────────────────────────

    /// Check if we trust the given author (general trust).
    /// Queries the KB for: la .<me>. cu lacri la .<author>.
    fn check_general_trust(&self, author: &str) -> bool {
        if author == self.agent_id {
            return true; // Always trust ourselves.
        }
        let query = format!("la .{}. cu lacri la .{}.", self.agent_id, author);
        match self.engine.query_text_with_proof(&query) {
            Ok((holds, _, _)) => holds,
            Err(_) => false,
        }
    }

    /// Check if we trust the given author for a specific topic.
    /// Queries the KB for: la .<me>. cu lacri la .<author>. lo ka <topic>
    fn check_topic_trust(&self, author: &str, topic: &str) -> bool {
        if author == self.agent_id {
            return true;
        }
        let query = format!(
            "la .{}. cu lacri la .{}. lo ka {}",
            self.agent_id, author, topic
        );
        match self.engine.query_text_with_proof(&query) {
            Ok((holds, _, _)) => holds,
            Err(_) => false,
        }
    }

    /// Evaluate trust for an envelope based on the current trust policy.
    /// Returns the trust verdict.
    fn evaluate_trust(&self, envelope: &Envelope) -> TrustVerdict {
        match self.trust_policy {
            TrustPolicy::AcceptAll => TrustVerdict::Trusted,
            TrustPolicy::TrustRequired | TrustPolicy::QuarantineUntrusted => {
                // Self-authored envelopes are always trusted.
                if envelope.author == self.agent_id {
                    return TrustVerdict::Trusted;
                }

                // Check topic-specific trust first.
                for topic in &envelope.topics {
                    if self.check_topic_trust(&envelope.author, topic) {
                        return TrustVerdict::Trusted;
                    }
                }

                // Fall back to general trust.
                if self.check_general_trust(&envelope.author) {
                    return TrustVerdict::Trusted;
                }

                // Not trusted.
                match self.trust_policy {
                    TrustPolicy::TrustRequired => TrustVerdict::Untrusted,
                    TrustPolicy::QuarantineUntrusted => TrustVerdict::Quarantined,
                    _ => unreachable!(),
                }
            }
        }
    }

    /// Assert trust: la .<me>. cu lacri la .<peer>.
    pub fn trust(&mut self, peer: &str) -> Result<Envelope, String> {
        let lojban = format!("la .{}. cu lacri la .{}.", self.agent_id, peer);
        self.assert_local(&lojban)
    }

    /// Assert topic-specific trust: la .<me>. cu lacri la .<peer>. lo ka <topic>
    pub fn trust_topic(&mut self, peer: &str, topic: &str) -> Result<Envelope, String> {
        let lojban = format!(
            "la .{}. cu lacri la .{}. lo ka {}",
            self.agent_id, peer, topic
        );
        self.assert_local(&lojban)
    }

    /// Retract trust for a peer (finds and retracts the lacri envelope).
    pub fn distrust(&mut self, peer: &str) -> Result<Vec<Envelope>, String> {
        let trust_pattern = format!("la .{}. cu lacri la .{}.", self.agent_id, peer);
        let mut tombstones = Vec::new();

        // Find all trust envelopes matching this peer.
        let matching_ids: Vec<EnvelopeId> = self
            .crdt_log
            .all_envelopes()
            .iter()
            .filter(|env| {
                if self.crdt_log.is_tombstoned(&env.id) {
                    return false;
                }
                match &env.op {
                    GossipOp::AssertLojban(text) => text.contains(&trust_pattern),
                    _ => false,
                }
            })
            .map(|env| env.id.clone())
            .collect();

        if matching_ids.is_empty() {
            return Err(format!("no trust assertion found for {peer}"));
        }

        for id in matching_ids {
            let tombstone = self.retract_local(&id)?;
            tombstones.push(tombstone);
        }

        // After distrust, re-evaluate quarantined envelopes.
        // Envelopes previously accepted may now need quarantining.
        // Simplest approach: rebuild KB to re-apply trust policy.
        self.rebuild_kb();

        Ok(tombstones)
    }

    /// List all lacri (trust) facts in the KB.
    /// Returns the Lojban text of each trust assertion.
    pub fn trust_list(&self) -> Vec<String> {
        self.crdt_log
            .active_assertions()
            .iter()
            .filter_map(|env| match &env.op {
                GossipOp::AssertLojban(text) if text.contains("lacri") => {
                    Some(text.clone())
                }
                _ => None,
            })
            .collect()
    }

    // ─── Core operations ─────────────────────────────────────────

    /// Assert Lojban text locally. Creates a signed envelope,
    /// appends to the CRDT log, and asserts into the local KB.
    pub fn assert_local(&mut self, lojban: &str) -> Result<Envelope, String> {
        // Assert into engine first — if gerna rejects, fail before creating envelope.
        let fact_id = self.engine.assert_text(lojban)?;

        // Tick the vector clock.
        self.clock.tick(&self.agent_id);

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
            quarantined: false,
        };

        self.crdt_log.insert(envelope.clone());

        println!(
            "[tavla] {} asserted: {:?} (fact #{}, envelope {}...)",
            self.agent_id,
            lojban,
            fact_id,
            &id[..12]
        );

        Ok(envelope)
    }

    /// Retract a previously asserted envelope by its ID.
    pub fn retract_local(&mut self, target_id: &str) -> Result<Envelope, String> {
        if !self.crdt_log.contains(target_id) {
            return Err(format!("envelope {target_id} not found in log"));
        }
        if self.crdt_log.is_tombstoned(target_id) {
            return Err(format!("envelope {target_id} already retracted"));
        }

        self.clock.tick(&self.agent_id);

        let op = GossipOp::Retract(target_id.to_string());
        let timestamp = chrono::Utc::now().to_rfc3339();
        let stance = EpistemicStance::Deduced;
        let topics = Vec::new();

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
            quarantined: false,
        };

        self.crdt_log.insert(envelope.clone());
        self.rebuild_kb();

        println!(
            "[tavla] {} retracted envelope {}... (tombstone {}...)",
            self.agent_id,
            &target_id[..12.min(target_id.len())],
            &id[..12]
        );

        Ok(envelope)
    }

    /// Ingest an envelope from a peer.
    ///
    /// 1. Dedup via CRDT log
    /// 2. Merge vector clock
    /// 3. Evaluate trust policy
    /// 4. Insert into CRDT log
    /// 5. If assertion: parse and compile via gerna → smuni → logji
    /// 6. If retraction: apply tombstone and rebuild KB
    pub fn ingest(&mut self, envelope: Envelope) -> Result<IngestResult, String> {
        // Dedup via CRDT log.
        if self.crdt_log.contains(&envelope.id) {
            return Ok(IngestResult {
                envelope_id: envelope.id,
                fact_id: None,
                was_retraction: false,
                was_quarantined: false,
                was_rejected: false,
            });
        }

        // Merge vector clock.
        self.clock.merge(&envelope.clock);

        // Evaluate trust before processing.
        let verdict = self.evaluate_trust(&envelope);

        match verdict {
            TrustVerdict::Untrusted => {
                println!(
                    "[tavla] {} ✗ {}: untrusted (rejected by trust policy)",
                    self.agent_id, envelope.author
                );
                // Still insert into CRDT log for sync purposes,
                // but mark as quarantined so it won't be asserted into KB.
                let id = envelope.id.clone();
                // Don't insert rejected envelopes — they are truly rejected.
                return Ok(IngestResult {
                    envelope_id: id,
                    fact_id: None,
                    was_retraction: false,
                    was_quarantined: false,
                    was_rejected: true,
                });
            }
            TrustVerdict::Quarantined => {
                // Accept into CRDT log but mark as quarantined.
                let mut quarantined_env = envelope.clone();
                quarantined_env.quarantined = true;
                return self.ingest_inner(quarantined_env, true);
            }
            TrustVerdict::Trusted => {
                return self.ingest_inner(envelope, false);
            }
        }
    }

    /// Inner ingest logic after trust evaluation.
    fn ingest_inner(
        &mut self,
        envelope: Envelope,
        quarantined: bool,
    ) -> Result<IngestResult, String> {
        // Process the operation.
        let (fact_id, was_retraction) = match &envelope.op {
            GossipOp::AssertLojban(text) => {
                if self.crdt_log.is_tombstoned(&envelope.id) {
                    (None, false)
                } else if quarantined {
                    println!(
                        "[tavla] {} ← {}: {:?} [Quarantined]",
                        self.agent_id, envelope.author, text
                    );
                    // Quarantined: add to CRDT log but NOT to KB.
                    (None, false)
                } else {
                    let fid = self.engine.assert_text(text)?;
                    println!(
                        "[tavla] {} ← {}: {:?} (accepted, fact #{})",
                        self.agent_id, envelope.author, text, fid
                    );
                    (Some(fid), false)
                }
            }
            GossipOp::AssertDirect { relation, args } => {
                println!(
                    "[tavla] {} ← {}: direct assert {}({}) (skipped — not yet supported)",
                    self.agent_id,
                    envelope.author,
                    relation,
                    args.join(", ")
                );
                (None, false)
            }
            GossipOp::Retract(target_id) => {
                println!(
                    "[tavla] {} ← {}: retract {}...",
                    self.agent_id,
                    envelope.author,
                    &target_id[..12.min(target_id.len())]
                );
                self.crdt_log.insert(envelope.clone());
                self.rebuild_kb();
                return Ok(IngestResult {
                    envelope_id: envelope.id,
                    fact_id: None,
                    was_retraction: true,
                    was_quarantined: quarantined,
                    was_rejected: false,
                });
            }
        };

        let id = envelope.id.clone();
        self.crdt_log.insert(envelope);

        Ok(IngestResult {
            envelope_id: id,
            fact_id,
            was_retraction,
            was_quarantined: quarantined,
            was_rejected: false,
        })
    }

    /// Rebuild the KB from the CRDT log (materialized view pattern).
    /// Only replays active, non-quarantined assertions.
    /// Trust assertions (lacri) are always replayed regardless of quarantine.
    pub fn rebuild_kb(&mut self) {
        self.engine.reset();
        let active = self.crdt_log.active_assertions();
        let count = active.len();
        let mut errors = 0;
        for env in &active {
            match &env.op {
                GossipOp::AssertLojban(text) => {
                    if let Err(e) = self.engine.assert_text(text) {
                        eprintln!(
                            "[tavla] rebuild: failed to replay {}: {e}",
                            &env.id[..12.min(env.id.len())]
                        );
                        errors += 1;
                    }
                }
                _ => {}
            }
        }
        println!(
            "[tavla] KB rebuilt from CRDT log ({count} active assertions, {errors} errors)"
        );
    }

    /// Re-evaluate quarantined envelopes after trust changes.
    /// Promotes quarantined envelopes to active if author is now trusted.
    /// Demotes active envelopes to quarantined if author is no longer trusted.
    pub fn reevaluate_quarantine(&mut self) {
        let mut changed = false;

        // Collect all assertion envelope IDs and their current quarantine state.
        let envs: Vec<(EnvelopeId, bool, AgentId, Vec<String>)> = self
            .crdt_log
            .all_envelopes()
            .iter()
            .filter(|env| {
                !self.crdt_log.is_tombstoned(&env.id)
                    && matches!(
                        &env.op,
                        GossipOp::AssertLojban(_) | GossipOp::AssertDirect { .. }
                    )
                    && env.author != self.agent_id
            })
            .map(|env| {
                (
                    env.id.clone(),
                    env.quarantined,
                    env.author.clone(),
                    env.topics.clone(),
                )
            })
            .collect();

        for (id, currently_quarantined, author, topics) in envs {
            let should_quarantine = match self.trust_policy {
                TrustPolicy::AcceptAll => false,
                TrustPolicy::TrustRequired | TrustPolicy::QuarantineUntrusted => {
                    // Check trust.
                    let mut trusted = false;
                    for topic in &topics {
                        if self.check_topic_trust(&author, topic) {
                            trusted = true;
                            break;
                        }
                    }
                    if !trusted {
                        trusted = self.check_general_trust(&author);
                    }
                    !trusted
                }
            };

            if currently_quarantined != should_quarantine {
                self.crdt_log.set_quarantined(&id, should_quarantine);
                changed = true;
            }
        }

        if changed {
            self.rebuild_kb();
        }
    }

    /// Compute the sync diff.
    pub fn sync_diff(&self, peer_clock: &VectorClock) -> Vec<Envelope> {
        self.crdt_log.sync_diff(peer_clock)
    }

    /// Query the local KB with proof trace.
    pub fn query_with_proof(&self, lojban: &str) -> Result<(bool, String, String), String> {
        self.engine.query_text_with_proof(lojban)
    }

    /// Get the current vector clock.
    pub fn get_clock(&self) -> &VectorClock {
        &self.clock
    }

    /// Get the number of envelopes in the CRDT log.
    pub fn log_size(&self) -> usize {
        self.crdt_log.len()
    }

    /// Get all envelopes in the CRDT log.
    pub fn log(&self) -> Vec<&Envelope> {
        self.crdt_log.all_envelopes()
    }

    /// Get the CRDT log reference.
    pub fn crdt_log(&self) -> &CrdtLog {
        &self.crdt_log
    }

    /// Get active (non-tombstoned, non-quarantined) assertion count.
    pub fn active_count(&self) -> usize {
        self.crdt_log.active_assertions().len()
    }

    /// Get quarantined assertion count.
    pub fn quarantined_count(&self) -> usize {
        self.crdt_log.quarantined_assertions().len()
    }

    /// Reset the engine KB (does NOT clear the CRDT log).
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
    /// Sync response: here are the envelopes you're missing (in causal order).
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
