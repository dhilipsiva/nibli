use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use anyhow::Result;
use async_graphql::{EmptySubscription, Object, Schema};
use async_graphql_axum::GraphQL;
use axum::Router;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::net::TcpStream;
use tower_http::cors::CorsLayer;

use nibli_engine::NibliEngine;
use nibli_protocol::{
    ContradictionSummary, EnvelopeSummary, GossipEvent, NetworkAgent, NetworkSnapshot, StanceCounts,
};
use tavla::{EpistemicStance, GossipNode, GossipOp, WireMessage};

// ── Ollama types ──

#[derive(serde::Serialize)]
struct OllamaChatRequest {
    model: String,
    messages: Vec<OllamaMessage>,
    stream: bool,
    options: OllamaOptions,
}

#[derive(serde::Serialize)]
struct OllamaMessage {
    role: String,
    content: String,
}

#[derive(serde::Serialize)]
struct OllamaOptions {
    temperature: f64,
}

#[derive(serde::Deserialize)]
struct OllamaChatResponse {
    message: OllamaResponseMessage,
}

#[derive(serde::Deserialize)]
struct OllamaResponseMessage {
    content: String,
}

const LOJBAN_SYSTEM_PROMPT: &str = r#"You are a Lojban translator. Translate the user's English text into grammatically correct Lojban.

Rules:
- Output ONLY the Lojban translation, nothing else. No explanations, no notes.
- Use standard Lojban grammar: [sumti] [selbri] [sumti] structure
- Use gadri: "lo" for veridical descriptions, "le" for non-veridical
- Wrap names in dots as cmevla: "Adam" → ".adam."
- Use "cu" to separate sumti from selbri when needed
- Use tense markers: "pu" (past), "ca" (present), "ba" (future)

Examples:
- "The dog goes to the market" → "lo gerku cu klama lo zarci"
- "I love you" → "mi prami do"
- "Adam sees the cat" → "la .adam. viska lo mlatu"
- "The big dog runs" → "lo barda gerku cu bajra"
- "I ate the food" → "mi pu citka lo cidja"
"#;

// ── GraphQL schema ──

struct QueryRoot;

#[Object]
impl QueryRoot {
    async fn status(&self, ctx: &async_graphql::Context<'_>) -> StatusResult {
        let engine = ctx.data::<Arc<Mutex<NibliEngine>>>().unwrap();
        let ok = engine.lock().is_ok();
        StatusResult { ready: ok }
    }

    /// Get a snapshot of the gossip network state.
    async fn network_snapshot(&self, ctx: &async_graphql::Context<'_>) -> NetworkSnapshotGql {
        let gossip = ctx.data::<Arc<Mutex<GossipNode>>>().unwrap();
        let node = gossip.lock().unwrap();
        let snapshot = build_network_snapshot(&node);
        snapshot_to_gql(&snapshot)
    }

    /// Get all envelopes authored by a specific agent.
    async fn agent_envelopes(&self, ctx: &async_graphql::Context<'_>, agent: String) -> Vec<EnvelopeSummaryGql> {
        let gossip = ctx.data::<Arc<Mutex<GossipNode>>>().unwrap();
        let node = gossip.lock().unwrap();
        node.log()
            .iter()
            .filter(|e| e.author == agent)
            .map(|e| envelope_to_gql(e))
            .collect()
    }

    /// Get details of a specific envelope by ID prefix.
    async fn envelope_detail(&self, ctx: &async_graphql::Context<'_>, id_prefix: String) -> Option<EnvelopeSummaryGql> {
        let gossip = ctx.data::<Arc<Mutex<GossipNode>>>().unwrap();
        let node = gossip.lock().unwrap();
        node.log()
            .iter()
            .find(|e| e.id.starts_with(&id_prefix))
            .map(|e| envelope_to_gql(e))
    }

    /// Get the gossip event log (most recent events).
    async fn gossip_events(&self, ctx: &async_graphql::Context<'_>, limit: Option<u32>) -> Vec<GossipEventGql> {
        let events = ctx.data::<Arc<Mutex<Vec<GossipEvent>>>>().unwrap();
        let events = events.lock().unwrap();
        let limit = limit.unwrap_or(50) as usize;
        events.iter().rev().take(limit).map(event_to_gql).collect()
    }
}

struct OllamaConfig {
    url: String,
    model: String,
}

struct MutationRoot;

#[Object]
impl MutationRoot {
    async fn translate_to_lojban(
        &self,
        ctx: &async_graphql::Context<'_>,
        input: String,
    ) -> TranslateResult {
        let config = ctx.data::<Arc<OllamaConfig>>().unwrap();
        let client = reqwest::Client::new();
        let req = OllamaChatRequest {
            model: config.model.clone(),
            messages: vec![
                OllamaMessage {
                    role: "system".to_string(),
                    content: LOJBAN_SYSTEM_PROMPT.to_string(),
                },
                OllamaMessage {
                    role: "user".to_string(),
                    content: format!("Translate to Lojban: {}", input),
                },
            ],
            stream: false,
            options: OllamaOptions { temperature: 0.3 },
        };
        let url = format!("{}/api/chat", config.url);
        match client.post(&url).json(&req).send().await {
            Ok(resp) => match resp.json::<OllamaChatResponse>().await {
                Ok(chat) => TranslateResult {
                    lojban: Some(chat.message.content.trim().to_string()),
                    error: None,
                },
                Err(e) => TranslateResult {
                    lojban: None,
                    error: Some(format!("Failed to parse Ollama response: {}", e)),
                },
            },
            Err(e) => {
                let msg = if e.is_connect() {
                    "Connection refused — is Ollama running? (ollama serve)".to_string()
                } else {
                    format!("Ollama request failed: {}", e)
                };
                TranslateResult {
                    lojban: None,
                    error: Some(msg),
                }
            }
        }
    }

    async fn assert_text(
        &self,
        ctx: &async_graphql::Context<'_>,
        input: String,
    ) -> AssertResult {
        let engine = ctx.data::<Arc<Mutex<NibliEngine>>>().unwrap();
        let engine = engine.lock().unwrap();
        match engine.assert_text(&input) {
            Ok(fact_id) => AssertResult {
                fact_id: Some(fact_id),
                error: None,
            },
            Err(e) => AssertResult {
                fact_id: None,
                error: Some(e),
            },
        }
    }

    async fn query_text(
        &self,
        ctx: &async_graphql::Context<'_>,
        input: String,
    ) -> QueryResult {
        let engine = ctx.data::<Arc<Mutex<NibliEngine>>>().unwrap();
        let engine = engine.lock().unwrap();
        match engine.query_text_with_proof(&input) {
            Ok((holds, trace, json)) => QueryResult {
                holds: Some(holds),
                proof_trace: Some(trace),
                proof_trace_json: Some(json),
                kb_status: None,
                error: None,
            },
            Err(e) => QueryResult {
                holds: None,
                proof_trace: None,
                proof_trace_json: None,
                kb_status: None,
                error: Some(e),
            },
        }
    }

    /// Reset the engine, assert all KB lines, then run a query.
    async fn query_with_kb(
        &self,
        ctx: &async_graphql::Context<'_>,
        kb: String,
        query: String,
    ) -> QueryResult {
        let engine = ctx.data::<Arc<Mutex<NibliEngine>>>().unwrap();
        let engine = engine.lock().unwrap();
        engine.reset();
        let kb_status = assert_kb_lines(&engine, &kb);
        match engine.query_text_with_proof(&query) {
            Ok((holds, trace, json)) => QueryResult {
                holds: Some(holds),
                proof_trace: Some(trace),
                proof_trace_json: Some(json),
                kb_status: Some(kb_status),
                error: None,
            },
            Err(e) => QueryResult {
                holds: None,
                proof_trace: None,
                proof_trace_json: None,
                kb_status: Some(kb_status),
                error: Some(e),
            },
        }
    }

    /// Assert Lojban into the gossip node and broadcast.
    async fn gossip_assert(
        &self,
        ctx: &async_graphql::Context<'_>,
        lojban: String,
        stance: Option<String>,
    ) -> GossipAssertResult {
        let gossip = ctx.data::<Arc<Mutex<GossipNode>>>().unwrap();
        let events = ctx.data::<Arc<Mutex<Vec<GossipEvent>>>>().unwrap();
        let mut node = gossip.lock().unwrap();

        let ep_stance = match stance.as_deref() {
            Some("Expected") | Some("ba'a") => EpistemicStance::Expected,
            Some("Opinion") | Some("pe'i") => EpistemicStance::Opinion,
            Some("Hearsay") | Some("ti'e") => EpistemicStance::Hearsay,
            _ => EpistemicStance::Deduced,
        };

        match node.assert_local_with_stance(&lojban, ep_stance) {
            Ok(envelope) => {
                let event = GossipEvent::NewEnvelope {
                    envelope_id: envelope.id.clone(),
                    author: envelope.author.clone(),
                    lojban: Some(lojban),
                    stance: format!("{}", envelope.stance),
                    topics: envelope.topics.clone(),
                    timestamp: envelope.timestamp.clone(),
                };
                events.lock().unwrap().push(event);
                GossipAssertResult {
                    envelope_id: Some(envelope.id),
                    error: None,
                }
            }
            Err(e) => GossipAssertResult {
                envelope_id: None,
                error: Some(e),
            },
        }
    }

    /// Resolve a contradiction by ID.
    async fn resolve_contradiction(
        &self,
        ctx: &async_graphql::Context<'_>,
        id: u32,
    ) -> SimpleResult {
        let gossip = ctx.data::<Arc<Mutex<GossipNode>>>().unwrap();
        let mut node = gossip.lock().unwrap();
        match node.resolve_contradiction(id as usize) {
            Ok(()) => SimpleResult { success: true, error: None },
            Err(e) => SimpleResult { success: false, error: Some(e) },
        }
    }
}

// ── Gossip helpers ──

fn build_network_snapshot(node: &GossipNode) -> NetworkSnapshot {
    let envelopes = node.log();
    let mut agent_map: HashMap<String, (u32, StanceCounts, Vec<String>)> = HashMap::new();

    let mut envelope_summaries = Vec::new();
    for env in &envelopes {
        // Track per-agent stats.
        let entry = agent_map.entry(env.author.clone()).or_insert_with(|| {
            (0, StanceCounts::default(), Vec::new())
        });
        entry.0 += 1;
        match env.stance {
            EpistemicStance::Deduced => entry.1.deduced += 1,
            EpistemicStance::Expected => entry.1.expected += 1,
            EpistemicStance::Opinion => entry.1.opinion += 1,
            EpistemicStance::Hearsay => entry.1.hearsay += 1,
        }
        for t in &env.topics {
            if !entry.2.contains(t) {
                entry.2.push(t.clone());
            }
        }

        let (lojban, is_retraction) = match &env.op {
            GossipOp::AssertLojban(s) => (Some(s.clone()), false),
            GossipOp::AssertDirect { relation, args } => {
                (Some(format!("{}({})", relation, args.join(", "))), false)
            }
            GossipOp::Retract(_) => (None, true),
        };

        envelope_summaries.push(EnvelopeSummary {
            id: env.id.clone(),
            author: env.author.clone(),
            lojban,
            stance: format!("{}", env.stance),
            topics: env.topics.clone(),
            timestamp: env.timestamp.clone(),
            is_retraction,
            is_quarantined: env.quarantined,
        });
    }

    let agents: Vec<NetworkAgent> = agent_map
        .into_iter()
        .map(|(name, (count, stances, topics))| NetworkAgent {
            is_local: name == node.agent_id,
            name,
            envelope_count: count,
            stance_counts: stances,
            topics,
        })
        .collect();

    let contradictions: Vec<ContradictionSummary> = node
        .contradictions()
        .iter()
        .map(|c| ContradictionSummary {
            id: c.id,
            envelope_id: c.envelope_id.clone(),
            assertion: c.assertion.clone(),
            author: c.author.clone(),
            resolved: c.resolved,
        })
        .collect();

    NetworkSnapshot {
        agents,
        envelopes: envelope_summaries,
        contradictions,
        peers: Vec::new(), // TCP peers not available without transport reference
        local_agent: node.agent_id.clone(),
        total_facts: node.active_count() as u32,
    }
}

fn envelope_to_gql(env: &tavla::Envelope) -> EnvelopeSummaryGql {
    let (lojban, is_retraction) = match &env.op {
        GossipOp::AssertLojban(s) => (Some(s.clone()), false),
        GossipOp::AssertDirect { relation, args } => {
            (Some(format!("{}({})", relation, args.join(", "))), false)
        }
        GossipOp::Retract(_) => (None, true),
    };

    EnvelopeSummaryGql {
        id: env.id.clone(),
        author: env.author.clone(),
        lojban,
        stance: format!("{}", env.stance),
        topics: env.topics.clone(),
        timestamp: env.timestamp.clone(),
        is_retraction,
        is_quarantined: env.quarantined,
    }
}

fn event_to_gql(event: &GossipEvent) -> GossipEventGql {
    match event {
        GossipEvent::NewEnvelope { envelope_id, author, lojban, stance, topics, timestamp } => {
            GossipEventGql {
                kind: "envelope".to_string(),
                envelope_id: Some(envelope_id.clone()),
                author: Some(author.clone()),
                lojban: lojban.clone(),
                stance: Some(stance.clone()),
                topics: Some(topics.clone()),
                timestamp: Some(timestamp.clone()),
                peer_id: None,
                connected: None,
                envelope_count: None,
                trusted: None,
                from: None,
                to: None,
                contradiction_id: None,
                assertion: None,
                resolved: None,
            }
        }
        GossipEvent::Contradiction { id, envelope_id, assertion, author } => {
            GossipEventGql {
                kind: "contradiction".to_string(),
                contradiction_id: Some(*id as u32),
                envelope_id: Some(envelope_id.clone()),
                assertion: Some(assertion.clone()),
                author: Some(author.clone()),
                lojban: None, stance: None, topics: None, timestamp: None,
                peer_id: None, connected: None, envelope_count: None,
                trusted: None, from: None, to: None, resolved: None,
            }
        }
        GossipEvent::PeerChange { peer_id, connected } => {
            GossipEventGql {
                kind: "peer_change".to_string(),
                peer_id: Some(peer_id.clone()),
                connected: Some(*connected),
                envelope_id: None, author: None, lojban: None, stance: None,
                topics: None, timestamp: None, envelope_count: None,
                trusted: None, from: None, to: None, contradiction_id: None,
                assertion: None, resolved: None,
            }
        }
        GossipEvent::TrustChange { from, to, trusted } => {
            GossipEventGql {
                kind: "trust_change".to_string(),
                from: Some(from.clone()),
                to: Some(to.clone()),
                trusted: Some(*trusted),
                envelope_id: None, author: None, lojban: None, stance: None,
                topics: None, timestamp: None, peer_id: None, connected: None,
                envelope_count: None, contradiction_id: None, assertion: None,
                resolved: None,
            }
        }
        GossipEvent::Sync { peer_id, envelope_count } => {
            GossipEventGql {
                kind: "sync".to_string(),
                peer_id: Some(peer_id.clone()),
                envelope_count: Some(*envelope_count as u32),
                envelope_id: None, author: None, lojban: None, stance: None,
                topics: None, timestamp: None, connected: None,
                trusted: None, from: None, to: None, contradiction_id: None,
                assertion: None, resolved: None,
            }
        }
    }
}

/// Assert all non-blank, non-comment lines from KB text, collecting per-line results.
fn assert_kb_lines(engine: &NibliEngine, kb: &str) -> KbStatusGql {
    let mut line_results = Vec::new();
    let mut asserted = 0u32;
    let mut errors = 0u32;
    let mut skipped = 0u32;

    for (i, line) in kb.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            skipped += 1;
            continue;
        }
        let line_number = (i + 1) as u32;
        match engine.assert_text(trimmed) {
            Ok(fact_id) => {
                asserted += 1;
                line_results.push(LineResultGql {
                    line_number,
                    text: trimmed.to_string(),
                    success: true,
                    fact_id: Some(fact_id),
                    error: None,
                });
            }
            Err(e) => {
                errors += 1;
                line_results.push(LineResultGql {
                    line_number,
                    text: trimmed.to_string(),
                    success: false,
                    fact_id: None,
                    error: Some(e),
                });
            }
        }
    }

    KbStatusGql {
        asserted,
        errors,
        skipped,
        line_results,
    }
}

// ── GraphQL output types ──

#[derive(async_graphql::SimpleObject)]
struct StatusResult {
    ready: bool,
}

#[derive(async_graphql::SimpleObject)]
struct TranslateResult {
    lojban: Option<String>,
    error: Option<String>,
}

#[derive(async_graphql::SimpleObject)]
struct AssertResult {
    fact_id: Option<u64>,
    error: Option<String>,
}

#[derive(async_graphql::SimpleObject)]
struct SimpleResult {
    success: bool,
    error: Option<String>,
}

#[derive(async_graphql::SimpleObject)]
struct GossipAssertResult {
    envelope_id: Option<String>,
    error: Option<String>,
}

#[derive(async_graphql::SimpleObject)]
struct LineResultGql {
    line_number: u32,
    text: String,
    success: bool,
    fact_id: Option<u64>,
    error: Option<String>,
}

#[derive(async_graphql::SimpleObject)]
struct KbStatusGql {
    asserted: u32,
    errors: u32,
    skipped: u32,
    line_results: Vec<LineResultGql>,
}

#[derive(async_graphql::SimpleObject)]
struct QueryResult {
    holds: Option<bool>,
    proof_trace: Option<String>,
    proof_trace_json: Option<String>,
    kb_status: Option<KbStatusGql>,
    error: Option<String>,
}

#[derive(async_graphql::SimpleObject)]
struct StanceCountsGql {
    deduced: u32,
    expected: u32,
    opinion: u32,
    hearsay: u32,
}

#[derive(async_graphql::SimpleObject)]
struct NetworkAgentGql {
    name: String,
    envelope_count: u32,
    stance_counts: StanceCountsGql,
    topics: Vec<String>,
    is_local: bool,
}

#[derive(async_graphql::SimpleObject)]
struct EnvelopeSummaryGql {
    id: String,
    author: String,
    lojban: Option<String>,
    stance: String,
    topics: Vec<String>,
    timestamp: String,
    is_retraction: bool,
    is_quarantined: bool,
}

#[derive(async_graphql::SimpleObject)]
struct ContradictionSummaryGql {
    id: u32,
    envelope_id: String,
    assertion: String,
    author: String,
    resolved: bool,
}

#[derive(async_graphql::SimpleObject)]
struct NetworkSnapshotGql {
    agents: Vec<NetworkAgentGql>,
    envelopes: Vec<EnvelopeSummaryGql>,
    contradictions: Vec<ContradictionSummaryGql>,
    peers: Vec<String>,
    local_agent: String,
    total_facts: u32,
}

#[derive(async_graphql::SimpleObject)]
struct GossipEventGql {
    kind: String,
    envelope_id: Option<String>,
    author: Option<String>,
    lojban: Option<String>,
    stance: Option<String>,
    topics: Option<Vec<String>>,
    timestamp: Option<String>,
    peer_id: Option<String>,
    connected: Option<bool>,
    envelope_count: Option<u32>,
    trusted: Option<bool>,
    from: Option<String>,
    to: Option<String>,
    contradiction_id: Option<u32>,
    assertion: Option<String>,
    resolved: Option<bool>,
}

fn snapshot_to_gql(snap: &NetworkSnapshot) -> NetworkSnapshotGql {
    NetworkSnapshotGql {
        agents: snap.agents.iter().map(|a| NetworkAgentGql {
            name: a.name.clone(),
            envelope_count: a.envelope_count,
            stance_counts: StanceCountsGql {
                deduced: a.stance_counts.deduced,
                expected: a.stance_counts.expected,
                opinion: a.stance_counts.opinion,
                hearsay: a.stance_counts.hearsay,
            },
            topics: a.topics.clone(),
            is_local: a.is_local,
        }).collect(),
        envelopes: snap.envelopes.iter().map(|e| EnvelopeSummaryGql {
            id: e.id.clone(),
            author: e.author.clone(),
            lojban: e.lojban.clone(),
            stance: e.stance.clone(),
            topics: e.topics.clone(),
            timestamp: e.timestamp.clone(),
            is_retraction: e.is_retraction,
            is_quarantined: e.is_quarantined,
        }).collect(),
        contradictions: snap.contradictions.iter().map(|c| ContradictionSummaryGql {
            id: c.id as u32,
            envelope_id: c.envelope_id.clone(),
            assertion: c.assertion.clone(),
            author: c.author.clone(),
            resolved: c.resolved,
        }).collect(),
        peers: snap.peers.clone(),
        local_agent: snap.local_agent.clone(),
        total_facts: snap.total_facts,
    }
}

// ── Main ──

#[tokio::main]
async fn main() -> Result<()> {
    println!("Nibli GraphQL Server starting...");

    let engine_state = Arc::new(Mutex::new(NibliEngine::new()));

    let gossip_agent = std::env::var("NIBLI_GOSSIP_AGENT")
        .unwrap_or_else(|_| "nibli-server".to_string());
    let gossip_state = Arc::new(Mutex::new(GossipNode::new(&gossip_agent)));
    let gossip_events: Arc<Mutex<Vec<GossipEvent>>> = Arc::new(Mutex::new(Vec::new()));

    println!("Gossip agent: {}", gossip_agent);

    // Connect to gossip hub if NIBLI_GOSSIP_HUB is set.
    if let Ok(hub_addr) = std::env::var("NIBLI_GOSSIP_HUB") {
        let gs = gossip_state.clone();
        let ge = gossip_events.clone();
        let es = engine_state.clone();
        let agent = gossip_agent.clone();
        tokio::spawn(async move {
            gossip_hub_listener(&hub_addr, &agent, gs, ge, es).await;
        });
    }

    let ollama_url = std::env::var("NIBLI_OLLAMA_URL")
        .unwrap_or_else(|_| "http://localhost:11434".to_string());
    let ollama_model = std::env::var("NIBLI_OLLAMA_MODEL")
        .unwrap_or_else(|_| "qwen3-coder:30b".to_string());
    println!(
        "Ollama config: url={}, model={}",
        ollama_url, ollama_model
    );
    let ollama_config = Arc::new(OllamaConfig {
        url: ollama_url,
        model: ollama_model,
    });

    let schema = Schema::build(QueryRoot, MutationRoot, EmptySubscription)
        .data(engine_state)
        .data(ollama_config)
        .data(gossip_state)
        .data(gossip_events)
        .finish();

    let port: u16 = std::env::var("NIBLI_SERVER_PORT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(8081);

    let app = Router::new()
        .route(
            "/graphql",
            axum::routing::get(graphql_playground).post_service(GraphQL::new(schema)),
        )
        .layer(CorsLayer::permissive());

    let listener = tokio::net::TcpListener::bind(format!("0.0.0.0:{}", port)).await?;
    println!(
        "GraphQL server listening on http://localhost:{}/graphql",
        port
    );

    axum::serve(listener, app).await?;
    Ok(())
}

async fn graphql_playground() -> impl axum::response::IntoResponse {
    axum::response::Html(async_graphql::http::playground_source(
        async_graphql::http::GraphQLPlaygroundConfig::new("/graphql"),
    ))
}

/// Connect to the gossip hub as a peer, receive envelopes, ingest into GossipNode + engine.
async fn gossip_hub_listener(
    addr: &str,
    agent_name: &str,
    gossip_state: Arc<Mutex<GossipNode>>,
    gossip_events: Arc<Mutex<Vec<GossipEvent>>>,
    engine_state: Arc<Mutex<NibliEngine>>,
) {
    // Connect with retry.
    let stream = loop {
        match TcpStream::connect(addr).await {
            Ok(s) => break s,
            Err(e) => {
                eprintln!("[gossip] Connect to hub {addr} failed: {e}, retrying in 3s...");
                tokio::time::sleep(std::time::Duration::from_secs(3)).await;
            }
        }
    };

    // Handshake: send our name.
    let (read_half, mut write_half) = stream.into_split();
    let hello = format!("{agent_name}\n");
    if write_half.write_all(hello.as_bytes()).await.is_err() {
        eprintln!("[gossip] Handshake failed");
        return;
    }
    println!("[gossip] Connected to hub at {addr}");

    // Read JSON Lines from hub.
    let mut reader = BufReader::new(read_half);
    let mut line = String::new();
    loop {
        line.clear();
        match reader.read_line(&mut line).await {
            Ok(0) => {
                eprintln!("[gossip] Hub disconnected");
                break;
            }
            Ok(_) => {
                let trimmed = line.trim();
                if trimmed.is_empty() {
                    continue;
                }
                match serde_json::from_str::<WireMessage>(trimmed) {
                    Ok(WireMessage::Envelope(env)) => {
                        let author = env.author.clone();
                        let lojban = match &env.op {
                            GossipOp::AssertLojban(text) => Some(text.clone()),
                            _ => None,
                        };

                        // Ingest into GossipNode.
                        {
                            let mut node = gossip_state.lock().unwrap();
                            let _ = node.ingest(env.clone());
                        }

                        // Record event.
                        {
                            let mut events = gossip_events.lock().unwrap();
                            events.push(GossipEvent::NewEnvelope {
                                envelope_id: env.id.clone(),
                                author: author.clone(),
                                lojban: lojban.clone(),
                                stance: format!("{}", env.stance),
                                topics: env.topics.clone(),
                                timestamp: env.timestamp.clone(),
                            });
                            // Cap event log.
                            if events.len() > 200 {
                                events.drain(..100);
                            }
                        }

                        // Assert Lojban into engine KB.
                        if let Some(text) = lojban {
                            let engine = engine_state.lock().unwrap();
                            match engine.assert_text(&text) {
                                Ok(id) => println!("[gossip] {author}: \"{text}\" → fact #{id}"),
                                Err(e) => eprintln!("[gossip] {author}: assert error: {e}"),
                            }
                        }
                    }
                    Ok(_) => {} // Ignore sync messages.
                    Err(e) => {
                        eprintln!("[gossip] Bad JSON: {e}");
                    }
                }
            }
            Err(e) => {
                eprintln!("[gossip] Read error: {e}");
                break;
            }
        }
    }
}
