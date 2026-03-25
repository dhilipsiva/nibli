use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use anyhow::{Context, Result};
use async_graphql::{EmptySubscription, Object, Schema};
use async_graphql_axum::{GraphQLRequest, GraphQLResponse};
use axum::extract::{DefaultBodyLimit, State};
use axum::http::{HeaderValue, Method, StatusCode};
use axum::response::IntoResponse;
use axum::{Json, Router};
use tokio::task;
use tower_http::cors::CorsLayer;
use tower_http::trace::{DefaultMakeSpan, DefaultOnResponse, TraceLayer};
use tracing::{Level, error, info, warn};

use nibli_engine::NibliEngine;
use nibli_protocol::{
    ContradictionSummary, EnvelopeSummary, GossipEvent, NetworkAgent, NetworkSnapshot, StanceCounts,
};
use tavla::tcp::TcpTransport;
use tavla::transport::{InboundMessage, Transport};
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

type SharedGossip = Arc<Mutex<GossipNode>>;
type SharedEvents = Arc<Mutex<Vec<GossipEvent>>>;
type SharedTransport = Option<Arc<dyn Transport>>;
type SharedMetrics = Arc<ServerMetrics>;
type SharedConfig = Arc<ServerConfig>;
type AppSchema = Schema<QueryRoot, MutationRoot, EmptySubscription>;

#[derive(Clone)]
struct HttpState {
    schema: Arc<AppSchema>,
    gossip: SharedGossip,
    events: SharedEvents,
    transport: SharedTransport,
    metrics: SharedMetrics,
    config: SharedConfig,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LogFormat {
    Pretty,
    Json,
}

#[derive(Clone, Debug)]
struct ServerConfig {
    bind_addr: SocketAddr,
    enable_playground: bool,
    require_gossip_peer: bool,
    max_request_bytes: usize,
    max_gossip_events: usize,
    cors_allowed_origins: Vec<String>,
    log_format: LogFormat,
    log_filter: String,
}

impl ServerConfig {
    fn from_env() -> Result<Self> {
        let bind_addr = if let Ok(bind) = std::env::var("NIBLI_SERVER_BIND") {
            bind.parse::<SocketAddr>()
                .with_context(|| format!("invalid NIBLI_SERVER_BIND value: {bind}"))?
        } else {
            let port = std::env::var("NIBLI_SERVER_PORT")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(8081);
            SocketAddr::from(([127, 0, 0, 1], port))
        };

        let bind_is_loopback = bind_addr.ip().is_loopback();
        let cors_allowed_origins =
            Self::read_origins("NIBLI_SERVER_CORS_ALLOW_ORIGINS", bind_is_loopback);

        Ok(Self {
            bind_addr,
            enable_playground: Self::read_bool("NIBLI_SERVER_ENABLE_PLAYGROUND")
                .unwrap_or(bind_is_loopback),
            require_gossip_peer: Self::read_bool("NIBLI_SERVER_REQUIRE_GOSSIP_PEER")
                .unwrap_or(false),
            max_request_bytes: Self::read_usize("NIBLI_SERVER_MAX_REQUEST_BYTES")
                .unwrap_or(1_048_576),
            max_gossip_events: Self::read_usize("NIBLI_SERVER_MAX_GOSSIP_EVENTS")
                .unwrap_or(500)
                .max(1),
            cors_allowed_origins,
            log_format: match std::env::var("NIBLI_SERVER_LOG_FORMAT")
                .unwrap_or_else(|_| "pretty".to_string())
                .to_ascii_lowercase()
                .as_str()
            {
                "json" => LogFormat::Json,
                _ => LogFormat::Pretty,
            },
            log_filter: std::env::var("NIBLI_SERVER_LOG")
                .or_else(|_| std::env::var("RUST_LOG"))
                .unwrap_or_else(|_| "info,tower_http=info".to_string()),
        })
    }

    fn read_bool(name: &str) -> Option<bool> {
        let value = std::env::var(name).ok()?;
        match value.trim().to_ascii_lowercase().as_str() {
            "1" | "true" | "yes" | "on" => Some(true),
            "0" | "false" | "no" | "off" => Some(false),
            _ => None,
        }
    }

    fn read_usize(name: &str) -> Option<usize> {
        std::env::var(name).ok()?.trim().parse().ok()
    }

    fn read_origins(name: &str, loopback_defaults: bool) -> Vec<String> {
        if let Ok(value) = std::env::var(name) {
            return value
                .split(',')
                .map(str::trim)
                .filter(|origin| !origin.is_empty())
                .map(ToOwned::to_owned)
                .collect();
        }

        if loopback_defaults {
            vec![
                "http://localhost:3000".to_string(),
                "http://127.0.0.1:3000".to_string(),
                "http://localhost:4173".to_string(),
                "http://127.0.0.1:4173".to_string(),
                "http://localhost:8080".to_string(),
                "http://127.0.0.1:8080".to_string(),
                "http://localhost:8081".to_string(),
                "http://127.0.0.1:8081".to_string(),
            ]
        } else {
            Vec::new()
        }
    }
}

#[derive(Default)]
struct ServerMetrics {
    http_requests_total: AtomicU64,
    graphql_requests_total: AtomicU64,
    graphql_failures_total: AtomicU64,
    playground_requests_total: AtomicU64,
    health_requests_total: AtomicU64,
    readiness_requests_total: AtomicU64,
    metrics_requests_total: AtomicU64,
    gossip_events_total: AtomicU64,
    gossip_events_dropped_total: AtomicU64,
    gossip_envelopes_ingested_total: AtomicU64,
    gossip_duplicate_envelopes_total: AtomicU64,
    gossip_rejected_envelopes_total: AtomicU64,
    gossip_broadcast_failures_total: AtomicU64,
    transport_receive_errors_total: AtomicU64,
}

#[derive(Debug, Clone, serde::Serialize)]
struct HealthResponse {
    status: &'static str,
    service: &'static str,
}

#[derive(Debug, Clone, serde::Serialize)]
struct ReadyResponse {
    ready: bool,
    gossip_lock_ok: bool,
    event_log_lock_ok: bool,
    require_gossip_peer: bool,
    gossip_peer_count: usize,
    event_buffer_len: usize,
    max_event_buffer_len: usize,
}

#[derive(Debug, Clone, Copy)]
struct ReadinessSnapshot {
    ready: bool,
    gossip_lock_ok: bool,
    event_log_lock_ok: bool,
    gossip_peer_count: usize,
    event_buffer_len: usize,
}

fn init_tracing(config: &ServerConfig) {
    let env_filter = tracing_subscriber::EnvFilter::try_new(config.log_filter.clone())
        .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info"));

    let fmt = tracing_subscriber::fmt()
        .with_env_filter(env_filter)
        .with_target(false)
        .with_thread_ids(true)
        .with_file(false)
        .with_line_number(false);

    match config.log_format {
        LogFormat::Pretty => {
            fmt.compact().init();
        }
        LogFormat::Json => {
            fmt.json().init();
        }
    }
}

fn readiness_snapshot(
    gossip: &SharedGossip,
    events: &SharedEvents,
    transport: &SharedTransport,
    config: &ServerConfig,
) -> ReadinessSnapshot {
    let gossip_lock_ok = gossip.lock().is_ok();
    let (event_log_lock_ok, event_buffer_len) = match events.lock() {
        Ok(events) => (true, events.len()),
        Err(_) => (false, 0),
    };
    let gossip_peer_count = transport.as_ref().map_or(0, |transport| transport.peers().len());
    let ready = gossip_lock_ok
        && event_log_lock_ok
        && (!config.require_gossip_peer || gossip_peer_count > 0);

    ReadinessSnapshot {
        ready,
        gossip_lock_ok,
        event_log_lock_ok,
        gossip_peer_count,
        event_buffer_len,
    }
}

fn build_metrics_response(state: &HttpState) -> String {
    let readiness = readiness_snapshot(
        &state.gossip,
        &state.events,
        &state.transport,
        state.config.as_ref(),
    );

    let mut lines = Vec::new();
    lines.push("# TYPE nibli_http_requests_total counter".to_string());
    lines.push(format!(
        "nibli_http_requests_total {}",
        state.metrics.http_requests_total.load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_graphql_requests_total counter".to_string());
    lines.push(format!(
        "nibli_graphql_requests_total {}",
        state.metrics.graphql_requests_total.load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_graphql_failures_total counter".to_string());
    lines.push(format!(
        "nibli_graphql_failures_total {}",
        state.metrics.graphql_failures_total.load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_playground_requests_total counter".to_string());
    lines.push(format!(
        "nibli_playground_requests_total {}",
        state.metrics.playground_requests_total.load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_health_requests_total counter".to_string());
    lines.push(format!(
        "nibli_health_requests_total {}",
        state.metrics.health_requests_total.load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_readiness_requests_total counter".to_string());
    lines.push(format!(
        "nibli_readiness_requests_total {}",
        state.metrics.readiness_requests_total.load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_metrics_requests_total counter".to_string());
    lines.push(format!(
        "nibli_metrics_requests_total {}",
        state.metrics.metrics_requests_total.load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_gossip_events_total counter".to_string());
    lines.push(format!(
        "nibli_gossip_events_total {}",
        state.metrics.gossip_events_total.load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_gossip_events_dropped_total counter".to_string());
    lines.push(format!(
        "nibli_gossip_events_dropped_total {}",
        state.metrics.gossip_events_dropped_total.load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_gossip_envelopes_ingested_total counter".to_string());
    lines.push(format!(
        "nibli_gossip_envelopes_ingested_total {}",
        state
            .metrics
            .gossip_envelopes_ingested_total
            .load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_gossip_duplicate_envelopes_total counter".to_string());
    lines.push(format!(
        "nibli_gossip_duplicate_envelopes_total {}",
        state
            .metrics
            .gossip_duplicate_envelopes_total
            .load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_gossip_rejected_envelopes_total counter".to_string());
    lines.push(format!(
        "nibli_gossip_rejected_envelopes_total {}",
        state
            .metrics
            .gossip_rejected_envelopes_total
            .load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_gossip_broadcast_failures_total counter".to_string());
    lines.push(format!(
        "nibli_gossip_broadcast_failures_total {}",
        state
            .metrics
            .gossip_broadcast_failures_total
            .load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_transport_receive_errors_total counter".to_string());
    lines.push(format!(
        "nibli_transport_receive_errors_total {}",
        state
            .metrics
            .transport_receive_errors_total
            .load(Ordering::Relaxed)
    ));
    lines.push("# TYPE nibli_gossip_event_buffer_len gauge".to_string());
    lines.push(format!(
        "nibli_gossip_event_buffer_len {}",
        readiness.event_buffer_len
    ));
    lines.push("# TYPE nibli_gossip_event_buffer_capacity gauge".to_string());
    lines.push(format!(
        "nibli_gossip_event_buffer_capacity {}",
        state.config.max_gossip_events
    ));
    lines.push("# TYPE nibli_gossip_peer_count gauge".to_string());
    lines.push(format!(
        "nibli_gossip_peer_count {}",
        readiness.gossip_peer_count
    ));
    lines.push("# TYPE nibli_ready gauge".to_string());
    lines.push(format!("nibli_ready {}", u8::from(readiness.ready)));

    lines.join("\n") + "\n"
}

fn build_cors_layer(config: &ServerConfig) -> Option<CorsLayer> {
    if config.cors_allowed_origins.is_empty() {
        return None;
    }

    let mut invalid_origins = 0usize;
    let origins: Vec<HeaderValue> = config
        .cors_allowed_origins
        .iter()
        .filter_map(|origin| match HeaderValue::from_str(origin) {
            Ok(origin) => Some(origin),
            Err(_) => {
                invalid_origins += 1;
                None
            }
        })
        .collect();

    if invalid_origins > 0 {
        warn!(
            invalid_origins,
            "ignoring invalid entries in NIBLI_SERVER_CORS_ALLOW_ORIGINS"
        );
    }

    if origins.is_empty() {
        warn!("no valid CORS origins configured; cross-origin requests remain disabled");
        return None;
    }

    Some(
        CorsLayer::new()
            .allow_methods([Method::GET, Method::POST])
            .allow_headers([axum::http::header::ACCEPT, axum::http::header::CONTENT_TYPE])
            .allow_origin(origins),
    )
}

async fn run_blocking<T, F>(f: F) -> T
where
    T: Send + 'static,
    F: FnOnce() -> T + Send + 'static,
{
    task::spawn_blocking(f)
        .await
        .expect("blocking server task should not panic")
}

// ── GraphQL schema ──

struct QueryRoot;

#[Object]
impl QueryRoot {
    async fn status(&self, ctx: &async_graphql::Context<'_>) -> StatusResult {
        let gossip = ctx.data::<SharedGossip>().unwrap().clone();
        let events = ctx.data::<SharedEvents>().unwrap().clone();
        let transport = ctx.data::<SharedTransport>().unwrap().clone();
        let config = ctx.data::<SharedConfig>().unwrap().clone();
        run_blocking(move || {
            let readiness = readiness_snapshot(&gossip, &events, &transport, config.as_ref());
            StatusResult {
                ready: readiness.ready,
            }
        })
        .await
    }

    /// Get a snapshot of the gossip network state.
    async fn network_snapshot(&self, ctx: &async_graphql::Context<'_>) -> NetworkSnapshotGql {
        let gossip = ctx.data::<SharedGossip>().unwrap().clone();
        let transport = ctx.data::<SharedTransport>().unwrap().clone();
        run_blocking(move || match gossip.lock() {
            Ok(node) => {
                let peers = transport
                    .as_ref()
                    .map_or_else(Vec::new, |transport| transport.peers());
                let snapshot = build_network_snapshot(&node, peers);
                snapshot_to_gql(&snapshot)
            }
            Err(_) => NetworkSnapshotGql {
                agents: Vec::new(),
                envelopes: Vec::new(),
                contradictions: Vec::new(),
                peers: Vec::new(),
                local_agent: String::new(),
                total_facts: 0,
            },
        })
        .await
    }

    /// Get all envelopes authored by a specific agent.
    async fn agent_envelopes(
        &self,
        ctx: &async_graphql::Context<'_>,
        agent: String,
    ) -> Vec<EnvelopeSummaryGql> {
        let gossip = ctx.data::<SharedGossip>().unwrap().clone();
        run_blocking(move || match gossip.lock() {
            Ok(node) => node
                .log()
                .iter()
                .filter(|e| e.author == agent)
                .map(|env| envelope_to_gql(env))
                .collect(),
            Err(_) => Vec::new(),
        })
        .await
    }

    /// Get details of a specific envelope by ID prefix.
    async fn envelope_detail(
        &self,
        ctx: &async_graphql::Context<'_>,
        id_prefix: String,
    ) -> Option<EnvelopeSummaryGql> {
        let gossip = ctx.data::<SharedGossip>().unwrap().clone();
        run_blocking(move || match gossip.lock() {
            Ok(node) => node
                .log()
                .iter()
                .find(|e| e.id.starts_with(&id_prefix))
                .map(|env| envelope_to_gql(env)),
            Err(_) => None,
        })
        .await
    }

    /// Get the gossip event log (most recent events).
    async fn gossip_events(
        &self,
        ctx: &async_graphql::Context<'_>,
        limit: Option<u32>,
    ) -> Vec<GossipEventGql> {
        let limit = limit.unwrap_or(50) as usize;
        let events = ctx.data::<SharedEvents>().unwrap().clone();
        run_blocking(move || match events.lock() {
            Ok(events) => events.iter().rev().take(limit).map(event_to_gql).collect(),
            Err(_) => Vec::new(),
        })
        .await
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

    async fn assert_text(&self, ctx: &async_graphql::Context<'_>, input: String) -> AssertResult {
        let gossip = ctx.data::<SharedGossip>().unwrap().clone();
        run_blocking(move || match gossip.lock() {
            Ok(mut node) => match node.assert_local_result(&input) {
                Ok((fact_id, _envelope)) => AssertResult {
                    fact_id: Some(fact_id),
                    error: None,
                },
                Err(e) => AssertResult {
                    fact_id: None,
                    error: Some(e),
                },
            },
            Err(_) => AssertResult {
                fact_id: None,
                error: Some("gossip state lock poisoned".to_string()),
            },
        })
        .await
    }

    async fn query_text(&self, ctx: &async_graphql::Context<'_>, input: String) -> QueryResult {
        let gossip = ctx.data::<SharedGossip>().unwrap().clone();
        run_blocking(move || match gossip.lock() {
            Ok(node) => match node.query_with_proof(&input) {
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
            },
            Err(_) => QueryResult {
                holds: None,
                proof_trace: None,
                proof_trace_json: None,
                kb_status: None,
                error: Some("gossip state lock poisoned".to_string()),
            },
        })
        .await
    }

    /// Reset the engine, assert all KB lines, then run a query.
    async fn query_with_kb(
        &self,
        _ctx: &async_graphql::Context<'_>,
        kb: String,
        query: String,
    ) -> QueryResult {
        run_blocking(move || {
            let engine = NibliEngine::new();
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
        })
        .await
    }

    /// Assert Lojban into the gossip-backed authoritative knowledge state.
    async fn gossip_assert(
        &self,
        ctx: &async_graphql::Context<'_>,
        lojban: String,
        stance: Option<String>,
    ) -> GossipAssertResult {
        let gossip = ctx.data::<SharedGossip>().unwrap().clone();
        let events = ctx.data::<SharedEvents>().unwrap().clone();
        let transport = ctx.data::<SharedTransport>().unwrap().clone();
        let metrics = ctx.data::<SharedMetrics>().unwrap().clone();
        let config = ctx.data::<SharedConfig>().unwrap().clone();
        let mutation_metrics = metrics.clone();
        let ep_stance = match stance.as_deref() {
            Some("Expected") | Some("ba'a") => EpistemicStance::Expected,
            Some("Opinion") | Some("pe'i") => EpistemicStance::Opinion,
            Some("Hearsay") | Some("ti'e") => EpistemicStance::Hearsay,
            _ => EpistemicStance::Deduced,
        };

        let envelope = match run_blocking(move || -> Result<tavla::Envelope, String> {
            let envelope = match gossip.lock() {
                Ok(mut node) => match node.assert_local_with_stance_result(&lojban, ep_stance) {
                    Ok((_fact_id, envelope)) => envelope,
                    Err(e) => return Err(e),
                },
                Err(_) => return Err("gossip state lock poisoned".to_string()),
            };

            push_gossip_event(
                &events,
                &mutation_metrics,
                config.max_gossip_events,
                GossipEvent::NewEnvelope {
                    envelope_id: envelope.id.clone(),
                    author: envelope.author.clone(),
                    lojban: Some(lojban),
                    stance: format!("{}", envelope.stance),
                    topics: envelope.topics.clone(),
                    timestamp: envelope.timestamp.clone(),
                },
            );

            Ok(envelope)
        })
        .await
        {
            Ok(envelope) => envelope,
            Err(e) => {
                return GossipAssertResult {
                    envelope_id: None,
                    error: Some(e),
                };
            }
        };

        if let Err(e) = broadcast_wire_message(
            transport,
            WireMessage::Envelope(envelope.clone()),
            metrics.clone(),
        )
        .await
        {
            return GossipAssertResult {
                envelope_id: Some(envelope.id),
                error: Some(format!("local assert succeeded, but broadcast failed: {e}")),
            };
        }

        GossipAssertResult {
            envelope_id: Some(envelope.id),
            error: None,
        }
    }

    /// Retract a known envelope by ID prefix and broadcast the tombstone.
    async fn gossip_retract(
        &self,
        ctx: &async_graphql::Context<'_>,
        envelope_id: String,
    ) -> GossipAssertResult {
        let gossip = ctx.data::<SharedGossip>().unwrap().clone();
        let events = ctx.data::<SharedEvents>().unwrap().clone();
        let transport = ctx.data::<SharedTransport>().unwrap().clone();
        let metrics = ctx.data::<SharedMetrics>().unwrap().clone();
        let config = ctx.data::<SharedConfig>().unwrap().clone();
        let mutation_metrics = metrics.clone();

        let tombstone = match run_blocking(move || -> Result<tavla::Envelope, String> {
            let tombstone = match gossip.lock() {
                Ok(mut node) => {
                    let matches: Vec<String> = node
                        .log()
                        .into_iter()
                        .filter(|env| {
                            env.id.starts_with(&envelope_id)
                                && !node.crdt_log().is_tombstoned(&env.id)
                        })
                        .map(|env| env.id.clone())
                        .collect();

                    match matches.as_slice() {
                        [] => return Err(format!("no envelope matching prefix '{envelope_id}'")),
                        [_, _, ..] => {
                            return Err(format!("ambiguous envelope prefix '{envelope_id}'"));
                        }
                        [target_id] => node.retract_local(target_id)?,
                    }
                }
                Err(_) => return Err("gossip state lock poisoned".to_string()),
            };

            push_gossip_event(
                &events,
                &mutation_metrics,
                config.max_gossip_events,
                GossipEvent::NewEnvelope {
                    envelope_id: tombstone.id.clone(),
                    author: tombstone.author.clone(),
                    lojban: None,
                    stance: format!("{}", tombstone.stance),
                    topics: tombstone.topics.clone(),
                    timestamp: tombstone.timestamp.clone(),
                },
            );

            Ok(tombstone)
        })
        .await
        {
            Ok(tombstone) => tombstone,
            Err(e) => {
                return GossipAssertResult {
                    envelope_id: None,
                    error: Some(e),
                };
            }
        };

        if let Err(e) = broadcast_wire_message(
            transport,
            WireMessage::Envelope(tombstone.clone()),
            metrics.clone(),
        )
        .await
        {
            return GossipAssertResult {
                envelope_id: Some(tombstone.id),
                error: Some(format!(
                    "local retraction succeeded, but broadcast failed: {e}"
                )),
            };
        }

        GossipAssertResult {
            envelope_id: Some(tombstone.id),
            error: None,
        }
    }

    /// Resolve a contradiction by ID.
    async fn resolve_contradiction(
        &self,
        ctx: &async_graphql::Context<'_>,
        id: u32,
    ) -> SimpleResult {
        let gossip = ctx.data::<SharedGossip>().unwrap().clone();
        run_blocking(move || match gossip.lock() {
            Ok(mut node) => match node.resolve_contradiction(id as usize) {
                Ok(()) => SimpleResult {
                    success: true,
                    error: None,
                },
                Err(e) => SimpleResult {
                    success: false,
                    error: Some(e),
                },
            },
            Err(_) => SimpleResult {
                success: false,
                error: Some("gossip state lock poisoned".to_string()),
            },
        })
        .await
    }
}

// ── Gossip helpers ──

fn build_network_snapshot(node: &GossipNode, peers: Vec<String>) -> NetworkSnapshot {
    let envelopes = node.log();
    let mut agent_map: HashMap<String, (u32, StanceCounts, Vec<String>)> = HashMap::new();

    let mut envelope_summaries = Vec::new();
    for env in &envelopes {
        // Track per-agent stats.
        let entry = agent_map
            .entry(env.author.clone())
            .or_insert_with(|| (0, StanceCounts::default(), Vec::new()));
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
        peers,
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

fn envelope_display_text(env: &tavla::Envelope) -> Option<String> {
    match &env.op {
        GossipOp::AssertLojban(text) => Some(text.clone()),
        GossipOp::AssertDirect { relation, args } => {
            Some(format!("{}({})", relation, args.join(", ")))
        }
        GossipOp::Retract(_) => None,
    }
}

fn push_gossip_event(
    events: &SharedEvents,
    metrics: &SharedMetrics,
    max_events: usize,
    event: GossipEvent,
) {
    let mut events = events.lock().unwrap();
    events.push(event);
    metrics.gossip_events_total.fetch_add(1, Ordering::Relaxed);
    if events.len() > max_events {
        let overflow = events.len() - max_events;
        events.drain(..overflow);
        metrics
            .gossip_events_dropped_total
            .fetch_add(overflow as u64, Ordering::Relaxed);
    }
}

async fn broadcast_wire_message(
    transport: SharedTransport,
    msg: WireMessage,
    metrics: SharedMetrics,
) -> Result<(), String> {
    match transport {
        Some(transport) => transport.broadcast(&msg).await.map_err(|err| {
            metrics
                .gossip_broadcast_failures_total
                .fetch_add(1, Ordering::Relaxed);
            err
        }),
        None => Ok(()),
    }
}

fn event_to_gql(event: &GossipEvent) -> GossipEventGql {
    match event {
        GossipEvent::NewEnvelope {
            envelope_id,
            author,
            lojban,
            stance,
            topics,
            timestamp,
        } => GossipEventGql {
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
        },
        GossipEvent::Contradiction {
            id,
            envelope_id,
            assertion,
            author,
        } => GossipEventGql {
            kind: "contradiction".to_string(),
            contradiction_id: Some(*id as u32),
            envelope_id: Some(envelope_id.clone()),
            assertion: Some(assertion.clone()),
            author: Some(author.clone()),
            lojban: None,
            stance: None,
            topics: None,
            timestamp: None,
            peer_id: None,
            connected: None,
            envelope_count: None,
            trusted: None,
            from: None,
            to: None,
            resolved: None,
        },
        GossipEvent::PeerChange { peer_id, connected } => GossipEventGql {
            kind: "peer_change".to_string(),
            peer_id: Some(peer_id.clone()),
            connected: Some(*connected),
            envelope_id: None,
            author: None,
            lojban: None,
            stance: None,
            topics: None,
            timestamp: None,
            envelope_count: None,
            trusted: None,
            from: None,
            to: None,
            contradiction_id: None,
            assertion: None,
            resolved: None,
        },
        GossipEvent::TrustChange { from, to, trusted } => GossipEventGql {
            kind: "trust_change".to_string(),
            from: Some(from.clone()),
            to: Some(to.clone()),
            trusted: Some(*trusted),
            envelope_id: None,
            author: None,
            lojban: None,
            stance: None,
            topics: None,
            timestamp: None,
            peer_id: None,
            connected: None,
            envelope_count: None,
            contradiction_id: None,
            assertion: None,
            resolved: None,
        },
        GossipEvent::Sync {
            peer_id,
            envelope_count,
        } => GossipEventGql {
            kind: "sync".to_string(),
            peer_id: Some(peer_id.clone()),
            envelope_count: Some(*envelope_count as u32),
            envelope_id: None,
            author: None,
            lojban: None,
            stance: None,
            topics: None,
            timestamp: None,
            connected: None,
            trusted: None,
            from: None,
            to: None,
            contradiction_id: None,
            assertion: None,
            resolved: None,
        },
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
        agents: snap
            .agents
            .iter()
            .map(|a| NetworkAgentGql {
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
            })
            .collect(),
        envelopes: snap
            .envelopes
            .iter()
            .map(|e| EnvelopeSummaryGql {
                id: e.id.clone(),
                author: e.author.clone(),
                lojban: e.lojban.clone(),
                stance: e.stance.clone(),
                topics: e.topics.clone(),
                timestamp: e.timestamp.clone(),
                is_retraction: e.is_retraction,
                is_quarantined: e.is_quarantined,
            })
            .collect(),
        contradictions: snap
            .contradictions
            .iter()
            .map(|c| ContradictionSummaryGql {
                id: c.id as u32,
                envelope_id: c.envelope_id.clone(),
                assertion: c.assertion.clone(),
                author: c.author.clone(),
                resolved: c.resolved,
            })
            .collect(),
        peers: snap.peers.clone(),
        local_agent: snap.local_agent.clone(),
        total_facts: snap.total_facts,
    }
}

async fn graphql_handler(
    State(state): State<HttpState>,
    request: GraphQLRequest,
) -> GraphQLResponse {
    state
        .metrics
        .http_requests_total
        .fetch_add(1, Ordering::Relaxed);
    state
        .metrics
        .graphql_requests_total
        .fetch_add(1, Ordering::Relaxed);

    let response = state.schema.execute(request.into_inner()).await;
    if !response.errors.is_empty() {
        state
            .metrics
            .graphql_failures_total
            .fetch_add(1, Ordering::Relaxed);
    }
    response.into()
}

async fn graphql_playground(State(state): State<HttpState>) -> impl IntoResponse {
    state
        .metrics
        .http_requests_total
        .fetch_add(1, Ordering::Relaxed);
    state
        .metrics
        .playground_requests_total
        .fetch_add(1, Ordering::Relaxed);

    axum::response::Html(async_graphql::http::playground_source(
        async_graphql::http::GraphQLPlaygroundConfig::new("/graphql"),
    ))
}

async fn healthz(State(state): State<HttpState>) -> impl IntoResponse {
    state
        .metrics
        .http_requests_total
        .fetch_add(1, Ordering::Relaxed);
    state
        .metrics
        .health_requests_total
        .fetch_add(1, Ordering::Relaxed);

    (
        StatusCode::OK,
        Json(HealthResponse {
            status: "ok",
            service: "nibli-server",
        }),
    )
}

async fn readyz(State(state): State<HttpState>) -> impl IntoResponse {
    state
        .metrics
        .http_requests_total
        .fetch_add(1, Ordering::Relaxed);
    state
        .metrics
        .readiness_requests_total
        .fetch_add(1, Ordering::Relaxed);

    let readiness = readiness_snapshot(
        &state.gossip,
        &state.events,
        &state.transport,
        state.config.as_ref(),
    );
    let body = ReadyResponse {
        ready: readiness.ready,
        gossip_lock_ok: readiness.gossip_lock_ok,
        event_log_lock_ok: readiness.event_log_lock_ok,
        require_gossip_peer: state.config.require_gossip_peer,
        gossip_peer_count: readiness.gossip_peer_count,
        event_buffer_len: readiness.event_buffer_len,
        max_event_buffer_len: state.config.max_gossip_events,
    };

    let status = if readiness.ready {
        StatusCode::OK
    } else {
        StatusCode::SERVICE_UNAVAILABLE
    };

    (status, Json(body))
}

async fn metrics_handler(State(state): State<HttpState>) -> impl IntoResponse {
    state
        .metrics
        .http_requests_total
        .fetch_add(1, Ordering::Relaxed);
    state
        .metrics
        .metrics_requests_total
        .fetch_add(1, Ordering::Relaxed);

    (
        StatusCode::OK,
        [(axum::http::header::CONTENT_TYPE, "text/plain; version=0.0.4")],
        build_metrics_response(&state),
    )
}

fn build_app(state: HttpState) -> Router {
    let config = state.config.clone();
    let trace_layer = TraceLayer::new_for_http()
        .make_span_with(DefaultMakeSpan::new().level(Level::INFO))
        .on_response(DefaultOnResponse::new().level(Level::INFO));

    let mut app = Router::new()
        .route("/healthz", axum::routing::get(healthz))
        .route("/readyz", axum::routing::get(readyz))
        .route("/metrics", axum::routing::get(metrics_handler))
        .route("/graphql", axum::routing::post(graphql_handler));

    if config.enable_playground {
        app = app.route("/graphql", axum::routing::get(graphql_playground).post(graphql_handler));
    }

    if let Some(cors) = build_cors_layer(config.as_ref()) {
        app = app.layer(cors);
    }

    app.layer(DefaultBodyLimit::max(config.max_request_bytes))
        .layer(trace_layer)
        .with_state(state)
}

// ── Main ──

#[tokio::main]
async fn main() -> Result<()> {
    let config = Arc::new(ServerConfig::from_env()?);
    init_tracing(config.as_ref());
    info!("nibli-server starting");

    let gossip_agent =
        std::env::var("NIBLI_GOSSIP_AGENT").unwrap_or_else(|_| "nibli-server".to_string());
    let gossip_state: SharedGossip = Arc::new(Mutex::new(GossipNode::new(&gossip_agent)));
    let gossip_events: SharedEvents = Arc::new(Mutex::new(Vec::new()));
    let metrics: SharedMetrics = Arc::new(ServerMetrics::default());

    info!(gossip_agent = %gossip_agent, "configured gossip agent");

    let gossip_transport = if let Ok(hub_addr) = std::env::var("NIBLI_GOSSIP_HUB") {
        Some(
            attach_tcp_transport(
                &hub_addr,
                &gossip_agent,
                gossip_state.clone(),
                gossip_events.clone(),
                metrics.clone(),
                config.clone(),
            )
            .await
            .map_err(anyhow::Error::msg)?,
        )
    } else {
        None
    };

    let ollama_url =
        std::env::var("NIBLI_OLLAMA_URL").unwrap_or_else(|_| "http://localhost:11434".to_string());
    let ollama_model =
        std::env::var("NIBLI_OLLAMA_MODEL").unwrap_or_else(|_| "qwen3-coder:30b".to_string());
    info!(ollama_url = %ollama_url, ollama_model = %ollama_model, "configured ollama client");
    let ollama_config = Arc::new(OllamaConfig {
        url: ollama_url,
        model: ollama_model,
    });

    let schema: Arc<AppSchema> = Arc::new(
        Schema::build(QueryRoot, MutationRoot, EmptySubscription)
        .data(ollama_config)
        .data(gossip_state.clone())
        .data(gossip_events.clone())
        .data(gossip_transport.clone())
        .data(config.clone())
        .data(metrics.clone())
        .finish(),
    );

    let app_state = HttpState {
        schema: schema.clone(),
        gossip: gossip_state,
        events: gossip_events,
        transport: gossip_transport,
        metrics,
        config: config.clone(),
    };
    let app = build_app(app_state);

    let listener = tokio::net::TcpListener::bind(config.bind_addr)
        .await
        .with_context(|| format!("failed to bind {}", config.bind_addr))?;
    info!(
        bind_addr = %config.bind_addr,
        enable_playground = config.enable_playground,
        require_gossip_peer = config.require_gossip_peer,
        max_request_bytes = config.max_request_bytes,
        max_gossip_events = config.max_gossip_events,
        cors_allowed_origins = ?config.cors_allowed_origins,
        "server ready"
    );

    axum::serve(listener, app).await?;
    Ok(())
}

async fn attach_tcp_transport(
    addr: &str,
    agent_name: &str,
    gossip_state: SharedGossip,
    gossip_events: SharedEvents,
    metrics: SharedMetrics,
    config: SharedConfig,
) -> Result<Arc<dyn Transport>, String> {
    let transport: Arc<dyn Transport> = TcpTransport::client(addr, agent_name).await?;
    info!(peer = %addr, "connected to gossip transport peer");

    let listener_transport = transport.clone();
    tokio::spawn(async move {
        gossip_transport_listener(listener_transport, gossip_state, gossip_events, metrics, config)
            .await;
    });

    Ok(transport)
}

async fn gossip_transport_listener(
    transport: Arc<dyn Transport>,
    gossip_state: SharedGossip,
    gossip_events: SharedEvents,
    metrics: SharedMetrics,
    config: SharedConfig,
) {
    loop {
        match transport.recv().await {
            Ok(inbound) => {
                handle_inbound_wire_message(
                    &transport,
                    inbound,
                    gossip_state.clone(),
                    gossip_events.clone(),
                    metrics.clone(),
                    config.clone(),
                )
                .await;
            }
            Err(e) => {
                metrics
                    .transport_receive_errors_total
                    .fetch_add(1, Ordering::Relaxed);
                error!(error = %e, "gossip transport receive error");
                break;
            }
        }
    }
}

async fn handle_inbound_wire_message(
    transport: &Arc<dyn Transport>,
    inbound: InboundMessage,
    gossip_state: SharedGossip,
    gossip_events: SharedEvents,
    metrics: SharedMetrics,
    config: SharedConfig,
) {
    let InboundMessage { peer_id, message } = inbound;
    match message {
        WireMessage::Envelope(envelope) => {
            let forwarded = WireMessage::Envelope(envelope.clone());
            for peer in transport
                .peers()
                .into_iter()
                .filter(|peer| peer != &peer_id)
            {
                if let Err(err) = transport.send_to(&peer, &forwarded).await {
                    metrics
                        .gossip_broadcast_failures_total
                        .fetch_add(1, Ordering::Relaxed);
                    error!(peer = %peer, error = %err, "failed to forward envelope to peer");
                }
            }

            if let Err(e) = ingest_envelope_from_peer(
                envelope,
                Some(peer_id),
                gossip_state,
                gossip_events,
                metrics.clone(),
                config.clone(),
            )
            .await
            {
                error!(error = %e, "gossip envelope ingest error");
            }
        }
        WireMessage::SyncRequest { clock } => {
            let peer_for_event = peer_id.clone();
            let missing = run_blocking(move || -> Result<Vec<tavla::Envelope>, String> {
                match gossip_state.lock() {
                    Ok(node) => Ok(node.sync_diff(&clock)),
                    Err(_) => Err("gossip state lock poisoned".to_string()),
                }
            })
            .await;

            match missing {
                Ok(missing) => {
                    let count = missing.len();
                    let msg = WireMessage::SyncResponse { envelopes: missing };
                    if let Err(e) = transport.send_to(&peer_id, &msg).await {
                        metrics
                            .gossip_broadcast_failures_total
                            .fetch_add(1, Ordering::Relaxed);
                        error!(peer_id = %peer_id, error = %e, "gossip sync response error");
                    } else {
                        push_gossip_event(
                            &gossip_events,
                            &metrics,
                            config.max_gossip_events,
                            GossipEvent::Sync {
                                peer_id: peer_for_event,
                                envelope_count: count,
                            },
                        );
                    }
                }
                Err(e) => error!(peer_id = %peer_id, error = %e, "gossip sync diff error"),
            }
        }
        WireMessage::SyncResponse { envelopes } => {
            let count = envelopes.len();
            push_gossip_event(
                &gossip_events,
                &metrics,
                config.max_gossip_events,
                GossipEvent::Sync {
                    peer_id: peer_id.clone(),
                    envelope_count: count,
                },
            );
            for envelope in envelopes {
                if let Err(e) = ingest_envelope_from_peer(
                    envelope,
                    Some(peer_id.clone()),
                    gossip_state.clone(),
                    gossip_events.clone(),
                    metrics.clone(),
                    config.clone(),
                )
                .await
                {
                    error!(peer_id = %peer_id, error = %e, "gossip sync ingest error");
                }
            }
        }
    }
}

async fn ingest_envelope_from_peer(
    envelope: tavla::Envelope,
    via_peer: Option<String>,
    gossip_state: SharedGossip,
    gossip_events: SharedEvents,
    metrics: SharedMetrics,
    config: SharedConfig,
) -> Result<(), String> {
    let author = envelope.author.clone();
    let display_text = envelope_display_text(&envelope);

    run_blocking(move || -> Result<(), String> {
        let result = match gossip_state.lock() {
            Ok(mut node) => node.ingest_from(envelope.clone(), via_peer.as_deref())?,
            Err(_) => return Err("gossip state lock poisoned".to_string()),
        };

        if result.was_duplicate {
            metrics
                .gossip_duplicate_envelopes_total
                .fetch_add(1, Ordering::Relaxed);
            return Ok(());
        }

        if result.was_rejected {
            metrics
                .gossip_rejected_envelopes_total
                .fetch_add(1, Ordering::Relaxed);
            return Ok(());
        }

        metrics
            .gossip_envelopes_ingested_total
            .fetch_add(1, Ordering::Relaxed);

        push_gossip_event(
            &gossip_events,
            &metrics,
            config.max_gossip_events,
            GossipEvent::NewEnvelope {
                envelope_id: envelope.id.clone(),
                author: author.clone(),
                lojban: display_text.clone(),
                stance: format!("{}", envelope.stance),
                topics: envelope.topics.clone(),
                timestamp: envelope.timestamp.clone(),
            },
        );

        if let (Some(id), Some(assertion)) = (result.contradiction, display_text) {
            push_gossip_event(
                &gossip_events,
                &metrics,
                config.max_gossip_events,
                GossipEvent::Contradiction {
                    id,
                    envelope_id: envelope.id.clone(),
                    assertion,
                    author,
                },
            );
        }

        Ok(())
    })
    .await
}

#[cfg(test)]
mod tests {
    use super::*;
    use async_graphql::Request;
    use axum::body::{Body, to_bytes};
    use axum::http::Request as HttpRequest;
    use tavla::TrustPolicy;
    use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
    use tokio::sync::{mpsc, oneshot};
    use tokio::time::{Duration, sleep, timeout};
    use tower::util::ServiceExt;

    type TestSchema = Schema<QueryRoot, MutationRoot, EmptySubscription>;

    struct FakeHub {
        addr: String,
        outbound: mpsc::UnboundedSender<String>,
        inbound: mpsc::UnboundedReceiver<String>,
        handshake: oneshot::Receiver<String>,
        task: tokio::task::JoinHandle<()>,
    }

    fn should_skip_network_test(err: &std::io::Error) -> bool {
        matches!(
            err.kind(),
            std::io::ErrorKind::PermissionDenied | std::io::ErrorKind::AddrNotAvailable
        )
    }

    async fn start_fake_hub() -> Option<FakeHub> {
        let listener = match tokio::net::TcpListener::bind("127.0.0.1:0").await {
            Ok(listener) => listener,
            Err(err) if should_skip_network_test(&err) => {
                eprintln!("[test] skipping network test: {err}");
                return None;
            }
            Err(err) => panic!("fake hub should bind: {err}"),
        };
        let addr = listener
            .local_addr()
            .expect("fake hub should have local addr")
            .to_string();
        let (outbound, mut outbound_rx) = mpsc::unbounded_channel::<String>();
        let (inbound_tx, inbound) = mpsc::unbounded_channel::<String>();
        let (handshake_tx, handshake) = oneshot::channel::<String>();

        let task = tokio::spawn(async move {
            let (stream, _) = listener.accept().await.expect("fake hub should accept");
            let (read_half, mut write_half) = stream.into_split();
            let mut reader = BufReader::new(read_half);
            let mut line = String::new();

            match reader.read_line(&mut line).await {
                Ok(0) | Err(_) => return,
                Ok(_) => {
                    let _ = handshake_tx.send(line.trim().to_string());
                }
            }

            let read_task = tokio::spawn(async move {
                let mut reader = reader;
                let mut line = String::new();
                loop {
                    line.clear();
                    match reader.read_line(&mut line).await {
                        Ok(0) | Err(_) => break,
                        Ok(_) => {
                            let trimmed = line.trim();
                            if !trimmed.is_empty() {
                                let _ = inbound_tx.send(trimmed.to_string());
                            }
                        }
                    }
                }
            });

            while let Some(message) = outbound_rx.recv().await {
                let mut payload = message;
                payload.push('\n');
                if write_half.write_all(payload.as_bytes()).await.is_err() {
                    break;
                }
                if write_half.flush().await.is_err() {
                    break;
                }
            }

            read_task.abort();
        });

        Some(FakeHub {
            addr,
            outbound,
            inbound,
            handshake,
            task,
        })
    }

    fn build_test_schema(
        gossip_state: Arc<Mutex<GossipNode>>,
        gossip_events: Arc<Mutex<Vec<GossipEvent>>>,
        gossip_transport: SharedTransport,
        config: SharedConfig,
        metrics: SharedMetrics,
    ) -> TestSchema {
        let ollama_config = Arc::new(OllamaConfig {
            url: "http://localhost:11434".to_string(),
            model: "test-model".to_string(),
        });

        Schema::build(QueryRoot, MutationRoot, EmptySubscription)
            .data(ollama_config)
            .data(gossip_state)
            .data(gossip_events)
            .data(gossip_transport)
            .data(config)
            .data(metrics)
            .finish()
    }

    fn test_server_config() -> SharedConfig {
        Arc::new(ServerConfig {
            bind_addr: SocketAddr::from(([127, 0, 0, 1], 8081)),
            enable_playground: false,
            require_gossip_peer: false,
            max_request_bytes: 1_048_576,
            max_gossip_events: 16,
            cors_allowed_origins: Vec::new(),
            log_format: LogFormat::Pretty,
            log_filter: "info".to_string(),
        })
    }

    fn build_test_http_state(
        gossip_state: Arc<Mutex<GossipNode>>,
        gossip_events: Arc<Mutex<Vec<GossipEvent>>>,
        gossip_transport: SharedTransport,
        config: SharedConfig,
        metrics: SharedMetrics,
    ) -> HttpState {
        let schema = Arc::new(build_test_schema(
            gossip_state.clone(),
            gossip_events.clone(),
            gossip_transport.clone(),
            config.clone(),
            metrics.clone(),
        ));

        HttpState {
            schema,
            gossip: gossip_state,
            events: gossip_events,
            transport: gossip_transport,
            metrics,
            config,
        }
    }

    async fn start_server_transport(
        hub_addr: &str,
        gossip_state: Arc<Mutex<GossipNode>>,
        gossip_events: Arc<Mutex<Vec<GossipEvent>>>,
        metrics: SharedMetrics,
        config: SharedConfig,
    ) -> (Arc<dyn Transport>, tokio::task::JoinHandle<()>) {
        let transport: Arc<dyn Transport> = TcpTransport::client(hub_addr, "server")
            .await
            .expect("server transport should start");
        let listener_transport = transport.clone();
        let listener_handle = tokio::spawn(async move {
            gossip_transport_listener(
                listener_transport,
                gossip_state,
                gossip_events,
                metrics,
                config,
            )
            .await;
        });
        (transport, listener_handle)
    }

    async fn execute_json(schema: &TestSchema, query: String) -> serde_json::Value {
        let response = schema.execute(Request::new(query)).await;
        assert!(
            response.errors.is_empty(),
            "GraphQL execution should succeed: {:?}",
            response.errors
        );
        response
            .data
            .into_json()
            .expect("response data should convert to json")
    }

    fn gql_string(value: &str) -> String {
        serde_json::to_string(value).expect("gql string should serialize")
    }

    async fn query_holds(schema: &TestSchema, input: &str) -> bool {
        let query = format!(
            "mutation {{ queryText(input: {}) {{ holds error }} }}",
            gql_string(input)
        );
        let json = execute_json(schema, query).await;
        json["queryText"]["holds"].as_bool().unwrap_or(false)
    }

    async fn wait_for_query_result(schema: &TestSchema, input: &str, expected: bool) -> bool {
        for _ in 0..20 {
            if query_holds(schema, input).await == expected {
                return true;
            }
            sleep(Duration::from_millis(25)).await;
        }
        false
    }

    async fn wait_for_event_count(events: &Arc<Mutex<Vec<GossipEvent>>>, expected: usize) -> bool {
        for _ in 0..20 {
            if events.lock().unwrap().len() == expected {
                return true;
            }
            sleep(Duration::from_millis(25)).await;
        }
        false
    }

    #[tokio::test]
    async fn gossip_assert_should_affect_query_results() {
        let gossip_state = Arc::new(Mutex::new(GossipNode::new("server")));
        let gossip_events = Arc::new(Mutex::new(Vec::new()));
        let config = test_server_config();
        let metrics = Arc::new(ServerMetrics::default());
        let schema = build_test_schema(gossip_state, gossip_events, None, config, metrics);

        let mutation = format!(
            "mutation {{ gossipAssert(lojban: {}) {{ envelopeId error }} }}",
            gql_string("la .adam. cu gerku")
        );
        let json = execute_json(&schema, mutation).await;
        assert!(
            json["gossipAssert"]["error"].is_null(),
            "gossipAssert should succeed"
        );

        assert!(
            wait_for_query_result(&schema, "la .adam. cu gerku", true).await,
            "gossipAssert should make the asserted fact queryable through queryText"
        );
    }

    #[tokio::test]
    async fn remote_retraction_should_remove_query_results() {
        let gossip_state = Arc::new(Mutex::new(GossipNode::new("server")));
        let gossip_events = Arc::new(Mutex::new(Vec::new()));
        let config = test_server_config();
        let metrics = Arc::new(ServerMetrics::default());
        let Some(hub) = start_fake_hub().await else {
            return;
        };
        let (transport, listener_handle) = start_server_transport(
            &hub.addr,
            gossip_state.clone(),
            gossip_events.clone(),
            metrics.clone(),
            config.clone(),
        )
        .await;
        let schema = build_test_schema(
            gossip_state.clone(),
            gossip_events.clone(),
            Some(transport.clone()),
            config,
            metrics,
        );

        let handshake = timeout(Duration::from_secs(1), hub.handshake)
            .await
            .expect("server should handshake with fake hub")
            .expect("handshake should arrive");
        assert_eq!(handshake, "server");

        let mut remote = GossipNode::new("bob");
        let asserted = remote
            .assert_local("la .adam. cu gerku")
            .expect("remote assert should succeed");
        let tombstone = remote
            .retract_local(&asserted.id)
            .expect("remote retract should succeed");

        hub.outbound
            .send(
                serde_json::to_string(&WireMessage::Envelope(asserted))
                    .expect("assert envelope should serialize"),
            )
            .expect("hub should send assert envelope");

        assert!(
            wait_for_query_result(&schema, "la .adam. cu gerku", true).await,
            "remote assertion should become queryable"
        );

        hub.outbound
            .send(
                serde_json::to_string(&WireMessage::Envelope(tombstone))
                    .expect("tombstone should serialize"),
            )
            .expect("hub should send tombstone");

        assert!(
            wait_for_query_result(&schema, "la .adam. cu gerku", false).await,
            "remote retraction should remove the fact from queryText results"
        );

        transport.shutdown().await;
        listener_handle.abort();
        hub.task.abort();
    }

    #[tokio::test]
    async fn gossip_assert_should_broadcast_to_connected_hub() {
        let gossip_state = Arc::new(Mutex::new(GossipNode::new("server")));
        let gossip_events = Arc::new(Mutex::new(Vec::new()));
        let config = test_server_config();
        let metrics = Arc::new(ServerMetrics::default());
        let Some(mut hub) = start_fake_hub().await else {
            return;
        };
        let (transport, listener_handle) = start_server_transport(
            &hub.addr,
            gossip_state.clone(),
            gossip_events.clone(),
            metrics.clone(),
            config.clone(),
        )
        .await;
        let schema = build_test_schema(
            gossip_state.clone(),
            gossip_events.clone(),
            Some(transport.clone()),
            config,
            metrics,
        );

        let handshake = timeout(Duration::from_secs(1), hub.handshake)
            .await
            .expect("server should handshake with fake hub")
            .expect("handshake should arrive");
        assert_eq!(handshake, "server");

        let mutation = format!(
            "mutation {{ gossipAssert(lojban: {}) {{ envelopeId error }} }}",
            gql_string("la .adam. cu gerku")
        );
        let json = execute_json(&schema, mutation).await;
        assert!(
            json["gossipAssert"]["error"].is_null(),
            "gossipAssert should succeed"
        );

        let broadcast = timeout(Duration::from_millis(500), hub.inbound.recv())
            .await
            .expect("connected hub should receive a broadcast after gossipAssert")
            .expect("hub should receive an outbound message");
        let message: WireMessage =
            serde_json::from_str(&broadcast).expect("broadcast should be a valid wire message");
        assert!(
            matches!(message, WireMessage::Envelope(_)),
            "gossipAssert should broadcast an envelope"
        );

        transport.shutdown().await;
        listener_handle.abort();
        hub.task.abort();
    }

    #[tokio::test]
    async fn gossip_retract_should_broadcast_tombstone_to_connected_hub() {
        let gossip_state = Arc::new(Mutex::new(GossipNode::new("server")));
        let gossip_events = Arc::new(Mutex::new(Vec::new()));
        let config = test_server_config();
        let metrics = Arc::new(ServerMetrics::default());
        let Some(mut hub) = start_fake_hub().await else {
            return;
        };
        let (transport, listener_handle) = start_server_transport(
            &hub.addr,
            gossip_state.clone(),
            gossip_events.clone(),
            metrics.clone(),
            config.clone(),
        )
        .await;
        let schema = build_test_schema(
            gossip_state.clone(),
            gossip_events.clone(),
            Some(transport.clone()),
            config,
            metrics,
        );

        let handshake = timeout(Duration::from_secs(1), hub.handshake)
            .await
            .expect("server should handshake with fake hub")
            .expect("handshake should arrive");
        assert_eq!(handshake, "server");

        let assert_mutation = format!(
            "mutation {{ gossipAssert(lojban: {}) {{ envelopeId error }} }}",
            gql_string("la .adam. cu gerku")
        );
        let asserted_json = execute_json(&schema, assert_mutation).await;
        let asserted_id = asserted_json["gossipAssert"]["envelopeId"]
            .as_str()
            .expect("assert should return envelope id")
            .to_string();

        let _first_broadcast = timeout(Duration::from_millis(500), hub.inbound.recv())
            .await
            .expect("hub should receive asserted envelope")
            .expect("hub should receive outbound assertion");

        let retract_mutation = format!(
            "mutation {{ gossipRetract(envelopeId: {}) {{ envelopeId error }} }}",
            gql_string(&asserted_id)
        );
        let retract_json = execute_json(&schema, retract_mutation).await;
        assert!(
            retract_json["gossipRetract"]["error"].is_null(),
            "gossipRetract should succeed"
        );

        let tombstone_broadcast = timeout(Duration::from_millis(500), hub.inbound.recv())
            .await
            .expect("hub should receive tombstone after gossipRetract")
            .expect("hub should receive outbound tombstone");
        let message: WireMessage = serde_json::from_str(&tombstone_broadcast)
            .expect("tombstone broadcast should be a valid wire message");
        assert!(
            matches!(
                message,
                WireMessage::Envelope(tavla::Envelope {
                    op: GossipOp::Retract(ref target_id),
                    ..
                }) if target_id == &asserted_id
            ),
            "gossipRetract should broadcast a tombstone targeting the asserted envelope"
        );
        assert!(
            wait_for_query_result(&schema, "la .adam. cu gerku", false).await,
            "local gossip retraction should remove the fact from query results"
        );

        transport.shutdown().await;
        listener_handle.abort();
        hub.task.abort();
    }

    #[tokio::test]
    async fn duplicate_inbound_envelope_should_not_create_duplicate_events() {
        let gossip_state = Arc::new(Mutex::new(GossipNode::new("server")));
        let gossip_events = Arc::new(Mutex::new(Vec::new()));
        let config = test_server_config();
        let metrics = Arc::new(ServerMetrics::default());
        let Some(hub) = start_fake_hub().await else {
            return;
        };
        let (transport, listener_handle) = start_server_transport(
            &hub.addr,
            gossip_state.clone(),
            gossip_events.clone(),
            metrics.clone(),
            config.clone(),
        )
        .await;
        let schema = build_test_schema(
            gossip_state.clone(),
            gossip_events.clone(),
            Some(transport.clone()),
            config,
            metrics,
        );

        let handshake = timeout(Duration::from_secs(1), hub.handshake)
            .await
            .expect("server should handshake with fake hub")
            .expect("handshake should arrive");
        assert_eq!(handshake, "server");

        let mut remote = GossipNode::new("bob");
        let asserted = remote
            .assert_local("la .adam. cu gerku")
            .expect("remote assert should succeed");
        let payload = serde_json::to_string(&WireMessage::Envelope(asserted))
            .expect("assert envelope should serialize");

        hub.outbound
            .send(payload.clone())
            .expect("hub should send first copy");
        assert!(
            wait_for_event_count(&gossip_events, 1).await,
            "first inbound envelope should produce one server event"
        );

        hub.outbound
            .send(payload)
            .expect("hub should send duplicate");
        sleep(Duration::from_millis(100)).await;

        assert_eq!(
            gossip_events.lock().unwrap().len(),
            1,
            "duplicate inbound envelopes should not be logged as fresh events"
        );
        assert!(
            wait_for_query_result(&schema, "la .adam. cu gerku", true).await,
            "deduplicated inbound assertion should still be queryable"
        );

        transport.shutdown().await;
        listener_handle.abort();
        hub.task.abort();
    }

    #[tokio::test]
    async fn rejected_inbound_envelope_should_not_create_server_events() {
        let gossip_state = Arc::new(Mutex::new(GossipNode::with_policy(
            "server",
            TrustPolicy::TrustRequired,
        )));
        let gossip_events = Arc::new(Mutex::new(Vec::new()));
        let config = test_server_config();
        let metrics = Arc::new(ServerMetrics::default());
        let Some(hub) = start_fake_hub().await else {
            return;
        };
        let (transport, listener_handle) = start_server_transport(
            &hub.addr,
            gossip_state.clone(),
            gossip_events.clone(),
            metrics.clone(),
            config.clone(),
        )
        .await;
        let schema = build_test_schema(
            gossip_state.clone(),
            gossip_events.clone(),
            Some(transport.clone()),
            config,
            metrics,
        );

        let handshake = timeout(Duration::from_secs(1), hub.handshake)
            .await
            .expect("server should handshake with fake hub")
            .expect("handshake should arrive");
        assert_eq!(handshake, "server");

        let mut remote = GossipNode::new("bob");
        let asserted = remote
            .assert_local("la .adam. cu gerku")
            .expect("remote assert should succeed");
        hub.outbound
            .send(
                serde_json::to_string(&WireMessage::Envelope(asserted))
                    .expect("assert envelope should serialize"),
            )
            .expect("hub should send assert envelope");

        sleep(Duration::from_millis(100)).await;

        assert_eq!(
            gossip_events.lock().unwrap().len(),
            0,
            "rejected inbound envelopes should not be logged as accepted server events"
        );
        assert!(
            wait_for_query_result(&schema, "la .adam. cu gerku", false).await,
            "rejected inbound assertions must stay out of query results"
        );

        transport.shutdown().await;
        listener_handle.abort();
        hub.task.abort();
    }

    #[test]
    fn gossip_event_buffer_should_be_bounded() {
        let events = Arc::new(Mutex::new(Vec::new()));
        let metrics = Arc::new(ServerMetrics::default());

        for idx in 0..5 {
            push_gossip_event(
                &events,
                &metrics,
                3,
                GossipEvent::Sync {
                    peer_id: format!("peer-{idx}"),
                    envelope_count: idx,
                },
            );
        }

        let events = events.lock().unwrap();
        assert_eq!(events.len(), 3, "event buffer should keep only the newest items");
        match &events[0] {
            GossipEvent::Sync { peer_id, .. } => assert_eq!(peer_id, "peer-2"),
            other => panic!("expected sync event, got {other:?}"),
        }
        assert_eq!(metrics.gossip_events_total.load(Ordering::Relaxed), 5);
        assert_eq!(
            metrics.gossip_events_dropped_total.load(Ordering::Relaxed),
            2
        );
    }

    #[test]
    fn readiness_should_require_a_peer_when_config_demands_it() {
        let gossip_state = Arc::new(Mutex::new(GossipNode::new("server")));
        let gossip_events = Arc::new(Mutex::new(Vec::new()));
        let mut config = ServerConfig {
            bind_addr: SocketAddr::from(([127, 0, 0, 1], 8081)),
            enable_playground: false,
            require_gossip_peer: true,
            max_request_bytes: 1_048_576,
            max_gossip_events: 16,
            cors_allowed_origins: Vec::new(),
            log_format: LogFormat::Pretty,
            log_filter: "info".to_string(),
        };

        let readiness = readiness_snapshot(&gossip_state, &gossip_events, &None, &config);
        assert!(!readiness.ready, "readiness should fail without a required gossip peer");

        config.require_gossip_peer = false;
        let readiness = readiness_snapshot(&gossip_state, &gossip_events, &None, &config);
        assert!(readiness.ready, "readiness should pass when gossip peers are optional");
    }

    #[tokio::test]
    async fn health_ready_and_metrics_endpoints_should_reflect_server_state() {
        let gossip_state = Arc::new(Mutex::new(GossipNode::new("server")));
        let gossip_events = Arc::new(Mutex::new(Vec::new()));
        let mut config = Arc::unwrap_or_clone(test_server_config());
        config.require_gossip_peer = true;
        config.max_gossip_events = 8;
        let config = Arc::new(config);
        let metrics = Arc::new(ServerMetrics::default());
        let state = build_test_http_state(
            gossip_state,
            gossip_events,
            None,
            config.clone(),
            metrics.clone(),
        );
        let app = build_app(state);

        let health = app
            .clone()
            .oneshot(
                HttpRequest::builder()
                    .uri("/healthz")
                    .body(Body::empty())
                    .expect("health request should build"),
            )
            .await
            .expect("health endpoint should respond");
        assert_eq!(health.status(), StatusCode::OK);

        let ready = app
            .clone()
            .oneshot(
                HttpRequest::builder()
                    .uri("/readyz")
                    .body(Body::empty())
                    .expect("ready request should build"),
            )
            .await
            .expect("ready endpoint should respond");
        assert_eq!(ready.status(), StatusCode::SERVICE_UNAVAILABLE);
        let ready_body = to_bytes(ready.into_body(), usize::MAX)
            .await
            .expect("ready body should read");
        let ready_json: serde_json::Value =
            serde_json::from_slice(&ready_body).expect("ready body should be valid json");
        assert_eq!(ready_json["ready"], false);
        assert_eq!(ready_json["require_gossip_peer"], true);
        assert_eq!(ready_json["max_event_buffer_len"], 8);

        let metrics_response = app
            .oneshot(
                HttpRequest::builder()
                    .uri("/metrics")
                    .body(Body::empty())
                    .expect("metrics request should build"),
            )
            .await
            .expect("metrics endpoint should respond");
        assert_eq!(metrics_response.status(), StatusCode::OK);
        let metrics_body = to_bytes(metrics_response.into_body(), usize::MAX)
            .await
            .expect("metrics body should read");
        let metrics_text =
            String::from_utf8(metrics_body.to_vec()).expect("metrics should be valid utf8");
        assert!(
            metrics_text.contains("nibli_health_requests_total 1"),
            "metrics should expose health counter"
        );
        assert!(
            metrics_text.contains("nibli_readiness_requests_total 1"),
            "metrics should expose readiness counter"
        );
        assert!(
            metrics_text.contains("nibli_metrics_requests_total 1"),
            "metrics should expose metrics counter"
        );
        assert!(
            metrics_text.contains("nibli_ready 0"),
            "metrics should expose readiness gauge"
        );
    }
}
