use std::collections::HashMap;
use std::io::Write;

use chrono::Utc;
use clap::{Parser, ValueEnum};
use rig::agent::Agent;
use rig::completion::Prompt;
use rig::prelude::*;
use rig::providers::{anthropic, ollama};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::net::TcpStream;
use tokio::sync::mpsc;

use nibli_engine::NibliEngine;
use tavla::{Envelope, EpistemicStance, GossipOp, VectorClock, WireMessage};

// ── Constants ──

const MAX_RETRIES: usize = 3;

const TRANSLATE_PROMPT: &str = r#"You are a Lojban translator. Translate the English sentence to grammatically correct Lojban. Output ONLY the Lojban sentence on a single line, nothing else. No markdown, no code fences, no explanations.

Rules:
- Use ONLY real Lojban gismu (5-letter root words) and cmavo (structure words). Do NOT invent words.
- Use standard Lojban grammar: [sumti] selbri [sumti] structure
- Use gadri: "lo" for descriptions, "la" for names
- Wrap names in dots as cmevla: "Adam" → ".adam."
- Use "cu" to separate sumti from selbri when needed
- Use tense markers: "pu" (past), "ca" (present), "ba" (future)
- For "every X", use "ro lo <gismu>" (e.g., "ro lo prenu"). Do NOT use "ro da" or bare "da".
- Do NOT use "lo nu" abstractions — keep it to simple predications.
- Keep sentences simple — one predicate per sentence

Common gismu: gerku (dog), mlatu (cat), prami (love), klama (go), citka (eat), viska (see), bajra (run), barda (big), xadni (body), tsali (strong), kanro (healthy), cidja (food), pinxe (drink), tatpi (tired), cortu (pain), bilma (ill), xamgu (good), xlali (bad), sutra (fast), masno (slow), zukte (act), troci (try), djica (desire), kakne (able)

Examples:
- "The dog goes to the market" → lo gerku cu klama lo zarci
- "I love you" → mi prami do
- "Adam sees the cat" → la .adam. viska lo mlatu
- "The big dog runs" → lo barda gerku cu bajra
- "I ate the food" → mi pu citka lo cidja
- "The athlete is strong" → lo prenu cu tsali
- "Every dog is an animal" → ro lo gerku cu danlu
- "Adam is healthy" → la .adam. cu kanro
- "The person exercises daily" → lo prenu cu bajra
- "The strong person runs fast" → lo tsali prenu cu sutra bajra
- "Food makes you healthy" → lo cidja cu xamgu

/no_think"#;

const GENERATE_PROMPT: &str = r#"Generate a single factual English sentence about the given topic. Keep it simple, declarative, and suitable for formal logic representation. Output ONLY the sentence, nothing else.

Examples for topic "fitness":
- "Regular exercise strengthens the heart"
- "Athletes need adequate protein"
- "Swimming is a low-impact exercise"

/no_think"#;

/// Domain topic tags for gossip envelopes.
fn domain_topics(domain: &str) -> Vec<String> {
    match domain {
        "xadni" => vec!["xadni", "kamni", "tsali"],
        "cidja" => vec!["cidja", "citka", "xagji"],
        "kelci" => vec!["kelci", "skami", "srana"],
        "krali" => vec!["krali", "turni", "flalu"],
        "gerku" => vec!["gerku", "danlu", "mabru"],
        "skami" => vec!["skami", "datni", "ciste"],
        _ => vec![],
    }
    .into_iter()
    .map(String::from)
    .collect()
}

// ── CLI ──

#[derive(Clone, ValueEnum)]
enum Provider {
    Anthropic,
    Ollama,
}

#[derive(Clone, ValueEnum)]
enum Stance {
    Deduced,
    Expected,
    Opinion,
    Hearsay,
}

impl From<Stance> for EpistemicStance {
    fn from(s: Stance) -> Self {
        match s {
            Stance::Deduced => EpistemicStance::Deduced,
            Stance::Expected => EpistemicStance::Expected,
            Stance::Opinion => EpistemicStance::Opinion,
            Stance::Hearsay => EpistemicStance::Hearsay,
        }
    }
}

#[derive(Parser)]
#[command(name = "nibli-agent", about = "LLM gossip agent for nibli")]
struct Cli {
    /// Agent name on the network.
    #[arg(long)]
    name: String,

    /// Tavla gossip hub address.
    #[arg(long, default_value = "127.0.0.1:7001")]
    peer: String,

    /// LLM provider.
    #[arg(long, value_enum, default_value = "anthropic")]
    provider: Provider,

    /// Model name override.
    #[arg(long)]
    model: Option<String>,

    /// Ollama server URL.
    #[arg(long, default_value = "http://localhost:11434")]
    ollama_url: String,

    /// Domain specialisation (xadni, cidja, kelci, krali, gerku, skami).
    #[arg(long)]
    domain: Option<String>,

    /// Epistemic stance for assertions.
    #[arg(long, value_enum, default_value = "deduced")]
    stance: Stance,

    /// Enable auto-gossip mode.
    #[arg(long)]
    auto_gossip: bool,

    /// Topic for auto-gossip sentence generation.
    #[arg(long)]
    topic: Option<String>,

    /// Seconds between auto-gossip assertions.
    #[arg(long, default_value = "30")]
    interval: u64,

    /// Max number of auto-gossip assertions (unlimited if unset).
    #[arg(long)]
    count: Option<u32>,
}

// ── LLM abstraction ──

type AnthropicAgent = Agent<anthropic::completion::CompletionModel>;
type OllamaAgent = Agent<ollama::CompletionModel>;

enum LlmClient {
    Anthropic {
        translator: AnthropicAgent,
        generator: AnthropicAgent,
    },
    Ollama {
        translator: OllamaAgent,
        generator: OllamaAgent,
    },
}

impl LlmClient {
    fn new_anthropic(model: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let client = anthropic::Client::new(
            std::env::var("ANTHROPIC_API_KEY")
                .expect("ANTHROPIC_API_KEY must be set"),
        )?;

        let translator = client
            .agent(model)
            .preamble(TRANSLATE_PROMPT)
            .temperature(0.0)
            .max_tokens(256)
            .build();

        let generator = client
            .agent(model)
            .preamble(GENERATE_PROMPT)
            .temperature(0.9)
            .max_tokens(256)
            .build();

        Ok(LlmClient::Anthropic { translator, generator })
    }

    fn new_ollama(url: &str, model: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let client = ollama::Client::builder()
            .api_key(rig::client::Nothing)
            .base_url(url)
            .build()?;

        let translator = client
            .agent(model)
            .preamble(TRANSLATE_PROMPT)
            .temperature(0.0)
            .max_tokens(256)
            .build();

        let generator = client
            .agent(model)
            .preamble(GENERATE_PROMPT)
            .temperature(0.9)
            .max_tokens(256)
            .build();

        Ok(LlmClient::Ollama { translator, generator })
    }

    async fn translate(&self, english: &str) -> Result<String, String> {
        let result = match self {
            LlmClient::Anthropic { translator, .. } => translator.prompt(english).await,
            LlmClient::Ollama { translator, .. } => translator.prompt(english).await,
        };
        result.map(|s| clean_llm_output(s.trim())).map_err(|e| e.to_string())
    }

    async fn generate(&self, topic: &str) -> Result<String, String> {
        let prompt = format!("Topic: {topic}");
        let result = match self {
            LlmClient::Anthropic { generator, .. } => generator.prompt(&prompt).await,
            LlmClient::Ollama { generator, .. } => generator.prompt(&prompt).await,
        };
        result.map(|s| clean_llm_output(s.trim())).map_err(|e| e.to_string())
    }
}

/// Strip thinking blocks, markdown code fences, and extra whitespace from LLM output.
fn clean_llm_output(s: &str) -> String {
    let s = s.trim();
    // Strip <think>...</think> blocks (qwen3 thinking mode).
    let s = if let Some(after) = s.split("</think>").last() {
        after.trim()
    } else {
        s
    };
    // Strip ```lojban ... ``` or ``` ... ``` fences.
    let s = if s.starts_with("```") {
        let inner = s.trim_start_matches("```");
        // Skip optional language tag on first line.
        let inner = if let Some(rest) = inner.strip_prefix("lojban") {
            rest
        } else {
            inner
        };
        inner.trim_start_matches('\n')
            .trim_end_matches("```")
            .trim()
    } else {
        s
    };
    // Take only the first line (LLMs sometimes add explanations).
    s.lines().next().unwrap_or(s).trim().to_string()
}

// ── Validation ──

fn validate_lojban(engine: &NibliEngine, text: &str) -> Result<(), String> {
    engine.validate(text)
}

// ── Envelope construction ──

fn build_envelope(
    agent_name: &str,
    clock: &mut VectorClock,
    lojban: &str,
    stance: EpistemicStance,
    extra_topics: &[String],
) -> Envelope {
    clock.tick(agent_name);

    let mut topics = tavla::extract_topics(lojban);
    for t in extra_topics {
        if !topics.contains(t) {
            topics.push(t.clone());
        }
    }

    let timestamp = Utc::now().to_rfc3339();
    let op = GossipOp::AssertLojban(lojban.to_string());

    let id = Envelope::compute_id(agent_name, clock, &op, &stance, &topics, &timestamp);

    Envelope {
        id,
        author: agent_name.to_string(),
        clock: clock.clone(),
        op,
        stance,
        topics,
        timestamp,
        sig: Vec::new(),
        quarantined: false,
    }
}

// ── Translate → validate → gossip pipeline ──

async fn translate_validate_gossip(
    llm: &LlmClient,
    engine: &NibliEngine,
    english: &str,
    agent_name: &str,
    clock: &mut VectorClock,
    stance: EpistemicStance,
    extra_topics: &[String],
) -> Option<Envelope> {
    let mut last_error = String::new();
    for attempt in 1..=MAX_RETRIES {
        // On retry, prepend the error feedback so the LLM can correct.
        let prompt = if attempt == 1 {
            english.to_string()
        } else {
            format!("Previous attempt was rejected: {last_error}\nPlease fix and translate again: {english}")
        };
        match llm.translate(&prompt).await {
            Ok(candidate) => {
                println!("[{agent_name}] Candidate ({attempt}/{MAX_RETRIES}): \"{candidate}\"");
                match validate_lojban(engine, &candidate) {
                    Ok(()) => {
                        println!("[{agent_name}] Validated (gerna pass)");
                        let envelope = build_envelope(agent_name, clock, &candidate, stance.clone(), extra_topics);
                        return Some(envelope);
                    }
                    Err(e) => {
                        println!("[{agent_name}] Rejected by gerna (attempt {attempt}): {e}");
                        last_error = e;
                    }
                }
            }
            Err(e) => {
                eprintln!("[{agent_name}] Translation error: {e}");
                last_error = e;
            }
        }
    }
    println!("[{agent_name}] Failed after {MAX_RETRIES} attempts");
    None
}

// ── TCP gossip connection ──

struct GossipConnection {
    writer: tokio::net::tcp::OwnedWriteHalf,
}

impl GossipConnection {
    async fn connect(
        name: &str,
        addr: &str,
        inbound_tx: mpsc::UnboundedSender<WireMessage>,
    ) -> Result<Self, String> {
        let mut stream = TcpStream::connect(addr)
            .await
            .map_err(|e| format!("connect to {addr}: {e}"))?;

        // Handshake: send agent name as first line.
        let hello = format!("{name}\n");
        stream
            .write_all(hello.as_bytes())
            .await
            .map_err(|e| format!("handshake: {e}"))?;

        let (read_half, write_half) = stream.into_split();

        // Spawn reader task.
        tokio::spawn(async move {
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
                            Ok(msg) => {
                                let _ = inbound_tx.send(msg);
                            }
                            Err(e) => {
                                eprintln!("[gossip] Bad JSON from hub: {e}");
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("[gossip] Read error: {e}");
                        break;
                    }
                }
            }
        });

        Ok(GossipConnection { writer: write_half })
    }

    async fn send_envelope(&mut self, env: &Envelope) -> Result<(), String> {
        let msg = WireMessage::Envelope(env.clone());
        let mut bytes = serde_json::to_vec(&msg).map_err(|e| format!("serialize: {e}"))?;
        bytes.push(b'\n');
        self.writer
            .write_all(&bytes)
            .await
            .map_err(|e| format!("write: {e}"))?;
        self.writer.flush().await.map_err(|e| format!("flush: {e}"))?;
        Ok(())
    }
}

// ── Display inbound messages ──

fn display_inbound(agent_name: &str, msg: &WireMessage) {
    match msg {
        WireMessage::Envelope(env) => {
            let stance_str = format!("{}", env.stance);
            match &env.op {
                GossipOp::AssertLojban(text) => {
                    println!("[{agent_name}] Received from {} [{stance_str}]: {text}", env.author);
                }
                GossipOp::AssertDirect { relation, args } => {
                    println!(
                        "[{agent_name}] Received from {} [{stance_str}]: {}({})",
                        env.author,
                        relation,
                        args.join(", ")
                    );
                }
                GossipOp::Retract(id) => {
                    println!("[{agent_name}] Received retraction from {}: {id}", env.author);
                }
            }
        }
        WireMessage::SyncResponse { envelopes } => {
            println!("[{agent_name}] Sync: received {} envelope(s)", envelopes.len());
        }
        WireMessage::SyncRequest { .. } => {}
    }
}

// ── Main ──

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    println!("[{}] Starting nibli gossip agent", cli.name);
    println!("[{}] Provider: {}", cli.name, match cli.provider {
        Provider::Anthropic => "anthropic",
        Provider::Ollama => "ollama",
    });

    // Create LLM client.
    let llm = match &cli.provider {
        Provider::Anthropic => {
            let model = cli.model.as_deref()
                .unwrap_or(anthropic::completion::CLAUDE_4_SONNET);
            println!("[{}] Model: {model}", cli.name);
            LlmClient::new_anthropic(model)?
        }
        Provider::Ollama => {
            let model = cli.model.as_deref().unwrap_or("qwen3-coder:30b");
            println!("[{}] Model: {model} ({})", cli.name, cli.ollama_url);
            LlmClient::new_ollama(&cli.ollama_url, model)?
        }
    };

    // Create validation engine.
    let engine = NibliEngine::new();
    println!("[{}] Gerna validation engine ready", cli.name);

    // Vector clock.
    let mut clock = VectorClock { entries: HashMap::new() };

    // Extra topics from domain.
    let extra_topics = cli.domain.as_deref().map(domain_topics).unwrap_or_default();

    // Epistemic stance.
    let stance: EpistemicStance = cli.stance.clone().into();

    // Connect to gossip hub.
    let (inbound_tx, mut inbound_rx) = mpsc::unbounded_channel();
    let mut conn = GossipConnection::connect(&cli.name, &cli.peer, inbound_tx).await?;
    println!("[{}] Connected to gossip hub at {}", cli.name, cli.peer);

    // Stats.
    let mut gossiped: u32 = 0;
    let mut failed: u32 = 0;

    if cli.auto_gossip {
        // ── Auto-gossip mode ──
        let topic = cli.topic.as_deref()
            .or(cli.domain.as_deref())
            .unwrap_or("general knowledge");
        println!("[{}] Auto-gossip mode: topic=\"{topic}\", interval={}s", cli.name, cli.interval);

        let mut generated: u32 = 0;
        let mut interval = tokio::time::interval(std::time::Duration::from_secs(cli.interval));
        interval.tick().await; // First tick is immediate.

        loop {
            tokio::select! {
                _ = interval.tick() => {
                    if let Some(max) = cli.count {
                        if generated >= max {
                            println!("[{}] Reached count limit ({max})", cli.name);
                            break;
                        }
                    }

                    match llm.generate(topic).await {
                        Ok(english) => {
                            println!("[{}] Generated: \"{english}\"", cli.name);
                            match translate_validate_gossip(
                                &llm, &engine, &english, &cli.name,
                                &mut clock, stance.clone(), &extra_topics,
                            ).await {
                                Some(env) => {
                                    let short_id = &env.id[..12];
                                    if let Err(e) = conn.send_envelope(&env).await {
                                        eprintln!("[{}] Send failed: {e}", cli.name);
                                    } else {
                                        println!("[{}] Gossiped (envelope {short_id}...)", cli.name);
                                        gossiped += 1;
                                    }
                                }
                                None => { failed += 1; }
                            }
                            generated += 1;
                        }
                        Err(e) => {
                            eprintln!("[{}] Generation error: {e}", cli.name);
                        }
                    }
                }
                Some(msg) = inbound_rx.recv() => {
                    display_inbound(&cli.name, &msg);
                }
            }
        }
    } else {
        // ── Interactive mode ──
        let (stdin_tx, mut stdin_rx) = mpsc::unbounded_channel::<String>();

        // Spawn blocking stdin reader.
        let agent_name = cli.name.clone();
        std::thread::spawn(move || {
            let stdin = std::io::stdin();
            loop {
                print!("{agent_name}> ");
                let _ = std::io::stdout().flush();
                let mut line = String::new();
                match stdin.read_line(&mut line) {
                    Ok(0) => break,
                    Ok(_) => {
                        let _ = stdin_tx.send(line.trim().to_string());
                    }
                    Err(_) => break,
                }
            }
        });

        loop {
            tokio::select! {
                Some(line) = stdin_rx.recv() => {
                    if line.is_empty() {
                        continue;
                    }
                    match line.as_str() {
                        ":quit" | ":exit" => {
                            println!("[{}] co'o (goodbye)", cli.name);
                            break;
                        }
                        ":status" => {
                            println!("  Gossiped: {gossiped}, Failed: {failed}");
                            println!("  Clock: {:?}", clock.entries);
                        }
                        english => {
                            println!("[{}] Translating: \"{english}\"", cli.name);
                            match translate_validate_gossip(
                                &llm, &engine, english, &cli.name,
                                &mut clock, stance.clone(), &extra_topics,
                            ).await {
                                Some(env) => {
                                    let short_id = &env.id[..12];
                                    if let Err(e) = conn.send_envelope(&env).await {
                                        eprintln!("[{}] Send failed: {e}", cli.name);
                                    } else {
                                        println!("[{}] Gossiped (envelope {short_id}...)", cli.name);
                                        gossiped += 1;
                                    }
                                }
                                None => { failed += 1; }
                            }
                            print!("{}> ", cli.name);
                            let _ = std::io::stdout().flush();
                        }
                    }
                }
                Some(msg) = inbound_rx.recv() => {
                    display_inbound(&cli.name, &msg);
                }
            }
        }
    }

    println!("[{}] Final stats: Gossiped={gossiped}, Failed={failed}", cli.name);
    Ok(())
}
