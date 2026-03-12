use std::sync::{Arc, Mutex};

use anyhow::Result;
use async_graphql::{EmptySubscription, Object, Schema};
use async_graphql_axum::GraphQL;
use axum::Router;
use tower_http::cors::CorsLayer;

use nibli_engine::NibliEngine;

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
        match engine.query_text(&input) {
            Ok(holds) => QueryResult {
                holds: Some(holds),
                error: None,
            },
            Err(e) => QueryResult {
                holds: None,
                error: Some(e),
            },
        }
    }

    async fn query_text_with_proof(
        &self,
        ctx: &async_graphql::Context<'_>,
        input: String,
    ) -> ProofQueryResult {
        let engine = ctx.data::<Arc<Mutex<NibliEngine>>>().unwrap();
        let engine = engine.lock().unwrap();
        match engine.query_text_with_proof(&input) {
            Ok((holds, trace)) => ProofQueryResult {
                holds: Some(holds),
                proof_trace: Some(trace),
                error: None,
            },
            Err(e) => ProofQueryResult {
                holds: None,
                proof_trace: None,
                error: Some(e),
            },
        }
    }
}

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
struct QueryResult {
    holds: Option<bool>,
    error: Option<String>,
}

#[derive(async_graphql::SimpleObject)]
struct ProofQueryResult {
    holds: Option<bool>,
    proof_trace: Option<String>,
    error: Option<String>,
}

// ── Main ──

#[tokio::main]
async fn main() -> Result<()> {
    println!("Nibli GraphQL Server starting...");

    let engine_state = Arc::new(Mutex::new(NibliEngine::new()));

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
