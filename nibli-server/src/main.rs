use std::sync::{Arc, Mutex};

use anyhow::Result;
use async_graphql::{EmptySubscription, Object, Schema};
use async_graphql_axum::GraphQL;
use axum::Router;
use tower_http::cors::CorsLayer;

use nibli_engine::NibliEngine;

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

struct MutationRoot;

#[Object]
impl MutationRoot {
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

    let schema = Schema::build(QueryRoot, MutationRoot, EmptySubscription)
        .data(engine_state)
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
