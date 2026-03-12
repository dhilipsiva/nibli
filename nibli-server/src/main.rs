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
    /// Placeholder — will be extended in Step 4
    async fn ping(&self) -> bool {
        true
    }
}

#[derive(async_graphql::SimpleObject)]
struct StatusResult {
    ready: bool,
}

// ── Main ──

#[tokio::main]
async fn main() -> Result<()> {
    println!("Nibli GraphQL Server starting...");

    let engine_state = Arc::new(Mutex::new(NibliEngine::new()?));

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
