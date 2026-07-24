//! Minimal axum demo for `nibli-auth`.
//!
//! Concurrency: each worker thread warms a thread-local authorizer (KB is
//! `!Send`). App "database" facts are passed per request as `context_kr`.
//!
//! Run: `cargo run -p auth-axum`
//!
//! Examples:
//!   curl -H 'X-Agent: Alice' http://127.0.0.1:3001/docs/Doc1
//!   curl -X PUT -H 'X-Agent: Bob' http://127.0.0.1:3001/docs/Doc1
//!   curl -X PUT -H 'X-Agent: Carol' http://127.0.0.1:3001/docs/Doc1

use std::collections::HashMap;
use std::sync::Arc;

use axum::extract::{Path, Query, State};
use axum::routing::get;
use axum::{Json, Router};
use nibli_auth::axum_ext::{field_mask, require, Agent, AuthRejection};
use nibli_auth::tls;
use serde::{Deserialize, Serialize};
use tower_http::trace::TraceLayer;

/// Simulated application DB: agent → KR context facts for that principal.
#[derive(Clone, Default)]
struct AppDb {
    /// Prebuilt context KR snippets keyed by agent name.
    by_agent: HashMap<String, String>,
}

impl AppDb {
    fn demo() -> Self {
        let mut by_agent = HashMap::new();
        by_agent.insert("Alice".into(), "owns(Alice, Doc1).".into());
        by_agent.insert(
            "Carol".into(),
            "has_role(Carol, \"admin\").\nresource(Doc1).".into(),
        );
        by_agent.insert(
            "Dave".into(),
            "in_tenant(Dave, \"acme\").\nresource_tenant(Doc1, \"acme\").".into(),
        );
        // Bob: empty context
        Self { by_agent }
    }

    fn context_for(&self, agent: &str) -> String {
        self.by_agent.get(agent).cloned().unwrap_or_default()
    }
}

#[derive(Clone)]
struct AppState {
    db: Arc<AppDb>,
}

#[derive(Serialize)]
struct DocView {
    name: String,
    fields: Vec<String>,
    verdict: String,
    reason: Option<String>,
}

#[derive(Deserialize)]
struct DocQuery {
    explain: Option<bool>,
}

async fn health() -> &'static str {
    "ok"
}

async fn get_doc(
    State(state): State<AppState>,
    Agent(agent): Agent,
    Path(name): Path<String>,
    Query(q): Query<DocQuery>,
) -> Result<Json<DocView>, AuthRejection> {
    let ctx = state.db.context_for(&agent);
    let object = name.clone();
    if q.explain.unwrap_or(false) {
        let ex = tls::explain(&agent, "read", &object, &ctx).map_err(AuthRejection::from_auth_error)?;
        if !ex.decision.allowed {
            return Err(AuthRejection::forbidden(&ex.decision));
        }
        let fields = field_mask(&agent, "read", &object, &ctx, &["title", "body", "secret"])?;
        return Ok(Json(DocView {
            name: object,
            fields,
            verdict: format!("{:?}", ex.decision.verdict),
            reason: ex.decision.reason,
        }));
    }
    let d = require(&agent, "read", &object, &ctx)?;
    let fields = field_mask(&agent, "read", &object, &ctx, &["title", "body", "secret"])?;
    Ok(Json(DocView {
        name: object,
        fields,
        verdict: format!("{:?}", d.verdict),
        reason: d.reason,
    }))
}

async fn put_doc(
    State(state): State<AppState>,
    Agent(agent): Agent,
    Path(name): Path<String>,
) -> Result<Json<DocView>, AuthRejection> {
    let ctx = state.db.context_for(&agent);
    let object = name.clone();
    let d = require(&agent, "update", &object, &ctx)?;
    let fields = field_mask(&agent, "update", &object, &ctx, &["title", "body"])?;
    Ok(Json(DocView {
        name: object,
        fields,
        verdict: format!("{:?}", d.verdict),
        reason: d.reason,
    }))
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();

    let state = AppState {
        db: Arc::new(AppDb::demo()),
    };

    let app = Router::new()
        .route("/health", get(health))
        .route("/docs/{name}", get(get_doc).put(put_doc))
        .layer(TraceLayer::new_for_http())
        .with_state(state);

    let addr = "127.0.0.1:3001";
    tracing::info!("auth-axum listening on http://{addr}");
    tracing::info!("try: curl -H 'X-Agent: Alice' http://{addr}/docs/Doc1");
    let listener = tokio::net::TcpListener::bind(addr).await.expect("bind");
    axum::serve(listener, app).await.expect("serve");
}
