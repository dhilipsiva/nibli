//! Minimal WebRTC signaling server.
//!
//! Simple HTTP relay for SDP offers/answers. This is the ONLY centralized
//! piece — once peers connect via WebRTC, the signaling server can die.
//! Peers stay connected P2P.
//!
//! Endpoints:
//!   POST /offer   { from, to, sdp }  — store an SDP offer
//!   GET  /offer/:to                  — retrieve pending offer for a peer
//!   POST /answer  { from, to, sdp }  — store an SDP answer
//!   GET  /answer/:to                 — retrieve pending answer for a peer

use std::collections::HashMap;
use std::sync::Arc;

use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::routing::{get, post};
use axum::{Json, Router};
use serde::{Deserialize, Serialize};
use tokio::sync::Mutex;

/// SDP exchange payload.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SdpExchange {
    pub from: String,
    pub to: String,
    pub sdp: String,
}

/// Signaling server state.
#[derive(Default)]
struct SignalState {
    /// Pending offers keyed by target peer name.
    offers: HashMap<String, SdpExchange>,
    /// Pending answers keyed by target peer name.
    answers: HashMap<String, SdpExchange>,
}

type SharedState = Arc<Mutex<SignalState>>;

/// Build the signaling server router.
pub fn signal_router() -> Router {
    let state: SharedState = Arc::new(Mutex::new(SignalState::default()));
    Router::new()
        .route("/offer", post(post_offer))
        .route("/offer/{to}", get(get_offer))
        .route("/answer", post(post_answer))
        .route("/answer/{to}", get(get_answer))
        .with_state(state)
}

/// Start the signaling server on the given port.
pub async fn run_signal_server(port: u16) -> Result<(), String> {
    let app = signal_router();
    let addr = format!("0.0.0.0:{port}");
    println!("[signal] listening on {addr}");
    let listener = tokio::net::TcpListener::bind(&addr)
        .await
        .map_err(|e| format!("signal bind: {e}"))?;
    axum::serve(listener, app)
        .await
        .map_err(|e| format!("signal serve: {e}"))
}

async fn post_offer(
    State(state): State<SharedState>,
    Json(payload): Json<SdpExchange>,
) -> StatusCode {
    println!("[signal] offer: {} → {}", payload.from, payload.to);
    let mut s = state.lock().await;
    s.offers.insert(payload.to.clone(), payload);
    StatusCode::OK
}

async fn get_offer(
    State(state): State<SharedState>,
    Path(to): Path<String>,
) -> Result<Json<SdpExchange>, StatusCode> {
    // Poll with short timeout — try for up to 10 seconds.
    for _ in 0..20 {
        {
            let mut s = state.lock().await;
            if let Some(offer) = s.offers.remove(&to) {
                return Ok(Json(offer));
            }
        }
        tokio::time::sleep(std::time::Duration::from_millis(500)).await;
    }
    Err(StatusCode::NOT_FOUND)
}

async fn post_answer(
    State(state): State<SharedState>,
    Json(payload): Json<SdpExchange>,
) -> StatusCode {
    println!("[signal] answer: {} → {}", payload.from, payload.to);
    let mut s = state.lock().await;
    s.answers.insert(payload.to.clone(), payload);
    StatusCode::OK
}

async fn get_answer(
    State(state): State<SharedState>,
    Path(to): Path<String>,
) -> Result<Json<SdpExchange>, StatusCode> {
    for _ in 0..20 {
        {
            let mut s = state.lock().await;
            if let Some(answer) = s.answers.remove(&to) {
                return Ok(Json(answer));
            }
        }
        tokio::time::sleep(std::time::Duration::from_millis(500)).await;
    }
    Err(StatusCode::NOT_FOUND)
}
