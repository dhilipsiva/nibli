//! Native TCP compute-backend client (JSON Lines over a stream socket).
//!
//! Mirrors gasnu's WASM-host bridge (`gasnu/src/main.rs`) but for the NATIVE
//! engine: it lets `nibli-engine` / `nibli-server` dispatch external compute
//! predicates (`tenfa`, `dugri`, custom) to the Python reference backend
//! (`python/nibli_backend.py`). Built-in arithmetic (`pilji`/`sumji`/`dilcu`) is
//! resolved in-engine by logji and never reaches this client.
//!
//! logji's per-KB dispatch hook is a bare `fn` pointer (Copy, no capture), so the
//! connection cannot live on the closure. It lives in a `thread_local!` here in
//! the EMBEDDER (keeping logji global-state-free); the bare `native_eval_fn` /
//! `native_batch_eval_fn` read it. nibli-server runs reasoning in per-thread
//! `spawn_blocking` workers, so the connection is per-worker (pooling, no races).
//!
//! Trust boundary: the backend is a plaintext, unauthenticated peer in the
//! trusted computing base — see `logji::set_compute_dispatch` / book Ch 17.

use std::cell::RefCell;
use std::io::{BufRead, BufReader, Write};
use std::net::TcpStream;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

use crate::{EngineComputeRequest, EngineLogicalTerm};

// ── JSON Lines protocol types (wire format) ──

#[derive(Serialize)]
struct BackendRequest {
    relation: String,
    args: Vec<BackendArg>,
}

#[derive(Serialize, Clone, Debug)]
#[serde(tag = "type", content = "value")]
enum BackendArg {
    #[serde(rename = "variable")]
    Variable(String),
    #[serde(rename = "constant")]
    Constant(String),
    #[serde(rename = "description")]
    Description(String),
    #[serde(rename = "unspecified")]
    Unspecified,
    #[serde(rename = "number")]
    Number(f64),
}

#[derive(Deserialize)]
struct BackendResponse {
    result: Option<bool>,
    error: Option<String>,
}

fn term_to_arg(term: &EngineLogicalTerm) -> BackendArg {
    match term {
        EngineLogicalTerm::Variable(s) => BackendArg::Variable(s.clone()),
        EngineLogicalTerm::Constant(s) => BackendArg::Constant(s.clone()),
        EngineLogicalTerm::Description(s) => BackendArg::Description(s.clone()),
        EngineLogicalTerm::Unspecified => BackendArg::Unspecified,
        EngineLogicalTerm::Number(n) => BackendArg::Number(*n),
    }
}

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

fn parse_response(line: &str) -> Result<bool, String> {
    let resp: BackendResponse =
        serde_json::from_str(line).map_err(|e| format!("Backend response parse: {}", e))?;
    match (resp.result, resp.error) {
        (_, Some(err)) => Err(err),
        (Some(r), None) => Ok(r),
        (None, None) => Err("Backend returned neither result nor error".to_string()),
    }
}

// ── The client (connection state) ──

struct BackendClient {
    addr: Option<String>,
    conn: Option<BufReader<TcpStream>>,
    /// Timestamp of last dispatch — used for idle-connection reaping.
    last_used: Option<Instant>,
}

impl BackendClient {
    const fn new() -> Self {
        BackendClient {
            addr: None,
            conn: None,
            last_used: None,
        }
    }

    /// Lazily connect, dropping a connection idle longer than
    /// `NIBLI_BACKEND_IDLE_TIMEOUT_SECS` (default 300s).
    fn connect(&mut self) -> Result<(), String> {
        if let (Some(conn_time), Some(_)) = (self.last_used, &self.conn) {
            let idle_timeout = env_u64("NIBLI_BACKEND_IDLE_TIMEOUT_SECS", 300);
            if conn_time.elapsed().as_secs() > idle_timeout {
                self.conn = None;
                self.last_used = None;
            }
        }
        if self.conn.is_some() {
            return Ok(());
        }
        let addr = self.addr.as_ref().ok_or("No compute backend configured")?;
        let stream =
            TcpStream::connect(addr).map_err(|e| format!("Backend connect to {}: {}", addr, e))?;
        stream
            .set_read_timeout(Some(Duration::from_secs(env_u64(
                "NIBLI_BACKEND_READ_TIMEOUT_SECS",
                10,
            ))))
            .map_err(|e| format!("Set read timeout: {}", e))?;
        stream
            .set_write_timeout(Some(Duration::from_secs(env_u64(
                "NIBLI_BACKEND_WRITE_TIMEOUT_SECS",
                5,
            ))))
            .map_err(|e| format!("Set write timeout: {}", e))?;
        stream
            .set_nodelay(true)
            .map_err(|e| format!("Set nodelay: {}", e))?;
        self.conn = Some(BufReader::new(stream));
        Ok(())
    }

    /// Dispatch a single predicate; on a connection-level error, drop and retry once.
    fn dispatch(&mut self, relation: &str, args: &[EngineLogicalTerm]) -> Result<bool, String> {
        if self.addr.is_none() {
            return Err(format!("Unknown compute predicate: {}", relation));
        }
        let request = BackendRequest {
            relation: relation.to_string(),
            args: args.iter().map(term_to_arg).collect(),
        };
        let mut payload =
            serde_json::to_string(&request).map_err(|e| format!("Serialize: {}", e))?;
        payload.push('\n');
        match self.try_dispatch(&payload) {
            Ok(result) => Ok(result),
            Err(_) => {
                self.conn = None;
                self.try_dispatch(&payload)
            }
        }
    }

    fn try_dispatch(&mut self, payload: &str) -> Result<bool, String> {
        self.connect()?;
        self.last_used = Some(Instant::now());
        let reader = self.conn.as_mut().ok_or("No backend connection")?;
        reader
            .get_mut()
            .write_all(payload.as_bytes())
            .map_err(|e| format!("Backend write: {}", e))?;
        reader
            .get_mut()
            .flush()
            .map_err(|e| format!("Backend flush: {}", e))?;
        let mut line = String::new();
        reader
            .read_line(&mut line)
            .map_err(|e| format!("Backend read: {}", e))?;
        parse_response(&line)
    }

    /// Pipeline-dispatch a batch: write ALL requests in one burst, then read ALL
    /// responses in order (eliminates N-1 round trips). Connection-level failure
    /// drops the connection and retries the whole batch once; per-response errors
    /// are carried as `Err` entries. Returns one result per request, in order.
    fn dispatch_batch(&mut self, requests: &[EngineComputeRequest]) -> Vec<Result<bool, String>> {
        if self.addr.is_none() {
            return requests
                .iter()
                .map(|_| Err("No compute backend configured".to_string()))
                .collect();
        }
        let payloads: Vec<String> = requests
            .iter()
            .map(|req| {
                let wire = BackendRequest {
                    relation: req.relation.clone(),
                    args: req.args.iter().map(term_to_arg).collect(),
                };
                let mut s = serde_json::to_string(&wire).unwrap_or_default();
                s.push('\n');
                s
            })
            .collect();
        match self.try_batch(&payloads) {
            Ok(results) => results,
            Err(_) => {
                self.conn = None;
                self.try_batch(&payloads)
                    .unwrap_or_else(|e| payloads.iter().map(|_| Err(e.clone())).collect())
            }
        }
    }

    fn try_batch(&mut self, payloads: &[String]) -> Result<Vec<Result<bool, String>>, String> {
        self.connect()?;
        self.last_used = Some(Instant::now());
        let reader = self.conn.as_mut().ok_or("No backend connection")?;
        for payload in payloads {
            reader
                .get_mut()
                .write_all(payload.as_bytes())
                .map_err(|e| format!("Backend batch write: {}", e))?;
        }
        reader
            .get_mut()
            .flush()
            .map_err(|e| format!("Backend batch flush: {}", e))?;
        let mut results = Vec::with_capacity(payloads.len());
        for _ in 0..payloads.len() {
            let mut line = String::new();
            reader
                .read_line(&mut line)
                .map_err(|e| format!("Backend batch read: {}", e))?;
            results.push(parse_response(&line));
        }
        Ok(results)
    }
}

thread_local! {
    static CLIENT: RefCell<BackendClient> = const { RefCell::new(BackendClient::new()) };
}

/// Point this thread's client at `addr`, dropping any stale connection if the
/// address changed. Called by `NibliEngine::enable_compute_backend`.
pub(crate) fn set_addr(addr: &str) {
    CLIENT.with(|c| {
        let mut c = c.borrow_mut();
        if c.addr.as_deref() != Some(addr) {
            c.conn = None;
            c.last_used = None;
            c.addr = Some(addr.to_string());
        }
    });
}

/// The single-predicate `EvalFn` registered on the KB.
pub(crate) fn native_eval_fn(rel: &str, args: &[EngineLogicalTerm]) -> Result<bool, String> {
    CLIENT.with(|c| c.borrow_mut().dispatch(rel, args))
}

/// The batch `BatchEvalFn` registered on the KB.
pub(crate) fn native_batch_eval_fn(requests: &[EngineComputeRequest]) -> Vec<Result<bool, String>> {
    CLIENT.with(|c| c.borrow_mut().dispatch_batch(requests))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::TcpListener;
    use std::thread;

    /// A local TCP server that replies with a fixed line to EACH request line on
    /// each connection (so it serves both single and pipelined-batch dispatch).
    fn mock_server(response: &str) -> String {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap().to_string();
        let resp = response.to_string();
        thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(stream) = stream else { continue };
                let mut reader = BufReader::new(stream);
                loop {
                    let mut line = String::new();
                    match reader.read_line(&mut line) {
                        Ok(0) | Err(_) => break,
                        Ok(_) => {
                            let mut r = resp.clone();
                            r.push('\n');
                            if reader.get_mut().write_all(r.as_bytes()).is_err() {
                                break;
                            }
                            let _ = reader.get_mut().flush();
                        }
                    }
                }
            }
        });
        addr
    }

    fn client_at(addr: &str) -> BackendClient {
        let mut c = BackendClient::new();
        c.addr = Some(addr.to_string());
        c
    }

    fn req(rel: &str, args: Vec<EngineLogicalTerm>) -> EngineComputeRequest {
        EngineComputeRequest {
            relation: rel.to_string(),
            args,
        }
    }

    #[test]
    fn dispatch_success() {
        let mut c = client_at(&mock_server(r#"{"result": true}"#));
        let args = vec![
            EngineLogicalTerm::Number(8.0),
            EngineLogicalTerm::Number(2.0),
            EngineLogicalTerm::Number(3.0),
        ];
        assert_eq!(c.dispatch("tenfa", &args), Ok(true));
    }

    #[test]
    fn dispatch_error_propagates() {
        let mut c = client_at(&mock_server(r#"{"error": "Unknown relation: foobar"}"#));
        let r = c.dispatch("foobar", &[EngineLogicalTerm::Number(1.0)]);
        assert!(r.is_err());
        assert!(r.unwrap_err().contains("Unknown relation"));
    }

    #[test]
    fn dispatch_batch_two_requests() {
        let mut c = client_at(&mock_server(r#"{"result": true}"#));
        let n = |v: f64| EngineLogicalTerm::Number(v);
        let results = c.dispatch_batch(&[
            req("tenfa", vec![n(8.0), n(2.0), n(3.0)]),
            req("dugri", vec![n(3.0), n(8.0), n(2.0)]),
        ]);
        assert_eq!(results, vec![Ok(true), Ok(true)]);
    }

    #[test]
    fn no_addr_errors_not_panics() {
        let mut c = BackendClient::new();
        assert!(
            c.dispatch("tenfa", &[EngineLogicalTerm::Number(1.0)])
                .is_err()
        );
        let batch = c.dispatch_batch(&[req("tenfa", vec![EngineLogicalTerm::Number(1.0)])]);
        assert_eq!(batch.len(), 1);
        assert!(batch[0].is_err());
    }

    #[test]
    fn json_serialization_shape() {
        let req = BackendRequest {
            relation: "tenfa".to_string(),
            args: vec![
                BackendArg::Number(8.0),
                BackendArg::Variable("x".to_string()),
                BackendArg::Constant("adam".to_string()),
                BackendArg::Description("gerku".to_string()),
                BackendArg::Unspecified,
            ],
        };
        let json = serde_json::to_string(&req).unwrap();
        assert!(json.contains(r#""relation":"tenfa""#));
        assert!(json.contains(r#""type":"number""#));
        assert!(json.contains(r#""type":"variable""#));
        assert!(json.contains(r#""type":"constant""#));
        assert!(json.contains(r#""type":"description""#));
        assert!(json.contains(r#""type":"unspecified""#));
    }
}
