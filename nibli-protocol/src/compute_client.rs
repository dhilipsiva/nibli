//! Shared native TCP compute-backend client (JSON Lines over a stream socket).
//!
//! One implementation, two consumers:
//! - `gasnu` — the WASM host bridge holds a `BackendClient` on its `HostState`.
//! - `nibli-engine` — the native embedder holds one in a `thread_local!` (per
//!   `spawn_blocking` worker on `nibli-server`).
//!
//! It dispatches external compute predicates (`tenfa`, `dugri`, custom) to the
//! Python reference backend (`python/nibli_backend.py`). Built-in arithmetic
//! (`pilji`/`sumji`/`dilcu`) is resolved upstream (in logji for the engine, in
//! gasnu's host impl) and never reaches this client.
//!
//! The client is term-type-AGNOSTIC: callers pre-convert their own logical-term
//! representation (WIT `compute-backend.logical-term` for gasnu,
//! `nibli_types::logic::LogicalTerm` for the engine) into [`BackendArg`], so this
//! module depends on neither.
//!
//! Trust boundary: the backend is a plaintext, unauthenticated peer in the
//! trusted computing base — see `logji::set_compute_dispatch` / book Ch 17.

use std::io::{BufRead, BufReader, Write};
use std::net::TcpStream;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

// ── JSON Lines protocol types (wire format) ──

/// One argument of a compute request, serialized as `{"type": "<tag>", "value": <v>}`.
#[derive(Serialize, Clone, Debug, PartialEq)]
#[serde(tag = "type", content = "value")]
pub enum BackendArg {
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

/// A single compute request: `{"relation": "<rel>", "args": [<BackendArg>, ...]}`.
#[derive(Serialize, Clone, Debug)]
pub struct BackendRequest {
    pub relation: String,
    pub args: Vec<BackendArg>,
}

#[derive(Deserialize)]
struct BackendResponse {
    result: Option<bool>,
    error: Option<String>,
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

/// A lazily-connected, reused TCP connection to a JSON-Lines compute backend.
pub struct BackendClient {
    addr: Option<String>,
    conn: Option<BufReader<TcpStream>>,
    /// Timestamp of last dispatch — used for idle-connection reaping.
    last_used: Option<Instant>,
}

impl Default for BackendClient {
    fn default() -> Self {
        Self::new()
    }
}

impl BackendClient {
    /// A disconnected client with no address. `const` so it can seed a
    /// `thread_local!`'s `const {}` initializer.
    pub const fn new() -> Self {
        BackendClient {
            addr: None,
            conn: None,
            last_used: None,
        }
    }

    /// Point the client at `addr`, dropping any stale connection if the address
    /// changed (a no-op if it is unchanged).
    pub fn set_addr(&mut self, addr: &str) {
        if self.addr.as_deref() != Some(addr) {
            self.conn = None;
            self.last_used = None;
            self.addr = Some(addr.to_string());
        }
    }

    /// The configured backend address, if any.
    pub fn addr(&self) -> Option<&str> {
        self.addr.as_deref()
    }

    /// Whether a live connection is currently held (connections are lazy).
    pub fn is_connected(&self) -> bool {
        self.conn.is_some()
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
    /// `args` are pre-converted by the caller.
    pub fn dispatch(&mut self, relation: &str, args: &[BackendArg]) -> Result<bool, String> {
        if self.addr.is_none() {
            return Err(format!("Unknown compute predicate: {}", relation));
        }
        let request = BackendRequest {
            relation: relation.to_string(),
            args: args.to_vec(),
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
    pub fn dispatch_batch(&mut self, requests: &[BackendRequest]) -> Vec<Result<bool, String>> {
        if self.addr.is_none() {
            return requests
                .iter()
                .map(|_| Err("No compute backend configured".to_string()))
                .collect();
        }
        let payloads: Vec<String> = requests
            .iter()
            .map(|req| {
                let mut s = serde_json::to_string(req).unwrap_or_default();
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
        c.set_addr(addr);
        c
    }

    fn req(rel: &str, args: Vec<BackendArg>) -> BackendRequest {
        BackendRequest {
            relation: rel.to_string(),
            args,
        }
    }

    #[test]
    fn dispatch_success() {
        let mut c = client_at(&mock_server(r#"{"result": true}"#));
        let args = vec![
            BackendArg::Number(8.0),
            BackendArg::Number(2.0),
            BackendArg::Number(3.0),
        ];
        assert_eq!(c.dispatch("tenfa", &args), Ok(true));
    }

    #[test]
    fn dispatch_error_propagates() {
        let mut c = client_at(&mock_server(r#"{"error": "Unknown relation: foobar"}"#));
        let r = c.dispatch("foobar", &[BackendArg::Number(1.0)]);
        assert!(r.is_err());
        assert!(r.unwrap_err().contains("Unknown relation"));
    }

    #[test]
    fn dispatch_batch_two_requests() {
        let mut c = client_at(&mock_server(r#"{"result": true}"#));
        let n = BackendArg::Number;
        let results = c.dispatch_batch(&[
            req("tenfa", vec![n(8.0), n(2.0), n(3.0)]),
            req("dugri", vec![n(3.0), n(8.0), n(2.0)]),
        ]);
        assert_eq!(results, vec![Ok(true), Ok(true)]);
    }

    #[test]
    fn no_addr_errors_not_panics() {
        let mut c = BackendClient::new();
        assert!(c.dispatch("tenfa", &[BackendArg::Number(1.0)]).is_err());
        let batch = c.dispatch_batch(&[req("tenfa", vec![BackendArg::Number(1.0)])]);
        assert_eq!(batch.len(), 1);
        assert!(batch[0].is_err());
    }

    #[test]
    fn no_addr_single_names_the_predicate() {
        // The single-dispatch no-addr error names the predicate (gasnu surfaces it
        // as "Unknown compute predicate: ..."), distinct from the batch message.
        let mut c = BackendClient::new();
        let err = c.dispatch("tenfa", &[BackendArg::Number(1.0)]).unwrap_err();
        assert!(err.contains("Unknown compute predicate"));
        assert!(err.contains("tenfa"));
    }

    #[test]
    fn set_addr_change_drops_connection() {
        let addr = mock_server(r#"{"result": true}"#);
        let mut c = client_at(&addr);
        assert!(c.dispatch("tenfa", &[BackendArg::Number(1.0)]).is_ok());
        assert!(c.is_connected());
        // Same address: keep the connection.
        c.set_addr(&addr);
        assert!(c.is_connected());
        // Different address: drop the stale connection.
        c.set_addr("127.0.0.1:1");
        assert!(!c.is_connected());
        assert_eq!(c.addr(), Some("127.0.0.1:1"));
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
