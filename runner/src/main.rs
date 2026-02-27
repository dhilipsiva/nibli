use anyhow::Result;
use reedline::{DefaultPrompt, Reedline, Signal};
use serde::{Deserialize, Serialize};
use std::io::{BufRead, BufReader, Write};
use std::net::TcpStream;
use std::time::Duration;
use wasmtime::component::{Component, HasSelf, Linker};
use wasmtime::{Config, Engine, Store};
use wasmtime_wasi::{ResourceTable, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

// ── JSON Lines protocol types ──

#[derive(Serialize)]
struct ComputeRequest {
    relation: String,
    args: Vec<ComputeArg>,
}

#[derive(Serialize, Clone, Debug)]
#[serde(tag = "type", content = "value")]
enum ComputeArg {
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
struct ComputeResponse {
    result: Option<bool>,
    error: Option<String>,
}

// ── Host state ──

struct HostState {
    ctx: WasiCtx,
    table: ResourceTable,
    backend_addr: Option<String>,
    backend_conn: Option<BufReader<TcpStream>>,
}

impl HostState {
    /// Lazily connect to the external compute backend.
    fn connect_backend(&mut self) -> std::result::Result<(), String> {
        if self.backend_conn.is_some() {
            return Ok(());
        }
        let addr = self
            .backend_addr
            .as_ref()
            .ok_or("No compute backend configured")?;
        let stream = TcpStream::connect(addr)
            .map_err(|e| format!("Backend connect to {}: {}", addr, e))?;
        stream
            .set_read_timeout(Some(Duration::from_secs(10)))
            .map_err(|e| format!("Set read timeout: {}", e))?;
        stream
            .set_write_timeout(Some(Duration::from_secs(5)))
            .map_err(|e| format!("Set write timeout: {}", e))?;
        stream
            .set_nodelay(true)
            .map_err(|e| format!("Set nodelay: {}", e))?;
        self.backend_conn = Some(BufReader::new(stream));
        Ok(())
    }

    /// Dispatch a compute request to the external backend.
    /// On connection error, drops the connection and retries once.
    fn dispatch_to_backend(
        &mut self,
        relation: &str,
        args: &[compute_backend::LogicalTerm],
    ) -> std::result::Result<bool, String> {
        if self.backend_addr.is_none() {
            return Err(format!("Unknown compute predicate: {}", relation));
        }

        let request = ComputeRequest {
            relation: relation.to_string(),
            args: args.iter().map(term_to_arg).collect(),
        };
        let mut payload =
            serde_json::to_string(&request).map_err(|e| format!("Serialize: {}", e))?;
        payload.push('\n');

        // Try send+recv, on failure drop connection and retry once
        match self.try_dispatch(&payload) {
            Ok(result) => Ok(result),
            Err(_first_err) => {
                self.backend_conn = None;
                self.try_dispatch(&payload)
            }
        }
    }

    fn try_dispatch(&mut self, payload: &str) -> std::result::Result<bool, String> {
        self.connect_backend()?;
        let reader = self
            .backend_conn
            .as_mut()
            .ok_or("No backend connection")?;

        // Send request
        reader
            .get_mut()
            .write_all(payload.as_bytes())
            .map_err(|e| format!("Backend write: {}", e))?;
        reader
            .get_mut()
            .flush()
            .map_err(|e| format!("Backend flush: {}", e))?;

        // Read response line
        let mut line = String::new();
        reader
            .read_line(&mut line)
            .map_err(|e| format!("Backend read: {}", e))?;

        let resp: ComputeResponse =
            serde_json::from_str(&line).map_err(|e| format!("Backend response parse: {}", e))?;

        if let Some(err) = resp.error {
            Err(err)
        } else if let Some(result) = resp.result {
            Ok(result)
        } else {
            Err("Backend returned neither result nor error".into())
        }
    }
}

fn term_to_arg(term: &compute_backend::LogicalTerm) -> ComputeArg {
    use compute_backend::LogicalTerm;
    match term {
        LogicalTerm::Variable(s) => ComputeArg::Variable(s.clone()),
        LogicalTerm::Constant(s) => ComputeArg::Constant(s.clone()),
        LogicalTerm::Description(s) => ComputeArg::Description(s.clone()),
        LogicalTerm::Unspecified => ComputeArg::Unspecified,
        LogicalTerm::Number(n) => ComputeArg::Number(*n),
    }
}

impl WasiView for HostState {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView {
            ctx: &mut self.ctx,
            table: &mut self.table,
        }
    }
}

mod pipeline_bind {
    wasmtime::component::bindgen!({ path: "../wit/world.wit", world: "engine-pipeline" });
}

use pipeline_bind::lojban::nesy::compute_backend;
use pipeline_bind::lojban::nesy::logic_types::LogicalTerm as EngineLogicalTerm;
use pipeline_bind::lojban::nesy::logic_types::WitnessBinding;

/// Format a LogicalTerm from the engine bindings for display.
fn format_term(term: &EngineLogicalTerm) -> String {
    match term {
        EngineLogicalTerm::Constant(s) => s.clone(),
        EngineLogicalTerm::Variable(s) => format!("?{}", s),
        EngineLogicalTerm::Description(s) => format!("lo {}", s),
        EngineLogicalTerm::Number(n) => {
            if *n == (*n as i64) as f64 {
                format!("{}", *n as i64)
            } else {
                format!("{}", n)
            }
        }
        EngineLogicalTerm::Unspecified => "zo'e".to_string(),
    }
}

impl compute_backend::Host for HostState {
    fn evaluate(
        &mut self,
        relation: String,
        args: Vec<compute_backend::LogicalTerm>,
    ) -> std::result::Result<bool, String> {
        use compute_backend::LogicalTerm;

        // Extract i64 from a LogicalTerm::Number
        let extract_num = |t: &LogicalTerm| -> Option<i64> {
            if let LogicalTerm::Number(n) = t {
                Some(*n as i64)
            } else {
                None
            }
        };

        // 1. Built-in arithmetic predicates: x1 = op(x2, x3) — zero overhead
        if args.len() >= 3 {
            if let (Some(x1), Some(x2), Some(x3)) =
                (extract_num(&args[0]), extract_num(&args[1]), extract_num(&args[2]))
            {
                let result = match relation.as_str() {
                    "pilji" => Some(x1 == x2 * x3),
                    "sumji" => Some(x1 == x2 + x3),
                    "dilcu" => {
                        if x3 == 0 {
                            Some(false)
                        } else {
                            Some(x1 == x2 / x3)
                        }
                    }
                    _ => None,
                };
                if let Some(r) = result {
                    return Ok(r);
                }
            }
        }

        // 2. Forward to external backend (if configured)
        self.dispatch_to_backend(&relation, &args)
    }
}

/// Parse a `:assert` command string into (relation, args).
/// Numbers are detected automatically; everything else is treated as a Constant.
/// Format: `<relation> <arg1> <arg2> ...`
fn parse_assert_args(input: &str) -> std::result::Result<(String, Vec<EngineLogicalTerm>), String> {
    let parts: Vec<&str> = input.split_whitespace().collect();
    if parts.is_empty() {
        return Err("Usage: :assert <relation> <arg1> <arg2> ...".to_string());
    }
    let relation = parts[0].to_string();
    let args = parts[1..]
        .iter()
        .map(|&s| {
            if let Ok(n) = s.parse::<f64>() {
                EngineLogicalTerm::Number(n)
            } else {
                EngineLogicalTerm::Constant(s.to_string())
            }
        })
        .collect();
    Ok((relation, args))
}

fn main() -> Result<()> {
    println!("==================================================");
    println!(" Lojban Neuro-Symbolic Engine - V4 Typed Pipeline  ");
    println!("==================================================");

    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine = Engine::new(&config)?;

    let mut linker = Linker::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;
    compute_backend::add_to_linker::<HostState, HasSelf<HostState>>(
        &mut linker,
        |state: &mut HostState| state,
    )?;

    let backend_addr = std::env::var("NIBLI_COMPUTE_ADDR").ok();
    if let Some(ref addr) = backend_addr {
        println!("Compute backend: {}", addr);
    } else {
        println!("Compute backend: built-in only (set NIBLI_COMPUTE_ADDR=host:port for external)");
    }

    let state = HostState {
        ctx: WasiCtxBuilder::new().inherit_stdio().build(),
        table: ResourceTable::new(),
        backend_addr,
        backend_conn: None,
    };
    let mut store = Store::new(&engine, state);

    println!("Loading fused WebAssembly Component...");
    let pipeline_comp =
        Component::from_file(&engine, "target/wasm32-wasip2/release/engine-pipeline.wasm")?;
    let pipeline =
        pipeline_bind::EnginePipeline::instantiate(&mut store, &pipeline_comp, &linker)?;

    // Get the exported engine interface and create a session
    let engine_iface = pipeline.lojban_nesy_engine();
    let session = engine_iface.session();
    let session_handle = session.call_constructor(&mut store)?;

    let mut line_editor = Reedline::create();
    let prompt = DefaultPrompt::default();

    println!(
        "Ready. Commands: :quit :reset :debug <text> :compute <name> :assert <rel> <args..> :backend [addr] :help"
    );
    println!("Prefix '?' for queries, '??' for find (witness extraction), plain text for assertions.\n");

    loop {
        let sig = line_editor.read_line(&prompt);
        match sig {
            Ok(Signal::Success(buffer)) => {
                let input = buffer.trim();
                if input.is_empty() {
                    continue;
                }

                match input {
                    ":quit" | ":q" => break,
                    ":reset" | ":r" => {
                        match session.call_reset_kb(&mut store, session_handle) {
                            Ok(Ok(())) => println!("[Reset] Knowledge base cleared."),
                            Ok(Err(e)) => println!("[Error] {}", e),
                            Err(e) => println!("[Host Error] {:?}", e),
                        }
                        continue;
                    }
                    ":backend" | ":b" => {
                        let state = store.data();
                        match &state.backend_addr {
                            Some(addr) => {
                                let status = if state.backend_conn.is_some() {
                                    "connected"
                                } else {
                                    "not connected (lazy)"
                                };
                                println!("[Backend] {} ({})", addr, status);
                            }
                            None => println!("[Backend] Not configured"),
                        }
                        continue;
                    }
                    ":help" | ":h" => {
                        println!("  <text>              Assert Lojban as fact");
                        println!("  ? <text>            Query entailment (true/false)");
                        println!("  ?? <text>           Find witnesses (answer variables)");
                        println!("  :debug <text>       Show compiled logic tree");
                        println!("  :compute <name>     Register predicate for compute dispatch");
                        println!("  :assert <rel> <args..> Assert a ground fact directly");
                        println!("  :backend [host:port] Show or set compute backend address");
                        println!("  :reset              Clear all facts (fresh KB)");
                        println!("  :quit               Exit");
                        continue;
                    }
                    _ => {}
                }

                // ── Route by prefix ──
                if let Some(debug_text) = input.strip_prefix(":debug ") {
                    let text = debug_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: :debug <lojban text>");
                        continue;
                    }
                    match session.call_compile_debug(&mut store, session_handle, text) {
                        Ok(Ok(sexp)) => println!("[Logic] {}", sexp),
                        Ok(Err(e)) => println!("[Error] {}", e),
                        Err(e) => println!("[Host Error] {:?}", e),
                    }
                } else if let Some(backend_arg) = input.strip_prefix(":backend ") {
                    let addr = backend_arg.trim();
                    if addr.is_empty() {
                        let state = store.data();
                        match &state.backend_addr {
                            Some(a) => println!("[Backend] {}", a),
                            None => println!("[Backend] Not configured"),
                        }
                    } else {
                        let state = store.data_mut();
                        state.backend_conn = None; // drop existing connection
                        state.backend_addr = Some(addr.to_string());
                        println!("[Backend] Set to {} (connects on first use)", addr);
                    }
                } else if let Some(compute_name) = input.strip_prefix(":compute ") {
                    let name = compute_name.trim();
                    if name.is_empty() {
                        println!("[Host] Usage: :compute <predicate-name>");
                        continue;
                    }
                    match session
                        .call_register_compute_predicate(&mut store, session_handle, name)
                    {
                        Ok(()) => {
                            println!("[Compute] Registered '{}' for external dispatch", name)
                        }
                        Err(e) => println!("[Host Error] {:?}", e),
                    }
                } else if let Some(assert_args) = input.strip_prefix(":assert ") {
                    let text = assert_args.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: :assert <relation> <arg1> <arg2> ...");
                        continue;
                    }
                    match parse_assert_args(text) {
                        Ok((relation, args)) => {
                            let display_args: Vec<String> = args
                                .iter()
                                .map(|a| match a {
                                    EngineLogicalTerm::Number(n) => format!("{}", n),
                                    EngineLogicalTerm::Constant(s) => s.clone(),
                                    _ => "?".to_string(),
                                })
                                .collect();
                            match session.call_assert_fact(
                                &mut store,
                                session_handle,
                                &relation,
                                &args,
                            ) {
                                Ok(Ok(())) => println!(
                                    "[Assert] Fact {}({}) inserted.",
                                    relation,
                                    display_args.join(", ")
                                ),
                                Ok(Err(e)) => println!("[Error] {}", e),
                                Err(e) => println!("[Host Error] {:?}", e),
                            }
                        }
                        Err(e) => println!("[Error] {}", e),
                    }
                } else if let Some(find_text) = input.strip_prefix("??") {
                    let text = find_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: ?? <lojban query with ma>");
                        continue;
                    }
                    match session.call_query_find_text(&mut store, session_handle, text) {
                        Ok(Ok(binding_sets)) => {
                            if binding_sets.is_empty() {
                                println!("[Find] No witnesses found.");
                            } else {
                                for bindings in &binding_sets {
                                    let parts: Vec<String> = bindings
                                        .iter()
                                        .map(|b| {
                                            format!("{} = {}", b.variable, format_term(&b.term))
                                        })
                                        .collect();
                                    println!("[Find] {}", parts.join(", "));
                                }
                            }
                        }
                        Ok(Err(e)) => println!("[Error] {}", e),
                        Err(e) => println!("[Host Error] {:?}", e),
                    }
                } else if let Some(query_text) = input.strip_prefix('?') {
                    let text = query_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: ? <lojban query>");
                        continue;
                    }
                    match session.call_query_text(&mut store, session_handle, text) {
                        Ok(Ok(true)) => println!("[Query] TRUE"),
                        Ok(Ok(false)) => println!("[Query] FALSE"),
                        Ok(Err(e)) => println!("[Error] {}", e),
                        Err(e) => println!("[Host Error] {:?}", e),
                    }
                } else {
                    match session.call_assert_text(&mut store, session_handle, input) {
                        Ok(Ok(n)) => println!("[Assert] {} fact(s) inserted.", n),
                        Ok(Err(e)) => println!("[Error] {}", e),
                        Err(e) => println!("[Host Error] {:?}", e),
                    }
                }
            }
            Ok(Signal::CtrlD) | Ok(Signal::CtrlC) => break,
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }

    // Drop the session resource
    session_handle.resource_drop(&mut store)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use compute_backend::Host;
    use std::io::Write;
    use std::net::TcpListener;
    use std::thread;

    /// Start a mock TCP server that sends a fixed response to the first request.
    fn mock_server(response: &str) -> (String, TcpListener) {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap().to_string();
        let resp = response.to_string();
        let listener2 = listener.try_clone().unwrap();
        thread::spawn(move || {
            for stream in listener2.incoming() {
                let stream = stream.unwrap();
                let mut reader = BufReader::new(stream);
                let mut line = String::new();
                // Read request
                if reader.read_line(&mut line).is_ok() && !line.is_empty() {
                    // Send response
                    let mut resp_line = resp.clone();
                    resp_line.push('\n');
                    let _ = reader.get_mut().write_all(resp_line.as_bytes());
                    let _ = reader.get_mut().flush();
                }
            }
        });
        (addr, listener)
    }

    fn make_host(addr: Option<String>) -> HostState {
        HostState {
            ctx: WasiCtxBuilder::new().build(),
            table: ResourceTable::new(),
            backend_addr: addr,
            backend_conn: None,
        }
    }

    #[test]
    fn test_backend_dispatch_success() {
        let (addr, _listener) = mock_server(r#"{"result": true}"#);
        let mut host = make_host(Some(addr));

        let args = vec![
            compute_backend::LogicalTerm::Number(8.0),
            compute_backend::LogicalTerm::Number(2.0),
            compute_backend::LogicalTerm::Number(3.0),
        ];
        let result = host.dispatch_to_backend("tenfa", &args);
        assert_eq!(result, Ok(true));
    }

    #[test]
    fn test_backend_dispatch_false() {
        let (addr, _listener) = mock_server(r#"{"result": false}"#);
        let mut host = make_host(Some(addr));

        let args = vec![compute_backend::LogicalTerm::Number(9.0)];
        let result = host.dispatch_to_backend("tenfa", &args);
        assert_eq!(result, Ok(false));
    }

    #[test]
    fn test_backend_dispatch_error() {
        let (addr, _listener) = mock_server(r#"{"error": "Unknown relation: foobar"}"#);
        let mut host = make_host(Some(addr));

        let args = vec![compute_backend::LogicalTerm::Number(1.0)];
        let result = host.dispatch_to_backend("foobar", &args);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unknown relation"));
    }

    #[test]
    fn test_backend_not_configured() {
        let mut host = make_host(None);
        let args = vec![compute_backend::LogicalTerm::Number(1.0)];
        let result = host.dispatch_to_backend("tenfa", &args);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unknown compute predicate"));
    }

    #[test]
    fn test_builtin_arithmetic_bypasses_backend() {
        // Even with no backend, built-in arithmetic works
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(6.0),
            compute_backend::LogicalTerm::Number(2.0),
            compute_backend::LogicalTerm::Number(3.0),
        ];
        // pilji: 6 == 2 * 3
        let result = host.evaluate("pilji".to_string(), args);
        assert_eq!(result, Ok(true));
    }

    #[test]
    fn test_evaluate_falls_through_to_backend() {
        let (addr, _listener) = mock_server(r#"{"result": true}"#);
        let mut host = make_host(Some(addr));

        let args = vec![
            compute_backend::LogicalTerm::Number(8.0),
            compute_backend::LogicalTerm::Number(2.0),
            compute_backend::LogicalTerm::Number(3.0),
        ];
        // tenfa is NOT built-in, should forward to backend
        let result = host.evaluate("tenfa".to_string(), args);
        assert_eq!(result, Ok(true));
    }

    #[test]
    fn test_json_serialization() {
        let req = ComputeRequest {
            relation: "tenfa".to_string(),
            args: vec![
                ComputeArg::Number(8.0),
                ComputeArg::Variable("x".to_string()),
                ComputeArg::Constant("abc".to_string()),
                ComputeArg::Description("lo gerku".to_string()),
                ComputeArg::Unspecified,
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

    #[test]
    fn test_backend_reconnect_after_drop() {
        // Start a server, connect, then drop the server and start a new one on same port
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap().to_string();
        let addr_clone = addr.clone();

        // Server thread: accept one connection, respond, then accept another
        thread::spawn(move || {
            for stream in listener.incoming() {
                let stream = stream.unwrap();
                let mut reader = BufReader::new(stream);
                let mut line = String::new();
                if reader.read_line(&mut line).is_ok() && !line.is_empty() {
                    let _ = reader.get_mut().write_all(b"{\"result\": true}\n");
                    let _ = reader.get_mut().flush();
                }
            }
        });

        let mut host = make_host(Some(addr_clone));
        let args = vec![compute_backend::LogicalTerm::Number(1.0)];

        // First call — establishes connection
        let r1 = host.dispatch_to_backend("test", &args);
        assert_eq!(r1, Ok(true));

        // Simulate connection drop
        host.backend_conn = None;

        // Second call — should reconnect
        let r2 = host.dispatch_to_backend("test", &args);
        assert_eq!(r2, Ok(true));
    }
}
