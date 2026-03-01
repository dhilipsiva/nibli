//! Nibli native host runner: Wasmtime WASI P2 host + interactive REPL.
//!
//! Loads the fused WASM engine component, provides the `compute-backend` host
//! implementation (built-in arithmetic + external TCP backend), and runs an
//! interactive REPL (reedline-based) with these prefixes:
//!
//! - **(bare text)** — Assert Lojban facts
//! - **`?`** — Query entailment (TRUE/FALSE)
//! - **`??`** — Query with witness extraction (find satisfying bindings)
//! - **`?!`** — Query with proof trace (indented proof tree)
//! - **`:debug`** — Compile to logic s-expression without asserting
//! - **`:assert`** — Assert ground facts directly (bypasses Lojban parsing)
//! - **`:retract`** — Retract a fact by ID (triggers KB rebuild)
//! - **`:facts`** — List all active facts in the KB
//! - **`:compute`** — Register predicates for compute dispatch
//! - **`:backend`** — Show/change external compute backend address
//! - **`:reset`** — Clear the knowledge base
//! - **`:fuel`** / **`:memory`** — Show/set WASM execution limits
//! - **`:saturate`** — Show/set egglog saturation run bound (iterations)

use anyhow::Result;
use reedline::{DefaultPrompt, Reedline, Signal};
use serde::{Deserialize, Serialize};
use std::io::{BufRead, BufReader, Write};
use std::net::TcpStream;
use std::time::Duration;
use wasmtime::component::{Component, HasSelf, Linker};
use wasmtime::{Config, Engine, Store, StoreLimits, StoreLimitsBuilder};
use wasmtime_wasi::{ResourceTable, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

// ── JSON Lines protocol types ──

/// Request sent to the external compute backend over TCP + JSON Lines.
#[derive(Serialize)]
struct ComputeRequest {
    relation: String,
    args: Vec<ComputeArg>,
}

/// A logical term serialized for the JSON Lines compute backend protocol.
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

/// Response received from the external compute backend.
#[derive(Deserialize)]
struct ComputeResponse {
    result: Option<bool>,
    error: Option<String>,
}

// ── Host state ──

/// Wasmtime host state: WASI context, resource table, memory limits,
/// and optional external compute backend TCP connection.
struct HostState {
    ctx: WasiCtx,
    table: ResourceTable,
    limits: StoreLimits,
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
use pipeline_bind::lojban::nesy::error_types::NibliError;
use pipeline_bind::lojban::nesy::logic_types::LogicalTerm as EngineLogicalTerm;
use pipeline_bind::lojban::nesy::logic_types::{ProofRule, ProofStep, ProofTrace};

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

/// Format a proof rule for display.
fn format_rule(rule: &ProofRule, result: bool) -> String {
    let tag = if result { "TRUE" } else { "FALSE" };
    match rule {
        ProofRule::Conjunction => format!("Conjunction → {}", tag),
        ProofRule::DisjunctionEgraph(s) => format!("Disjunction (e-graph: {}) → {}", s, tag),
        ProofRule::DisjunctionIntro(side) => format!("Disjunction ({}) → {}", side, tag),
        ProofRule::Negation => format!("Negation → {}", tag),
        ProofRule::ModalPassthrough(kind) => format!("Modal ({}) → {}", kind, tag),
        ProofRule::ExistsWitness((var, term)) => {
            format!("Exists: {} = {} → {}", var, format_term(term), tag)
        }
        ProofRule::ExistsFailed => format!("Exists: no witness → {}", tag),
        ProofRule::ForallVacuous => format!("ForAll: vacuous (empty domain) → {}", tag),
        ProofRule::ForallVerified(entities) => {
            let names: Vec<String> = entities.iter().map(format_term).collect();
            format!("ForAll: verified [{}] → {}", names.join(", "), tag)
        }
        ProofRule::ForallCounterexample(term) => {
            format!("ForAll: counterexample {} → {}", format_term(term), tag)
        }
        ProofRule::CountResult((expected, actual)) => {
            format!("Count: expected={}, actual={} → {}", expected, actual, tag)
        }
        ProofRule::PredicateCheck((method, detail)) => {
            format!("{}: {} → {}", method, detail, tag)
        }
        ProofRule::ComputeCheck((method, detail)) => {
            format!("Compute ({}): {} → {}", method, detail, tag)
        }
        ProofRule::Asserted(sexp) => format!("Asserted: {} → {}", sexp, tag),
        ProofRule::Derived((label, sexp)) => {
            format!("Derived ({}): {} → {}", label, sexp, tag)
        }
        ProofRule::ProofRef(sexp) => format!("(proved above): {} → {}", sexp, tag),
    }
}

/// Recursively format a proof tree node with indentation.
fn format_proof_node(steps: &[ProofStep], idx: u32, indent: usize, out: &mut String) {
    let step = &steps[idx as usize];
    for _ in 0..indent {
        out.push_str("  ");
    }
    out.push_str(&format_rule(&step.rule, step.holds));
    out.push('\n');
    for &child in &step.children {
        format_proof_node(steps, child, indent + 1, out);
    }
}

/// Format an entire proof trace as an indented tree string.
fn format_proof_trace(trace: &ProofTrace) -> String {
    let mut out = String::new();
    format_proof_node(&trace.steps, trace.root, 1, &mut out);
    out
}

impl compute_backend::Host for HostState {
    fn evaluate(
        &mut self,
        relation: String,
        args: Vec<compute_backend::LogicalTerm>,
    ) -> std::result::Result<bool, NibliError> {
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
            .map_err(|msg| NibliError::Backend((relation, msg)))
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

fn refuel(store: &mut Store<HostState>, budget: u64) {
    let _ = store.set_fuel(budget);
}

fn format_host_error(e: &anyhow::Error) -> String {
    let msg = e.to_string();
    if msg.contains("fuel") {
        "[Limit] Execution fuel exhausted. Increase with NIBLI_FUEL env var or :fuel command."
            .to_string()
    } else if msg.contains("memory") || msg.contains("Memory") {
        "[Limit] Memory limit exceeded. Increase with NIBLI_MEMORY_MB env var or :memory command."
            .to_string()
    } else {
        format!("[Host Error] {:?}", e)
    }
}

fn format_nibli_error(e: &NibliError) -> String {
    match e {
        NibliError::Syntax(d) => {
            format!("[Syntax Error] line {}:{}: {}", d.line, d.column, d.message)
        }
        NibliError::Semantic(msg) => format!("[Semantic Error] {}", msg),
        NibliError::Reasoning(msg) => format!("[Reasoning Error] {}", msg),
        NibliError::Backend((kind, msg)) => format!("[Backend Error] {} — {}", kind, msg),
    }
}

fn main() -> Result<()> {
    println!("==================================================");
    println!(" Lojban Neuro-Symbolic Engine - V4 Typed Pipeline  ");
    println!("==================================================");

    let mut config = Config::new();
    config.wasm_component_model(true);
    config.consume_fuel(true);
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

    let mut fuel_budget: u64 = std::env::var("NIBLI_FUEL")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(10_000_000_000);
    println!("Fuel budget: {} per command", fuel_budget);

    let mut memory_limit_mb: usize = std::env::var("NIBLI_MEMORY_MB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(512);
    println!("Memory limit: {} MB", memory_limit_mb);

    let mut run_bound: u32 = std::env::var("NIBLI_RUN_BOUND")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    println!("Run bound: {} iterations", run_bound);

    let state = HostState {
        ctx: WasiCtxBuilder::new().inherit_stdout().inherit_stderr().build(),
        table: ResourceTable::new(),
        limits: StoreLimitsBuilder::new()
            .memory_size(memory_limit_mb * 1024 * 1024)
            .build(),
        backend_addr,
        backend_conn: None,
    };
    let mut store = Store::new(&engine, state);
    store.set_fuel(fuel_budget)?;
    store.limiter(|state| &mut state.limits);

    println!("Loading fused WebAssembly Component...");
    let pipeline_comp =
        Component::from_file(&engine, "target/wasm32-wasip2/release/engine-pipeline.wasm")?;
    let pipeline =
        pipeline_bind::EnginePipeline::instantiate(&mut store, &pipeline_comp, &linker)?;

    // Get the exported engine interface and create a session
    let engine_iface = pipeline.lojban_nesy_engine();
    let session = engine_iface.session();
    let session_handle = session.call_constructor(&mut store)?;

    // Apply non-default run bound from env var
    if run_bound != 100 {
        session
            .call_set_run_bound(&mut store, session_handle, run_bound)
            .ok();
    }

    let mut line_editor = Reedline::create();
    let prompt = DefaultPrompt::default();

    println!(
        "Ready. Commands: :quit :reset :facts :retract <id> :debug <text> :compute <name> :assert <rel> <args..> :backend [addr] :fuel [n] :memory [mb] :saturate [n] :help"
    );
    println!("Prefix '?' for queries, '?!' for proof trace, '??' for find, plain text for assertions.\n");

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
                        refuel(&mut store, fuel_budget);
                        match session.call_reset_kb(&mut store, session_handle) {
                            Ok(Ok(())) => println!("[Reset] Knowledge base cleared."),
                            Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                            Err(e) => println!("{}", format_host_error(&e)),
                        }
                        continue;
                    }
                    ":fuel" | ":f" => {
                        println!("[Fuel] Budget: {} per command", fuel_budget);
                        continue;
                    }
                    ":memory" | ":m" => {
                        println!("[Memory] Limit: {} MB", memory_limit_mb);
                        continue;
                    }
                    ":saturate" | ":sat" => {
                        println!("[Saturate] Run bound: {} iterations", run_bound);
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
                    ":facts" => {
                        refuel(&mut store, fuel_budget);
                        match session.call_list_facts(&mut store, session_handle) {
                            Ok(Ok(facts)) => {
                                if facts.is_empty() {
                                    println!("[Facts] Knowledge base is empty.");
                                } else {
                                    println!("[Facts] {} active fact(s):", facts.len());
                                    for f in &facts {
                                        let roots_label = if f.root_count == 1 { "root" } else { "roots" };
                                        println!("  #{}: {} ({} {})", f.id, f.label, f.root_count, roots_label);
                                    }
                                }
                            }
                            Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                            Err(e) => println!("{}", format_host_error(&e)),
                        }
                        continue;
                    }
                    ":help" | ":h" => {
                        println!("  <text>              Assert Lojban as fact");
                        println!("  ? <text>            Query entailment (true/false)");
                        println!("  ?! <text>           Query with proof trace");
                        println!("  ?? <text>           Find witnesses (answer variables)");
                        println!("  :debug <text>       Show compiled logic tree");
                        println!("  :compute <name>     Register predicate for compute dispatch");
                        println!("  :assert <rel> <args..> Assert a ground fact directly");
                        println!("  :retract <id>       Retract a fact by ID (rebuilds KB)");
                        println!("  :facts              List all active facts in the KB");
                        println!("  :backend [host:port] Show or set compute backend address");
                        println!("  :fuel [amount]      Show or set WASM fuel budget per command");
                        println!("  :memory [mb]        Show or set WASM memory limit in MB");
                        println!("  :saturate [n]       Show or set egglog saturation run bound");
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
                    refuel(&mut store, fuel_budget);
                    match session.call_compile_debug(&mut store, session_handle, text) {
                        Ok(Ok(sexp)) => println!("[Logic] {}", sexp),
                        Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                        Err(e) => println!("{}", format_host_error(&e)),
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
                } else if let Some(fuel_arg) = input.strip_prefix(":fuel ") {
                    let arg = fuel_arg.trim();
                    match arg.parse::<u64>() {
                        Ok(n) if n > 0 => {
                            fuel_budget = n;
                            println!("[Fuel] Budget set to {}", fuel_budget);
                        }
                        _ => println!("[Host] Usage: :fuel <positive-integer>"),
                    }
                } else if let Some(mem_arg) = input.strip_prefix(":memory ") {
                    let arg = mem_arg.trim();
                    match arg.parse::<usize>() {
                        Ok(n) if n > 0 => {
                            memory_limit_mb = n;
                            let state = store.data_mut();
                            state.limits = StoreLimitsBuilder::new()
                                .memory_size(memory_limit_mb * 1024 * 1024)
                                .build();
                            println!("[Memory] Limit set to {} MB", memory_limit_mb);
                        }
                        _ => println!("[Host] Usage: :memory <positive-integer-mb>"),
                    }
                } else if let Some(sat_arg) = input.strip_prefix(":saturate ").or_else(|| input.strip_prefix(":sat ")) {
                    match sat_arg.trim().parse::<u32>() {
                        Ok(n) if n > 0 => {
                            run_bound = n;
                            refuel(&mut store, fuel_budget);
                            match session.call_set_run_bound(&mut store, session_handle, n) {
                                Ok(()) => println!("[Saturate] Run bound set to {} iterations", n),
                                Err(e) => println!("{}", format_host_error(&e)),
                            }
                        }
                        _ => println!("[Host] Usage: :saturate <positive-integer>"),
                    }
                } else if let Some(compute_name) = input.strip_prefix(":compute ") {
                    let name = compute_name.trim();
                    if name.is_empty() {
                        println!("[Host] Usage: :compute <predicate-name>");
                        continue;
                    }
                    refuel(&mut store, fuel_budget);
                    match session
                        .call_register_compute_predicate(&mut store, session_handle, name)
                    {
                        Ok(()) => {
                            println!("[Compute] Registered '{}' for external dispatch", name)
                        }
                        Err(e) => println!("{}", format_host_error(&e)),
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
                            refuel(&mut store, fuel_budget);
                            match session.call_assert_fact(
                                &mut store,
                                session_handle,
                                &relation,
                                &args,
                            ) {
                                Ok(Ok(fact_id)) => println!(
                                    "[Fact #{}] {}({}) asserted.",
                                    fact_id,
                                    relation,
                                    display_args.join(", ")
                                ),
                                Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                                Err(e) => println!("{}", format_host_error(&e)),
                            }
                        }
                        Err(e) => println!("[Error] {}", e),
                    }
                } else if let Some(retract_arg) = input.strip_prefix(":retract ") {
                    let arg = retract_arg.trim();
                    match arg.parse::<u64>() {
                        Ok(id) => {
                            refuel(&mut store, fuel_budget);
                            match session.call_retract_fact(&mut store, session_handle, id) {
                                Ok(Ok(())) => println!("[Retract] Fact #{} retracted. KB rebuilt.", id),
                                Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                                Err(e) => println!("{}", format_host_error(&e)),
                            }
                        }
                        Err(_) => println!("[Host] Usage: :retract <fact-id>"),
                    }
                } else if let Some(find_text) = input.strip_prefix("??") {
                    let text = find_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: ?? <lojban query with ma>");
                        continue;
                    }
                    refuel(&mut store, fuel_budget);
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
                        Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                        Err(e) => println!("{}", format_host_error(&e)),
                    }
                } else if let Some(proof_text) = input.strip_prefix("?!") {
                    let text = proof_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: ?! <lojban query>");
                        continue;
                    }
                    refuel(&mut store, fuel_budget);
                    match session.call_query_text_with_proof(&mut store, session_handle, text) {
                        Ok(Ok((result, trace))) => {
                            let tag = if result { "TRUE" } else { "FALSE" };
                            println!("[Proof] {}", tag);
                            print!("{}", format_proof_trace(&trace));
                        }
                        Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                        Err(e) => println!("{}", format_host_error(&e)),
                    }
                } else if let Some(query_text) = input.strip_prefix('?') {
                    let text = query_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: ? <lojban query>");
                        continue;
                    }
                    refuel(&mut store, fuel_budget);
                    match session.call_query_text(&mut store, session_handle, text) {
                        Ok(Ok(true)) => println!("[Query] TRUE"),
                        Ok(Ok(false)) => println!("[Query] FALSE"),
                        Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                        Err(e) => println!("{}", format_host_error(&e)),
                    }
                } else {
                    refuel(&mut store, fuel_budget);
                    match session.call_assert_text(&mut store, session_handle, input) {
                        Ok(Ok(fact_id)) => println!("[Fact #{}] Asserted.", fact_id),
                        Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                        Err(e) => println!("{}", format_host_error(&e)),
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
            limits: StoreLimitsBuilder::new()
                .memory_size(512 * 1024 * 1024)
                .build(),
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
        assert_eq!(host.evaluate("pilji".to_string(), args).unwrap(), true);
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
        assert_eq!(host.evaluate("tenfa".to_string(), args).unwrap(), true);
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

    // ── format_nibli_error tests ──

    #[test]
    fn test_format_nibli_error_syntax() {
        use pipeline_bind::lojban::nesy::error_types::SyntaxDetail;
        let e = NibliError::Syntax(SyntaxDetail {
            message: "expected selbri or terms".to_string(),
            line: 3,
            column: 7,
        });
        let out = format_nibli_error(&e);
        assert_eq!(out, "[Syntax Error] line 3:7: expected selbri or terms");
    }

    #[test]
    fn test_format_nibli_error_semantic() {
        let e = NibliError::Semantic("go'i has no antecedent".to_string());
        let out = format_nibli_error(&e);
        assert_eq!(out, "[Semantic Error] go'i has no antecedent");
    }

    #[test]
    fn test_format_nibli_error_reasoning() {
        let e = NibliError::Reasoning("egglog assertion failed".to_string());
        let out = format_nibli_error(&e);
        assert_eq!(out, "[Reasoning Error] egglog assertion failed");
    }

    #[test]
    fn test_format_nibli_error_backend() {
        let e = NibliError::Backend(("tenfa".to_string(), "connection refused".to_string()));
        let out = format_nibli_error(&e);
        assert_eq!(out, "[Backend Error] tenfa \u{2014} connection refused");
    }

    // ── evaluate wraps errors as NibliError::Backend ──

    #[test]
    fn test_evaluate_wraps_dispatch_error_as_backend() {
        // No backend configured → dispatch_to_backend returns Err(String)
        // evaluate should wrap it as NibliError::Backend((relation, msg))
        let mut host = make_host(None);
        let args = vec![compute_backend::LogicalTerm::Number(1.0)];
        let result = host.evaluate("tenfa".to_string(), args);
        match result {
            Err(NibliError::Backend((kind, msg))) => {
                assert_eq!(kind, "tenfa");
                assert!(msg.contains("Unknown compute predicate"));
            }
            other => panic!("expected NibliError::Backend, got {:?}", other),
        }
    }

    #[test]
    fn test_evaluate_backend_error_from_server() {
        let (addr, _listener) = mock_server(r#"{"error": "division by zero"}"#);
        let mut host = make_host(Some(addr));
        let args = vec![compute_backend::LogicalTerm::Number(1.0)];
        let result = host.evaluate("dilcu_ext".to_string(), args);
        match result {
            Err(NibliError::Backend((kind, msg))) => {
                assert_eq!(kind, "dilcu_ext");
                assert!(msg.contains("division by zero"));
            }
            other => panic!("expected NibliError::Backend, got {:?}", other),
        }
    }

    // ── Memory limit tests ──

    #[test]
    fn test_make_host_has_limits() {
        // HostState should contain StoreLimits
        let _host = make_host(None);
        // If it compiles and runs, the limits field is present
    }

    #[test]
    fn test_format_host_error_memory() {
        let e = anyhow::anyhow!("memory allocation limit exceeded");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Limit]"));
        assert!(out.contains("Memory limit"));
        assert!(out.contains("NIBLI_MEMORY_MB"));
        assert!(out.contains(":memory"));
    }

    #[test]
    fn test_format_host_error_memory_uppercase() {
        let e = anyhow::anyhow!("Memory allocation failed");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Limit]"));
        assert!(out.contains("Memory limit"));
    }

    #[test]
    fn test_format_host_error_fuel_unchanged() {
        let e = anyhow::anyhow!("all fuel consumed");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Limit]"));
        assert!(out.contains("fuel"));
        assert!(out.contains("NIBLI_FUEL"));
    }

    #[test]
    fn test_format_host_error_other_unchanged() {
        let e = anyhow::anyhow!("something else broke");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Host Error]"));
    }

    #[test]
    fn test_store_limits_builder_creates_valid_limits() {
        // Verify StoreLimitsBuilder API works as expected
        let limits = StoreLimitsBuilder::new()
            .memory_size(256 * 1024 * 1024)
            .build();
        // Assign into a HostState — if it compiles, the types are correct
        let _host = HostState {
            ctx: WasiCtxBuilder::new().build(),
            table: ResourceTable::new(),
            limits,
            backend_addr: None,
            backend_conn: None,
        };
    }

    #[test]
    fn test_store_limiter_integration() {
        // Verify Store::limiter works with our HostState
        let mut config = Config::new();
        config.wasm_component_model(true);
        config.consume_fuel(true);
        let engine = Engine::new(&config).unwrap();

        let state = HostState {
            ctx: WasiCtxBuilder::new().build(),
            table: ResourceTable::new(),
            limits: StoreLimitsBuilder::new()
                .memory_size(64 * 1024 * 1024)
                .build(),
            backend_addr: None,
            backend_conn: None,
        };
        let mut store = Store::new(&engine, state);
        store.set_fuel(1_000_000).unwrap();
        store.limiter(|state| &mut state.limits);
        // Store is set up with both fuel and memory limits — if no panic, success
    }

    #[test]
    fn test_parse_assert_args_basic() {
        let (rel, args) = parse_assert_args("gerku alis").unwrap();
        assert_eq!(rel, "gerku");
        assert_eq!(args.len(), 1);
        match &args[0] {
            EngineLogicalTerm::Constant(s) => assert_eq!(s, "alis"),
            other => panic!("expected Constant, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_assert_args_number() {
        let (rel, args) = parse_assert_args("pilji 6 2 3").unwrap();
        assert_eq!(rel, "pilji");
        assert_eq!(args.len(), 3);
        match &args[0] {
            EngineLogicalTerm::Number(n) => assert_eq!(*n, 6.0),
            other => panic!("expected Number, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_assert_args_empty() {
        assert!(parse_assert_args("").is_err());
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

    // ─── Built-in arithmetic edge cases ──────────────────────────

    #[test]
    fn test_builtin_pilji_correct() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(12.0),
            compute_backend::LogicalTerm::Number(3.0),
            compute_backend::LogicalTerm::Number(4.0),
        ];
        assert_eq!(host.evaluate("pilji".to_string(), args).unwrap(), true);
    }

    #[test]
    fn test_builtin_pilji_incorrect() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(13.0),
            compute_backend::LogicalTerm::Number(3.0),
            compute_backend::LogicalTerm::Number(4.0),
        ];
        assert_eq!(host.evaluate("pilji".to_string(), args).unwrap(), false);
    }

    #[test]
    fn test_builtin_sumji_correct() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(7.0),
            compute_backend::LogicalTerm::Number(3.0),
            compute_backend::LogicalTerm::Number(4.0),
        ];
        assert_eq!(host.evaluate("sumji".to_string(), args).unwrap(), true);
    }

    #[test]
    fn test_builtin_sumji_incorrect() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(8.0),
            compute_backend::LogicalTerm::Number(3.0),
            compute_backend::LogicalTerm::Number(4.0),
        ];
        assert_eq!(host.evaluate("sumji".to_string(), args).unwrap(), false);
    }

    #[test]
    fn test_builtin_dilcu_correct() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(4.0),
            compute_backend::LogicalTerm::Number(12.0),
            compute_backend::LogicalTerm::Number(3.0),
        ];
        assert_eq!(host.evaluate("dilcu".to_string(), args).unwrap(), true);
    }

    #[test]
    fn test_builtin_dilcu_incorrect() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(5.0),
            compute_backend::LogicalTerm::Number(12.0),
            compute_backend::LogicalTerm::Number(3.0),
        ];
        assert_eq!(host.evaluate("dilcu".to_string(), args).unwrap(), false);
    }

    // ─── parse_assert_args edge cases ────────────────────────────

    #[test]
    fn test_parse_assert_args_multiple_constants() {
        let (rel, args) = parse_assert_args("nelci alis bob").unwrap();
        assert_eq!(rel, "nelci");
        assert_eq!(args.len(), 2);
        match &args[0] {
            EngineLogicalTerm::Constant(s) => assert_eq!(s, "alis"),
            other => panic!("expected Constant, got {:?}", other),
        }
        match &args[1] {
            EngineLogicalTerm::Constant(s) => assert_eq!(s, "bob"),
            other => panic!("expected Constant, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_assert_args_mixed_number_and_constant() {
        let (rel, args) = parse_assert_args("pilji 6 alis 3").unwrap();
        assert_eq!(rel, "pilji");
        assert_eq!(args.len(), 3);
        assert!(matches!(&args[0], EngineLogicalTerm::Number(n) if *n == 6.0));
        assert!(matches!(&args[1], EngineLogicalTerm::Constant(s) if s == "alis"));
        assert!(matches!(&args[2], EngineLogicalTerm::Number(n) if *n == 3.0));
    }

    #[test]
    fn test_parse_assert_args_relation_only_no_args() {
        // Just the relation name with no arguments — should this be valid?
        // It depends on implementation. Let's verify it doesn't panic.
        let result = parse_assert_args("gerku");
        // Relation without args — may error or return empty args
        if let Ok((rel, args)) = result {
            assert_eq!(rel, "gerku");
            assert!(args.is_empty());
        }
    }

    #[test]
    fn test_parse_assert_args_whitespace_handling() {
        let (rel, args) = parse_assert_args("  gerku   alis  ").unwrap();
        assert_eq!(rel, "gerku");
        assert_eq!(args.len(), 1);
        match &args[0] {
            EngineLogicalTerm::Constant(s) => assert_eq!(s, "alis"),
            other => panic!("expected Constant, got {:?}", other),
        }
    }

    // ─── JSON deserialization tests ──────────────────────────────

    #[test]
    fn test_json_response_true() {
        let resp: ComputeResponse = serde_json::from_str(r#"{"result": true}"#).unwrap();
        assert_eq!(resp.result, Some(true));
        assert!(resp.error.is_none());
    }

    #[test]
    fn test_json_response_false() {
        let resp: ComputeResponse = serde_json::from_str(r#"{"result": false}"#).unwrap();
        assert_eq!(resp.result, Some(false));
    }

    #[test]
    fn test_json_response_error() {
        let resp: ComputeResponse = serde_json::from_str(r#"{"error": "fail"}"#).unwrap();
        assert!(resp.result.is_none());
        assert_eq!(resp.error, Some("fail".to_string()));
    }

    // ─── format_nibli_error comprehensive tests ──────────────────

    #[test]
    fn test_format_nibli_error_syntax_with_position() {
        use pipeline_bind::lojban::nesy::error_types::SyntaxDetail;
        let e = NibliError::Syntax(SyntaxDetail {
            message: "unexpected token".to_string(),
            line: 1,
            column: 15,
        });
        let out = format_nibli_error(&e);
        assert!(out.contains("[Syntax Error]"));
        assert!(out.contains("1:15"));
        assert!(out.contains("unexpected token"));
    }

    // ─── format_host_error edge cases ────────────────────────────

    #[test]
    fn test_format_host_error_generic_error() {
        let e = anyhow::anyhow!("unknown wasm trap");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Host Error]"));
        assert!(out.contains("unknown wasm trap"));
    }

    #[test]
    fn test_format_host_error_fuel_case_insensitive() {
        // "fuel" match should be case insensitive or at least match lower case
        let e = anyhow::anyhow!("all fuel consumed by execution");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Limit]"));
    }

    // ─── Backend with various LogicalTerm types ──────────────────

    #[test]
    fn test_backend_dispatch_with_constant_args() {
        let (addr, _listener) = mock_server(r#"{"result": true}"#);
        let mut host = make_host(Some(addr));

        let args = vec![
            compute_backend::LogicalTerm::Constant("alis".to_string()),
            compute_backend::LogicalTerm::Variable("x".to_string()),
        ];
        let result = host.dispatch_to_backend("custom_rel", &args);
        assert_eq!(result, Ok(true));
    }

    #[test]
    fn test_backend_dispatch_with_description_arg() {
        let (addr, _listener) = mock_server(r#"{"result": false}"#);
        let mut host = make_host(Some(addr));

        let args = vec![
            compute_backend::LogicalTerm::Description("lo gerku".to_string()),
        ];
        let result = host.dispatch_to_backend("test_rel", &args);
        assert_eq!(result, Ok(false));
    }

    #[test]
    fn test_backend_dispatch_with_unspecified_arg() {
        let (addr, _listener) = mock_server(r#"{"result": true}"#);
        let mut host = make_host(Some(addr));

        let args = vec![
            compute_backend::LogicalTerm::Unspecified,
        ];
        let result = host.dispatch_to_backend("test_rel", &args);
        assert_eq!(result, Ok(true));
    }
}
