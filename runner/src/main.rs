use anyhow::Result;
use reedline::{DefaultPrompt, Reedline, Signal};
use wasmtime::component::{Component, HasSelf, Linker};
use wasmtime::{Config, Engine, Store};
use wasmtime_wasi::{ResourceTable, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

struct HostState {
    ctx: WasiCtx,
    table: ResourceTable,
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

        // Arithmetic predicates: x1 = op(x2, x3)
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

        Err(format!("Unknown compute predicate: {}", relation))
    }
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
    compute_backend::add_to_linker::<HostState, HasSelf<HostState>>(&mut linker, |state: &mut HostState| state)?;

    let state = HostState {
        ctx: WasiCtxBuilder::new().inherit_stdio().build(),
        table: ResourceTable::new(),
    };
    let mut store = Store::new(&engine, state);

    println!("Loading fused WebAssembly Component...");
    let pipeline_comp =
        Component::from_file(&engine, "target/wasm32-wasip2/release/engine-pipeline.wasm")?;
    let pipeline = pipeline_bind::EnginePipeline::instantiate(&mut store, &pipeline_comp, &linker)?;

    // Get the exported engine interface and create a session
    let engine_iface = pipeline.lojban_nesy_engine();
    let session = engine_iface.session();
    let session_handle = session.call_constructor(&mut store)?;

    let mut line_editor = Reedline::create();
    let prompt = DefaultPrompt::default();

    println!("Ready. Commands: :quit :reset :debug <text> :compute <name> :help");
    println!("Prefix '?' for queries, plain text for assertions.\n");

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
                    ":help" | ":h" => {
                        println!("  <text>           Assert Lojban as fact");
                        println!("  ? <text>         Query entailment");
                        println!("  :debug <text>    Show compiled logic tree");
                        println!("  :compute <name>  Register predicate for compute dispatch");
                        println!("  :reset           Clear all facts (fresh KB)");
                        println!("  :quit            Exit");
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
                } else if let Some(compute_name) = input.strip_prefix(":compute ") {
                    let name = compute_name.trim();
                    if name.is_empty() {
                        println!("[Host] Usage: :compute <predicate-name>");
                        continue;
                    }
                    match session.call_register_compute_predicate(&mut store, session_handle, name) {
                        Ok(()) => println!("[Compute] Registered '{}' for external dispatch", name),
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
