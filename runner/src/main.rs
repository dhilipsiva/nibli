use anyhow::Result;
use reedline::{DefaultPrompt, Reedline, Signal};
use wasmtime::component::{Component, Linker};
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

fn main() -> Result<()> {
    println!("==================================================");
    println!(" Lojban Neuro-Symbolic Engine - V4 Typed Pipeline  ");
    println!("==================================================");

    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine = Engine::new(&config)?;

    let mut linker = Linker::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;

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

    println!("Ready. Commands: :quit :reset :debug <text> :help");
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
