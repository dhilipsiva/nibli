use anyhow::Result;
use reedline::{DefaultPrompt, Reedline, Signal};
use wasmtime::component::{Component, Linker};
use wasmtime::{Config, Engine, Store};
use wasmtime_wasi::{ResourceTable, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

// 1. Define Host State to fulfill WASI Preview 2 requirements
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

// Generate strictly typed host bindings for each WASM component
mod parser_bind {
    wasmtime::component::bindgen!({ path: "../wit/world.wit", world: "parser-component" });
}
mod semantics_bind {
    wasmtime::component::bindgen!({ path: "../wit/world.wit", world: "semantics-component" });
}
mod reasoning_bind {
    wasmtime::component::bindgen!({ path: "../wit/world.wit", world: "reasoning-component" });
}

fn main() -> Result<()> {
    println!("==================================================");
    println!(" Lojban Neuro-Symbolic Engine - V2 WASM Pipeline  ");
    println!("==================================================");

    // 1. Initialize Wasmtime Engine
    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine = Engine::new(&config)?;

    // 2. Setup WASI Linker (Explicitly target Preview 2 / p2)
    let mut linker = Linker::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;

    // 3. Setup Store with WASI Context
    let state = HostState {
        ctx: WasiCtxBuilder::new().inherit_stdio().build(),
        table: ResourceTable::new(),
    };
    let mut store = Store::new(&engine, state);

    // 4. Load the compiled WASM components from disk
    println!("Loading WebAssembly Components...");
    let parser_comp = Component::from_file(&engine, "target/wasm32-wasip2/release/parser.wasm")?;
    let semantics_comp =
        Component::from_file(&engine, "target/wasm32-wasip2/release/semantics.wasm")?;
    let reasoning_comp =
        Component::from_file(&engine, "target/wasm32-wasip2/release/reasoning.wasm")?;

    // 5. Instantiate the components in the Wasmtime sandbox
    let parser_inst = parser_bind::ParserComponent::instantiate(&mut store, &parser_comp, &linker)?;
    let semantics_inst =
        semantics_bind::SemanticsComponent::instantiate(&mut store, &semantics_comp, &linker)?;
    let reasoning_inst =
        reasoning_bind::ReasoningComponent::instantiate(&mut store, &reasoning_comp, &linker)?;

    let mut line_editor = Reedline::create();
    let prompt = DefaultPrompt::default();
    println!("Pipeline ready. Type ':quit' to exit.");

    loop {
        let sig = line_editor.read_line(&prompt);
        match sig {
            Ok(Signal::Success(buffer)) => {
                let input = buffer.trim();
                if input.is_empty() {
                    continue;
                }
                if input == ":quit" || input == ":q" {
                    break;
                }

                println!("\n[Host] Input: {}", input);

                // --- Phase 1: WASM Parser ---
                let parse_result = parser_inst
                    .lojban_nesy_parser()
                    .call_parse_text(&mut store, input)?;
                let ast_buffer_1 = match parse_result {
                    Ok(buf) => buf,
                    Err(e) => {
                        eprintln!("[Host] Parser Error: {}", e);
                        continue;
                    }
                };
                println!(
                    "[Host] Parsed {} bridi. Crossing WASM boundary to Semantics...",
                    ast_buffer_1.sentences.len()
                );

                // --- Memory Mapping Bridge ---
                let ast_buffer_2 = map_buffer_to_semantics(ast_buffer_1);

                // --- Phase 2: WASM Semantics ---
                let sexps = semantics_inst
                    .lojban_nesy_semantics()
                    .call_compile_buffer(&mut store, &ast_buffer_2)?;

                for sexp in sexps {
                    println!("[Host] Logical Form: {}", sexp);

                    // --- Phase 3: WASM Reasoning ---
                    reasoning_inst
                        .lojban_nesy_reasoning()
                        .call_assert_fact(&mut store, &sexp)?;
                    reasoning_inst
                        .lojban_nesy_reasoning()
                        .call_query_entailment(&mut store, &sexp)?;
                }
            }
            Ok(Signal::CtrlD) | Ok(Signal::CtrlC) => break,
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
    Ok(())
}

fn map_buffer_to_semantics(
    p: parser_bind::lojban::nesy::ast_types::AstBuffer,
) -> semantics_bind::lojban::nesy::ast_types::AstBuffer {
    let selbris = p
        .selbris
        .into_iter()
        .map(|s| match s {
            parser_bind::lojban::nesy::ast_types::Selbri::Root(r) => {
                semantics_bind::lojban::nesy::ast_types::Selbri::Root(r)
            }
            parser_bind::lojban::nesy::ast_types::Selbri::Compound(c) => {
                semantics_bind::lojban::nesy::ast_types::Selbri::Compound(c)
            }
            parser_bind::lojban::nesy::ast_types::Selbri::Tanru((m, h)) => {
                semantics_bind::lojban::nesy::ast_types::Selbri::Tanru((m, h))
            }
        })
        .collect();

    let sumtis = p
        .sumtis
        .into_iter()
        .map(|s| match s {
            parser_bind::lojban::nesy::ast_types::Sumti::ProSumti(ps) => {
                semantics_bind::lojban::nesy::ast_types::Sumti::ProSumti(ps)
            }
            parser_bind::lojban::nesy::ast_types::Sumti::Description(d) => {
                semantics_bind::lojban::nesy::ast_types::Sumti::Description(d)
            }
            parser_bind::lojban::nesy::ast_types::Sumti::Name(n) => {
                semantics_bind::lojban::nesy::ast_types::Sumti::Name(n)
            }
            parser_bind::lojban::nesy::ast_types::Sumti::QuotedLiteral(q) => {
                semantics_bind::lojban::nesy::ast_types::Sumti::QuotedLiteral(q)
            }
        })
        .collect();

    let sentences = p
        .sentences
        .into_iter()
        .map(|s| semantics_bind::lojban::nesy::ast_types::Bridi {
            relation: s.relation,
            terms: s.terms,
        })
        .collect();

    semantics_bind::lojban::nesy::ast_types::AstBuffer {
        selbris,
        sumtis,
        sentences,
    }
}
