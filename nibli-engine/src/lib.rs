#![allow(dead_code)]

use anyhow::Result;
use wasmtime::component::{Component, HasSelf, Linker, ResourceAny};
use wasmtime::{Config, Engine, Store, StoreLimits, StoreLimitsBuilder};
use wasmtime_wasi::{ResourceTable, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

// ── WIT bindings ──

mod pipeline_bind {
    wasmtime::component::bindgen!({ path: "../wit/world.wit", world: "lasna-pipeline" });
}

use pipeline_bind::lojban::nibli::compute_backend;
use pipeline_bind::lojban::nibli::error_types::NibliError;

// ── Host state (simplified from gasnu — no TCP backend) ──

struct HostState {
    ctx: WasiCtx,
    table: ResourceTable,
    limits: StoreLimits,
}

impl WasiView for HostState {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView {
            ctx: &mut self.ctx,
            table: &mut self.table,
        }
    }
}

impl compute_backend::Host for HostState {
    fn evaluate(
        &mut self,
        relation: String,
        args: Vec<compute_backend::LogicalTerm>,
    ) -> std::result::Result<bool, NibliError> {
        use compute_backend::LogicalTerm;

        let extract_num = |t: &LogicalTerm| -> Option<i64> {
            if let LogicalTerm::Number(n) = t {
                Some(*n as i64)
            } else {
                None
            }
        };

        // Built-in arithmetic only
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

        Err(NibliError::Backend((
            relation,
            "Unknown compute predicate".to_string(),
        )))
    }
}

// ── Engine wrapper ──

pub struct NibliEngine {
    store: Store<HostState>,
    pipeline: pipeline_bind::LasnaPipeline,
    session_handle: ResourceAny,
    fuel_budget: u64,
}

impl NibliEngine {
    pub fn new() -> Result<Self> {
        let mut config = Config::new();
        config.wasm_component_model(true);
        config.consume_fuel(true);
        let wasm_engine = Engine::new(&config)?;

        let mut linker = Linker::new(&wasm_engine);
        wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;
        compute_backend::add_to_linker::<HostState, HasSelf<HostState>>(
            &mut linker,
            |state: &mut HostState| state,
        )?;

        let fuel_budget: u64 = std::env::var("NIBLI_FUEL")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(10_000_000_000);

        let memory_limit_mb: usize = std::env::var("NIBLI_MEMORY_MB")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(512);

        let state = HostState {
            ctx: WasiCtxBuilder::new()
                .inherit_stdout()
                .inherit_stderr()
                .build(),
            table: ResourceTable::new(),
            limits: StoreLimitsBuilder::new()
                .memory_size(memory_limit_mb * 1024 * 1024)
                .build(),
        };
        let mut store = Store::new(&wasm_engine, state);
        store.set_fuel(fuel_budget)?;
        store.limiter(|state| &mut state.limits);

        let wasm_path = std::env::var("NIBLI_WASM_PATH")
            .unwrap_or_else(|_| "target/wasm32-wasip2/debug/lasna-pipeline.wasm".to_string());
        println!("Loading engine from {}...", wasm_path);
        let pipeline_comp = Component::from_file(&wasm_engine, &wasm_path)?;
        let pipeline =
            pipeline_bind::LasnaPipeline::instantiate(&mut store, &pipeline_comp, &linker)?;

        let engine_iface = pipeline.lojban_nibli_lasna();
        let session = engine_iface.session();
        let session_handle = session.call_constructor(&mut store)?;

        println!(
            "Engine ready (fuel={}, memory={}MB)",
            fuel_budget, memory_limit_mb
        );

        Ok(Self {
            store,
            pipeline,
            session_handle,
            fuel_budget,
        })
    }

    pub fn refuel(&mut self) {
        let _ = self.store.set_fuel(self.fuel_budget);
    }
}
