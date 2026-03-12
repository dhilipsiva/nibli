# Dioxus + WASI P2 Component Model: a complete integration guide

**The most viable path to running your 867KB WASI P2 Component Model engine in a Dioxus web app is a dual-target architecture** — not the jco transpilation path alone. jco v1.16.1 can transpile your wac-fused composite component and map WIT resources to JavaScript classes, but browser WASI shims remain officially "experimental and not suitable for production." The recommended approach factors your engine into a target-agnostic core logic crate, then wraps it separately for Wasmtime (native/desktop) and wasm-bindgen (browser). A desktop-first prototype using Dioxus 0.7.3 + native Wasmtime eliminates the browser complexity entirely while you iterate on the UI. Below is the full technical analysis across all nine research areas.

---

## 1. Dioxus 0.7.3 is the target, and `dx` is the only build tool you need

The current stable release is **Dioxus 0.7.3** (January 17, 2026), not 0.6.x. Key additions in 0.7 include subsecond Rust hot-patching, automatic Tailwind CSS detection, a first-party component library (Radix-primitives style), WASM bundle splitting, and Dioxus Native (experimental WGPU renderer). The `dx` CLI handles everything — building, serving, hot-reload, asset optimization, Tailwind integration, and platform targeting. Trunk is no longer recommended.

The rendering architecture is **Virtual DOM → web-sys → real DOM**. The `dioxus-core` crate maintains a renderer-agnostic VirtualDom that diffs and emits mutations. The `dioxus-web` renderer applies those mutations to the browser DOM via `web-sys` calls. The framework compiles to `wasm32-unknown-unknown` using `wasm-bindgen` under the hood. A minimal app looks like this:

```rust
use dioxus::prelude::*;

fn main() {
    dioxus::launch(App);
}

#[component]
fn App() -> Element {
    rsx! { h1 { "Nibli IDE" } }
}
```

For async operations — critical for Ollama HTTP calls and engine queries — Dioxus provides four primitives. **`spawn`** fires a one-off async task from an event handler. **`use_resource`** reactively re-fetches data when dependent signals change. **`use_coroutine`** creates a long-lived async process with a message channel (ideal for engine command dispatch). **`use_future`** runs a fire-and-forget future on mount. All futures execute on the main thread in WASM (single-threaded async), yielding at await points.

State management uses **signals** as the primary reactive primitive. Signals are `Copy`, can cross async boundaries, and update subscribers automatically. For app-wide state like the engine session, `use_context_provider` injects a struct of signals that any descendant component accesses via `use_context()`. `GlobalSignal` offers truly global state without provider wiring. The pattern for the engine session:

```rust
#[derive(Clone, Copy)]
struct EngineSession {
    engine: Signal<Option<NibliEngine>>,
    status: Signal<EngineStatus>,
}

fn App() -> Element {
    use_context_provider(|| EngineSession {
        engine: Signal::new(None),
        status: Signal::new(EngineStatus::Loading),
    });
    // async init via use_resource, then child components access via use_context()
}
```

**Tailwind CSS is zero-config in 0.7**: place a `tailwind.css` file at the project root with `@import "tailwindcss"; @source "./src/**/*.{rs,html,css}";` and `dx serve` automatically starts the Tailwind watcher. For tabs, the official component library provides accessible, unstyled primitives installed via `dx component add tabs`. For split panes, the `dioxus-mosaic` crate provides React-Mosaic-style tiling windows.

---

## 2. The jco transpilation path works but carries production risk

This is the highest-risk area. **jco v1.16.1** (Bytecode Alliance) transpiles WASI P2 Component Model binaries into browser-runnable ES modules plus core `.wasm` files. The command `jco transpile nibli.wasm --instantiation async --no-nodejs-compat -o output/` produces:

```
output/
├── nibli.core.wasm        # Core WASM module(s) from your 4 sub-components
├── nibli.core2.wasm       # Additional core modules (common with composed components)
├── nibli.js               # ES module wrapper (20-100KB depending on WIT complexity)
├── nibli.d.ts             # TypeScript declarations
└── interfaces/            # Type declarations for WASI interfaces
```

**jco handles wac-fused composite components correctly.** This is demonstrated in the official `string-reverse-upper` example — two components composed with `wac plug`, then transpiled as one unit. Your 4-sub-component engine will produce multiple `.core.wasm` files (one per original core module in the composition) plus the JS glue.

**WIT resources map to JavaScript classes.** Your `resource session { constructor(); assert-text(...); query-text-with-proof(...); }` becomes a JS class `Session` with methods `assertText(text)` and `queryTextWithProof(query)`. Resource handles persist across calls — the JS object wraps an internal handle tracked via finalization registry. TypeScript declarations are generated automatically.

**The critical limitation: jco only produces JavaScript bindings.** Since Dioxus itself compiles to `wasm32-unknown-unknown`, calling the jco-transpiled engine requires a double boundary crossing:

```
Dioxus WASM ──wasm-bindgen──► JavaScript ──ES import──► jco JS wrapper ──► engine.core.wasm
```

Each crossing involves string serialization (UTF-8 ↔ JS strings via TextEncoder/TextDecoder). For your use case — 1-3 engine calls per user action with string inputs/outputs and millisecond-scale computation — **this overhead is negligible**. The actual reasoning runs at near-native speed on V8/SpiderMonkey's compiled WASM.

**WASI shims for stdout/stderr work**: The `@bytecodealliance/preview2-shim` package maps stdout and stderr to `console.log` and `console.error` in browser environments. Your diagnostic `println!` statements will appear in the browser dev console. However, **browser shims are officially "experimental and not suitable for production applications."**

**Fuel and StoreLimits are not available after jco transpilation.** These are Wasmtime-specific host features. The browser's WebAssembly engine provides no fuel-based metering. Practical alternatives: run the engine in a Web Worker with `setTimeout`-based watchdog, enforce input size limits before calling the engine, or use `worker.terminate()` for hard timeouts.

**No runtime currently supports WASI P2 Component Model natively in the browser** — not Wasmtime (cannot compile to WASM), not Wasmer-js (WASI P1 only), not `browser_wasi_shim` (P1 only). jco transpilation is the only viable path for running Component Model binaries in the browser.

### The dual-target alternative eliminates browser risk

The recommended architecture factors the engine into layers:

```
nibli-core/          # Pure logic, no WASI deps, no_std-compatible
├── wasm32-wasip2 wrapper (nibli-engine → Wasmtime native)
│   └── cargo-component → wac plug → Wasmtime
└── wasm32-unknown-unknown wrapper (nibli-web-engine → browser)
    └── wasm-bindgen → single .wasm + .js → Dioxus app
```

This loses Component Model composition and WIT contracts for the web target, but gains a **production-ready, single-boundary, battle-tested browser path** using wasm-bindgen. The native target retains the full Component Model architecture via Wasmtime. Both share the same `nibli-core` logic crate. No existing project has combined Dioxus + WASI P2 in the browser — you would be the first with the jco path.

---

## 3. Desktop-first prototyping with native Wasmtime is the fastest path

**Dioxus desktop runs as native Rust** in a multithreaded Tokio runtime, rendering via system webview (WRY). Desktop binaries are ~15MB. The same RSX/component code works for both web and desktop with different feature flags. This means you can use native Wasmtime directly:

```rust
// nibli-desktop/src/main.rs — native Wasmtime, no jco needed
fn main() {
    let engine = wasmtime::Engine::default();
    let component = wasmtime::component::Component::from_file(
        &engine, "nibli_engine.wasm"
    ).unwrap();
    // Create instance with WASI bindings, inject into Dioxus context
    dioxus::launch(App);
}
```

This completely avoids jco, browser WASI shims, and the double-boundary crossing. You get native-speed engine execution, full fuel/memory limits, and the identical UI code you'll later deploy to web. Develop the entire UI and engine interaction model on desktop, then port to web once the jco browser path matures or you've built the dual-target wasm-bindgen wrapper.

For **engine isolation on web**, run the engine in a Web Worker. The jco-transpiled engine is a JS module, so create a small JavaScript worker file that imports it:

```javascript
// nibli-worker.js
import { instantiate } from './nibli-engine/nibli_engine.js';

let session = null;
self.onmessage = async (event) => {
    const { id, type, payload } = event.data;
    if (type === 'init') {
        const engine = await instantiate(getCoreModule, wasiImports);
        session = new engine.Session();
        self.postMessage({ id, ok: true });
    } else if (type === 'assert') {
        const result = session.assertText(payload);
        self.postMessage({ id, ok: true, result });
    }
    // ... query, retract, etc.
};
```

The Dioxus app communicates via `web-sys::Worker` + `postMessage`, wrapped in a `use_coroutine` for clean async integration.

---

## 4. Ollama integration is straightforward with reqwest

The Ollama HTTP API exposes `POST /api/chat` for conversational completions. Use `reqwest` (which automatically uses the browser Fetch API when compiled to WASM) for HTTP calls:

```rust
let resp = reqwest::Client::new()
    .post("http://localhost:11434/api/chat")
    .json(&serde_json::json!({
        "model": "llama3.2",
        "messages": [
            {"role": "system", "content": LOJBAN_SYSTEM_PROMPT},
            {"role": "user", "content": format!("Translate to Lojban: {}", text)}
        ],
        "stream": false,
        "options": {"temperature": 0.3}
    }))
    .send().await?
    .json::<OllamaResponse>().await?;
```

**CORS is handled by default**: Ollama allows localhost origins. If issues arise, set `OLLAMA_ORIGINS="http://localhost:8080"` as an environment variable before starting the Ollama server. On Linux with systemd, add `Environment="OLLAMA_ORIGINS=http://localhost:8080"` to the service override.

**Streaming** is supported via `reqwest`'s `stream` feature + `wasm-streams` on the WASM target. Each chunk from `response.bytes_stream()` contains a newline-delimited JSON object. Start with `"stream": false` for simplicity; add progressive output later by updating a Dioxus signal on each chunk.

**No current LLM produces reliable Lojban.** The Lojban community explicitly warns against using LLMs for Lojban. However, this is acceptable for your use case — the translation only needs to be close enough for an expert to verify and correct, with the back-translation tab serving as the quality check. Use few-shot prompting with a detailed system prompt covering bridi structure, gismu place structures, gadri (lo/le/la), cmavo usage, tanru composition, and negation. Include 5-10 example translations. Recommended models via Ollama: **llama3.2** (8B, best balance) or **gemma3** (strong multilingual).

---

## 5. The PHF dictionary crate should be shared between engine and Dioxus app

**Option (b) is correct**: run the back-translator in the Dioxus app itself with the jbovlaste dictionary embedded via PHF at compile time. The `phf` crate is fully WASM-compatible (supports `no_std`) and produces `static` data baked directly into the binary's data section — **O(1) lookup with zero runtime initialization cost**.

Create a shared crate:

```
smuni-dictionary/
├── Cargo.toml      # depends on phf (no_std)
├── build.rs        # parses jbovlaste-en.xml → PHF map
└── src/lib.rs      # exports static DICTIONARY + lookup()
```

Both the `smuni` WASI component and the `nibli-web` Dioxus app depend on `smuni-dictionary`. For ~1,527 entries with words, glosswords, keywords, and type info, expect **~75-100KB** embedded in the WASM binary.

The back-translation algorithm is straightforward: for each token, look up gismu/lujvo in the PHF map and return the primary glossword; map cmavo to structural notation from a hardcoded table (~60 entries); pass through cmevla names unchanged. Compose as `predicate(arg1, arg2)` notation. Existing tools that implement this pattern include **jbofi'e** (C, word-by-word glosser), **ilmentufa** (JavaScript, web-based parser + glosser), and **ianek-s-glosser** (Python).

**Phase 1**: Simple space-split word-by-word lookup — gives a rough gloss in ~50 lines of Rust. **Phase 2**: Use the engine's `compile-debug` s-expression output for structure-aware back-translation with proper place-structure mapping.

---

## 6. An indented tree view is the right starting point for proof visualization

Proof traces of 50-200 nodes are best visualized in two phases. **Phase 1** uses an indented tree view with native HTML `<details>/<summary>` elements — zero external dependencies, full interactivity via the browser's built-in collapse mechanism, and approximately 50 lines of Dioxus code:

```rust
#[component]
fn ProofStepView(trace: Signal<ProofTrace>, index: u32, depth: u32) -> Element {
    let step = &trace.read().steps[index as usize];
    let bg = if step.holds { "#e8f5e9" } else { "#ffebee" };

    rsx! {
        div { style: "padding-left: {depth * 20}px;",
            if !step.children.is_empty() {
                details { open: depth < 3,
                    summary {
                        style: "cursor:pointer; background:{bg}; padding:4px 8px; border-radius:4px;",
                        span { class: "font-mono text-sm", "{step.rule:?}" }
                        if !step.holds { span { style: "color:red;", " ✗" } }
                    }
                    for child_idx in &step.children {
                        ProofStepView { trace, index: *child_idx, depth: depth + 1 }
                    }
                }
            } else {
                div {
                    style: "background:{bg}; padding:4px 8px; border-radius:4px; margin:2px 0;",
                    "{step.rule:?}"
                }
            }
        }
    }
}
```

For `ProofRef` nodes (DAG back-references), render a clickable "↑ See step #N" link that scrolls to and highlights the referenced node.

**Phase 2** upgrades to SVG-based visualization using the **`rust-sugiyama`** crate for proper DAG layout (handles shared subproofs natively via Sugiyama's layered algorithm) and Dioxus's full SVG support in RSX. Dioxus renders SVG elements directly — `svg`, `circle`, `rect`, `line`, `path`, `text`, `g` are all available and compile-time checked. Compute layout positions in Rust, render as interactive SVG with click-to-collapse, color-coding by rule type (green for Asserted, blue for Derived, yellow for ProofRef, red for failed), and hover tooltips.

- **`rust-sugiyama`**: Full Sugiyama algorithm for directed graphs, accepts edge lists or `petgraph::StableDiGraph`, returns (x,y) coordinates + dimensions. Best for DAGs.
- **`reingold-tilford`** crate: Classic tree layout if treating proof as tree with back-reference markers. Returns `HashMap<Key, Coordinate>`.
- **`layout-rs`**: Full Graphviz-compatible layout + SVG rendering. Can generate complete SVG strings for quick results.

Color-code the 16 `ProofRule` variants: green shades for constructive rules (Asserted, Derived, Conjunction), blue for universal rules (ForallVerified, ForallVacuous), yellow for references (ProofRef), orange for existential rules (ExistsWitness), red for failures (ExistsFailed, ForallCounterexample). Auto-expand the first 3 levels, collapse deeper subtrees.

---

## 7. The two-row layout maps cleanly to CSS Grid + Tailwind

The layout — 85% main content with two columns (tabs + proof trace), 15% query bar — is CSS Grid with Tailwind classes:

```rust
fn App() -> Element {
    rsx! {
        document::Stylesheet { href: asset!("/assets/tailwind.css") }
        div { class: "flex flex-col h-screen",
            div { class: "flex-1 min-h-0 flex",                    // Row 1 (85%)
                div { class: "w-1/2 border-r overflow-hidden",     // Col 1a: Tabs
                    SourceTabs {}
                }
                div { class: "w-1/2 overflow-auto",                // Col 1b: Proof trace
                    ProofTracePanel {}
                }
            }
            div { class: "h-[15vh] border-t bg-gray-50 p-4",      // Row 2: Query bar
                QueryBar {}
            }
        }
    }
}
```

Tab navigation uses a signal-driven pattern with match-based content switching. For a draggable splitter, use CSS Grid with dynamic `grid-template-columns` driven by a signal updated via mouse event handlers.

For the Lojban editor, **start with a styled `<textarea>`** and plan CodeMirror 6 integration later. CodeMirror 6 is modular (~300KB core vs Monaco's 5-10MB), supports custom language modes (define Lojban tokenization via Lezer parser grammar), and integrates via `document::eval()` or `wasm-bindgen` JS module binding. Monaco is too large for an app already loading ~1.5MB of WASM.

---

## 8. Build pipeline with Nix, Justfile, and dx

The Nix flake needs `rust-overlay` for multi-target Rust toolchain, `dioxus-cli`, Node.js (for jco), and `binaryen` (for wasm-opt):

```nix
rustToolchain = pkgs.rust-bin.stable.latest.default.override {
    extensions = [ "rust-src" "rust-analyzer" ];
    targets = [ "wasm32-unknown-unknown" "wasm32-wasip2" ];
};
buildInputs = [
    rustToolchain
    pkgs.dioxus-cli pkgs.nodejs pkgs.wasm-bindgen-cli pkgs.binaryen
    pkgs.pkg-config pkgs.openssl  # build deps
    pkgs.glib pkgs.gtk3 pkgs.libsoup_3 pkgs.webkitgtk_4_1  # desktop deps
];
```

Install jco via npm in the shell hook: `npm list -g @bytecodealliance/jco || npm install -g @bytecodealliance/jco @bytecodealliance/preview2-shim`.

**Critical**: The `wasm-bindgen-cli` version must exactly match the `wasm-bindgen` version in `Cargo.lock`.

Justfile targets:

```makefile
web-serve:
    cd nibli-web && dx serve --platform web

web-build:
    cd nibli-web && dx build --release --platform web

desktop-serve:
    cd nibli-desktop && dx serve --platform desktop

transpile-engine:
    jco transpile target/wasm32-wasip2/release/nibli_engine.wasm \
        --optimize --valid-lifting-optimization --no-nodejs-compat \
        --instantiation async -o nibli-web/static/nibli-engine/
```

**Expected bundle size**: ~**500-700KB gzipped** total. Dioxus framework WASM compresses to ~60KB gzipped, the Nibli engine to ~300-400KB gzipped (WASM compresses well), jco JS glue adds ~15-20KB, the PHF dictionary ~30-50KB, and purged Tailwind CSS ~10-30KB.

Development workflow: `dx serve` provides instant RSX/CSS hot-reload (subsecond). `dx serve --hotpatch` enables experimental Rust logic hot-patching via the Subsecond system — function body changes apply without full rebuild or state loss. The jco transpile step only runs when the engine WASM changes, not on UI edits.

---

## 9. Workspace structure and the desktop-first question

**Keep the Dioxus app as a separate crate in the Nibli workspace.** The challenge is that existing crates target `wasm32-wasip2` while Dioxus needs `wasm32-unknown-unknown` — fundamentally incompatible compile targets. Solve with per-crate build configuration:

```
nibli/
├── nibli-core/              # Target-agnostic logic (parser, AST, error types)
├── nibli-engine/            # wasm32-wasip2 (cargo-component → wac plug)
├── smuni-dictionary/        # Shared PHF dictionary crate (no_std)
├── nibli-web/               # Dioxus web app (wasm32-unknown-unknown)
│   └── .cargo/config.toml   # [build] target = "wasm32-unknown-unknown"
└── nibli-desktop/           # Dioxus desktop app (native, uses Wasmtime directly)
```

`nibli-web` does **not** depend on `nibli-engine` as a Rust dependency — it loads the jco-transpiled (or wasm-bindgen-wrapped) engine at runtime. It **can** depend on `nibli-core` and `smuni-dictionary` for shared types and the PHF dictionary.

**Yes, start with Dioxus desktop.** The desktop target uses native Rust with a system webview, so you get native Wasmtime with full fuel/memory limits, the same RSX/component code, and no jco complexity. Build the UI interaction model (create session → assert → query → proof trace → retract), validate the proof visualization, tune the Ollama prompts, and perfect the back-translation. The web target can follow once the jco browser ecosystem matures or you've built the dual-target wasm-bindgen wrapper — either path reuses 95%+ of the UI code.

## Conclusion

The three highest-leverage decisions for this project are: **(1)** prototype on Dioxus desktop with native Wasmtime before tackling browser deployment, **(2)** factor the engine into a target-agnostic `nibli-core` crate that enables both the WASI P2 Wasmtime path and a future wasm-bindgen browser path, and **(3)** start proof visualization with the indented `<details>`/`<summary>` tree view — it's 50 lines of code and covers 90% of the use case.

The jco transpilation path is technically functional for composite WASI P2 components with WIT resources, and the double-boundary crossing (Dioxus WASM → JS → engine WASM) adds negligible overhead for your call frequency. But browser WASI shims remain experimental with no fuel metering, making the desktop-first or dual-target approach significantly lower risk. The Ollama integration, back-translation, and UI layout are all well-served by mature, production-ready tooling — reqwest for HTTP, PHF for the dictionary, Tailwind + Dioxus signals for the interface, and `rust-sugiyama` for eventual DAG visualization.