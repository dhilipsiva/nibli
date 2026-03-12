# Transparency Triad UI — 10-Step Implementation Plan

## Context

Build a Dioxus **desktop** application ("Transparency Triad") that embeds the Nibli symbolic reasoning engine via native Wasmtime. The UI provides: (1) English→Lojban translation via Ollama, (2) robotic back-translation via jbovlaste dictionary, (3) interactive proof trace visualization. Desktop-first avoids all jco/browser WASI risk. The existing `gasnu/src/main.rs` Wasmtime integration pattern is the template.

**Architecture**: Dioxus desktop (native Rust + system webview via WRY) → Wasmtime embedding → existing `lasna-pipeline.wasm` (unchanged). New workspace crates: `nibli-ui/` (Dioxus app), `smuni-dictionary/` (shared PHF dictionary).

**Each step**: You give me the prompt → I implement with tests → you verify manually → we iterate → commit → next step.

---

## Step 1: Workspace Scaffolding + Nix Dev Shell + Empty Dioxus Window

### Goal
Create the `nibli-ui` Dioxus desktop crate, update the workspace, update `flake.nix` with Dioxus/GTK/WebKit dependencies, and display an empty window titled "Nibli — Transparency Triad".

### Non-Goals
- No engine integration yet
- No styling beyond confirming the window opens
- No Ollama, no dictionary, no tabs

### Implementation Details
1. **Create `nibli-ui/` crate** as a new workspace member:
   - `nibli-ui/Cargo.toml` — depends on `dioxus` with `desktop` feature
   - `nibli-ui/src/main.rs` — minimal `dioxus::launch(App)` with a placeholder `h1 { "Nibli — Transparency Triad" }`
2. **Update root `Cargo.toml`** — add `"nibli-ui"` to workspace members
3. **Update `flake.nix`** — add GTK3/WebKitGTK/libsoup/glib/cairo/pango/atk/gdk-pixbuf to `buildInputs` (Dioxus desktop on Linux needs these for WRY's WebKitGTK backend). Add `dioxus-cli` if available in nixpkgs, otherwise add instructions for `cargo install dioxus-cli`.
4. **Update `Justfile`** — add targets:
   - `ui`: `cargo run -p nibli-ui`
   - `ui-dev`: `dx serve` (if dx is available) or just `cargo run -p nibli-ui`
5. **Create `nibli-ui/Dioxus.toml`** — basic config with app name, desktop platform target

### Unit Tests
- `cargo check -p nibli-ui` compiles without errors
- `cargo test -p nibli-ui` passes (even if no tests yet — just confirms the crate links)

### Manual Acceptance Test
- Run `just ui` (or `cargo run -p nibli-ui`) inside the Nix dev shell
- A native window appears with the title "Nibli — Transparency Triad"
- The window shows "Nibli — Transparency Triad" as an h1 heading
- Window is resizable and closes cleanly on window close / Ctrl+C

### Key Files
- `nibli-ui/Cargo.toml` (new)
- `nibli-ui/src/main.rs` (new)
- `nibli-ui/Dioxus.toml` (new)
- `Cargo.toml` (workspace members edit)
- `flake.nix` (add desktop deps)
- `Justfile` (add `ui` target)

---

## Step 2: Two-Row Layout with Tabs (Static UI Shell)

### Goal
Implement the full layout skeleton: Row 1 (85% height, two columns — tabs on left, empty proof panel on right), Row 2 (15% height, query bar with text input and button). All tabs and panels are present but contain placeholder text. No functionality yet.

### Non-Goals
- No engine integration
- No Ollama calls
- No proof trace rendering
- No Tailwind (use inline styles or a single CSS file to keep it simple)

### Implementation Details
1. **App component** — CSS flexbox/grid layout:
   - Outer `div` with `display: flex; flex-direction: column; height: 100vh;`
   - Row 1: `flex: 1; display: flex;` containing two columns (50/50 split)
   - Row 2: `height: 15vh; border-top` containing input + button
2. **Column 1a (SourceTabs component)** — signal-driven tab state:
   - Three tabs: "Source", "Lojban", "Back-translation"
   - Tab bar with clickable tab headers, active tab highlighted
   - Tab content: "Source" shows a `textarea` + "Translate" button; "Lojban" shows a read-only text area; "Back-translation" shows a `pre` block
   - `use_signal(|| ActiveTab::Source)` drives which content renders
3. **Column 1b (ProofPanel component)** — placeholder:
   - Gray background with centered text "Run a query to see proof trace"
4. **Row 2 (QueryBar component)**:
   - Text input (full width minus button) + "Query" button
   - Input value tracked with `use_signal`
5. **Styling**: Use a `nibli-ui/assets/style.css` file linked via Dioxus asset system. Dark header bar, light content areas, monospace for Lojban text.

### Unit Tests
- `cargo check -p nibli-ui` compiles
- Test that `ActiveTab` enum has 3 variants: `Source`, `Lojban`, `BackTranslation`

### Manual Acceptance Test
- Window shows two-row layout filling the screen
- Top row has two columns; left column has 3 clickable tabs
- Clicking tabs switches content (Source shows textarea + button, Lojban shows read-only area, Back-translation shows placeholder)
- Bottom row has a text input and a "Query" button
- Right column shows "Run a query to see proof trace"
- Layout handles window resize (no overflow, no scroll on main container)

### Key Files
- `nibli-ui/src/main.rs` (layout + components)
- `nibli-ui/assets/style.css` (new)

---

## Step 3: Wasmtime Engine Embedding + Session Lifecycle

### Goal
Embed the Nibli engine via Wasmtime in the Dioxus app. On app startup, load `lasna-pipeline.wasm`, create a session, and store it in Dioxus context. Display engine status (Loading → Ready → Error) in the UI header.

### Non-Goals
- No assert/query commands yet (just init + status)
- No compute backend (skip TCP backend entirely — built-in arithmetic only)
- No Ollama

### Implementation Details
1. **Copy the Wasmtime setup pattern from `gasnu/src/main.rs` lines 373-435**:
   - `Config::new()` with `wasm_component_model(true)` and `consume_fuel(true)`
   - `Engine::new(&config)`
   - `Linker` with `wasmtime_wasi::p2::add_to_linker_sync`
   - `Store` with `HostState` (WasiCtx, ResourceTable, StoreLimits)
   - `Component::from_file(&engine, wasm_path)`
   - `LasnaPipeline::instantiate(&mut store, &component, &linker)`
   - `session.call_constructor(&mut store)`
2. **HostState struct** — simplified from gasnu (no TCP backend, no reedline):
   ```rust
   struct HostState {
       ctx: WasiCtx,
       table: ResourceTable,
       limits: StoreLimits,
   }
   ```
3. **Engine wrapper struct** — holds `Store<HostState>` + pipeline + session handle. Wraps call methods. Since Wasmtime Store is `!Send`, engine must live on the **main thread**. Use `use_hook` (not `use_resource` which is async) to initialize synchronously, or `use_signal` + `spawn` for async init on the main thread.
4. **Context provider** — `EngineState` signal injected via `use_context_provider`:
   ```rust
   enum EngineStatus { Loading, Ready, Error(String) }
   struct EngineState {
       status: Signal<EngineStatus>,
       engine: Signal<Option<NibliEngine>>,
   }
   ```
5. **WASM path** — `NIBLI_WASM_PATH` env var (read at startup), defaulting to `target/wasm32-wasip2/debug/lasna-pipeline.wasm`
6. **Fuel/memory** — defaults: 10 billion fuel, 512MB memory (same as gasnu)
7. **Status badge** — header bar shows "Loading...", "Ready", or "Error: ..." with color coding
8. **WIT bindings** — add `wasmtime` and `wasmtime-wasi` deps to `nibli-ui/Cargo.toml`. For the WIT-generated types, use the same `wasmtime::component::bindgen!` macro approach as gasnu (or reference gasnu's bindings module).

### Unit Tests
- Test `EngineStatus` enum serialization/display
- Test `NibliEngine::new(path)` returns `Ok` when given a valid wasm path (integration test — may skip if too heavy, rely on manual test)

### Manual Acceptance Test
- Run `just build-wasm && just ui` (build engine first, then UI)
- Window opens, header shows "Loading..." briefly, then "Ready" (green)
- If WASM file is missing, header shows "Error: ..." (red)
- No crash, no hang

### Key Files
- `nibli-ui/src/main.rs` (engine init + context)
- `nibli-ui/src/engine.rs` (new — NibliEngine wrapper)
- `nibli-ui/Cargo.toml` (add wasmtime, wasmtime-wasi deps)
- `gasnu/src/main.rs` (reference — copy patterns from here)

---

## Step 4: Assert + Query Commands via the Query Bar

### Goal
Wire the Query Bar (Row 2) to the engine. Bare text asserts facts; `?` prefix queries entailment (TRUE/FALSE); `?!` prefix queries with proof trace (result stored for Step 7). Display results in a status/output area.

### Non-Goals
- No proof trace visualization yet (just store the ProofTrace data)
- No `??` witness extraction yet
- No `:retract`, `:facts`, `:reset` commands yet

### Implementation Details
1. **Command routing** — parse input prefix (same logic as gasnu lines 548-778):
   - No prefix → `session.call_assert_text(&mut store, handle, text)` → show "Fact #N asserted"
   - `?` prefix → `session.call_query_text(&mut store, handle, text)` → show "TRUE" / "FALSE"
   - `?!` prefix → `session.call_query_text_with_proof(&mut store, handle, text)` → show "TRUE" / "FALSE", store `ProofTrace` in signal
2. **Output display** — add a scrollable output log below the query bar (or as a toast/status area):
   - Each command result appended: timestamp + input + result
   - Errors shown in red with structured formatting (syntax errors show line:column)
3. **Refueling** — call `store.set_fuel(budget)` before each command (same pattern as gasnu `refuel()`)
4. **NibliEngine methods**:
   ```rust
   impl NibliEngine {
       fn assert_text(&mut self, text: &str) -> Result<u64, NibliError>;
       fn query_text(&mut self, text: &str) -> Result<bool, NibliError>;
       fn query_with_proof(&mut self, text: &str) -> Result<(bool, ProofTrace), NibliError>;
   }
   ```
5. **State management** — `EngineState` gains:
   - `output_log: Signal<Vec<OutputEntry>>` — history of commands + results
   - `last_proof: Signal<Option<ProofTrace>>` — latest proof trace for visualization

### Unit Tests
- Test command prefix parsing: `"? gerku adam"` → Query, `"?! gerku adam"` → QueryWithProof, `"gerku adam"` → Assert
- Test `NibliError` formatting matches gasnu's `format_nibli_error`

### Manual Acceptance Test
- Type `lo gerku cu gerku` in query bar, press Enter/click Query → output shows "Fact #1 asserted"
- Type `? lo gerku cu gerku` → output shows "TRUE"
- Type `? lo mlatu cu mlatu` → output shows "FALSE"
- Type `invalid lojban here!!!` → output shows red "[Syntax Error] line 1:..."
- Type `?! lo gerku cu gerku` → output shows "TRUE" (proof trace stored internally, shown in Step 7)

### Key Files
- `nibli-ui/src/main.rs` (QueryBar wiring)
- `nibli-ui/src/engine.rs` (add assert/query methods)
- `nibli-ui/src/commands.rs` (new — command parsing + routing)

---

## Step 5: smuni-dictionary Crate + Robotic Back-Translation

### Goal
Extract the jbovlaste PHF dictionary into a shared `smuni-dictionary` crate. Build a word-by-word back-translator that runs in the Dioxus app. Wire it to the "Back-translation" tab — when Lojban text appears in the Lojban tab, the back-translation tab auto-updates.

### Non-Goals
- No grammar-aware parsing (just space-split word lookup)
- No Ollama yet (Lojban text will be manually entered for testing)
- No structure-aware back-translation (no s-expression parsing)

### Implementation Details
1. **Create `smuni-dictionary/` crate**:
   - `smuni-dictionary/Cargo.toml` — depends on `phf` (with `no_std` support)
   - `smuni-dictionary/build.rs` — extracted from `smuni/build.rs`, but generates a **richer** PHF map:
     - Key: word (String)
     - Value: `DictEntry { arity: usize, gloss: &'static str, word_type: WordType }` (not just arity)
     - Parse `<glossword>` tags for the primary English gloss
     - Parse `<keyword>` tags for per-place keywords
   - `smuni-dictionary/src/lib.rs` — exports `pub static DICTIONARY: phf::Map<&'static str, DictEntry>` + `pub fn back_translate(lojban: &str) -> String`
2. **Update `smuni/`** — depend on `smuni-dictionary` for arity lookups (replace inline PHF)
3. **Back-translation algorithm** (`back_translate` function):
   ```
   Input:  "lo gerku cu klama lo zarci"
   Output: "the dog [pred] go(the market)"
   ```
   - Split on whitespace
   - For each token:
     - If in DICTIONARY → use primary gloss (e.g., "gerku" → "dog", "klama" → "go")
     - If cmavo → hardcoded structural map (~60 entries: "lo" → "the", "cu" → "[pred]", "ro" → "every", ".i" → ".", "poi" → "which", "na" → "not", etc.)
     - If starts with `.` and ends with `.` → cmevla, pass through without dots (e.g., ".adam." → "adam")
     - Otherwise → pass through as-is
   - Join with spaces
4. **Wire to Dioxus** — `nibli-ui` depends on `smuni-dictionary`. When the Lojban signal updates, recompute back-translation and update the BackTranslation tab signal.

### Unit Tests (in `smuni-dictionary`)
- `back_translate("mi klama lo zarci")` → `"I go the market"` (or similar)
- `back_translate("lo gerku cu gerku")` → `"the dog [pred] dog"` (identity predication)
- `back_translate(".adam. prami .evas.")` → `"adam love evas"`
- `back_translate("")` → `""`
- Dictionary lookup: `DICTIONARY.get("klama").unwrap().arity == 5`
- Dictionary lookup: `DICTIONARY.get("gerku").unwrap().gloss == "dog"`

### Manual Acceptance Test
- Switch to "Lojban" tab, manually type `lo gerku cu klama lo zarci`
- Switch to "Back-translation" tab → shows `"the dog [pred] go(the market)"` (or similar word-by-word rendering)
- Back-translation updates live as Lojban text changes

### Key Files
- `smuni-dictionary/Cargo.toml` (new)
- `smuni-dictionary/build.rs` (new — extracted + extended from `smuni/build.rs`)
- `smuni-dictionary/src/lib.rs` (new)
- `smuni/Cargo.toml` (depend on smuni-dictionary)
- `smuni/build.rs` (simplified — delegate to smuni-dictionary)
- `nibli-ui/Cargo.toml` (depend on smuni-dictionary)
- `nibli-ui/src/main.rs` (wire back-translation to tab)

---

## Step 6: Ollama Integration (English → Lojban Translation)

### Goal
Wire the "Source" tab: user enters English text, clicks "Translate", an HTTP call goes to local Ollama, the Lojban translation populates the "Lojban" tab, and the back-translation auto-updates in the third tab.

### Non-Goals
- No streaming responses (use `"stream": false` for simplicity)
- No model selection UI (hardcode model name, configurable via env var)
- No prompt tuning UI (hardcode the system prompt)

### Implementation Details
1. **Add `reqwest` dependency** to `nibli-ui/Cargo.toml` (with `json` feature; native TLS for desktop)
2. **Ollama client module** (`nibli-ui/src/ollama.rs`):
   ```rust
   pub async fn translate_to_lojban(english: &str, base_url: &str, model: &str) -> Result<String, OllamaError> {
       let resp = reqwest::Client::new()
           .post(format!("{}/api/chat", base_url))
           .json(&ChatRequest {
               model: model.to_string(),
               messages: vec![
                   Message { role: "system", content: LOJBAN_SYSTEM_PROMPT },
                   Message { role: "user", content: format!("Translate to Lojban: {}", english) },
               ],
               stream: false,
               options: Options { temperature: 0.3 },
           })
           .send().await?
           .json::<ChatResponse>().await?;
       Ok(resp.message.content)
   }
   ```
3. **System prompt** — include Lojban bridi structure, place structure examples, gadri usage, 5-10 translation pairs. Store as `const LOJBAN_SYSTEM_PROMPT: &str`.
4. **Config** — env vars: `NIBLI_OLLAMA_URL` (default `http://localhost:11434`), `NIBLI_OLLAMA_MODEL` (default `llama3.2`)
5. **UI wiring**:
   - Source tab: textarea + "Translate" button
   - On click: `spawn` async task calling `translate_to_lojban`
   - While loading: button shows "Translating..." and is disabled
   - On success: update `lojban_text` signal → Lojban tab shows result → back-translation auto-computes
   - On error: show error toast (connection refused = "Is Ollama running?")
6. **Lojban tab** — the translated text is shown AND is editable (expert can correct). Edits update the signal, which triggers back-translation refresh.

### Unit Tests
- Test `ChatRequest` serialization matches Ollama API format
- Test `ChatResponse` deserialization from sample JSON
- Test system prompt is non-empty and contains key Lojban terms

### Manual Acceptance Test
- Start Ollama locally (`ollama serve`)
- Type "The dog goes to the market" in Source tab
- Click "Translate" → button shows "Translating..."
- After 2-5 seconds, Lojban tab shows a Lojban sentence (quality may vary)
- Back-translation tab immediately shows word-by-word English render
- Edit the Lojban in the Lojban tab → back-translation updates live
- With Ollama stopped: click Translate → error message "Connection refused — is Ollama running?"

### Key Files
- `nibli-ui/src/ollama.rs` (new)
- `nibli-ui/src/main.rs` (wire translate button)
- `nibli-ui/Cargo.toml` (add reqwest)

---

## Step 7: Proof Trace Visualization (Indented Tree)

### Goal
When a `?!` query returns a ProofTrace, render it as an interactive indented tree in Column 1b (the proof panel). Use `<details>/<summary>` HTML elements for expand/collapse. Color-code by rule type. Show s-expressions for leaf nodes.

### Non-Goals
- No SVG/canvas DAG visualization (that's a future enhancement)
- No Sugiyama layout algorithm
- No drag-to-pan or zoom

### Implementation Details
1. **ProofTracePanel component** — reads `last_proof: Signal<Option<ProofTrace>>` from context:
   - If `None` → show "Run a ?! query to see proof trace"
   - If `Some(trace)` → render `ProofStepView` starting from `trace.root`
2. **ProofStepView component** — recursive:
   ```rust
   #[component]
   fn ProofStepView(trace: ProofTrace, index: u32, depth: u32) -> Element {
       let step = &trace.steps[index as usize];
       let (bg_color, icon) = style_for_rule(&step.rule, step.holds);
       let label = format_rule_label(&step.rule);

       rsx! {
           div { style: "padding-left: {depth * 20}px;",
               if !step.children.is_empty() {
                   details { open: depth < 3,
                       summary { style: "background: {bg_color}; ...",
                           span { "{icon} {label}" }
                           if !step.holds { span { class: "failed", " FAILED" } }
                       }
                       for child in &step.children {
                           ProofStepView { trace: trace.clone(), index: *child, depth: depth + 1 }
                       }
                   }
               } else {
                   div { style: "background: {bg_color}; ...",
                       "{icon} {label}"
                   }
               }
           }
       }
   }
   ```
3. **Color scheme** (matching the 16 ProofRule variants):
   - Green: `Asserted`, `Conjunction` (when holds)
   - Blue: `Derived`, `ForallVerified`, `ForallVacuous`
   - Yellow/gold: `ProofRef` (memoized — shows "see above" link)
   - Orange: `ExistsWitness`, `ModalPassthrough`
   - Red: `ExistsFailed`, `ForallCounterexample`, any step where `holds == false`
   - Gray: `PredicateCheck`, `ComputeCheck`
4. **Rule label formatting** — human-readable descriptions:
   - `Asserted(sexp)` → "Fact: {sexp}"
   - `Derived((label, sexp))` → "Rule: {label} → {sexp}"
   - `Conjunction` → "AND (both must hold)"
   - `ExistsWitness((var, term))` → "Found {var} = {term}"
   - `ProofRef(sexp)` → "↑ Already proved: {sexp}"
   - etc.
5. **ProofRef handling** — render as a highlighted link. On click, scroll to and flash the first occurrence of that sexp in the tree (find the matching `Asserted` or `Derived` node).
6. **Auto-expand** — first 3 levels open by default, deeper levels collapsed

### Unit Tests
- Test `style_for_rule` returns correct colors for each ProofRule variant
- Test `format_rule_label` produces expected strings for each variant
- Test a synthetic ProofTrace with 5 nodes renders without panic

### Manual Acceptance Test
- Assert: `lo gerku cu gerku` then `ro lo gerku cu danlu`
- Query: `?! lo danlu cu danlu`
- Proof panel shows an indented tree with:
  - Root: ForallVerified (blue)
  - Children: Derived (blue) showing the rule application
  - Leaf: Asserted (green) showing the ground fact
- Clicking a collapsed node expands it
- Failed queries show red nodes
- ProofRef nodes show "↑ Already proved" with distinctive styling

### Key Files
- `nibli-ui/src/proof_view.rs` (new — ProofStepView + helpers)
- `nibli-ui/src/main.rs` (wire ProofTracePanel to context signal)
- `nibli-ui/assets/style.css` (proof tree styles)

---

## Step 8: Fact Management (List, Retract, Reset, Load)

### Goal
Add UI for knowledge base management: view asserted facts, retract individual facts, reset the KB, and load `.lojban` files. This completes the engine interaction surface.

### Non-Goals
- No `:compute` / `:backend` commands (no TCP backend in UI)
- No `:saturate` / run-bound configuration
- No drag-and-drop file loading

### Implementation Details
1. **Facts sidebar/panel** — add a collapsible panel (drawer) on the left side or as a tab in Column 1a:
   - Lists all active facts from `session.call_list_facts()`
   - Each fact shows: ID, label, root count
   - Each fact has a "Retract" button (with confirmation)
   - "Reset KB" button at the top (with confirmation dialog)
   - "Load File" button opens a file picker → reads `.lojban` file → asserts each line
2. **NibliEngine methods**:
   ```rust
   fn list_facts(&mut self) -> Result<Vec<FactSummary>, NibliError>;
   fn retract_fact(&mut self, id: u64) -> Result<(), NibliError>;
   fn reset_kb(&mut self) -> Result<(), NibliError>;
   fn load_file(&mut self, path: &Path) -> Vec<LoadResult>; // per-line results
   ```
3. **Auto-refresh** — after assert, retract, reset, or load: re-fetch fact list and update signal
4. **File loading** — reuse gasnu's line-by-line logic (skip blanks, skip `#` comments, refuel per line)
5. **Query bar extensions** — support `:retract <id>`, `:facts`, `:reset`, `:load <path>` as typed commands (in addition to UI buttons)

### Unit Tests
- Test file loading parser: blank lines skipped, `#` comments skipped, non-empty lines returned
- Test `:retract 5` parses as `Retract(5)`
- Test `:load readme.lojban` parses as `LoadFile("readme.lojban")`

### Manual Acceptance Test
- Assert several facts via query bar
- Open facts panel → all facts listed with IDs
- Click "Retract" on one → fact disappears from list, subsequent queries reflect retraction
- Click "Reset KB" → confirmation → all facts gone
- Click "Load File" → select `readme.lojban` → facts loaded with per-line status
- Type `:facts` in query bar → fact list refreshes

### Key Files
- `nibli-ui/src/engine.rs` (add fact management methods)
- `nibli-ui/src/commands.rs` (extend command parser)
- `nibli-ui/src/facts_panel.rs` (new)
- `nibli-ui/src/main.rs` (integrate facts panel)

---

## Step 9: Polish — Styling, Keyboard Shortcuts, Error UX

### Goal
Polish the UI for daily use: consistent styling, keyboard shortcuts (Enter to submit, Ctrl+Enter for newline in textarea), proper error display, loading states, and responsive layout.

### Non-Goals
- No dark mode (defer)
- No i18n
- No user preferences persistence

### Implementation Details
1. **Styling pass**:
   - Consistent color palette: dark header (#1a1a2e), light content (#f5f5f5), accent (#e94560)
   - Monospace font for all Lojban text (JetBrains Mono or system monospace)
   - Tab bar: pill-style active indicator
   - Query bar: terminal-like dark background, green text
   - Proof tree: subtle indentation guides (left border lines)
   - Status badges: green "Ready", red "Error", yellow "Loading"
2. **Keyboard shortcuts**:
   - `Enter` in query bar → submit command
   - `Shift+Enter` in query bar → newline (if multi-line mode needed)
   - `Ctrl+L` → clear output log
   - `Ctrl+R` → reset KB (with confirmation)
   - `Ctrl+O` → load file dialog
3. **Error UX**:
   - Syntax errors: highlight line:column in the Lojban text if the error came from the Lojban tab content
   - Semantic errors: show in output with icon
   - Reasoning errors: show with "Search limit reached" explanation
   - Fuel exhaustion: show "[Limit] Computation exceeded fuel budget" with suggestion to increase via `:fuel`
4. **Loading states**:
   - Engine init: full-screen loader with Nibli logo
   - Ollama translation: spinner on the Translate button
   - Query execution: brief spinner in proof panel
5. **Output log** — scrollable with auto-scroll-to-bottom, max 500 entries, clear button

### Unit Tests
- Test keyboard shortcut mapping
- Test error formatting for each NibliError variant
- Test output log truncation at 500 entries

### Manual Acceptance Test
- App looks visually cohesive (no raw HTML feel)
- Enter in query bar submits immediately
- Errors are clearly distinguishable (red, with icons)
- Proof tree is readable with clear indentation guides
- Loading spinners appear during async operations
- No visual glitches on resize

### Key Files
- `nibli-ui/assets/style.css` (major overhaul)
- `nibli-ui/src/main.rs` (keyboard event handlers)
- `nibli-ui/src/components/` (refactor into component files if needed)

---

## Step 10: Integration Test + Documentation + Justfile Targets

### Goal
End-to-end integration test: English → Translate → Lojban → Back-translate → Assert → Query → Proof Trace. Update all documentation. Add complete Justfile targets.

### Non-Goals
- No CI/CD setup
- No web target (deferred)
- No automated E2E tests (manual verification is the acceptance test)

### Implementation Details
1. **Justfile targets** (final set):
   ```makefile
   ui:          cargo run -p nibli-ui
   ui-release:  cargo build --release -p nibli-ui && ./target/release/nibli-ui
   ui-check:    cargo check -p nibli-ui
   ui-test:     cargo test -p nibli-ui --lib -- --nocapture
   dict-test:   cargo test -p smuni-dictionary --lib -- --nocapture
   ```
2. **CLAUDE.md updates**:
   - Add `nibli-ui` and `smuni-dictionary` to architecture table
   - Update workspace members list
   - Add UI-related Justfile commands
   - Update Current Status with Transparency Triad milestone
3. **README.md updates**:
   - Add Transparency Triad UI section
   - Screenshots (if applicable)
   - Quick start: `just build-wasm && just ui`
4. **todo.md updates** — mark Transparency Triad as completed, add deferred items (web target, dark mode, streaming Ollama, SVG proof visualization)
5. **Integration walkthrough test script** — document the full manual test:
   1. `just build-wasm` → engine WASM builds
   2. `ollama serve` → Ollama running
   3. `just ui` → app opens, shows "Ready"
   4. Type English → Translate → Lojban appears → back-translation appears
   5. Assert the Lojban (copy to query bar, or auto-assert button)
   6. Query with `?!` → proof trace renders in right panel
   7. Retract a fact → re-query → proof changes
   8. Load `readme.lojban` → large KB populated
   9. Complex multi-hop query → deep proof tree with expand/collapse

### Unit Tests
- All existing tests still pass (`just test`)
- `cargo test -p smuni-dictionary` passes
- `cargo test -p nibli-ui` passes

### Manual Acceptance Test
- Full walkthrough of the 9-step integration test above
- All documentation files updated and accurate
- `just ui` works from a fresh `nix develop` shell

### Key Files
- `Justfile` (final targets)
- `CLAUDE.md` (architecture + status update)
- `README.md` (UI section)
- `todo.md` (milestone tracking)

---

## Dependency Graph

```
Step 1 (scaffold) ──► Step 2 (layout) ──► Step 3 (engine) ──► Step 4 (assert/query)
                                                │
Step 5 (dictionary) ◄──────────────────────────►│
                                                │
                      Step 6 (ollama) ◄─────────┤
                                                │
                      Step 7 (proof viz) ◄──────┤
                                                │
                      Step 8 (fact mgmt) ◄──────┘
                                                │
                      Step 9 (polish) ◄─────────┤
                                                │
                      Step 10 (docs) ◄──────────┘
```

Steps 5 and 6 can potentially be done in parallel with Steps 3-4, but for the linear feedback-loop workflow, the ordering above is recommended.
