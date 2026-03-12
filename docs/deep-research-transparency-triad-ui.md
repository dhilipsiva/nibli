# Deep Research Prompt: Building the Transparency Triad UI

## Context

This prompt is for deep-researching the architecture, tooling, and implementation strategy for building a **Transparency Triad UI** — a web-first Dioxus (Rust) application that embeds the Nibli symbolic reasoning engine (a WASI P2 WASM Component Model binary) and provides an interactive compliance/reasoning workbench.

---

## The Prompt

---

### Deep Research: Building a Dioxus Web Application That Embeds a WASI P2 WASM Component Model Engine with Ollama-Powered Translation

I am building a web-first UI in **Dioxus** (Rust's React-like framework) that embeds a **symbolic reasoning engine compiled to WASI P2 WASM Component Model** format. The engine is ~867KB (release), built with `cargo-component` targeting `wasm32-wasip2`, and fused from 4 sub-components using `wac plug`. The host currently runs via Wasmtime (native). I need to bring this to the browser.

Please research the following areas thoroughly and provide concrete, actionable findings with code examples where possible.

---

#### 1. Dioxus Web Platform — Current State (2025-2026)

- What is the current recommended way to create a **Dioxus web** application? (`dx` CLI vs `trunk` vs manual setup)
- What Dioxus version should I target? (0.6.x stable vs latest)
- How does Dioxus web rendering work? (Does it use `wasm-bindgen` + virtual DOM → real DOM? Or `web-sys` directly?)
- What is the Dioxus project structure for a web app? (`Dioxus.toml`, `assets/`, `src/main.rs` with `launch(app)`)
- How does Dioxus handle **async operations** in web? (e.g., `use_future`, `use_coroutine`, `spawn` for calling Ollama HTTP API and running WASM engine operations that may take time)
- How does Dioxus handle **state management** for complex apps? (signals, contexts, global state for the knowledge base session)
- What CSS/styling approach works best with Dioxus web? (Tailwind CSS integration? Inline styles? CSS modules?)
- How does Dioxus handle **tab components** and **split-pane layouts**? Are there community component libraries, or do I build from scratch?

---

#### 2. WASI P2 Component Model in the Browser — The `jco` Transpilation Path

This is the most critical and least-documented area. My engine is a **WASI P2 Component Model** binary (NOT a plain `wasm32-unknown-unknown` module). It uses WIT interfaces, resources, and typed error variants.

- **How does `jco` (JavaScript Component Objects) work?** What does `jco transpile my-component.wasm -o output/` produce? (JS wrapper + core WASM?)
- **Can a `jco`-transpiled WASI P2 component be called from Rust/WASM (Dioxus) in the browser?** Or does `jco` only produce JavaScript bindings? If JS-only, how do I call into it from Dioxus (via `web-sys` / `js-sys` / `wasm-bindgen` FFI)?
- **WIT resource types in the browser**: My engine exposes `resource session { constructor(); assert-text(...); query-text-with-proof(...); ... }`. How do WIT resources map after `jco` transpilation? Do they become JS classes? Can I hold a session handle across multiple calls?
- **Alternative: `wasmtime` in the browser?** Is there a way to run Wasmtime itself compiled to WASM (`wasm32-unknown-unknown`) to host WASI P2 components? (I've seen `wasmtime` has experimental web support.) Pros/cons vs `jco`?
- **Alternative: Compile the engine directly to `wasm32-unknown-unknown`?** Could I bypass the Component Model entirely for the web target and compile the Rust crates (gerna, smuni, logji, lasna) as a single `wasm-bindgen` library? What would I lose? (Component isolation, typed WIT interfaces, but gain simpler browser integration.)
- **WASI P2 shims in the browser**: My component uses `stdout`/`stderr` for diagnostic prints. What WASI shims does `jco` provide? Does `console.log` get wired up automatically?
- **Memory and fuel limits**: In native Wasmtime, I use `StoreLimits` for memory caps and `consume_fuel` for instruction budgets. Are these available after `jco` transpilation? Or do I need a different mechanism for resource limiting in the browser?
- **Performance**: What is the overhead of the `jco` JS wrapper layer? Is there measurable latency for each cross-boundary call? For my use case, each user action triggers 1-3 engine calls (assert, query, proof trace).

---

#### 3. Embedding the Engine in Dioxus — Architecture Patterns

Given the engine interaction model (create session → assert facts → query with proof → retract → re-query), research:

- **Initialization pattern**: How to load and initialize the WASM engine once at app startup and share the session across components? (Dioxus context provider? Global signal? `use_resource` with `OnceCell`?)
- **Async engine calls**: Engine operations (especially proof trace queries on large KBs) can take 10-100ms. How to run these without blocking the UI? (`spawn_blocking` equivalent in Dioxus web? Web Workers?)
- **Web Workers for engine isolation**: Can I run the WASM engine in a Web Worker to keep the main thread responsive? How would Dioxus communicate with a Web Worker? (Message passing via `postMessage`? Shared memory?)
- **Error display**: The engine returns structured errors (`nibli-error` variant with syntax/semantic/reasoning/backend categories, syntax errors include line:column). Best Dioxus patterns for displaying structured errors inline.

---

#### 4. Ollama Integration — Local LLM Translation

The UI's "Source Text" tab accepts English. Clicking "Translate" calls a local Ollama instance to translate English → Lojban.

- **Ollama HTTP API**: What is the current API format? (`POST http://localhost:11434/api/generate` with model, prompt, stream params?) What models are best for English→Lojban translation? (Likely needs a custom system prompt with Lojban grammar examples.)
- **Calling HTTP from Dioxus web**: How to make `fetch` calls from Dioxus? (`reqwest` with WASM feature? `gloo-net`? Raw `web-sys::Request`?)
- **CORS considerations**: Ollama runs on `localhost:11434`. The Dioxus app runs on `localhost:8080` (or similar). Will CORS block the request? Does Ollama set `Access-Control-Allow-Origin`? Do I need a proxy?
- **Streaming responses**: Ollama supports streaming (`"stream": true`). Should I stream the translation to show progressive output, or wait for the complete response? How does Dioxus handle streaming data updates?
- **Prompt engineering for Lojban translation**: What system prompt produces reasonable Lojban output from current models? The translation quality is outside the firewall (verified by the back-translation tab), so it doesn't need to be perfect — just close enough for the expert to verify and correct.

---

#### 5. Robotic Back-Translation — Jbovlaste Dictionary Lookup

After the Lojban text appears in tab 2, tab 3 immediately shows a "robotic back-translation" — a mechanical, non-grammatical English rendering using the jbovlaste dictionary. Example: `mi klama lo zarci` → `go(I, market)` or `act-of-going(me, market)`.

- **Dictionary data available**: The project has `jbovlaste-en.xml` (10MB) with entries like:
  ```xml
  <valsi word="klama" type="gismu">
    <definition>$x_1$ comes/goes to destination $x_2$ from origin $x_3$ via route $x_4$ using means/vehicle $x_5$.</definition>
    <glossword word="come" /><glossword word="go" />
    <keyword word="goer" place="1" /><keyword word="destination" place="2" />
  </valsi>
  ```
  Each entry has: word, type (gismu/cmavo/lujvo), definition with place structure (`$x_1$`...`$x_N$`), glosswords (English equivalents), keywords per place, rafsi (affixes), and notes.

- **Back-translation algorithm**: Given tokenized Lojban, for each content word (gismu/lujvo), look up its primary glossword or first keyword. For cmavo, map to structural notation (e.g., `lo` → `the`, `ro` → `every`, `cu` → `[pred]`, `poi` → `which`, `.i` → `[sentence]`). For cmevla (names), pass through. Compose as `predicate(arg1, arg2, ...)` notation. This does NOT need grammatical English — just enough for an expert to verify the encoding.

- **Where to run the back-translator**: Should this run:
  (a) **In the Nibli WASM engine** as a new WIT method? (Would need to add a `back-translate` function to the `session` resource.)
  (b) **In the Dioxus app itself** (Rust compiled to `wasm32-unknown-unknown`) with the jbovlaste dictionary embedded at compile time (same PHF approach as smuni)?
  (c) **As a JavaScript module** alongside the jco-transpiled engine?

  Option (b) seems best — it's pure Rust, runs client-side, and can reuse the existing `smuni/build.rs` PHF dictionary generation pattern. Research how to share the PHF dictionary between the smuni WASI component and the Dioxus web app (separate build? shared crate?).

- **Parsing Lojban for back-translation**: The engine's `gerna` component already tokenizes and parses Lojban. Can I use `compile-debug` (which returns s-expression FOL output) as the basis for back-translation? Or should I tokenize independently in the Dioxus app?

---

#### 6. Proof Trace Visualization — Tree/DAG Rendering

The engine produces a `ProofTrace` — a flat vector of `ProofStep` nodes with a root index. Each step has a `ProofRule` variant, a `holds: bool`, and `children: list<u32>` indices. With memoization, the structure is a DAG (directed acyclic graph), not a pure tree — `ProofRef` nodes reference previously-proved sub-proofs.

The 16 proof rule variants are:
- `Conjunction` — both conjuncts checked
- `DisjunctionCheck(s)` / `DisjunctionIntro(side)` — disjunction
- `Negation` — inner failed, so negation succeeded
- `ModalPassthrough(kind)` — tense/deontic wrapper (e.g., "Past", "Obligatory")
- `ExistsWitness((var, term))` / `ExistsFailed` — existential quantifier
- `ForallVacuous` / `ForallVerified(entities)` / `ForallCounterexample(term)` — universal
- `CountResult((expected, actual))` — numeric count
- `PredicateCheck((method, detail))` — leaf predicate check
- `ComputeCheck((method, relation))` — external compute dispatch
- `Asserted(sexp)` — ground truth (leaf node)
- `Derived((label, sexp))` — backward-chaining rule application
- `ProofRef(sexp)` — memoized reference ("proved above")

Research:

- **Tree/graph visualization in Dioxus web**: What libraries or approaches exist for rendering interactive tree diagrams in a Dioxus web app? Options:
  (a) **SVG rendering** via Dioxus RSX (manually position nodes and draw edges)
  (b) **Canvas-based** (use `web-sys::CanvasRenderingContext2d`)
  (c) **D3.js integration** via `web-sys` / `js-sys` interop
  (d) **A Rust graph layout library** (e.g., `layout-rs`, `petgraph` layout algorithms) that computes positions, then render with SVG in Dioxus

- **Collapsible tree UX**: Proof traces can be large (50-200 nodes for multi-hop derivations). The UI should support:
  - Expand/collapse nodes (click to expand children)
  - Color-coding by rule type (green for Asserted, blue for Derived, yellow for ProofRef, red for failed)
  - Hover for details (s-expression, rule label)
  - "Proved above" links (ProofRef) that scroll/highlight the original proof

- **DAG handling**: ProofRef creates shared sub-trees. How to render a DAG as a tree with back-references? (Render the first occurrence as a full subtree, subsequent occurrences as clickable "see above" links?)

- **Layout algorithms**: For a proof tree with 10-100 nodes, what layout algorithm works well? (Reingold-Tilford for trees? Sugiyama for DAGs? Simple indented list like the current REPL output?)

---

#### 7. UI Layout — Two-Row Split with Tabs

The layout specification:

```
┌─────────────────────────────────────────────────────────┐
│ ROW 1 (takes ~85% of screen height)                     │
│ ┌──────────────────────┬────────────────────────────────┐│
│ │ Column 1a            │ Column 1b                      ││
│ │                      │                                ││
│ │ [Source] [Lojban]    │ Proof Trace Diagram            ││
│ │ [Back-translation]   │ (empty until query)            ││
│ │                      │                                ││
│ │ ┌──────────────────┐ │ ┌────────────────────────────┐ ││
│ │ │ Tab content area │ │ │                            │ ││
│ │ │                  │ │ │  Tree/DAG visualization    │ ││
│ │ │ Source: textarea │ │ │  of proof trace            │ ││
│ │ │ + [Translate] btn│ │ │                            │ ││
│ │ │                  │ │ │                            │ ││
│ │ │ Lojban: readonly │ │ │                            │ ││
│ │ │ text display     │ │ │                            │ ││
│ │ │                  │ │ │                            │ ││
│ │ │ Back-trans: auto │ │ │                            │ ││
│ │ │ robotic render   │ │ │                            │ ││
│ │ └──────────────────┘ │ └────────────────────────────┘ ││
│ └──────────────────────┴────────────────────────────────┘│
├─────────────────────────────────────────────────────────┤
│ ROW 2 (~15% height) — Query Bar                         │
│ ┌───────────────────────────────────────────┬──────────┐│
│ │ [Lojban query input field              ]  │ [Query]  ││
│ └───────────────────────────────────────────┴──────────┘│
└─────────────────────────────────────────────────────────┘
```

**Interaction flow:**
1. User enters English in Source tab → clicks [Translate] → Ollama translates to Lojban (shown in Lojban tab) → back-translation auto-renders in third tab
2. User can edit Lojban directly in the Lojban tab (expert mode)
3. User clicks [Assert] (or it auto-asserts) to load Lojban into the engine
4. User types a Lojban query in Row 2 → clicks [Query] → proof trace appears in Column 1b
5. Column 1b shows the proof trace as an interactive tree/DAG diagram

Research:
- **Dioxus layout**: How to create a responsive two-row layout with resizable split panes in Dioxus web? CSS Grid? Flexbox? A Dioxus-compatible split-pane component?
- **Tab component in Dioxus**: Best practice for tab navigation? (Signal-based active tab state, conditional rendering of tab content)
- **Textarea with syntax highlighting**: For the Lojban tab, is there a way to add basic syntax coloring (gismu in one color, cmavo in another) in a Dioxus textarea? Or use a code editor component (Monaco/CodeMirror via JS interop)?
- **Responsive design**: Should this target desktop-only (compliance officers at workstations), or also tablet (hospital nurses)?

---

#### 8. Build Pipeline and Tooling

Research the complete build pipeline needed:

- **Nix flake additions**: What Nix packages are needed for: Dioxus CLI (`dx`), `jco`, `nodejs`/`npm`, Trunk (if used), Tailwind CSS (if used)?
- **Justfile targets**: What new targets are needed? Suggested:
  - `web-build`: Build Nibli WASM components + jco transpile + Dioxus web build
  - `web-serve`: Development server with hot-reload
  - `web-release`: Optimized production build
- **Development workflow**: What does the edit-compile-preview cycle look like? How fast is Dioxus web hot-reload? Does `dx serve` support watching Rust file changes?
- **Bundle size**: What is the expected total bundle size? (Nibli WASM ~867KB + Dioxus framework + jbovlaste dictionary PHF + jco runtime)

---

#### 9. Key Open Questions

- **Should the Dioxus app be a separate crate in the Nibli workspace, or a separate repository?** (Workspace member seems cleaner for shared dictionary code.)
- **Can `jco` transpile a composite (wac-fused) WASI P2 component, or does it need individual components?**
- **Is there a Dioxus desktop target** that could use native Wasmtime (avoiding the jco transpilation entirely) for a desktop-first prototype?
- **How mature is `jco` for production use?** (Version, known limitations, browser compatibility)
- **Are there any existing projects that combine Dioxus + WASI P2 components in the browser?** (Precedent?)

---

### Additional Context

The Nibli engine's WIT interface (`wit/world.wit`) defines these key types the UI must handle:

```wit
// Session resource (main API)
resource session {
    constructor();
    assert-text: func(input: string) -> result<fact-id, nibli-error>;
    query-text: func(input: string) -> result<bool, nibli-error>;
    query-text-with-proof: func(input: string) -> result<tuple<bool, proof-trace>, nibli-error>;
    compile-debug: func(input: string) -> result<string, nibli-error>;
    retract-fact: func(id: fact-id) -> result<_, nibli-error>;
    list-facts: func() -> result<list<fact-summary>, nibli-error>;
}

// Proof trace types
record proof-trace { steps: list<proof-step>, root: u32 }
record proof-step { rule: proof-rule, holds: bool, children: list<u32> }
variant proof-rule { /* 16 variants: Conjunction, Derived, Asserted, ProofRef, etc. */ }

// Structured errors
variant nibli-error { syntax(syntax-detail), semantic(string), reasoning(string), backend(tuple<string, string>) }
record syntax-detail { message: string, line: u32, column: u32 }
```

The current native host (`gasnu`) uses Wasmtime with: `WasiCtxBuilder::new().inherit_stdout().inherit_stderr().build()` — components get only stdout/stderr, no filesystem, no network, no env vars.

The `jbovlaste-en.xml` dictionary has ~1,527 gismu/lujvo entries with definitions, glosswords, per-place keywords, and rafsi. The build script (`smuni/build.rs`) already parses this into a compile-time PHF map for arity lookup.

---

*Research priority order: Section 2 (jco/WASI in browser) is the highest-risk unknown. Section 6 (proof visualization) is the most complex UI challenge. Section 4 (Ollama) and Section 5 (back-translation) are straightforward but need concrete API patterns.*
