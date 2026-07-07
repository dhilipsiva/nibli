# nibli-fanva — backlog (absorbed into the Transparency Triad)

Workspace-adapted from the standalone `fanva` research backlog. The original
fine-grained sub-steps for Phases 1–9 remain a useful reference at
`~/projects/dhilipsiva/fanva/TODO.md`; the bullets below apply the absorption
deltas (path deps, nibli-ui mode, jbotci optional). Work the **first unchecked
bullet**; remove an item when fully done, or narrow it if partial.

## Ground truth / do-not-drift

- **Path deps, not git pins.** `gerna`/`smuni`/`nibli-types` (+ `nibli-render`/`smuni-dictionary` when the meaning view lands) are workspace path deps — no `<PIN>`/`NIBLI_REV`, no `nibli-types` dedup concern.
- **Verified upstream API** (see `README.md` table): `gerna::parse_checked(&str) -> Result<AstBuffer, NibliError>`; `smuni::compile_from_gerna_ast(AstBuffer) -> Result<LogicBuffer, NibliError>`; `NibliError` has **4** variants (Syntax/Semantic/Reasoning/Backend); `nibli_render::render_logic_buffer(&LogicBuffer, Register::Spec) -> String` and `smuni_dictionary::back_translate(&str) -> String` both exist (used in `nibli-ui/src/main.rs`).
- **Success gate = all three local gates pass:** gerna ∧ smuni ∧ camxes(official). gerna is the narrowest → the binding constraint → `max_attempts` caps runaway cost.
- **jbotci is optional/degradable.** MCP client points at a configurable proxy URL that may be empty ⇒ `is_available()==false` ⇒ no tool-use, no tersmu, local gates only. Keeps the Triad serverless by default.
- **jbotci facts:** MCP Streamable-HTTP at `https://jbotci.app/mcp`, protocol `2025-06-18`; 7 tools discovered via `tools/list` (do NOT hardcode schemas); jbotci **403s any cross-origin browser** (Origin allowlist) → the proxy is the only browser path. `gentufa` stays an LLM tool, NOT the validator gate (that's local camxes).
- **Provider tool-calling** shapes differ (Anthropic `tool_use`/`tool_result`; OpenAI/OpenRouter `tool_calls`/`role:"tool"`, `arguments` is stringified JSON; Gemini `functionCall`/`functionResponse`, assistant role `"model"`). Full detail in `~/projects/dhilipsiva/fanva/TODO.md` ground-truth header.

## Already landed in this crate

- **Phase 0 foundation:** `nibli-fanva` scaffolded as a workspace member (path deps); `gates::local_gates` (gerna + smuni) + `GateError`/`feedback_for` with native unit tests.
- **Phase 1 core — multi-turn LLM layer (`src/llm/`):** `Provider`/`LlmConfig`/`Turn` (types.rs); provider-agnostic `build_chat_request` for all 5 providers (multi-turn; per-provider `system` placement; Gemini assistant→`"model"`); `extract_text`/`clean_lojban_output` (response.rs); the iterative-correction system prompt. 7 native tests (request shapes + extraction). Pure/native-testable; no I/O yet.
- **Chat seam + agent-loop core (Phases 1/5):** the `Chat` async trait + `ChatError` (`src/llm/mod.rs`); `gates::validate`; `agent::translate_agentic` with `Attempt`/`Outcome`, attempt cap, oscillation guard, and provider-error (`ChatFailed`) handling. 4 native tests via a mock `Chat` (fail-once→Success@2, never-valid→Exhausted@cap, oscillation→early Exhausted, provider-error→ChatFailed).
- **Phase 1 complete — wasm `Chat` transport:** `llm::HttpChat` (`src/llm/http.rs`, wasm-only via gloo-net) ports nibli-ui's send + status classification into `ChatError`; target-gated so native tests stay mock-only. Verified: native `cargo test` (14) green AND `cargo build -p nibli-fanva --target wasm32-unknown-unknown` compiles.
- **nibli-ui prep:** `gates::validate_kb` (line-by-line KB validation, tagging the failing KB line) — the agent now validates multi-line KBs, not just single sentences; `HttpChat` refactored to exist on all targets (native stub, gloo-net wasm-only) so `nibli-ui` type-checks under `cargo check --workspace`. 16 native tests + wasm build green.
- **Phase 6 core — nibli-ui Translate mode:** the Source→Lojban button runs the agentic loop (`translate_agentic` + `HttpChat` + local gates) with a per-attempt self-correction trace; Success fills the Lojban tab, Exhausted shows best-effort + last error, ChatFailed shows the transport error. `CLAUDE.md` Architecture table updated with the `nibli-fanva` row. Verified: `cargo check --workspace` (native) + `cargo check -p nibli-ui --target wasm32-unknown-unknown` (wasm) both green. Live end-to-end pending a user API-key run of `just ui`.
- **Phase 4 — camxes "official" gate:** vendored ilmentufa standard `camxes.js` + `camxes_preproc.js` + a `camxes_shim.js` (`window.camxes_validate`) served by nibli-ui (`document::Script`+`asset!()`); `gates::official_gate` (wasm-only, synchronous js-sys) folded into `validate`, so the success gate is `gerna ∧ smuni ∧ camxes` (degrades to the local two when the shim is absent). 3 wasm marshalling tests (`just test-fanva-wasm`); native 16 unaffected; both wasm checks green. Real engine verified in-browser via `just ui`.
- **Phase 2 — jbotci MCP client (`src/mcp/`):** `McpClient` over Streamable-HTTP to a configurable proxy URL (`initialize`+`notifications/initialized`/`tools/list`/`tools/call`; JSON-or-SSE bodies; `MCP-Protocol-Version` + `Mcp-Session-Id` echo; 404→session reset); pure `wire`/`types` (native-tested) + a wasm-only gloo-net transport with a native `Unavailable` stub; `is_available()` degrades when the proxy URL is empty; discovered tools cached for Phase 3. 8 native tests (JSON + mock-SSE parse, 7-tool `tools/list`, tool-call text/isError, empty-URL degrade) → 24 total; wasm check + clippy clean.
- **Phase 3 — provider tool-calling adapters (`src/llm/` + `src/tools.rs`):** `Turn` gained `AssistantTools`/`ToolResults`; `build_chat_request_tools` declares tools + serializes tool turns per provider (Anthropic `tool_use`/`tool_result`, OpenAI `tool_calls` with stringified `arguments` + `role:"tool"`, Gemini `functionCall`/`functionResponse` by name); `parse_chat_response` normalizes tool calls (OpenAI args `JSON.parse`d, Gemini id synthesized); a `ToolChat` seam (`HttpChat` impls it); `tools::run_llm_tool_loop` (+ `ToolRunner`, `to_tool_decls`, `impl ToolRunner for McpClient`). 7 native tests (schema/turn shapes ×3, tool-call parse ×3, loop with mocked chat+runner) → 31 total; clippy-clean; wasm check green.
- **Phase 5 — tool loop threaded into `translate_agentic`:** each attempt gets its candidate via `tools::run_llm_tool_loop` (the model may call jbotci tools) instead of a single `Chat::chat`; a missing/unreachable proxy ⇒ no tools ⇒ local gates only, with a `degraded: bool` on every `Outcome`. `nibli-ui` passes `McpClient::new("")` (empty proxy) so behavior is unchanged until Phase 6 adds the URL field. 1 new native test (mcp-unavailable → Success + degraded) → 32 total; workspace + wasm-ui checks + clippy clean.
- **Phase 6 config surface + degraded banner:** the settings modal gained an optional **jbotci proxy URL** + a **max attempts** field (on nibli-ui's `LlmConfig`); `do_translate` builds `McpClient::new(cfg.proxy_url)` and passes `cfg.max_attempts`; a one-line **"jbotci off" banner** (reads `Outcome.degraded`) shows when no/unreachable proxy. Native workspace + wasm-ui checks green; no new clippy warnings; nibli-fanva 32 tests still pass.
- **Phase 6 trace polish:** per-attempt **per-gate chips** (`gerna ✓ smuni ✓ camxes ✗`, derived in nibli-ui from `Attempt.error`) + **jbotci tool-call sub-rows** (`run_llm_tool_loop` now returns the tool calls made → `Attempt.tool_calls`; rendered when a proxy is set). nibli-fanva 32 tests green (tool-loop trace asserted); workspace + wasm-ui + clippy clean.
- **`llm.rs` single-sourcing cleanup:** `nibli-ui/src/llm.rs` deleted; `nibli_fanva::llm` (`LlmConfig`/`Provider`/`HttpChat`/`clean_lojban_output`/`system_prompt`) is now the single source of truth for the LLM client. nibli-ui holds a thin `Settings { llm: LlmConfig, proxy_url, max_attempts }` wrapper; the query translate + modal key-test go through a small `fanva_translate` shim over `HttpChat`. Workspace + wasm-ui checks green; no new clippy warnings; nibli-fanva 32 tests still pass.
- **jbotci proxy Worker (`fanva-proxy/`, workspace-excluded):** a Cloudflare Worker that fronts `https://jbotci.app/mcp` — strips the browser `Origin`/`Host`/`Referer` (jbotci 403s any Origin) and adds CORS + synthesizes the preflight jbotci 405s. Hardcoded upstream (no SSRF), IP-keyed rate-limit binding (shipped active, graceful when absent), 256 KiB body cap, buffered request body (correct `Content-Length`, not chunked), faithful status pass-through, response-body streaming (SSE-safe). Config-driven CORS allowlist (`ALLOWED_ORIGINS`, default `https://dhilipsiva.dev`; `.dev.vars` for localhost). Locally verified end-to-end against LIVE jbotci via `wrangler dev`: initialize-through-proxy → 200 + `serverInfo` + ACAO; preflight → 204; disallowed origin → 200 with no ACAO leak. `Cargo.toml` `exclude` updated. Ships with `DEPLOY.md` + `README.md`; the only remaining step is the operator's `wrangler deploy` (needs their Cloudflare account).
- All backlog items landed. Remaining is out-of-scope of this crate: the operator's `wrangler deploy` of the proxy, and the future Phase 7–9 polish (meaning-view tersmu, hardening, hosting) if pursued.

## Phase 0 — remainder

- Vendor the standard `camxes.js` (ilmentufa, MIT) into `nibli-fanva/js/vendor/camxes/` pinned to the repo's ilmentufa flake input (`NIBLI_CAMXES_DIR`) so there's one grammar source of truth; add a `camxes_shim.js` exposing `parse(text) -> {ok} | {ok:false,message,line,column}`, plus `VENDOR.md` + `NOTICE` (MIT attribution). Pick fanva's own LICENSE if distinct. Done when: the shim file + NOTICE exist and VENDOR.md records source commit + observed error shape.
- Add `nibli-fanva = { path = "../nibli-fanva" }` to `nibli-ui/Cargo.toml`. Done when: `cargo check -p nibli-ui` still builds.

## Phase 1 — LLM layer: COMPLETE

Remaining pieces were reassigned to later phases:
- tool DECLARATION in the request builders + tool-call turns → **Phase 3** (folded into the tool-calling adapters so tools land end-to-end).
- `nibli-ui`'s translate delegating to `nibli_fanva::llm` (and using `HttpChat`) → **Phase 6**.
- larger few-shot set / gerna-fragment cheat-sheet in the system prompt → **Phase 8** (after convergence is measured).

## Phase 2 — MCP client — DONE (see "Already landed")

- Built as `src/mcp/{types,wire,mod}.rs`: pure JSON-RPC/SSE parsing (`wire`, native-tested) + a wasm-only `McpClient::rpc` transport (native stub returns `Unavailable`). Tools from `tools/list` are cached (`McpClient::tools()`) for Phase 3 to map into provider tool schemas.

## Phase 3 — Provider tool-calling adapters — DONE (see "Already landed")

- Built in `src/llm/{types,request,response}.rs` + `src/llm/mod.rs` (`ToolChat`) + `src/llm/http.rs` (`HttpChat: ToolChat`) + `src/tools.rs` (`run_llm_tool_loop`, `ToolRunner`, `impl ToolRunner for McpClient`, `to_tool_decls`). Phase 5 threads `run_llm_tool_loop` into `translate_agentic`.

## Phase 4 — Official gate + full validator — DONE (see "Already landed")

- Implemented as **synchronous js-sys**, not `#[wasm_bindgen(module=…)]` (which `dx` can't bundle): nibli-ui serves the vendored camxes via `document::Script`+`asset!()` exposing `window.camxes_validate`; `gates::official_gate` reads it and folds into `validate`. Degrades to `Ok` when the shim is absent. The trace already shows a `camxes` badge via `GateError::gate()`.

## Phase 5 — Agentic loop — DONE (see "Already landed")

- `translate_agentic<C: ToolChat>(chat, mcp, cfg, source, max_attempts, max_tool_steps)` discovers tools once (degrade if unavailable), runs `run_llm_tool_loop` per attempt, and carries `degraded` on `Outcome`. The one call site (`nibli-ui`) + the agent tests were updated.

## Phase 6 — nibli-ui integration — DONE (see "Already landed")

- Fully landed, including the single-sourcing cleanup: `nibli-ui/src/llm.rs` is gone and `nibli_fanva::llm` is the sole LLM client.

## Phase 7 — Meaning check

- Primary: local `nibli_render::render_logic_buffer(&logic, Register::Spec)` gloss (already in nibli-ui). Optional richer view: jbotci `tersmu` graph when a proxy is set. Done when: the meaning panel renders the local gloss, plus the tersmu view when jbotci is available.

## Phase 8 — Hardening & docs

- System-prompt fragment seeding tuned for convergence; history trimming; proxy failure/429 UX; root `CLAUDE.md` gains a `nibli-fanva` row + `test-fanva`; `README`/transparency note; `just test-fanva` (+ wasm leg into `verify-wasm-node`/`ci-wasm`); `just count-tests` for any doc figure. Done when: `cargo test` + the wasm gate pass and docs are updated.

## Phase 9 — Deploy

- Ships via the existing nibli-ui playground path (dhilipsiva.dev/nibli-playground); optional separate `wrangler deploy` for the proxy with its allowed origin set to the app origin. Done when: hosted Translate mode works end-to-end (local gates always; jbotci when the proxy is configured).

## Optional — jbotci proxy (`fanva-proxy/`, workspace-excluded) — BUILT (see "Already landed")

- The Worker + `wrangler.toml` + `DEPLOY.md`/`README.md` exist and are locally verified against live jbotci (200 + `serverInfo` + ACAO; 204 preflight; no ACAO leak for a disallowed origin). Root `Cargo.toml` `exclude` updated. The one remaining step is the operator running `wrangler deploy` (their Cloudflare account) and setting the deployed `ALLOWED_ORIGINS`.
