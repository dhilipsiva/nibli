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

Phase 0 foundation: `nibli-fanva` scaffolded as a workspace member (path deps),
`gates::local_gates` (gerna + smuni) + `GateError`/`feedback_for` with native
unit tests. `nibli-ui` not yet wired.

## Phase 0 — remainder

- Vendor the standard `camxes.js` (ilmentufa, MIT) into `nibli-fanva/js/vendor/camxes/` pinned to the repo's ilmentufa flake input (`NIBLI_CAMXES_DIR`) so there's one grammar source of truth; add a `camxes_shim.js` exposing `parse(text) -> {ok} | {ok:false,message,line,column}`, plus `VENDOR.md` + `NOTICE` (MIT attribution). Pick fanva's own LICENSE if distinct. Done when: the shim file + NOTICE exist and VENDOR.md records source commit + observed error shape.
- Add `nibli-fanva = { path = "../nibli-fanva" }` to `nibli-ui/Cargo.toml`. Done when: `cargo check -p nibli-ui` still builds.

## Phase 1 — LLM layer (multi-turn + tool-use), in `src/llm/`

- Port the provider client from `nibli-ui/src/llm.rs` (BYO key in a signal; direct-to-provider). Add `Role`/`ChatMessage`/`Provider`/`LlmConfig`, an async `chat(cfg, system, &[ChatMessage], &[ToolDecl]) -> ChatResponse` seam (trait or fn-pointer so native tests mock it), per-provider request builders, the extended system prompt (gerna-fragment cheat-sheet + few-shot + correction clause), and native request-shape tests. Then have `nibli-ui`'s single-shot translate delegate here. Done when: `cargo test -p nibli-fanva --lib providers` passes and nibli-ui builds against `nibli_fanva::llm`.

## Phase 2 — MCP client, in `src/mcp/`

- `McpClient` over Streamable-HTTP (gloo-net, wasm-only) → proxy: `initialize` (+ `notifications/initialized`), `tools/list` (cache schemas), `tools/call`; handle both `application/json` and SSE responses; echo `MCP-Protocol-Version` + any `Mcp-Session-Id`; `is_available()` for graceful degradation. Done when: a wasm test parses both a JSON and a mock-SSE result; with an empty proxy URL `is_available()` is false and nothing panics.

## Phase 3 — Provider tool-calling adapters

- Map each cached jbotci `inputSchema` → Anthropic/OpenAI/Gemini tool shape; parse tool calls (OpenAI `arguments` is stringified JSON — validate); submit tool results per provider; `run_llm_tool_loop(..., max_tool_steps)`. Done when: native tests map/parse a captured sample per provider into a normalized `ToolCall`, and a mocked-chat+mocked-mcp test drives one tool call then returns text.

## Phase 4 — Official gate + full validator, in `src/gates.rs`

- Add `official_gate(&str) -> Result<(), GateError>` calling the vendored camxes shim via `#[wasm_bindgen]` (fall back to `asset!()`+global bind if `dx` doesn't bundle lib-crate JS); map a parse failure → `GateError::Official{message,line,column}`. Add `validate(&str) -> Result<LogicBuffer, GateError>` = `local_gates` then `official_gate` (still all local — no `mcp` arg). Done when: a wasm-bindgen browser test asserts a grammatical string is Ok and an ungrammatical one is `GateError::Official`.

## Phase 5 — Agentic loop, in `src/agent.rs`

- `Attempt`/`Outcome`; `translate_agentic(cfg, english, mcp, max_attempts, max_tool_steps)` = outer validate/feedback loop around `run_llm_tool_loop`; oscillation guard; separate network-vs-gate errors; a missing/unreachable proxy ⇒ local gates only + degraded flag (never hard-fail); one `Attempt` trace per iteration. Done when: native mocked tests cover fail-once-then-pass ⇒ Success@2, always-fail ⇒ Exhausted@cap, oscillation early-stop, mcp-unavailable ⇒ local-only Success+degraded.

## Phase 6 — nibli-ui integration (the "Translate" mode)

- Upgrade nibli-ui's Source→Lojban Translate button to call `nibli_fanva::translate_agentic` via `spawn`; extend `LlmConfigModal` with an optional proxy URL + `max_attempts`/`max_tool_steps`; add a live trace panel (per attempt: candidate, jbotci tool calls, per-gate ✓/✗); Success/Exhausted/degraded states; jbotci-off banner when no proxy. Done when: `just ui` shows the mode self-correcting a wrong sentence to three green gates, and with no proxy DevTools shows only the provider endpoint.

## Phase 7 — Meaning check

- Primary: local `nibli_render::render_logic_buffer(&logic, Register::Spec)` gloss (already in nibli-ui). Optional richer view: jbotci `tersmu` graph when a proxy is set. Done when: the meaning panel renders the local gloss, plus the tersmu view when jbotci is available.

## Phase 8 — Hardening & docs

- System-prompt fragment seeding tuned for convergence; history trimming; proxy failure/429 UX; root `CLAUDE.md` gains a `nibli-fanva` row + `test-fanva`; `README`/transparency note; `just test-fanva` (+ wasm leg into `verify-wasm-node`/`ci-wasm`); `just count-tests` for any doc figure. Done when: `cargo test` + the wasm gate pass and docs are updated.

## Phase 9 — Deploy

- Ships via the existing nibli-ui playground path (dhilipsiva.dev/nibli-playground); optional separate `wrangler deploy` for the proxy with its allowed origin set to the app origin. Done when: hosted Translate mode works end-to-end (local gates always; jbotci when the proxy is configured).

## Optional — jbotci proxy (`fanva-proxy/`, workspace-excluded)

- Cloudflare Worker pass-through to `https://jbotci.app/mcp`: server-to-server fetch (drops browser Origin → 200), answers `OPTIONS` with the app's CORS headers, relays `Mcp-Session-Id`; light rate-limit; `wrangler deploy`. Add `"fanva-proxy"` to the root `Cargo.toml` `exclude` list. Done when: an `initialize` curl through the deployed proxy returns 200 + `serverInfo` + an `Access-Control-Allow-Origin` header.
