# Research & Planning Prompt — Agentic Lojban Translator with first-class jbotci integration

> **How to use this file:** Paste the prompt below into a capable research/coding agent
> (Claude Code, a deep-research harness, etc.) **from inside the new, empty repo** where you
> intend to build the tool. Its job is to research the open questions, verify every technical
> claim against live sources, and emit a single **`TODO.md`** broken into phases where every item
> is a concrete, independently-shippable step. You then drive the build one item at a time (see the
> companion `fanva-todo` skill).

---

## PROMPT (everything below the line is the instruction to the agent)

---

You are setting up a brand-new project: an **agentic English→Lojban translator** that self-corrects
using real Lojban compilers AND the **jbotci** Lojban toolkit (https://jbotci.app/mcp), which it
integrates as a first-class citizen. Your deliverable for THIS task is a single **`TODO.md`** — a
phased, richly-detailed implementation backlog. Do **not** write app code yet; produce the plan the
developer will execute item-by-item.

### What the product does

1. The user types English and picks an LLM provider (bring-your-own API key, held in memory only).
2. The app asks the LLM to translate to Lojban. During translation the LLM has **live access to the
   jbotci MCP tools** (dictionary, reference grammar, parser, semantics) and may call them to look
   up words/place-structure, check grammar rules, test-parse drafts, and verify meaning — an
   agentic tool-use loop, not a single shot.
3. When the LLM emits a candidate translation, the app **validates it through three gates**:
   - `gerna::parse_checked` — engine grammar (local WASM)
   - `nibli_semantics::compile_from_gerna_ast` — engine semantics/arity (local WASM)
   - jbotci **`gentufa`** — the *official* Lojban grammar parser (remote, via the proxy)
4. If any gate fails, the app appends the failing compiler's error to the **conversation history**
   and asks the LLM to fix it. Loop until **all three gates pass** (or a max-attempt cap is hit).
5. On success, the app shows the valid Lojban **plus a meaning check** — jbotci **`tersmu`** (deep
   logical-meaning graph) and/or the local `nibli-render` gloss — so the human verifies the meaning,
   not just the grammar.

The frontend is Dioxus/WASM in the browser. Because jbotci blocks cross-origin browser calls (see
below), a **tiny app-owned proxy** relays MCP traffic. The only other network egress is the LLM call.

### Grounding facts — VERIFIED against live endpoints (treat as authoritative; re-verify anything you change)

**jbotci MCP server** — `https://jbotci.app/mcp`, MCP protocol `2025-06-18`, Streamable-HTTP
transport (JSON-RPC over POST; responses are `application/json`). `serverInfo`: `{name: "jbotci",
version: "0.1.0"}`, capabilities `tools` + `resources`. Handshake that works from a non-browser
client:
```
POST https://jbotci.app/mcp
Content-Type: application/json
Accept: application/json, text/event-stream
{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"fanva","version":"0.1.0"}}}
```
then `tools/list`, then `tools/call`. (No `Mcp-Session-Id` was issued in probing; assume stateless
POST-per-call but handle a session header if one appears.)

**⚠ CORS / origin block (the reason a proxy is required):** jbotci enforces an **origin allowlist**.
Probed behavior: `initialize` returns **200 with no `Origin` header**, **200 with `Origin:
https://jbotci.app`**, but **403 Forbidden with any other `Origin`** — and it returns **no
`Access-Control-Allow-Origin`**. A browser always sends `Origin`, so **direct browser→jbotci calls
are blocked**. The proxy (server-to-server fetch, which sends no browser `Origin`) reaches jbotci at
200 and adds CORS headers so the browser can call the proxy.

**jbotci tools (7)** — every tool defaults to readable text/markdown; pass `format: "json"` where
available when you need machine-parseable output (`tersmu` is always JSON):

| Tool | Purpose | Key params |
|------|---------|-----------|
| `gentufa` | **Parse a sentence's grammar** — authoritative syntax tree; THE official grammar gate. | `text` (req), `format` (tree/…/json), `dialect`, `show-defs`, `show-refs`, `show-spans`, `decompose-lujvo`, `indent` |
| `tersmu` | **Deep semantics** — logical-meaning JSON graph (referents, predications, eventualities, formulas). Meaning check / back-translation. | `text` (req), `dialect`, `story-time`, `indent` |
| `vlacku` | **Dictionary lookup** (jbovlaste): definition, **place structure (arity!)**, rafsi, glosses, notes. Helps the LLM pick correct words + get arity right for the smuni gate. | `query` (req), `mode` (word/rafsi/lujvo/sound/meaning), `count`, `word-types`, `min-votes`, `min-similarity`, `decompose-lujvo`, `show-etymology` |
| `cukta` | **CLL reference grammar** — search/read *The Complete Lojban Language* for rules & examples. Lets the LLM cite a rule when fixing an error. | `mode` (meaning/word/section/example/toc), `query`, `count`, `search-result-kinds`, `format` (markdown/html/raw) |
| `vlasei` | **Morphology** — split text into words and classify each (gismu/cmavo/lujvo/…). | `text` (req), `format` (tree/brackets/ipa/raw/json), `dialect`, `show-spans`, `decompose-lujvo`, `indent` |
| `jvozba` | **Build a lujvo/cmevla** from source parts (rafsi selection + hyphenation). | `mode` (lujvo/cmevla), `parts[]` ({kind: word/fixed-rafsi, value}) |
| `gimfihi` | **Coin candidate gismu** from source-language words. | `sources`, `preset`, `shapes`, `check-collisions`, `count`, `format`, … |

> Discover these at runtime via `tools/list` rather than hardcoding — the `inputSchema` of each tool
> is a JSON Schema you will map into each LLM provider's tool/function-declaration format.

**nibli crates (git deps; same repo, pin ALL to one rev so shared `nibli-types` dedups):**
```toml
[dependencies]
dioxus     = { version = "0.7.3", features = ["web"] }
gloo-net   = { version = "0.6",   features = ["http"] }
serde_json = "1"
gerna            = { git = "https://github.com/dhilipsiva/nibli", package = "gerna",            rev = "<PIN>" }
smuni            = { git = "https://github.com/dhilipsiva/nibli", package = "smuni",            rev = "<PIN>" }
nibli-render     = { git = "https://github.com/dhilipsiva/nibli", package = "nibli-render",     rev = "<PIN>" }
nibli-lexicon = { git = "https://github.com/dhilipsiva/nibli", package = "nibli-lexicon", rev = "<PIN>" }
```
- `gerna::parse_checked(&str) -> Result<AstBuffer, NibliError>` — fail-closed; `NibliError::Syntax(SyntaxDetail{message,line,column})`, `Display` = `"[Syntax Error] line L:C: msg"`.
- `nibli_semantics::compile_from_gerna_ast(AstBuffer) -> Result<LogicBuffer, NibliError>` — by value; `NibliError::Semantic(String)`.
- `nibli_render::render_logic_buffer(&LogicBuffer, nibli_render::Register::Spec) -> String`; `nibli_lexicon::back_translate(&str)` fallback.
- Both compile to `wasm32-unknown-unknown` (pure Rust). **Dictionary caveat:** `nibli-lexicon`'s `build.rs` reads a gitignored `dictionary-en.json`; via a plain git dep it falls back to a curated ~140-entry table, so smuni's *arity* checking is strongest for common vocab. For full-vocab arity, use a **path dep against a local clone** and run its `just fetch-dict`. (Note jbotci `vlacku` also provides authoritative place structure at runtime — lean on it.)

**Reference LLM client to port + generalize:** `nibli-ui/src/llm.rs` (upstream) implements a BYO-key
client for **Anthropic / OpenAI / OpenRouter / Google Gemini / Custom** over `gloo-net`, currently
single-shot. Generalize it to (a) **multi-turn** `chat(cfg, system, &[ChatMessage])` and (b)
**tool-use** — declare jbotci tools and handle tool calls. Per-provider quirks: Gemini's assistant
role is `"model"`; system prompt placement differs (Anthropic top-level `system`; OpenAI-family
first `system` message; Gemini `systemInstruction`). Keep `max_tokens`, no `temperature`, and the
transparency guarantee (key only in a Dioxus signal, request straight to the provider).

### Architecture

- **`fanva-ui`** — Dioxus WASM app (fork nibli-ui's masthead, `LlmConfigModal`, provider picker,
  `assets/tokens.css` + `style.css`). Contains: the LLM client (multi-turn + tool-use), an **MCP
  client** (`initialize`/`tools/list`/`tools/call` over Streamable-HTTP, pointed at the proxy), the
  **three-gate validator**, and the two-loop **agent**.
- **`fanva-proxy`** — a tiny app-owned pass-through (Cloudflare Worker / Vercel or Deno edge fn,
  ~30–60 lines). Accepts the browser's MCP JSON-RPC POST, forwards it to `https://jbotci.app/mcp`
  **server-to-server** (no browser `Origin` → 200), returns the response with
  `Access-Control-Allow-Origin` for the app's origin. Stateless; no secrets (jbotci is open).
  Consider light rate-limiting.

**Two nested loops:**
```
outer (max_attempts):
  candidate = inner_llm_tool_loop(cfg, SYSTEM_PROMPT, convo, jbotci_tools, mcp, max_tool_steps)
  #   inner: send messages+tools; while the LLM returns tool calls →
  #          execute each via mcp.call_tool(...) (through the proxy) → append results → resend;
  #          when the LLM returns plain text, that's the candidate.
  match validate(mcp, candidate):        # gerna → smuni → gentufa (fail-fast, local first)
    all pass  → DONE (+ tersmu / nibli-render meaning check)
    any fail  → convo += [assistant: candidate, user: "<gate> reported: <err> — fix it"]; loop
```

### Known risks to design around (call these out in the TODO)

- **`gerna` is a *fragment*** of official Lojban; with the strict gate the LLM must hit the
  intersection of gerna-acceptable ∧ smuni-compilable ∧ gentufa-acceptable. Since gerna is narrowest
  it's the binding constraint. Mitigate: hard attempt cap (return best-effort), oscillation guard
  (stop if output repeats), and **seed the system prompt with the supported fragment + known-good
  few-shot examples**. Giving the LLM `cukta`/`vlacku`/`gentufa` tools materially improves
  convergence — that's the point of the integration.
- **jbotci reachability.** Everything jbotci depends on the proxy being up. Design graceful
  degradation: if the proxy/jbotci is unreachable, fall back to the local gerna+smuni gate and
  disable jbotci tool-use, surfacing a clear banner (don't hard-fail the whole app).
- **`gentufa` failure shape.** Determine (by probing) exactly how `gentufa` signals an *invalid*
  parse — an MCP error, or a success payload whose tree/text indicates failure — so the gate can
  reliably distinguish pass/fail and extract a useful message. This is a required research item.
- **Cost & latency.** Every attempt is an LLM round-trip plus possibly several jbotci tool calls.
  Cap both `max_attempts` (outer) and `max_tool_steps` (inner); expose them; consider trimming
  history.
- **CORS.** Anthropic browser calls need `anthropic-dangerous-direct-browser-access: true`; some
  providers block browser origins entirely (surface as a network error); the jbotci proxy handles
  jbotci's own block.

### What to research / verify before writing the TODO

Verify (don't assume) and cite where it matters:
- **Probe `gentufa` and `tersmu`** live (via a local proxy or non-browser client): the exact
  request params, the JSON shape of a *successful* parse vs an *invalid* input, and how errors
  surface. Same for `vlacku` (place-structure field) since the LLM will lean on it.
- **MCP client details:** whether jbotci needs the `notifications/initialized` step, whether a
  session header ever appears, and the response content type (`application/json` seen in probing;
  handle SSE too).
- **Per-provider tool-calling payloads** for Anthropic (`tools`/`tool_use`/`tool_result`), OpenAI &
  OpenRouter & Custom (`tools`/`tool_calls`/`role:"tool"`), and Gemini
  (`functionDeclarations`/`functionCall`/`functionResponse`) — current field names and how to map a
  JSON-Schema `inputSchema` into each.
- **Proxy platform:** pick one (Cloudflare Workers / Vercel Edge / Deno Deploy), its fetch + CORS
  API, local dev, and deploy. Confirm a server-to-server fetch to jbotci returns 200 (no `Origin`).
- **Dioxus 0.7** patterns: `use_signal`, `spawn`/async handlers, `asset!()`, `dx serve`/`dx build`.
- **`gloo-net`** POST with custom headers in WASM; **`wasm-pack test --node`** for WASM tests;
  confirm the validator + agent (with a mocked `chat` and a mocked MCP client) unit-test on native.
- Re-confirm the nibli API signatures above against the pinned rev.

### Deliverable format — `TODO.md`

Produce **one `TODO.md`** with:

- **Phases with clear headers.** Suggested skeleton (adapt as research dictates; cover all of it):
  - **Phase 0 — Repo, toolchain, proxy:** scaffold `fanva-ui`; `Cargo.toml` git deps (pinned rev);
    `dx` toolchain + wasm build; scaffold & **deploy `fanva-proxy`**; confirm proxy→jbotci `initialize`
    returns 200 and the browser→proxy call is CORS-clean; dictionary git-dep-vs-clone decision.
  - **Phase 1 — LLM layer (multi-turn):** port `llm.rs`; `Role`/`ChatMessage`; `chat()` +
    per-provider request builder; extended system prompt (fragment cheat-sheet + correction clause);
    request-shape unit tests.
  - **Phase 2 — MCP client:** `initialize`/`tools/list`/`tools/call` over Streamable-HTTP against the
    proxy; tool discovery + schema caching; a thin typed wrapper per tool used (`gentufa`, `tersmu`,
    `vlacku`, `cukta`); graceful-degradation flag when unreachable.
  - **Phase 3 — Provider tool-calling adapters:** map jbotci `inputSchema` → each provider's tool
    format; parse tool calls; submit tool results; the inner `run_llm_tool_loop` with `max_tool_steps`.
  - **Phase 4 — Three-gate validator:** async `validate()` = `parse_checked` → `compile_from_gerna_ast`
    → `gentufa` (fail-fast, local first); `GateError{Syntax,Semantic,Official}`; `feedback_for()`;
    native tests (good & bad inputs, mocked MCP).
  - **Phase 5 — Agentic loop:** outer `translate_agentic()` wrapping the inner tool loop + the gate;
    `Attempt`/`Outcome`; caps; oscillation guard; network-vs-gate error separation; mocked tests.
  - **Phase 6 — Dioxus UI:** masthead, config modal (add proxy URL + caps), source box; **live trace
    panel** showing each attempt, each **jbotci tool call (tool, args, result)**, and the per-gate
    pass/✗; result / exhausted states; spinner; wire via `spawn`.
  - **Phase 7 — Meaning check:** `tersmu` graph + `nibli-render` gloss side-by-side.
  - **Phase 8 — Hardening & docs:** fragment-seeding, history trimming, proxy rate-limit + failure
    UX, README + transparency note, `wasm-pack` test gate.
  - **Phase 9 — Deploy:** release wasm build + static hosting for `fanva-ui`; deploy `fanva-proxy`;
    per-provider CORS notes.
- **Every item is a plain bullet** (`- `), never numbered; cross-reference items by their text.
- **Every item is self-contained** (target file, function/signature, specific behavior) so a
  developer — or a one-item-at-a-time agent — can execute it without re-reading this prompt. Prefer
  many small items (one logical commit each) over few big ones.
- **Every item ends with a `Done when:`** concrete, checkable acceptance criterion (a passing test
  name, a command that succeeds, an observable UI behavior, a curl against the proxy).
- **Order items** so the first unchecked bullet in each phase is the next actionable one
  (dependencies earlier). Note items that can run in parallel.
- Put a **"Ground truth / do-not-drift"** header at the top of `TODO.md` capturing: the pinned nibli
  rev; the verified nibli API signatures; the jbotci endpoint, protocol version, the CORS/403
  finding, and the 7 tool names + the params you actually verified. So later items don't hallucinate.

Output the full `TODO.md`. If probing shows any grounding fact above is stale, correct it in the
TODO and flag what changed.
