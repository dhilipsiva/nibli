# nibli-formalize

The **agentic English→KB formalizer engine** for the Transparency Triad
(`fanva` = Lojban "translate" — the crate name predates THE FLIP). An LLM
formalizes English into the KB language (**nibli KR** by default; legacy Lojban
behind the same `Language` seam); the real nibli compilers verify; errors are
fed back until the KB text is valid. Surfaced inside `nibli-ui` as the
**Formalize** mode (this crate holds no UI). "Formalize", never "compile": the
LLM step is interpretive and sits outside the reasoning firewall, behind the
deterministic gates below.

## The loop

An LLM drafts KB text — in legacy Lojban mode it may call jbotci's
dictionary/grammar tools *while drafting* — and every candidate must then clear
a three-gate, fail-fast, **local** firewall before it is accepted:

- **nibli KR** (default): `nibli_kr::parse_checked` (grammar + fail-closed name
  resolution) → `nibli-semantics` (semantics/arity) → the **render round-trip gate**
  (the candidate's canonical `nibli_kr::render` re-spelling must re-compile to
  the SAME `LogicBuffer` — nibli-kr's fixpoint contract as a per-candidate
  drift-catcher; pure Rust, runs native + wasm).
- **Lojban** (legacy): `nibli-kr::parse_checked` → `nibli-semantics` → the official
  **camxes** parser (wasm-only JS-interop; skipped on native / without the
  shim).

A rejection feeds the compiler's own message back (`gates::feedback_for`) and
the LLM retries, bounded by `max_attempts` with an oscillation guard. A
gate-clean candidate then faces the **semantic verification turn**
(`verify.rs`): a fresh-context judge reads the engine's own IR-level
back-translation of each KB line and a MISMATCH retries through the same loop
— best-effort advisory, fail-open. This is the **formalization** step
(`agent::translate_agentic`): it runs before the KB text is shown, and is
separate from the engine's own front-end→nibli-semantics→nibli-reason compile that `nibli-ui`
runs later, at query time.

```mermaid
flowchart TD
    src(["English source"]) --> disc{"legacy Lojban mode with<br/>jbotci enabled + proxy reachable?"}
    disc -->|"no / unreachable / nibli KR mode"| deg["no tools · run degraded<br/>(local gates only)"]
    disc -->|yes| have["discover jbotci tools once<br/>dictionary · grammar · morphology"]
    deg --> loop
    have --> loop

    loop{"attempt n ≤ max_attempts?"} -->|"no · cap reached"| exh["Exhausted<br/>best effort + last error"]
    loop -->|yes| gen

    subgraph turn["LLM turn — run_llm_tool_loop, up to max_tool_steps"]
      direction TB
      gen["LLM proposes candidate KB text"] --> tcq{"model called<br/>a jbotci tool?"}
      tcq -->|"yes · optional tool-use (Lojban mode)"| mcp["MCP call via the proxy<br/>vlacku · cukta · gentufa · vlasei · …<br/>result fed back to the model"]
      mcp --> gen
    end

    tcq -->|no| clean["clean_lojban_output → candidate"]

    clean -->|"per non-comment KB line"| g1{"gate 1 · front-end<br/>nibli-kr (default) / nibli-kr (legacy)<br/>parse_checked — grammar"}
    g1 -->|ok| g2{"gate 2 · nibli-semantics<br/>compile_from_ast — semantics / arity"}
    g2 -->|ok| g3{"gate 3 · per language<br/>nibli KR: render round-trip (native+wasm)<br/>Lojban: camxes official_gate (wasm-only)"}
    g3 -->|ok| ver{"semantic verification turn<br/>fresh-context judge reads the<br/>IR back-translation (advisory)"}
    ver -->|MATCH / fail-open| ok["Success<br/>validated KB text → KB tab<br/>(nibli-ui compiles the FOL later)"]

    g1 -->|reject| osc
    g2 -->|reject| osc
    g3 -->|reject| osc
    ver -->|MISMATCH| osc

    osc{"candidate same<br/>as previous attempt?"} -->|"yes · oscillation"| exh
    osc -->|"no · append feedback_for"| loop

    gen -.->|"provider / network / auth error"| cf["ChatFailed<br/>transport error, not an invalid KB"]

    classDef good fill:#1a7f37,stroke:#116329,color:#fff;
    classDef warn fill:#9a6700,stroke:#7d4e00,color:#fff;
    classDef bad fill:#cf222e,stroke:#a40e26,color:#fff;
    class ok good;
    class exh warn;
    class cf bad;
```

Gates 1–3 are `gates::local_gates` + `gates::validate`, all keyed on
`nibli_types::lang::Language`. jbotci (`vlacku`/`cukta`/`tersmu`/`gentufa`) is
**Lojban-only tooling**, optional even there — reached only through an
app-owned proxy — and used as LLM tools + the tersmu meaning view, never as a
required gate. No proxy (or nibli KR mode) ⇒ local gates only, fully serverless.

## Test discipline

- Local gates (both languages, incl. the round-trip gate) + provider/agent
  logic + the verification turn: native `cargo test -p nibli-formalize --lib`
  (`just test-formalize`) with mocked `chat()` / MCP; the two shipped system
  prompts are pinned by gate-validity guard tests over their few-shots.
- MCP client (gloo-net) + the camxes `official_gate` (JS-interop): wasm-only,
  covered by `wasm-pack test` (`just test-formalize-wasm`).
