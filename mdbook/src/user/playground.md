# Playground

The Transparency Triad UI runs the full pipeline (**nibli-kr → nibli-semantics → nibli-reason**) **in the browser**. There is no nibli server.

<p><a href="https://dhilipsiva.dev/nibli-playground/"><strong>Open playground →</strong></a></p>

Local equivalent: `just ui` (Dioxus on port 8080). Ship path: [DEPLOY.md](https://github.com/dhilipsiva/nibli/blob/main/DEPLOY.md).

## Panes

| Pane | Role |
|------|------|
| **Source** | Plain English (optional Formalize input) |
| **nibli KR** | The knowledge base — formal claims the engine asserts |
| **Back-translation** | Structure-exposing gloss of the KR |

The **nibli KR pane is the knowledge base**. Each query rebuilds a fresh engine, re-asserts the KB, then runs the claim.

## Query model

**State a claim**, do not ask a question:

```text
eats(Adam).
```

The UI may show a decorative `?` next to the query box — it is **not** part of the text sent to the engine. Verdicts are `TRUE` / `FALSE` / `UNKNOWN` (see [guarantees](guarantees.md)).

## Formalize (optional)

**Formalize** (not “compile”) is a bring-your-own-key LLM step from the Source tab. The key stays in tab memory only; the request goes from your browser to the provider you choose. Drafts are checked by the real nibli-kr + nibli-semantics + render round-trip gates before they land in the KR pane. Formalize sits **outside** the deterministic reasoning core — always review the KR and back-translation.

## Example knowledge bases

The header dropdown loads preloaded KBs used in regression tests and demos (e.g. Syllogism, GDPR compliance, Drug interactions). Treat them as **example corpora**, not as chapters of any third-party book. In example mode the KR is read-only and Formalize is disabled; the query control becomes a preset list.

## Built-in vs external compute

In-browser: built-in arithmetic (`product` / `sum` / `quotient`) and ground numeric comparisons work locally. External compute backend predicates need the host + backend path (`just run-with-backend`) — not the pure playground.

## More

- [Quickstart](quickstart.md) for the CLI REPL
- [nibli KR cookbook](kr-cookbook.md) for syntax
- Product UI notes in the [README](https://github.com/dhilipsiva/nibli/blob/main/README.md)
