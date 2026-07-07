# fanva-proxy

A tiny Cloudflare Worker that fronts the **jbotci** MCP endpoint
(`https://jbotci.app/mcp`) so the [`nibli-fanva`](../nibli-fanva) browser client
(wasm/gloo-net) can reach it. Optional: the whole Transparency Triad stays
serverless by default; this proxy only matters when a user wants the agentic
translator to call jbotci's dictionary/grammar tools mid-translation.

## Why a proxy is needed

jbotci is not reachable directly from a browser:

| Probe (verified 2026-07-07) | Result |
|---|---|
| POST **without** `Origin` (server-to-server) | `200` + JSON-RPC `serverInfo` |
| POST **with** a browser `Origin` | `403 invalid Origin for MCP request` |
| `OPTIONS` preflight | `405` (jbotci has no CORS/preflight) |
| any response | **no** `Access-Control-*` headers |

So a browser fetch fails twice over — the `Origin` triggers a 403, and even a
200 would be unreadable without CORS. This Worker fixes both: it **strips the
browser `Origin`/`Host`/`Referer`** (jbotci then sees a plain server-to-server
call → 200) and **adds CORS** + synthesizes the preflight jbotci does not
implement.

## Not an open proxy

The upstream is a **hardcoded constant** — never derived from the request path,
query, or any header — so this is a fixed reverse proxy, not an SSRF/open relay.
It also ships with an IP-keyed rate-limit binding and a request-body size cap.

## Use it

1. Deploy it (see [DEPLOY.md](DEPLOY.md)) → `https://fanva-proxy.<acct>.workers.dev`.
2. In the nibli-ui settings modal, set the **jbotci proxy URL** to that Worker URL
   (e.g. `https://fanva-proxy.<acct>.workers.dev/mcp`). Leaving it blank keeps
   jbotci off — the translator then runs on the local gates only (`degraded`).

This directory is excluded from the Cargo workspace (it is a JS Worker, not a
crate) — see the root `Cargo.toml` `exclude` list.
