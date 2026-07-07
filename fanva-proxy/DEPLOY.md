# fanva-proxy — Deploy Runbook

A Cloudflare Worker that fronts the jbotci MCP endpoint (`https://jbotci.app/mcp`)
so the nibli-fanva browser client (wasm/gloo-net) can reach it. It adds CORS,
synthesizes the preflight jbotci does not implement, and strips the browser
`Origin`/`Host`/`Referer` so jbotci sees a plain server-to-server call. The
upstream is **hardcoded** — never user-controllable — so this is a fixed reverse
proxy, not an open/SSRF proxy.

## 1. Prerequisites

- Node.js 18+ and npm on PATH.
- A Cloudflare account (`npx wrangler login`) for `deploy` only. Local dev needs no login.

## 2. Install

```sh
npm install
```

## 3. Verify locally (`wrangler dev`)

`wrangler dev` runs `src/index.js` directly in workerd/miniflare; the outbound
`fetch` to jbotci uses real network egress, so the acceptance test hits the live
server. Start it (non-interactive) in the background:

```sh
CI=1 WRANGLER_SEND_METRICS=false npx wrangler dev --port 8787 &
# wait until the local port answers the (locally-synthesized) preflight — no
# upstream needed just to know the server is up:
until [ "$(curl -s -o /dev/null -w '%{http_code}' -X OPTIONS http://localhost:8787/ \
  -H 'Origin: https://dhilipsiva.dev' -H 'access-control-request-method: POST')" = 204 ]; do
  sleep 1
done
```

**Acceptance test** — an `initialize` **through** the proxy must return `200` + a
JSON-RPC `serverInfo` body + an `Access-Control-Allow-Origin` header. This asserts
(not just prints) so a regression fails loudly:

```sh
curl -s -D /tmp/fanva_h -o /tmp/fanva_b -X POST http://localhost:8787/mcp \
  -H 'Origin: https://dhilipsiva.dev' \
  -H 'content-type: application/json' \
  -H 'accept: application/json, text/event-stream' \
  -H 'mcp-protocol-version: 2025-06-18' \
  -d '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"curl","version":"0"}}}'
grep -qi '^access-control-allow-origin: https://dhilipsiva.dev' /tmp/fanva_h \
  && grep -q serverInfo /tmp/fanva_b \
  && echo "ACCEPT: 200 + serverInfo + ACAO OK" || { echo "FAIL"; exit 1; }
# A success WITH the Origin header present proves the proxy stripped it upstream
# (jbotci 403s any request that carries an Origin).
```

Stop the dev server when done (kill the whole process group so workerd is not orphaned):

```sh
pkill -f 'wrangler dev' || true
```

## 4. Deploy

```sh
npx wrangler login      # first time only
npm run deploy          # -> https://fanva-proxy.<acct>.workers.dev
```

`wrangler.toml` pins **no `account_id`** — wrangler infers it from the logged-in
account. If your `wrangler` is logged into **more than one** Cloudflare account,
deploy will prompt (or fail non-interactively); set the account explicitly:

```sh
CLOUDFLARE_ACCOUNT_ID=<your-account-id> npm run deploy
```

(or add `account_id = "<...>"` to `wrangler.toml`).

## 5. Configure

- **CORS allowlist (`ALLOWED_ORIGINS`):** edit `[vars]` in `wrangler.toml`
  (comma-separated exact origins, or `*` to echo any) and redeploy, or set it in
  the dashboard (Settings → Variables). The committed default is
  `https://dhilipsiva.dev` only; **do not** add `localhost` to the deployed var.
  For local UI dev, copy `.dev.vars.example` to `.dev.vars` (gitignored) — it
  overrides the var under `wrangler dev` only.
  **If your playground is served from an origin other than `https://dhilipsiva.dev`**
  (both the `wrangler.toml` var and the code default assume it), set `ALLOWED_ORIGINS`
  to that exact origin **before** deploy — otherwise the browser's CORS check fails
  and jbotci silently degrades to the local gates.

- **Rate limiting:** already enabled (`[[unsafe.bindings]]` `ratelimit`, 60 req /
  60s per client IP). Tune `simple.limit`/`period` in `wrangler.toml`. The Worker
  handles the binding gracefully whether present or not.

## 6. Point the client at it

Set the nibli-ui **jbotci proxy URL** (settings modal) to the Worker URL, e.g.
`https://fanva-proxy.<acct>.workers.dev/mcp`. The proxy ignores the path and
always targets jbotci's fixed `/mcp`, so a trailing `/` also works. Blank = jbotci
off (local gates only).

## 7. Acceptance test against production

Re-run the two `curl` commands from step 3 with the base URL swapped to your
`https://fanva-proxy.<acct>.workers.dev` deployment.
