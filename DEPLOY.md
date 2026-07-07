# Deploying nibli

nibli's web surfaces run **entirely in the browser** — the reasoning engine
(gerna → smuni → logji) is compiled into a WASM bundle and there is **no nibli
server**. "Deploying" is therefore just hosting static bundles, plus one optional
Cloudflare Worker for the translator's jbotci tool-use.

There are two distinct deployables (don't conflate them):

| URL | Crate | What it is |
|-----|-------|-----------|
| `dhilipsiva.dev/nibli-playground` | `nibli-ui` (Dioxus app) | The Transparency Triad playground, incl. the **Translate** feature (`nibli-fanva`) |
| `dhilipsiva.dev/nibli` | `nibli-wasm` (wasm-bindgen lib) | The live demo embedded on the site |

## 1. Ship the frontend (the playground + Translate)

The build/host pipeline lives in the **external `dhilipsiva/dhilipsiva.dev` repo**,
not here. This repo only *pings* it: on every push to `main`,
[`.github/workflows/redeploy-site.yml`](.github/workflows/redeploy-site.yml) fires a
`repository_dispatch` (`event_type=nibli-updated`) that tells the site to rebuild and
re-pull this crate. (It self-skips, staying green, until the `SITE_DISPATCH_TOKEN`
secret exists.)

So **shipping the translator = merging your branch into `main`.** Everything the
Translate feature needs is baked into the `nibli-ui` bundle at build time:

- `nibli-fanva` is a **path dependency compiled into the bundle** (`nibli-ui/Cargo.toml`)
  — no separate service.
- The vendored **camxes** grammar ships as `asset!()` static assets
  (`nibli-ui/assets/js/vendor/camxes/…`, wired in `nibli-ui/src/main.rs`).
- The three local gates (**gerna + smuni + camxes**) run in-browser with **zero
  network**. The *only* optional network call is the user's own BYO-key LLM request
  for Translate (and, if configured, the jbotci proxy below).

### Local release preview (optional)

To build the exact shipping bundle locally (a preview / pre-merge sanity check — the
**production** build runs in the external site repo):

```sh
just build-ui        # dx build --release
# output: target/dx/nibli-ui/release/web/public/  — serve it with any static server
```

## 2. Optional: the jbotci proxy (`fanva-proxy/`)

jbotci dictionary/grammar tool-use during translation is **off by default** and
degrades cleanly to the local gates. To enable it, deploy the Cloudflare Worker and
point the UI at it:

1. Deploy per [`fanva-proxy/DEPLOY.md`](fanva-proxy/DEPLOY.md) (`npx wrangler login`
   then `npm run deploy`).
2. **Set `ALLOWED_ORIGINS` to your app origin** (both the `wrangler.toml` var and the
   code default assume `https://dhilipsiva.dev`). If the playground is served from any
   other origin, set it there before deploy or the browser CORS check fails.
3. If `wrangler` is logged into multiple Cloudflare accounts, pin the account:
   `CLOUDFLARE_ACCOUNT_ID=<id> npm run deploy` (or add `account_id` to `wrangler.toml`).
4. Paste the resulting `https://fanva-proxy.<acct>.workers.dev/mcp` into the nibli-ui
   settings modal (**jbotci proxy URL**). Blank ⇒ jbotci off (local gates only,
   flagged `degraded`).

## 3. Acceptance ("done when")

Hosted **Translate works end-to-end**:

- **Always** (no proxy, no jbotci): open the playground, enter your LLM API key in
  settings (BYO-key, held in that tab's memory only), click **Translate** on the
  Source tab — the draft is validated by the local gerna+smuni+camxes gates and the
  self-correction trace shows the attempts; a valid result fills the Lojban tab.
- **With the proxy** (jbotci on): the self-correction trace shows jbotci tool calls,
  and the Back-translation tab's **Deep meaning (tersmu)** button renders jbotci's
  semantic graph.

Exercising Translate needs a user-supplied LLM key — there is no shared key and no
nibli server; the request goes straight from the browser to the chosen provider.
