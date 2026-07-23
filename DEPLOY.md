# Deploying nibli

nibli's web surfaces run **entirely in the browser** — the reasoning engine
(nibli-kr → nibli-semantics → nibli-reason) is compiled into a WASM bundle and there is **no nibli
server**. "Deploying" is therefore just hosting static bundles.

There are two distinct deployables (don't conflate them):

| URL | Crate | What it is |
|-----|-------|-----------|
| `dhilipsiva.dev/nibli-playground` | `nibli-ui` (Dioxus app) | The Transparency Triad playground (nibli KR-first), incl. the **Formalize** feature (`nibli-formalize`) |
| `dhilipsiva.dev/nibli` | `nibli-wasm` (wasm-bindgen lib) | The live demo embedded on the site (KR-only since THE DROP — its Lojban-era JS/KB breaks until the site-repo migration lands; `set_language` remains a no-op shim) |

## 1. Ship the frontend (the playground + Formalize)

The build/host pipeline lives in the **external `dhilipsiva/dhilipsiva.dev` repo**,
not here. This repo only *pings* it: on every push to `main`,
[`.github/workflows/redeploy-site.yml`](.github/workflows/redeploy-site.yml) fires a
`repository_dispatch` (`event_type=nibli-updated`) that tells the site to rebuild and
re-pull this crate. (It self-skips, staying green, until the `SITE_DISPATCH_TOKEN`
secret exists.)

So **shipping the formalizer = merging your branch into `main`.** Everything the
Formalize feature needs is baked into the `nibli-ui` bundle at build time:

- `nibli-formalize` is a **path dependency compiled into the bundle** (`nibli-ui/Cargo.toml`)
  — no separate service.
- **No dictionary fetch is needed** (since the committed-corpus milestone,
  2026-07-17): the full vocabulary is COMMITTED Rust source
  (`nibli-lexicon/src/corpus/`), so every build — local, CI, site — carries the
  identical ~1,342-entry corpus with zero network. The site repo's
  `scripts/build_nibli.sh` still carries a now-OBSOLETE `dictionary-en.json`
  fetch step from the dual-mode era; it is harmless (nothing reads the file at
  build time) but should be removed on the next site-repo touch.
- The local gates (**nibli-kr + nibli-semantics + round-trip**) run in-browser with **zero
  network**. The *only* optional network call is the user's own BYO-key LLM
  request for Formalize.

### Local release preview (optional)

To build the exact shipping bundle locally (a preview / pre-merge sanity check — the
**production** build runs in the external site repo):

```sh
just build-ui        # dx build --release
# output: target/dx/nibli-ui/release/web/public/  — serve it with any static server
```

## 2. The retired jbotci proxy (hand-over note)

The `fanva-proxy/` Cloudflare Worker (the legacy Lojban mode's jbotci CORS
relay) retired from this repo at THE DROP, together with the Lojban front-end
and the jbotci tool-use it served. The DEPLOYED worker at
`fanva-proxy.dhilipsiva.workers.dev` survives under the stewardship of the
donation repo (github.com/dhilipsiva/fanva), which carries the worker source,
deploy docs, and `ALLOWED_ORIGINS` configuration from here on.

## 3. Acceptance ("done when")

Hosted **Formalize works end-to-end**:

- Open the playground, enter your LLM API key in settings (BYO-key, held in
  that tab's memory only), click **Formalize** on the Source tab — the draft is
  validated by the local nibli-kr+nibli-semantics+round-trip gates and the self-correction
  trace shows the attempts; a valid result fills the nibli KR tab.
- The example dropdown's GDPR/Legal-domain/Drug KBs assert without "unknown predicate" errors —
  guaranteed by construction since the committed corpus (one build mode; the old
  built-with-the-dictionary check is moot).

Exercising Formalize needs a user-supplied LLM key — there is no shared key and no
nibli server; the request goes straight from the browser to the chosen provider.
