# Nibli Documentation Roadmap

Interactive, **code-derived** documentation for the Nibli ecosystem.

Plain bullets — delete when fully landed (no DONE ledger). This file is the live
tracker for the docs program.

## Decisions of record (locked)

| Decision | Choice |
|----------|--------|
| **SSG** | **[mdBook](https://rust-lang.github.io/mdBook/)** |
| **Primary URL** | **`https://dhilipsiva.dev/docs/nibli/`** (static host on the product site) |
| **Source tree** | `mdbook/` in this repo (`book.toml` + `mdbook/src/…`) — hand-authored |
| **Build output** | Generated only (e.g. `mdbook/book/` or CI artifact). Do **not** treat generated HTML as source. The CLAUDE exclusion of `docs/` as generated remains: **do not put the mdBook source under `docs/`**. |
| **Content law** | **Code-derived only.** Book rights are reserved by **Orange AVA**. Do not copy, paraphrase at length, or re-host manuscript prose, AVA outline copy, or book-only narratives. Every claim should re-derive from a path, test, recipe, corpus, or live engine output. |
| **Interactive surface** | Prefer **embed / deep-link** the existing playground (`dhilipsiva.dev/nibli-playground`). Do not fork a second triad UI until mdBook pages need a custom widget. |

### Mirrors (same content graph, different roles)

| Surface | URL / product | Role |
|---------|----------------|------|
| **Primary** | `https://dhilipsiva.dev/docs/nibli/` | Canonical human docs; same origin as playground for embeds |
| **Mirror A — GitHub Pages** | `https://dhilipsiva.github.io/nibli/` | Public mirror of the **same mdBook build** (availability + OSS discoverability). Byte-equivalent HTML preferred; footer/banner may note “mirror of dhilipsiva.dev/docs/nibli”. |
| **Mirror B — docs.rs** | `https://docs.rs/<crate>/…` | **Rust API reference only** (rustdoc), not the user guide. Ships when crates are published to crates.io; until then rustdoc is local/`cargo doc` and CI-optional. Cross-link from mdBook “Crate API” pages → docs.rs (or `cargo doc --open` instructions while unpublished). |

**Do not** host the book manuscript on any of these surfaces.

```text
code / pest / WIT / tests / corpora / just recipes
        ↓
repo root specs (README, NIBLI_KR.md, LOGIC_IR.md, GUARANTEES.md, DEPLOY.md)
        ↓  curate / link (never invent)
mdbook/src  ──mdbook build──▶  HTML artifact
        ├──▶  dhilipsiva.dev/docs/nibli/     (primary)
        └──▶  dhilipsiva.github.io/nibli/    (mirror)
crates ──cargo doc / publish──▶ docs.rs/<crate>  (API mirror, separate product)
```

---

## Content policy (book-safe)

| Allowed | Forbidden |
|---------|-----------|
| README, NIBLI_KR, LOGIC_IR, GUARANTEES, DEPLOY, WIT | Book chapter prose, AVA outline, pedagogical “story” arcs |
| Crate rustdoc, tests, `just` recipes | Long paraphrase of book sections |
| Corpora: `gdpr.nibli`, `drug-interactions.nibli`, `readme.nibli`, UI presets | Book-only characters/plot; “see Chapter N” as a content source |
| Live REPL / playground / capture output | Transcripts that exist only in the manuscript |
| Short operational “what / how / API” pages | Competing long-form textbook under `/docs/nibli` |

Case studies = **file walkthroughs of shipped corpora**, labeled example KBs — never “book Ch 19.”

---

## Information architecture (mdBook)

Two guides in one book (parts), shared glossary/appendix of links to root specs.

### Part I — Engine-user guide

*Audience: people writing `.nibli` KBs, integrating host/WASM, running the REPL/playground.*

- **What Nibli guarantees** — from `README` + `GUARANTEES` (four-valued contract, CWA/CDA, trusted compute). Not a “firewall essay.”
- **Quickstart** — Nix/`just run` (or release CLI), first assert+query from `readme.nibli` or minimal fences.
- **nibli KR cookbook** — thin pages pointing at `NIBLI_KR.md` + minimal validated fences: predicates, named places, rules, `~`, tense/deontic as shipped.
- **Playground** — how to use the triad; deep-link / embed; query model (state a claim, no interrogative).
- **Corpora walkthroughs** — `gdpr.nibli`, drug-interactions: load, query, retract — engine-checked.
- **Embedding** — `nibli-wasm` / host / `nibli-engine` from code + WIT; link docs.rs when live.

### Part II — Engine-developer guide

*Audience: contributors to the compiler, reasoner, host, CI.*

- **Crate map** — workspace graph (Mermaid), file pointers.
- **Pipeline & IR** — `LOGIC_IR.md` + seam tests.
- **WASM / host / compute protocol** — fuel, traps, backend wire from code + DEPLOY.
- **Soundness & CI** — index `just verify-*`, `GUARANTEES`, Lean `proofs/`.
- **Dev loop** — `just ci` / `ci-wasm`, fuzz, mutants as operator docs.

### Front matter / back matter

- Landing, version/commit badge (“built from `main` @ …”).
- Link-out page: full `NIBLI_KR.md`, `LOGIC_IR.md`, `GUARANTEES.md` (render in-book via include **only if** those files stay engine-owned and non-book).
- API index → docs.rs / `cargo doc`.

---

## Hosting & publish pipeline

### Primary — `dhilipsiva.dev/docs/nibli/`

1. CI (or site `repository_dispatch` path) runs `mdbook build` in this repo.
2. External **dhilipsiva.dev** site hosts the static tree at **`/docs/nibli/`** (trailing slash; relative links inside mdBook).
3. Redeploy: extend existing `nibli-updated` site rebuild (same family as playground) *or* upload Pages-style artifact the site pulls — prefer one artifact, two deploys (primary + GH Pages).

### Mirror A — `dhilipsiva.github.io/nibli/`

1. GitHub Actions on `main`: `mdbook build` → deploy to **GitHub Pages** (`peaceiris/actions-gh-pages` or `actions/upload-pages-artifact` + `deploy-pages`).
2. Same artifact as primary when possible (one job, two publish steps).
3. `book.toml` `site-url` / base path: primary may be `/docs/nibli/`; GH Pages base is `/nibli/` — use **relative links** inside chapters and set `site-url` per deploy or dual config so both bases work.
4. README badge: “Docs (primary) | Mirror | API”.

### Mirror B — docs.rs

1. **Scope:** rustdoc for library crates (`nibli-types`, `nibli-kr`, `nibli-semantics`, `nibli-reason`, `nibli-engine`, `nibli-session`, …). Not mdBook chapters.
2. **Prerequisite:** crates.io publish (most workspace crates are not yet a published set). Until publish: document `cargo doc -p <crate> --open`; optional CI job that builds rustdoc and fails on warnings.
3. **When publishing:** enable docs.rs via normal crates.io release; set `[package.metadata.docs.rs]` if needed (features, targets). mdBook “API” pages link to versioned docs.rs URLs.
4. **Cross-links:** rustdoc module docs may link *out* to `dhilipsiva.dev/docs/nibli/` for conceptual pages; never paste book text into `//!` comments.

### Playground cross-links

| Surface | Link |
|---------|------|
| mdBook | CTA → `https://dhilipsiva.dev/nibli-playground/` (+ optional preset query params if/when UI supports them) |
| Playground | Footer/help → `/docs/nibli/` |
| README | Primary docs URL + GH Pages mirror + docs.rs when available |

---

## Phased delivery

### Phase 0 — Scaffold

**Landed:** `mdbook/` stub site; `mdbook` in Nix flake; `just docs` / `just docs-serve`; CI job `docs` (`just docs`); dual base paths documented in `book.toml` + introduction; README / CLAUDE / DEPLOY pointers; no `book/` manuscript imports.

### Phase 1 — MVP user guide (ship primary + GH Pages mirror)

**Landed (nibli repo):** user pages (guarantees, quickstart, KR cookbook, playground CTA); `just docs [site_url]` / `docs-pages-build`; GitHub Pages workflow → `https://dhilipsiva.github.io/nibli/`; primary path documented in DEPLOY.md for the site repo.

**Still site-repo:** wire `dhilipsiva.dev/docs/nibli/` copy on `nibli-updated` (DEPLOY §2b). Do not claim primary live until that ships.

**Deferred:** fence lint via `nibli-validate` on ````nibli-kr` blocks (keep docs CI light).

### Phase 2 — Corpora + embed

- [ ] GDPR / DDI walkthroughs from shipped `.nibli` + engine-checked queries.
- [ ] Belief revision / retract as host or playground edit.
- [ ] Embed or deep-link playground presets (UI names byte-stable: Syllogism / GDPR / Drug — labels, not book chapters).

### Phase 3 — Developer guide

- [ ] Architecture Mermaid, pipeline/IR, WASM/host, soundness/CI index.
- [ ] WIT surface page from `wit/world.wit`.

### Phase 4 — docs.rs API mirror

- [ ] Decide publish set (which crates on crates.io).
- [ ] `cargo doc` clean; docs.rs metadata; mdBook API index links versioned docs.rs.
- [ ] Keep conceptual docs on primary/mirror only.

### Phase 5 — Polish

- [ ] Search (mdBook default), version badge, “verified against commit”.
- [ ] Editor/LSP docs only if editor track in root `TODO.md` lands.

---

## Open backlog (from original sketch, book-scrubbed)

### User guide

- What Nibli guarantees (README + GUARANTEES).
- Quickstart: install / `just run` / first REPL.
- KR: predicates, args, constants; rules; NAF; event surface as shipped.
- Playground / triad: reuse hosted UI.
- Corpora: `gdpr.nibli`, drug-interactions; retract/rebuild.
- Host integration: WASM JS, native embed, assertion structure.

### Developer guide

- Crate dependency graph (interactive Mermaid).
- Flat `u32` buffers vs trees; WASM boundary.
- Component model: sandbox, fuel, trap recovery.
- Semantic pipeline: event decomposition, Skolemization (from IR + code).
- Compute protocol: host dispatch wire.
- Testing: `just test` / `ci` / Vampire+clingo / Lean.

---

## Conventions

- **mdBook source** lives in `mdbook/`; generated HTML is not hand-edited.
- **Fences:** prefer `nibli` / `nibli-kr` (same policy as root `TODO.md` editor track).
- **Gates for docs PRs:** `mdbook build` green; KR fences validated when tooling exists; no `book/` paths in the diff.
- **Figures:** Mermaid in-page preferred; SVGs under `mdbook/src/images/` if needed — still code- or architecture-derived.
- **Never** describe aspirations as shipped (same epistemic rule as the engine README/GUARANTEES).
