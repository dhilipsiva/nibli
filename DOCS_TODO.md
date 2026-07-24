# Nibli Documentation & Release TODO

Live tracker for **code-derived docs** and **GitHub / crates.io releases**.
Plain bullets — **delete when fully landed** (no DONE ledger, no checkboxes-as-progress).

Book rights are reserved by **Orange AVA**. Docs never import the private
manuscript at `book/`. Every claim re-derives from code, tests, recipes, corpora,
or root engine specs (`README`, `NIBLI_KR.md`, `LOGIC_IR.md`, `GUARANTEES.md`,
`DEPLOY.md`, `wit/world.wit`).

---

## Decisions of record (locked)

| Decision | Choice |
|----------|--------|
| **SSG** | [mdBook](https://rust-lang.github.io/mdBook/) — source in **`mdbook/`** (not under generated `docs/`) |
| **Primary URL** | `https://dhilipsiva.dev/docs/nibli/` (site-repo host; not live until site copies the build) |
| **Live mirror** | **`https://dhilipsiva.github.io/nibli/`** — `docs-pages.yml`, `just docs /nibli/` |
| **API docs** | **docs.rs** after crates.io publish; until then `cargo doc -p <crate> --open` |
| **Content law** | Code-derived only; no AVA book prose |
| **Interactive** | Deep-link / CTA to playground; no second triad UI until needed |
| **Crate semver** | Workspace **lockstep** `X.Y.Z` for published crates; tags `vX.Y.Z` |
| **WIT ABI** | `nibli:engine@…` in `wit/world.wit` is **independent** of crate semver |
| **0.x** | Minor may break; CHANGELOG required. **1.0** only when embed API is intentionally stable |
| **crates.io Tier A** | `types` → `lexicon` → `protocol` → `kr` → `semantics` → `reason` → `render` → `session` → (`store`) → **`engine`** → optional `formalize` / `import` / `nibli` bins |
| **crates.io Tier Z** | `publish = false`: pipeline, host, ui, wasm, verify, lexigen, fuzz — ship via GH Release / site / repo only |
| **Release tooling (v0.1)** | `[workspace.package]` + Just + Actions on `v*` tags (not release-plz yet) |

```text
code / pest / WIT / tests / corpora / just
        ↓
root specs (README, NIBLI_KR, LOGIC_IR, GUARANTEES, DEPLOY)
        ↓
mdbook/src  ──build──▶  HTML
                ├── dhilipsiva.github.io/nibli/     ← LIVE
                └── dhilipsiva.dev/docs/nibli/      ← site-repo pending
crates ──publish──▶ crates.io ──▶ docs.rs
tag vX.Y.Z ──▶ GitHub Release (+ optional .wasm / host bins)
```

---

## Baseline (landed — not backlog)

| Item | Notes |
|------|--------|
| **Docs Phase 0** | `mdbook/` scaffold; `mdbook` in flake; `just docs` / `docs-serve`; CI job `docs`; gitignore `mdbook/book/` |
| **Docs Phase 1** | User MVP: guarantees, quickstart, KR cookbook, playground CTA; dual `site-url` (`just docs [/nibli/]`); **Pages live** at github.io/nibli; DEPLOY §2 primary recipe for site repo |
| **Release policy** | This file’s decisions table + Tier A/Z + R0–R3 track (not yet implemented) |

---

## Open — docs content & hosting

### Site primary (blocks “canonical” URL)

- Wire **`dhilipsiva.dev/docs/nibli/`** in `dhilipsiva/dhilipsiva.dev` on `nibli-updated`: checkout nibli → `just docs` → copy `mdbook/book/` → `public/docs/nibli/` (DEPLOY §2b). Do not claim primary live until HTTP 200.

### Phase 2 — Corpora + playground depth

- GDPR / drug-interactions walkthroughs from shipped `.nibli` + engine-checked queries (example KBs, not book chapters).
- Belief revision / `:retract` (host) and playground edit-and-re-query.
- Deep-link or preset hooks for Syllogism / GDPR / Drug UI labels (byte-stable names).

### Phase 3 — Developer guide

- Crate map (Mermaid), pipeline + IR (from `LOGIC_IR.md`), WASM/host/compute (code + DEPLOY).
- Soundness/CI index (`just verify-*`, GUARANTEES, Lean `proofs/`).
- WIT surface page from `wit/world.wit`.

### Phase 4 — docs.rs links *(after Release R2)*

- mdBook API index → versioned docs.rs URLs.
- Conceptual docs stay on primary/mirror only.

### Phase 5 — Polish

- Version / release badge on mdBook landing (“docs for `main`” + latest `v*` when tags exist).
- Optional KR fence lint (`nibli-validate`) — only if docs CI stays light.
- Editor/LSP docs if root `TODO.md` editor track lands.

### Deferred / optional

- Fence lint in CI (deferred: keep docs job free of full cargo build).
- mdBook search already default; no extra work unless broken under dual base paths.

---

## Open — release track (GitHub + crates.io)

**Status:** all crates `0.1.0`; path-only deps; almost no package metadata; no tags/releases; no crates.io. Dual license files at repo root.

### R0 — Packaging (no public release)

- `[workspace.package]`: version, `license = "MIT OR Apache-2.0"`, repository, homepage; members inherit.
- `publish = false` on Tier Z.
- `[workspace.dependencies]` for internal crates (`path` + `version`).
- Root `CHANGELOG.md` (Keep a Changelog; Unreleased stub).
- `just release-check` (version consistency; optional metadata lint).
- Confirm `nibli*` crate names free on crates.io; plan `CARGO_REGISTRY_TOKEN` secret.

### R1 — First GitHub Release

- Prefer **`v0.1.0-alpha.1`** if API still thrashing; else **`v0.1.0`** with clear 0.x note.
- Tag workflow: CHANGELOG notes + optional `nibli-pipeline.wasm` / host / `nibli-validate` + checksums.
- README badge → latest release + docs mirror.
- No crates.io until dry-run clean.

### R2 — First crates.io publish

- `cargo publish` Tier A in dependency order.
- Verify docs.rs (edition 2024).
- mdBook API links (Phase 4); embed snippet (`cargo add nibli-engine`) code-derived.

### R3 — Automation

- Tag → GH Release → crates.io fully automated.
- Optional multi-arch host binaries; yank/hotfix policy documented.

### Every release (checklist — keep short)

1. CI green on tagged commit.  
2. Lockstep version + CHANGELOG (+ WIT note if ABI moved).  
3. Tag `vX.Y.Z` + GitHub Release.  
4. Publish Tier A if this release includes crates.io.  
5. Smoke install/depend; update docs badges/links.  
6. Site redeploy via existing `nibli-updated` (unversioned playground).

### Release out of scope

- Manuscript / AVA materials in any release asset.
- crates.io for ui/wasm/playground (site only).
- Equating crate semver with WIT `0.5.0`.

---

## Conventions

- **mdBook source** = `mdbook/src/`; never hand-edit `mdbook/book/`.
- **Fences:** `nibli` / `nibli-kr` (align with root editor track).
- **Docs PR gate:** `just docs` (CI `docs` job); no `book/` paths in the diff.
- **Pages build:** always `just docs /nibli/` (or `docs-pages-build`).
- **Primary build:** default `just docs` (`site-url=/docs/nibli/`).
- **Epistemic:** never present aspirations as shipped (same as GUARANTEES/README).
