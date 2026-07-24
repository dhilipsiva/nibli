# Introduction

This site is the **code-derived** documentation for [Nibli](https://github.com/dhilipsiva/nibli): a zero-hallucination symbolic reasoning engine with a human-readable knowledge-representation surface (**nibli KR**).

It is **not** the Orange AVA book manuscript. Book rights are reserved by the publisher. Nothing here is copied from that manuscript. Claims should re-derive from the repository: source code, tests, `just` recipes, shipped corpora (`.nibli` files), and the root engine specifications.

## Where to run things

| Surface | URL / command |
|---------|----------------|
| **Interactive playground** | [dhilipsiva.dev/nibli-playground](https://dhilipsiva.dev/nibli-playground/) |
| **Docs (GitHub Pages mirror)** | [dhilipsiva.github.io/nibli](https://dhilipsiva.github.io/nibli/) |
| **Docs (primary, when site ships)** | [dhilipsiva.dev/docs/nibli/](https://dhilipsiva.dev/docs/nibli/) |
| **Local build** | `just docs` / `just docs-serve` (inside `nix develop`) |
| **Rust API** | `cargo doc -p <crate> --open` (docs.rs when crates are published) |

Primary host path is `/docs/nibli/`; the GitHub Pages project site uses base path `/nibli/`. CI builds the mirror with `site-url=/nibli/`. Prefer relative links inside chapters so both bases work.

<p><a href="https://dhilipsiva.dev/nibli-playground/"><strong>Open the playground →</strong></a></p>

## Source layout

| Path | Role |
|------|------|
| `mdbook/src/` | Hand-authored pages (this site) |
| `mdbook/book/` | Generated HTML only — do not edit |
| Repo root `NIBLI_KR.md`, `LOGIC_IR.md`, `GUARANTEES.md`, … | Normative engine specs (linked from [Reference](reference.md)) |
| `book/` | Private manuscript checkout — **never** imported into this tree |

The live docs roadmap is [`DOCS_TODO.md`](https://github.com/dhilipsiva/nibli/blob/main/DOCS_TODO.md) at the repository root.

## Start here

1. [What Nibli guarantees](user/guarantees.md) — the four-valued contract and scope.
2. [Quickstart](user/quickstart.md) — Nix + `just run`.
3. [nibli KR cookbook](user/kr-cookbook.md) — surface syntax cheat sheet.
4. [Playground](user/playground.md) — browser triad without installing anything.
5. [Authorization](user/authorization.md) — builtin policy and multi-language `can` / field masks.
