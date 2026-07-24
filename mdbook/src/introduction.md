# Introduction

This site is the **code-derived** documentation for [Nibli](https://github.com/dhilipsiva/nibli): a zero-hallucination symbolic reasoning engine with a human-readable knowledge-representation surface (**nibli KR**).

It is **not** the Orange AVA book manuscript. Book rights are reserved by the publisher. Nothing here is copied from that manuscript. Claims should re-derive from the repository: source code, tests, `just` recipes, shipped corpora (`.nibli` files), and the root engine specifications.

## Where to run things

| Surface | URL / command |
|---------|----------------|
| **Interactive playground** | [dhilipsiva.dev/nibli-playground](https://dhilipsiva.dev/nibli-playground/) |
| **This docs site (primary, when deployed)** | [dhilipsiva.dev/docs/nibli/](https://dhilipsiva.dev/docs/nibli/) |
| **Docs mirror (GitHub Pages, when deployed)** | [dhilipsiva.github.io/nibli/](https://dhilipsiva.github.io/nibli/) |
| **Local build** | `just docs` / `just docs-serve` (inside `nix develop`) |
| **Rust API** | `cargo doc -p <crate> --open` (docs.rs when crates are published) |

Primary and mirror hosts share one mdBook artifact under different base paths (`/docs/nibli/` vs `/nibli/`). Prefer relative links inside chapters so both remain valid.

## Source layout

| Path | Role |
|------|------|
| `mdbook/src/` | Hand-authored pages (this site) |
| `mdbook/book/` | Generated HTML only — do not edit |
| Repo root `NIBLI_KR.md`, `LOGIC_IR.md`, `GUARANTEES.md`, … | Normative engine specs (linked from [Reference](reference.md)) |
| `book/` | Private manuscript checkout — **never** imported into this tree |

The live docs roadmap is [`DOCS_TODO.md`](https://github.com/dhilipsiva/nibli/blob/main/DOCS_TODO.md) at the repository root.
