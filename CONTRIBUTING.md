# Contributing to nibli

Thank you for helping. nibli is a deterministic reasoning engine, so a change is judged first
by whether every guarantee in [GUARANTEES.md](GUARANTEES.md) still holds.

## Setup

Everything runs in the Nix dev shell, which pins the Rust toolchain, the WASM tools and the
oracles the soundness gates use (Vampire, clingo, Lean):

```sh
nix develop
just build-wasm   # generates the component bindings a fresh checkout lacks
just ci           # the native gate
```

`just --list` shows every recipe; [CLAUDE.md](CLAUDE.md) explains each one.

## Before you open a pull request

- `just ci-all` passes: the native gate plus the WASM smokes (`just ci-wasm`). CI runs the
  same two halves as separate jobs.
- A behaviour change comes with a test that fails without it. A soundness-path change keeps
  `just verify-soundness` green, and `cargo mutants --in-diff` shows no new survivor
  (`just mutants` has the details).
- Docs follow the code: a ` ```nibli-kr ` fence must compile (`just verify-doc-fences`), and a
  figure such as a test count is derived (`just count-tests`), never typed in.
- [CHANGELOG.md](CHANGELOG.md) gains a line under `[Unreleased]` for anything a user or an
  embedder would notice. The WIT package version in `wit/world.wit` moves independently of the
  crate versions (see the CHANGELOG preamble).

## Licence

nibli is dual-licensed under MIT OR Apache-2.0 ([LICENSE-MIT](LICENSE-MIT),
[LICENSE-APACHE](LICENSE-APACHE)). Unless you say otherwise, a contribution you submit is
licensed the same way, without additional terms.
