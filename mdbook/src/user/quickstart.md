# Quickstart

Source: [README — Getting Started](https://github.com/dhilipsiva/nibli/blob/main/README.md) and the root [Justfile](https://github.com/dhilipsiva/nibli/blob/main/Justfile).

## Prerequisites

- [Nix](https://nixos.org/download.html) — rustc, cargo-component, just, wasmtime, mdbook, and the rest come from `flake.nix`.

## Enter the shell and run the REPL

```bash
# From the nibli repository root
nix --extra-experimental-features 'nix-command flakes' develop

# Build the pipeline component + native host and launch the REPL
just run
```

`just run` is the full local operator path (WASM component + `nibli-host`). For a fast native check only:

```bash
just test          # unit tests (lib)
just check         # type-check workspace
```

## First claims

In the REPL, assert facts and rules, then query by **stating a claim** (not asking a question):

```nibli-kr
animal(every dog).
dog(Adam).
```

Then query:

```nibli-kr
animal(Adam).
```

Expect **TRUE** with a proof when the rule and fact support the claim. See [What Nibli guarantees](guarantees.md) for how to read **FALSE** vs **UNKNOWN**.

A larger starter table lives in the [nibli KR cookbook](kr-cookbook.md). The repo root also ships example files such as `readme.nibli`, `gdpr.nibli`, and `drug-interactions.nibli` (`:load path` in the host REPL).

## Dictionary note

The vocabulary is **committed Rust source** (`nibli-lexicon/src/corpus/`) — no network fetch at build or runtime. Local, CI, and the hosted playground share the same corpus.

## Docs site (this book)

```bash
just docs          # build → mdbook/book/
just docs-serve    # http://127.0.0.1:3000
```

## Prefer not to install?

Use the hosted [playground](playground.md) — the engine runs fully in the browser.
