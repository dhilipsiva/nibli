# Working on nibli

Read [README.md](README.md) for what nibli is and how to run it, and [CLAUDE.md](CLAUDE.md)
for the full guide: every `just` recipe, the crate architecture, the code and docs
conventions and the pre-commit checklist. [GUARANTEES.md](GUARANTEES.md) states what the
engine promises; a change that weakens a guarantee says so there. [TODO.md](TODO.md) is the
tracker. Lucy has moved to [dhilipsiva/lucy](https://github.com/dhilipsiva/lucy).

Layout: `nibli-kr` (the KR front-end), `nibli-semantics`, `nibli-reason`, `nibli-session`
and `nibli-engine` are the engine; `nibli-pipeline` is the one WASM component
(`wit/world.wit`) and `nibli-host` its Wasmtime host and REPL; `nibli-verify` holds the
differential soundness gates and `proofs/` the Lean 4 proofs.
`mdbook/src/` is the docs source. `book/` is a private manuscript: no docs diff cites it.

The toolchain comes from `nix develop`. The gates are `just ci` (native: fmt, clippy with
`-D warnings`, the test suites and the `verify-*` gates) and `just ci-wasm` (the component
smokes); `just ci-all` runs both and must pass before a push. Use `cargo test --lib`, not a
bare `cargo test` (the component crates' WIT export symbols break the linker), and never
hand-write a test count: derive it with `just count-tests`.

Keep: every verdict a derivation from what was asserted, with nothing fabricated; refusals
fail closed and atomically; the committed corpus is the only vocabulary; every ` ```nibli-kr `
fence compiles (`just verify-doc-fences`).

Implement authorized work and its tests autonomously; commit on a branch, never on `main`.
Do not push, tag, publish to crates.io, release or delete remote branches without the owner.
Keep secrets outside Git and the Nix store. Report what you could not verify (a credential,
a device, a network) as unverified: a passing build is not a working deployment.

Runbooks: [RELEASING.md](RELEASING.md) (versions, the release workflow, crates.io),
[DEPLOY.md](DEPLOY.md) (the site and the docs hosts), [CONTRIBUTING.md](CONTRIBUTING.md).
