# Engine upgrade to 0.2

The engine now preserves incomplete reasoning results through equality alternatives,
uses a bounded query-local closure of activated individual witnesses across
existential, universal, exact-count and enumeration queries, and preserves binder
scope and opaque duty content in English rendering. Generated witnesses remain
derivations from explicit premises; a failed bounded search is not a proof of absence.
Cycles through domain-sensitive negation leave affected searches non-definitive
(`UNKNOWN (naf-dependent)`) rather than establishing absence from a growing domain.
Witnesses activate only when their executable rule conditions hold. Individuals
mentioned solely inside quoted event descriptions do not become actual domain
members or facts; those descriptions still participate in dependency checks.

This is an unreleased workspace upgrade; no crates or artifacts are published by this change.

## API changes

- Cargo workspace: `0.2.0`; WIT package: `nibli:engine@0.12.0`.
- `set_max_chain_depth(u32)` is fallible and rejects zero. The default is 10;
  `max_chain_depth()` reports the current setting. Both REPLs expose `:depth [N]`;
  `NIBLI_MAX_CHAIN_DEPTH` configures CLI startup. Browser numbers are checked for
  finiteness, integral value and the positive u32 range before integer conversion.
- Depth survives reset, retraction, import-profile rebuild and host trap recovery.
  It bounds reasoning and generated witness dependency height; materialization can
  independently settle an eligible query. A fresh process starts from its startup
  configuration, not the previous process's depth setting.
- `NibliEngine::reset` and the browser `reset` report errors. Materialization and
  stratification report APIs also report an unavailable knowledge base explicitly.
- `list_assertion_records` adds stable IDs, labels and `Active`/`Withdrawn` status.
  Existing `list_facts` stays active-only. The new browser JSON uses decimal string
  IDs; its old active-facts JSON is unchanged. Both REPLs support `:facts --all`.
- Trusted replay uses `restore_withdrawn_assertion(id, label)` without decoding the
  old payload. IDs remain reserved until reset. Records are not an immutable audit
  chronology, and temporary assumptions do not enter the live registry.
- Proof envelopes are schema 2 and require `profile.max_chain_depth`. Regenerate
  schema 1 envelopes; they are rejected rather than assigned an invented budget.

## Mutation and persistence contract

A text assertion stages all roots on a detached candidate. Admission and durable
batch-write failures before commit leave the old live and durable state intact.
Publication occurs in the existing knowledge-base identity only after canonical
commit succeeds. The typed store is a recoverable mirror, not the authoritative
assertion registry. Retraction and reset use the same staging contract.

An uncertain commit outcome requires a fresh database open. Queries, mutation,
history and logical reports through already-exposed knowledge-base handles fail
closed. The host publishes a recovered component only after complete replay; it
records successful configuration changes in order so a later strict setting is
not applied retroactively to older assertions.

## Validation

Focused regression suites cover equality/resource propagation, finite nested
witnesses, counting and enumeration agreement, atomic admission and persistence,
withdrawn IDs, recovery guards, renderer scope, proof schema migration, and the
native/WASI/V8 interfaces. Inside the Nix dev shell, the validation recipes are:

```sh
just fmt-check release-check clippy-runtime test test-engine test-host \
  test-validate test-ui test-formalize test-backend test-store \
  test-persistence-replay verify-harness verify-soundness verify-alias-map \
  verify-nibli-kr-seam verify-dict verify-pins verify-adjudication \
  verify-proofs verify-grammar-parity verify-doc-fences
cargo test -p nibli-engine --test integration \
  native_compute_backend_real_python_tenfa -- --ignored --nocapture --test-threads=1
just ci-wasm
```

Use these explicit engine recipes for this reconciliation: `just ci` also calls
`verify-book-vocab`, which reads the outdated book Markdown. The latest manuscript
sources are DOCX and have not been edited by this engine change.
