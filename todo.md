# TODO

Goal: raise the codebase from roughly 7/10 maintainability and production readiness to 9/10.

Order matters:
- Finish Phase 1 before Phase 2.
- Finish Phase 2 before Phase 3.
- Do not start the big core-file split until items 1 through 13 are done.

## Phase 1 - Distributed Correctness

## Phase 2 - Runtime and Transport Hardening

## Phase 3 - Maintainability and Production Finish

- [ ] 14. Split the giant core files by subsystem.
  Targets: `logji/src/lib.rs`, `gerna/src/grammar.rs`, `smuni/src/semantic.rs`
  Do this only after Phases 1 and 2 are stable. Split by responsibility, not by arbitrary line count.

- [ ] 15. Add production guardrails.
  Targets: `nibli-server/src/main.rs`, runtime configuration, deployment docs
  Add structured logs, metrics, health and readiness endpoints, bounded event storage, and non-permissive defaults for network-facing deployment.

- [ ] 16. Reconcile docs, UI, and runtime behavior after the refactors.
  Targets: `README.md`, `AGENTS.md`, `CLAUDE.md`, `nibli-ui/src/main.rs`, `book/`
  The documented behavior, UI behavior, and runtime behavior should match exactly once the server and gossip path are fixed.

## Working Rule

Start with item 1 and do not skip ahead to item 14. The biggest risk right now is distributed-state correctness, not file aesthetics.
