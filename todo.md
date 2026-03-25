# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency. Items within each tier can be tackled in any order unless noted.

## Tier 1: Remove S-Expression Layer (High Impact, High Priority)

S-expressions are a vestigial artifact from the egglog era. Now that the engine uses demand-driven backward-chaining, the entire sexp serialize/parse/tokenize/match cycle is unnecessary overhead. Replace with direct typed `LogicNode` storage and structural unification. This is the single highest-impact refactor — it removes an entire abstraction layer and eliminates a class of silent bugs (formatting changes in `write_sexp` breaking `match_against_tokens`).

2. **Replace `SexpInterner` + `SortedU32Vec` with typed fact store** — `asserted_sexps` currently stores interned sexp string keys. Replace with `HashSet<LogicNode>` (or a predicate-indexed `HashMap<String, Vec<LogicNode>>`). Remove `SexpInterner`, `SortedU32Vec`, `sexp_is_asserted()`, and `extract_pred_name_deep()`. Touches: `logji/src/lib.rs`, `logji/src/rules.rs`.

3. **Replace `SexpTree` pattern matching with structural unification** — `UniversalRuleRecord` stores `SexpTree` templates parsed from sexp strings. Replace with `LogicNode` templates containing a `PatternVar` variant. Implement `unify(template: &LogicNode, concrete: &LogicNode) -> Option<Bindings>` that walks both trees structurally. Remove `SexpTree`, `match_against_tokens()`, `sexp_tokenize()`, `extract_sexp_at()`, `substitute()`. Depends on: item 2. Touches: `logji/src/lib.rs`, `logji/src/reasoning.rs`, `logji/src/rules.rs`.

4. **Replace sexp-based backward-chaining with typed traversal** — `try_backward_chain()` and `check_predicate_in_kb()` currently take `&str` sexp arguments, tokenize them, and match against `SexpTree` templates. Refactor to take `&LogicNode` directly and use structural unification from item 5. Remove `sexp_tokenize()` calls in reasoning hot path. Depends on: items 2, 3. Touches: `logji/src/reasoning.rs`.

5. **Remove `write_sexp` / `reconstruct_sexp` from assertion path** — `lasna` and `nibli-engine` both convert `LogicBuffer` nodes to sexp strings for assertion into logji. Instead, convert `LogicBuffer` → `LogicNode` directly (typed conversion, no string intermediary). Keep sexp formatting only for human-readable display (REPL output, proof trace rendering). Depends on: items 2-4. Touches: `lasna/src/lib.rs`, `nibli-engine/src/lib.rs`. Also eliminates the duplicated sexp reconstruction logic between these two crates.

6. **Update proof traces to use typed nodes** — Proof trace steps currently record sexp strings. Store `LogicNode` references instead; serialize to string only at display time (REPL `?` output, GraphQL `proof-json`, UI proof panel). Depends on: items 2-5. Touches: `logji/src/reasoning.rs`, `gasnu/src/main.rs`, `nibli-server/src/main.rs`.

## Tier 3: Remove Egglog-Era Vestiges (Low Effort, High Cleanup Value)

These are leftover from the egglog (equality saturation) architecture that was fully replaced by demand-driven backward-chaining. None affect correctness today, but they add confusion and dead weight.

7. **Remove `run_bound` / `:saturate` entirely** — `run_bound` field in `KnowledgeBaseInner`, `set-run-bound`/`get-run-bound` WIT methods on both `knowledge-base` and `session` resources, `NIBLI_RUN_BOUND` env var in gasnu, `:saturate` REPL command, and associated tests. The value is stored but **never read** during reasoning — pure egglog-era artifact. Touches: `wit/world.wit`, `logji/src/lib.rs`, `lasna/src/lib.rs`, `gasnu/src/main.rs`. Also update CLAUDE.md to remove run_bound references.

8. **Remove `check-membership` WIT method** — Defined in `wit/world.wit` `compute-backend` interface, stub implementation in gasnu (returns empty), `dispatch_check_membership()` in `logji/src/compute.rs` is **never called** from anywhere. Dead code end-to-end. Touches: `wit/world.wit`, `logji/src/compute.rs`, `gasnu/src/main.rs`.

9. **Remove `#![allow(dead_code)]` ICE workarounds and delete actually-dead code** — Crate-level `#![allow(dead_code)]` in `nibli-engine/src/lib.rs` and `tavla/src/lib.rs` were workarounds for rustc 1.93.1 ICE in `check_mod_deathness`. CLAUDE.md confirms this is fixed in rustc 1.94.0 (already in flake.nix). Remove the allows, then audit every dead code warning that surfaces: if the code is genuinely unused, delete it rather than suppressing the warning. Also audit item-level `#[allow(dead_code)]` across the workspace (gerna parser methods, logji `SortedU32Vec` utilities like `is_subset_of`/`intersection`, nibli-ui struct fields) — if the code has no callers and no concrete planned use, delete it.

## Tier 4: Correctness & Robustness (High Impact, Medium Priority)

10. **CRDT tombstone conflict handling** — `tavla` merge doesn't handle tombstone conflicts correctly. If two nodes retract different envelopes, merging could resurrect retracted facts. Vector clock comparison also assumes missing agents at counter 0, which breaks under network partitions.

## Tier 5: Maintainability (Medium Impact, Medium Priority)

11. **Consolidate duplicated formatting logic** — Three areas of duplication: (a) proof tree formatting in both `nibli-protocol/src/lib.rs` and `gasnu/src/main.rs`; (b) error formatting repeated 3x in `nibli-engine/src/lib.rs` (`format_gerna_error`, `format_smuni_error`, `format_logji_error` are nearly identical); (c) term serialization (`write_term`/`write_term_list`) duplicated between `lasna/src/lib.rs` and `nibli-engine/src/lib.rs`. Consolidate to `nibli-protocol` or a shared utility. Note: item 5 (sexp removal) partially addresses (c).

12. **Split god files** — `logji/src/lib.rs` (5,430 lines) and `gerna/src/grammar.rs` (4,471 lines) are too large for a single file. Split logji into `kb.rs`, `assertion.rs`, `query.rs`, `witness.rs`, `proof.rs`. Split grammar into per-construct modules (selbri, sumti, sentence, description, connective). No behavioral change, pure refactor.

13. **Make hardcoded constants configurable** — Backward-chaining depth limit (10), UI GraphQL URL, MAX_OUTPUT_ENTRIES (200), polling intervals, and other hardcoded values should be configurable via env vars or REPL commands. Some already are (fuel, memory); the pattern is inconsistent.

14. **WIT schema versioning** — No migration path for WIT interface evolution. Document versioning strategy and add version field to WIT world definitions.

## Tier 6: Infrastructure & Deployment (Lower Impact, Lower Priority)

15. **Fine-grained server locking** — Replace `Arc<Mutex<>>` around the entire gossip node with per-resource locks or `RwLock` to allow concurrent read queries.

16. **Runtime-configurable UI server URL** — `nibli-ui` hardcodes the GraphQL endpoint. Read from env or DOM config at runtime so deployment doesn't require recompilation.

17. **Guard `RefCell` usage against non-WASM misuse** — `RefCell` in WASM component crates is correct for single-threaded WASI but is a latent footgun if crates are used outside WASM. Add `#[cfg]` compile-time guards or document the constraint prominently.

18. **Stale TCP connection cleanup in gasnu** — No idle timeout on compute backend connections. Long REPL sessions hold connections indefinitely. Add configurable idle timeout with auto-reconnect on next use.

19. **Gossip envelope expiration** — CRDT log is append-only with no expiration. Ancient envelopes stay forever. Add TTL or compaction strategy for long-running nodes.
