# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency. Items within each tier can be tackled in any order unless noted.

## Tier 1: Security & Reliability (High Impact, High Priority)

1. **Server request timeouts and rate limiting** — `nibli-server` has no request timeouts or rate limiting. A slow/malicious GraphQL query blocks the entire server (coarse `Arc<Mutex<>>` lock). Add `tower::timeout` middleware and `governor` crate for per-route rate limiting. Low effort, high impact.

2. **Gossip signature verification** — `tavla` envelopes carry a `sig: Vec<u8>` field but signatures are never verified. Any peer can forge envelopes. Implement ed25519 verification (the `sig` field already exists). Blocks any production gossip deployment.

3. **Fuzz testing for parser and reasoning engine** — No adversarial input testing exists. Lojban's recursive grammar and the backward-chaining engine are rich targets for pathological inputs. Add `cargo-fuzz` targets for `gerna::parse_text` and `logji` assertion/query paths. Depth guards (MAX_DEPTH=64) and fuel limits mitigate but don't replace structured fuzzing.

## Tier 2: Remove S-Expression Layer (High Impact, High Priority)

S-expressions are a vestigial artifact from the egglog era. Now that the engine uses demand-driven backward-chaining, the entire sexp serialize/parse/tokenize/match cycle is unnecessary overhead. Replace with direct typed `LogicNode` storage and structural unification. This is the single highest-impact refactor — it removes an entire abstraction layer and eliminates a class of silent bugs (formatting changes in `write_sexp` breaking `match_against_tokens`).

4. **Replace `SexpInterner` + `SortedU32Vec` with typed fact store** — `asserted_sexps` currently stores interned sexp string keys. Replace with `HashSet<LogicNode>` (or a predicate-indexed `HashMap<String, Vec<LogicNode>>`). Remove `SexpInterner`, `SortedU32Vec`, `sexp_is_asserted()`, and `extract_pred_name_deep()`. Touches: `logji/src/lib.rs`, `logji/src/rules.rs`.

5. **Replace `SexpTree` pattern matching with structural unification** — `UniversalRuleRecord` stores `SexpTree` templates parsed from sexp strings. Replace with `LogicNode` templates containing a `PatternVar` variant. Implement `unify(template: &LogicNode, concrete: &LogicNode) -> Option<Bindings>` that walks both trees structurally. Remove `SexpTree`, `match_against_tokens()`, `sexp_tokenize()`, `extract_sexp_at()`, `substitute()`. Depends on: item 4. Touches: `logji/src/lib.rs`, `logji/src/reasoning.rs`, `logji/src/rules.rs`.

6. **Replace sexp-based backward-chaining with typed traversal** — `try_backward_chain()` and `check_predicate_in_kb()` currently take `&str` sexp arguments, tokenize them, and match against `SexpTree` templates. Refactor to take `&LogicNode` directly and use structural unification from item 5. Remove `sexp_tokenize()` calls in reasoning hot path. Depends on: items 4, 5. Touches: `logji/src/reasoning.rs`.

7. **Remove `write_sexp` / `reconstruct_sexp` from assertion path** — `lasna` and `nibli-engine` both convert `LogicBuffer` nodes to sexp strings for assertion into logji. Instead, convert `LogicBuffer` → `LogicNode` directly (typed conversion, no string intermediary). Keep sexp formatting only for human-readable display (REPL output, proof trace rendering). Depends on: items 4-6. Touches: `lasna/src/lib.rs`, `nibli-engine/src/lib.rs`. Also eliminates the duplicated sexp reconstruction logic between these two crates.

8. **Update proof traces to use typed nodes** — Proof trace steps currently record sexp strings. Store `LogicNode` references instead; serialize to string only at display time (REPL `?` output, GraphQL `proof-json`, UI proof panel). Depends on: items 4-7. Touches: `logji/src/reasoning.rs`, `gasnu/src/main.rs`, `nibli-server/src/main.rs`.

## Tier 3: Correctness & Robustness (High Impact, Medium Priority)

9. **CRDT tombstone conflict handling** — `tavla` merge doesn't handle tombstone conflicts correctly. If two nodes retract different envelopes, merging could resurrect retracted facts. Vector clock comparison also assumes missing agents at counter 0, which breaks under network partitions.

## Tier 4: Maintainability (Medium Impact, Medium Priority)

10. **Split god files** — `logji/src/lib.rs` (5,430 lines) and `gerna/src/grammar.rs` (4,471 lines) are too large for a single file. Split logji into `kb.rs`, `assertion.rs`, `query.rs`, `witness.rs`, `proof.rs`. Split grammar into per-construct modules (selbri, sumti, sentence, description, connective). No behavioral change, pure refactor.

11. **Make hardcoded constants configurable** — Backward-chaining depth limit (10), UI GraphQL URL, MAX_OUTPUT_ENTRIES (200), polling intervals, and other hardcoded values should be configurable via env vars or REPL commands. Some already are (fuel, memory); the pattern is inconsistent.

12. **WIT schema versioning** — No migration path for WIT interface evolution. Document versioning strategy and add version field to WIT world definitions.

## Tier 5: Infrastructure & Deployment (Lower Impact, Lower Priority)

13. **Fine-grained server locking** — Replace `Arc<Mutex<>>` around the entire gossip node with per-resource locks or `RwLock` to allow concurrent read queries.

14. **Runtime-configurable UI server URL** — `nibli-ui` hardcodes the GraphQL endpoint. Read from env or DOM config at runtime so deployment doesn't require recompilation.

15. **Guard `RefCell` usage against non-WASM misuse** — `RefCell` in WASM component crates is correct for single-threaded WASI but is a latent footgun if crates are used outside WASM. Add `#[cfg]` compile-time guards or document the constraint prominently.

16. **Stale TCP connection cleanup in gasnu** — No idle timeout on compute backend connections. Long REPL sessions hold connections indefinitely. Add configurable idle timeout with auto-reconnect on next use.

17. **Gossip envelope expiration** — CRDT log is append-only with no expiration. Ancient envelopes stay forever. Add TTL or compaction strategy for long-running nodes.
