# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency. Items within each tier can be tackled in any order unless noted.

## Tier 1: Security & Reliability (High Impact, High Priority)

1. **Server request timeouts and rate limiting** — `nibli-server` has no request timeouts or rate limiting. A slow/malicious GraphQL query blocks the entire server (coarse `Arc<Mutex<>>` lock). Add `tower::timeout` middleware and `governor` crate for per-route rate limiting. Low effort, high impact.

2. **Gossip signature verification** — `tavla` envelopes carry a `sig: Vec<u8>` field but signatures are never verified. Any peer can forge envelopes. Implement ed25519 verification (the `sig` field already exists). Blocks any production gossip deployment.

3. **Fuzz testing for parser and reasoning engine** — No adversarial input testing exists. Lojban's recursive grammar and the backward-chaining engine are rich targets for pathological inputs. Add `cargo-fuzz` targets for `gerna::parse_text` and `logji` assertion/query paths. Depth guards (MAX_DEPTH=64) and fuel limits mitigate but don't replace structured fuzzing.

## Tier 2: Correctness & Robustness (High Impact, Medium Priority)

4. **Replace string-based fact matching with typed terms** — The reasoning engine stores facts as interned s-expression strings and pattern-matches via string tokenization. A formatting change in `write_sexp` silently breaks `match_against_tokens`. Move to a proper term algebra with structural unification. This eliminates an entire class of silent bugs. Large effort but highest long-term correctness payoff. Depends on: nothing, but touches logji, lasna, nibli-engine.

5. **Eliminate duplicated s-expression logic** — S-expression reconstruction exists in both `lasna/src/lib.rs` and `nibli-engine/src/lib.rs`. Type conversion between WIT types is repeated in multiple places. Extract shared logic into a common crate or module. Reduces maintenance burden and drift risk. Partially addressed by item 4 if pursued.

6. **CRDT tombstone conflict handling** — `tavla` merge doesn't handle tombstone conflicts correctly. If two nodes retract different envelopes, merging could resurrect retracted facts. Vector clock comparison also assumes missing agents at counter 0, which breaks under network partitions.

## Tier 3: Maintainability (Medium Impact, Medium Priority)

7. **Split god files** — `logji/src/lib.rs` (5,430 lines) and `gerna/src/grammar.rs` (4,471 lines) are too large for a single file. Split logji into `kb.rs`, `assertion.rs`, `query.rs`, `witness.rs`, `proof.rs`. Split grammar into per-construct modules (selbri, sumti, sentence, description, connective). No behavioral change, pure refactor.

8. **Make hardcoded constants configurable** — Backward-chaining depth limit (10), UI GraphQL URL, MAX_OUTPUT_ENTRIES (200), polling intervals, and other hardcoded values should be configurable via env vars or REPL commands. Some already are (fuel, memory); the pattern is inconsistent.

9. **WIT schema versioning** — No migration path for WIT interface evolution. Document versioning strategy and add version field to WIT world definitions.

## Tier 4: Infrastructure & Deployment (Lower Impact, Lower Priority)

10. **Fine-grained server locking** — Replace `Arc<Mutex<>>` around the entire gossip node with per-resource locks or `RwLock` to allow concurrent read queries.

11. **Runtime-configurable UI server URL** — `nibli-ui` hardcodes the GraphQL endpoint. Read from env or DOM config at runtime so deployment doesn't require recompilation.

12. **Guard `RefCell` usage against non-WASM misuse** — `RefCell` in WASM component crates is correct for single-threaded WASI but is a latent footgun if crates are used outside WASM. Add `#[cfg]` compile-time guards or document the constraint prominently.

13. **Stale TCP connection cleanup in gasnu** — No idle timeout on compute backend connections. Long REPL sessions hold connections indefinitely. Add configurable idle timeout with auto-reconnect on next use.

14. **Gossip envelope expiration** — CRDT log is append-only with no expiration. Ancient envelopes stay forever. Add TTL or compaction strategy for long-running nodes.
