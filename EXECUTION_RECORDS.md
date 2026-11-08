# Execution records and recoverable sessions

`nibli-session::CoreSession` exposes optional observations for learning tools and
engine inspection. The typed result and `ProofTrace` remain the reasoning output;
`ExecutionRecord` records work the engine actually performed, including attempts
which did not contribute to that proof.

```rust
use nibli_session::{CoreSession, RecordingOptions, SessionChange};

let session = CoreSession::new();
let change = session.apply_changes_recorded(
    &[SessionChange::Assert { text: "dog(Adam).".into() }],
    RecordingOptions::standard(),
);
let ids = change.outcome.unwrap().operation_ids;
let query = session.query_text_recorded("dog(Adam).", RecordingOptions::standard());
let (verdict, proof) = query.outcome.unwrap();
assert!(verdict.is_true());
assert!(!query.record.events.is_empty());
let recovered = CoreSession::from_snapshot(&session.snapshot().unwrap()).unwrap();
```

The existing unrecorded APIs still use the same parser, compiler, admission and
reasoning implementations. Recording neither selects a different evaluator nor
replays a completed proof as execution history. The observer interface and
serializable DTOs live in the dependency leaf `nibli-types::execution`; the bounded
collector and operation orchestration live in `nibli-session`. Reasoner observers
are explicit per-KB handles, inherited by detached transaction candidates.

The `_with_phase_observer` variants accept a per-call `ExecutionObserverHandle`
for live worker progress. They forward only `phase()` transitions, outside the
collector mutex, even if history is disabled or truncated. The callback must not
re-enter the session. A phase message proves stage entry; a host must separately
check that no completed response arrived before claiming termination during that
stage. The regular APIs do not install a phase tap.

A proof query records its real iterative deepening verdict probes and its separate
certificate construction pass. Within either pass, quantified search can probe
candidates without constructing proof nodes. Only an event produced by a live
certificate operation has a `proof_node` link. Candidate, unification, antecedent,
indexed-join rejection, short-circuit, witness, cache and bound events describe
those operations at their execution sites. An empty indexed join is identified as
such; it is not described as a leaf check that never ran. These records cover the
published observer points, not every Rust instruction or index access.

Compiler artifacts retain the exact source, parser statement byte spans, parsed
arrays and roots, `lowered_logic` before compute routing, and the final marked
`logic` used by the evaluator. Formula events link their `logic_node` to that
artifact; source references without a span refer to the whole compilation unit.
Rule candidates and derivations separately cite assertion identities. A query's
initial snapshot supplies the assertion registry and profile against which it ran.

Standard recording retains at most 10,000 events and 8 MiB of serialized payload;
full recording retains at most 100,000 events and 64 MiB. Callers may lower either
budget. Payload accounting includes input, snapshots, artifacts, events and error
text, excluding the small record metadata envelope. On overflow, `status` becomes
`truncated` with a reason; the reasoning operation continues normally. The retained
history is a prefix and need not contain matching frame exits. A snapshot or
compiler artifact that does not fit is omitted. The separate typed outcome still
contains the full result or error. `aborted` means the operation failed, while
`disabled` means observations were not requested; neither is a logical verdict.

`apply_changes_recorded` executes the entire ordered assert/withdraw list in one
detached transaction. IDs are returned per operation and per asserted root.
Intermediate nested commits publish only into their immediate candidate. Only the
final `complete`-phase commit denotes publication of the whole change set into the
live session. Any failure discards every tentative source, withdrawal and ID
allocation. Duplicate content retains separate source support; withdrawing one
source does not silently remove another.

`SessionSnapshot` preserves active sources, withdrawn source identities and labels,
compiled roots, next-ID frontier, compute routing, admission declarations and the
engine profile. Import checks schema/version, canonical decimal IDs, uniqueness,
frontier and registries, recompiles every active source, checks its root buffer,
and replays into a fresh unpublished session. Admission declarations retain their
exact literal strings, including non-identifier values and declarations whose
source was withdrawn; they are sorted and unique, and never executed as code.
Sources replay permissively before the saved strict toggle is restored for future
admission. Existential-import is applied before replay because it changes derived
witnesses; materialization restores its configuration with fresh derived caches.
Withdrawn payloads are never parsed or reactivated.

The source-only snapshot boundary rejects native integrity constraints, sort
configuration and rule forward/priority overrides, which this schema cannot
preserve. A recorded operation against such a native KB still runs normally and
retains its execution history, but removes the `recoverable_snapshot` capability
and supplies `snapshot_unavailable_reason`; the successful operation is not
reported as an error or as truncated. Query caches, host compute callbacks,
cancellation handles, diagnostic settings and runtime observer objects are not
snapshot data. Compute callbacks have an explicit host rebind contract: recovery
without rebinding has no external backend and can return UNKNOWN where the original
host supplied a result. Recovered browser sessions likewise have no external
compute backend unless their host explicitly supplies one.

Assertion IDs, event sequences, frames and artifact identities in these DTOs are
decimal strings. IR/proof node indices remain bounded `u32` indices. The existing
canonical `ProofTrace` type retains its own citation encoding; a JavaScript boundary
must preserve its `u64` source IDs when serializing that separate type. Project and
worker epochs belong to the calling application, outside engine identity.
