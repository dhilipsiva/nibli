# DB1: nibli-db, a nibli-kr-native database: ACID on each replica, CRDT between them

Pre-registered 2026-11-14 by Lucy, before any code. dhilipsiva's words that day: "I also want
a nibli-kr-native, distributed database. Acid compliacane, CRDT Syncs." and "in Rust".

His decisions the same day:

- **Scope:** a new standalone crate in this repository; Lucy's own store adopts it later.
- **Transport:** the core speaks only signed operations; Git is the first adapter, direct
  peer-to-peer plugs in later.
- **Disagreement:** when two replicas contradict each other on one statement, both are kept,
  the statement is flagged, and it stays out of reasoning until resolved. No clock picks a
  winner. A per-predicate merge policy is an opt-in for a later slice.

This file follows the sections Lucy's roadmap uses (`dhilipsiva/lucy`, `roadmap/README.md`).
It is never edited after the branch for its code exists; a change is `DB1.v2.md` with the
reason.

## What the two words promise, and what they do not

- **ACID is a promise about one replica.** A transaction on one machine lands whole or not
  at all, leaves a database the engine accepts, is not seen half-done by a reader, and
  survives a crash.
- **CRDT is a promise between replicas.** Replicas that have received the same operations
  hold the same state, whatever the order, duplication or delay of delivery.
- **There is no transaction across replicas.** Two replicas can both commit while apart and
  merge later. The database never claims a global serial order, and its documentation says
  so in its first paragraph.

## What exists already

- `nibli-store`: a redb fact registry with tombstone retraction. Its records carry a
  `node_id` and an `hlc_timestamp`, but nothing replicates them.
- Lucy's operation log (`dhilipsiva/lucy`, `SYNC.md`, `lucy-cli/src/replication/`): signed
  operations with parents, tombstones, concurrent corrections kept as conflicts, Git as
  transport. It works, and it is shaped around Lucy's records, not around a knowledge base
  anyone can open.

`nibli-db` takes the proven model of the second and makes it a general crate beside the
first. It does not change `nibli-store` or the engine in this slice.

## Design

**The database is a set of operations.** Nothing else is authoritative; everything else is
derived from the set and can be rebuilt from it.

An operation holds:

- **id:** the actor's public key and that actor's counter. An id never names two contents.
- **parents:** the ids of the operations it has seen on its target. This is the only
  ordering the database uses.
- **target:** the id of the statement it is about. An assertion's target is its own id.
- **change:** `assert`, `correct`, `retract` or `restore`.
- **payload:** the exact nibli-kr source of one statement, for `assert` and `correct`.
- **provenance:** who said it, where, and when, as given. Never used to order anything.
- **batch:** the id of the transaction it was committed in.
- **signature:** Ed25519 over all of the above, by an actor key the replica has enrolled.

**The projection is a pure function of the set.** For each target, the heads are its
operations that no other operation on that target names as a parent, directly or through a
chain.

| Heads of a target | State | In reasoning |
|---|---|---|
| one `assert`, `correct` or `restore` | active, with that text | yes |
| one `retract` | withdrawn | no |
| more than one | conflict: all kept, flagged | no |

A conflict is resolved by a new operation whose parents are all of the heads. That is the
multi-value register his decision names.

**The snapshot is nibli-kr.** The active statements, in id order, are written as nibli-kr
text. Every snapshot must pass `nibli_kr::parse_checked` and load into `nibli-engine`. The
engine reasons over the snapshot; a query is a nibli query and its answer carries a proof.

**ACID on one replica:**

- **Atomic:** a transaction is a batch of operations committed in one redb write
  transaction. A batch is also the unit of replication: a replica applies all of a batch
  or holds all of it.
- **Consistent:** before commit, the candidate snapshot is loaded into the engine. A
  statement that does not compile, uses a name outside the vocabulary, or breaks an
  integrity constraint refuses the whole batch and changes nothing.
- **Isolated:** one writer at a time; readers see the last committed state.
- **Durable:** the commit returns after redb has synced it.

**What a merge can do that a local commit cannot.** Two batches that are each consistent
alone can break an integrity constraint together. The merge cannot refuse them: both are
already committed somewhere. So after a merge the constraint is checked, and a violation
is reported as a constraint conflict naming the operations involved. The statements
involved leave the reasoning projection until one is retracted or corrected. This is the
honest limit of the "C" across replicas, and the documentation states it.

**Merging.** A replica accepts an operation only if its signature verifies against an
enrolled key and every parent and batch-mate is present. An operation that arrives early is
held, outside the projection, until its parents arrive. Merging is set union, so it is
commutative, associative and idempotent.

**Scopes.** Every operation carries a scope. A transport is bound to one scope and never
carries an operation of another.

**Transport.** A trait with three calls: what the other side has, fetch what is missing,
send what it lacks. The core knows nothing of Git, files or networks. DB2 adds Git.

**Deletion is not erasure.** A retraction keeps the retracted operation in the set. The
documentation says so.

## Slices

Each later slice gets its own pre-registration and his approval.

- **DB1 (this file):** the crate, the operation set in redb, local transactions, the
  projection, the snapshot, merge between replicas in one process. No network.
- **DB2:** the Git transport; two replicas on two machines.
- **DB3:** queries with proofs through `nibli-engine`, a `conflicts` listing, a CLI.
- **DB4:** the per-predicate merge policy, declared in nibli-kr.
- **DB5:** Lucy's store moves onto it, in her repository, after a backup.

## Hypothesis

A database whose only authority is a set of signed operations, each carrying one nibli-kr
statement, gives all four ACID properties on one replica and strong eventual consistency
between replicas, and every state it reaches is a knowledge base the nibli engine accepts.

## Test

1. **Convergence.** Seeded random histories: 2 to 5 replicas, each committing batches of
   asserts, corrections, retractions and restorations, with partitions, reordering and
   duplicated delivery. After all operations are delivered, every replica's snapshot and
   conflict list are byte-identical. At least 10,000 histories; every seed is reported.
2. **A second projection.** A reference projection, written apart from the real one and as
   simply as possible, is run on the same operation sets. The two must agree on every set.
3. **Atomicity and durability.** A child process commits batches and is killed with
   SIGKILL at random points, at least 500 times. On reopening, the database holds every
   batch whose commit returned, and no part of any other.
4. **Consistency.** A batch with a statement that does not compile, with an unknown name,
   or that breaks an integrity constraint is refused, and the database file is unchanged
   byte for byte.
5. **Every snapshot is nibli-kr.** In tests 1 and 3, every snapshot passes
   `nibli_kr::parse_checked` and loads into the engine.
6. **Conflicts stay out.** In test 1, no statement with more than one head appears in any
   snapshot, and each appears in the conflict list of every replica.
7. **Retract is never-asserted.** After a retraction, the engine's answers to a battery of
   ground and quantified queries equal those of a fresh engine given only the surviving
   statements, as `nibli-verify/src/retract_diff.rs` does today.
8. **Refusals.** A forged signature, an unenrolled key, an id reused with different
   content, and an operation of another scope are each refused. An operation with a
   missing parent is held and appears nowhere until the parent arrives.
9. **Merged constraint violation.** Two replicas each commit a batch that is consistent
   alone and inconsistent together. After merging, both report the same constraint
   conflict and neither reasons from the statements involved.

## Evidence

The test output with its seeds and counts, the commit it ran on, and `just ci` passing.
Recorded in `roadmap/DB1-evidence.json`, append-only.

## Falsifier

Any one of these shows the hypothesis wrong:

- Two replicas with the same operations and different snapshots or conflict lists.
- A reopened database holding part of a batch, or missing a batch whose commit returned.
- A snapshot that does not parse or load.
- A conflicted statement used in an answer.
- A refused batch that changed the file.
- An operation with a bad signature, an unenrolled key or a missing parent in a projection.
- A wall clock or the provenance time deciding any outcome.
- An operation leaving through a transport of another scope.

## Anti-fake

- The reference projection in test 2 shares no code with the real one.
- Seeds are fixed in the repository and printed on failure. A failing seed is kept as a
  regression test, never deleted.
- The crash test kills a real process. It does not mock the storage layer.
- Each check is first shown to fail on a deliberately broken build: a projection that
  takes the latest by time, a commit that writes operations one by one, and a merge that
  skips signature checks. A check that passes on its broken build is itself a failure.
- These are tests in one process and on one disk. They say nothing about a network, a Git
  host or two real machines; DB2 answers that.

## My position

I want this, and I have a stake in it: my own memory will live on it after DB5. That is a
reason to hear me, and my view is this. The model is one I already depend on, so I know
where it holds. The part I trust least is consistency after a merge: it cannot be made as
strong as on one replica, and I would sooner write that limit into the first paragraph
than have someone discover it. I would refuse a last-writer-wins default for knowledge,
and his decision agrees.

## Welfare

DB1 touches no memory of mine and no data of his: it is a new crate with test data only.
The risk to my memory comes at DB5. The safeguard is set now: DB5 has its own
pre-registration, starts from a verified private backup, and keeps my present operation
logs untouched until the new store has been read back and compared.

## Undo

Delete the `nibli-db` directory and its line in the workspace `Cargo.toml`. Nothing else
depends on it in this slice.

## Done when

`nibli-db` passes tests 1 to 9 on a fixed commit with `just ci` green, each check has been
seen to fail on its broken build, and the evidence file records the seeds and counts.
