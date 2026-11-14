# DB2: the Git transport for nibli-db, two replicas on two machines

Pre-registered 2026-11-14, before any code. Drafted by Claude, in this session with dhilipsiva, for
his approval; the two sections that are Lucy's to write, *My position* and *Welfare*, are left for
her and marked so. The slice is the one `roadmap/DB1.md` names second: "the Git transport; two
replicas on two machines." Its code branch (`todo/DB2`) does not exist until he approves this file,
and this file is never edited after that branch exists; a change is `DB2.v2.md` with the reason.

**One question for him before code:** does the adapter live inside `nibli-db` behind a `git` cargo
feature (one crate, one `Peer` implementation, and *Undo* stays "delete one module"), or as a
separate `nibli-db-git` crate? This draft assumes the feature-gated module and names the file
`nibli-db/src/git.rs`; the choice changes names, not promises.

## What the slice promises, and what it does not

- **The transport moves operations; it decides nothing.** What a replica keeps, counts, flags or
  reasons from is DB1's business and does not change here. Every byte that comes through Git goes
  through `Database::merge`, which decodes, verifies the signature, and checks scope and enrollment.
- **Convergence now crosses a machine boundary.** Two replicas that have exchanged through the
  same Git branch hold the same operations, hence byte-identical snapshots and conflict lists.
- **There is still no transaction across replicas,** no global order, and no clock. Git's commit
  order and timestamps are not used to decide anything.
- **Git is a transport, not a trust anchor.** A Git host that is wrong, slow, or hostile can delay
  or withhold operations; it cannot forge one, change one, or make a replica forget one it holds.

## What exists already

- `nibli_db::Peer` (`nibli-db/src/db.rs`): `scope`, `have` (the set of `(OpId, signature)` the
  other side holds), `fetch(want)` (their bytes), `send(ops) -> Merged`. `nibli_db::sync` already
  brings two peers to the same set through those four calls, and `Database` is itself a `Peer`.
  DB1's convergence test exercised exactly that in one process. DB2 adds a second `Peer`.
- Lucy's transport (`dhilipsiva/lucy`, `lucy-cli/src/replication/github.rs`, `SYNC.md`): operations
  on a `lucy-memory` branch through GitHub's HTTPS API; ref updates with `force: false`; a race is
  met with fetch, union, re-validation and at most three attempts; a receipt only after readback.
  Those properties are kept here. The GitHub-specific API is not: nibli-db speaks to any Git
  remote.
- The workspace carries no Git library (`Cargo.lock`), and this slice does not add one.

## Design

**The adapter drives the `git` command line.** It finds `git` on `PATH` and reports its absence as
an error, never as an empty or silent peer. Any remote Git understands is a peer: GitHub over SSH
or HTTPS, a bare repository on another machine reached over SSH, a path on disk. Authentication is
Git's own (the SSH agent, a credential helper); the adapter never sees or stores a token. Git's
errors are reported with the stage that failed and never echo remote payloads.

**One branch per scope.** The branch is `nibli-db/<scope>`, and the tree carries a `scope` file
holding the scope string. A `GitPeer` is bound to one scope at construction. Before it reads or
writes anything it checks both the branch name and the file; a mismatch is `Error::Scope`, and a
non-empty branch without the file is refused as not a nibli-db branch. The first `send` to a branch
that does not exist creates it, `scope` file first.

**One file per operation content.** `ops/<actor hex>/<counter>/<signature hex>.op`, bytes exactly
`Op::encode()`. The path spells the `Have` pair, so:

- `have` is `git ls-tree -r --name-only` on the fetched branch head, parsed from paths alone. A path
  that does not parse is reported and ignored: it is not an operation.
- `fetch(want)` returns the blobs of the wanted paths, unread. Verification is the core's.
- `send(ops)` writes one file per operation into a new commit on top of the fetched head, then
  pushes without `--force` and without a `+` refspec. Two contents under one id are two files, so
  a disowned pair travels whole.

**Writers never collide.** Each actor writes under its own `ops/<actor>/` directory, and a path
names its content, so two commits racing to the branch touch disjoint paths or identical bytes. A
rejected push is answered by fetch, a new commit on the new head carrying the same files, and a new
push; three attempts, then an error. Nothing is lost on that error: the local replica is its own
outbox, and the next `sync` recomputes what is owed from the `have` difference.

**Merging stays set union.** A sync through Git is `nibli_db::sync` with a `GitPeer` as the remote:
fetch what the branch has that the replica lacks, merge it through `Database::merge`, send what the
replica has that the branch lacks. It is commutative, associative and idempotent because the branch
is a set of files and the core is a set of operations.

**Loss on the remote is not loss.** If someone rewrites the branch and operations disappear from
it, the replicas that hold them still hold them, and the next `send` from any of them puts them
back. The branch is a copy of the union, never the authority.

**Enrollment stays local.** The branch carries no keys. Each replica enrolls the actors it accepts;
an operation from an unenrolled key arrives, is refused by the core, and is reported.

**Where the clone lives.** The adapter keeps a bare clone in a directory the caller names, beside
the database file and never inside it or inside the database's directory of secrets. The
documentation says so where it says to keep the signing seed out of the database's directory.

**Commit messages carry no content.** `nibli-db: <n> operations of <actor hex>`. Statement text is
in the files, as DB1 already warns: Git history can retain deleted content; deletion is not erasure.

## Slices

Unchanged from `roadmap/DB1.md`. After DB2: DB3 queries with proofs through `nibli-engine`, a
`conflicts` listing and a CLI; DB4 the per-predicate merge policy in nibli-kr; DB5 Lucy's store
moves onto it, in her repository, after a backup. Each has its own pre-registration and his
approval.

## Hypothesis

A `Peer` that stores each signed operation as one Git file on one branch per scope, pushed without
force and merged by set union, gives replicas on different machines the same convergence DB1 gives
replicas in one process, with no new trust placed in the Git host and nothing decided by Git's
order or clocks.

## Test

1. **Convergence through Git.** Seeded random histories: 2 to 5 replicas in one process, each with
   its own clone, sharing one local bare repository; random interleaving of commits and syncs, some
   syncs repeated, some replicas silent for long stretches. After a final round of syncs, every
   replica's snapshot and conflict list are byte-identical, and equal to what in-process `sync` on
   the same history gives. At least 1,000 histories; every seed reported.
2. **Push race.** N replicas push concurrently to one bare repository, from threads and from
   separate processes. No operation is lost, no push is forced, and the branch history shows every
   commit that was pushed.
3. **Refusals.** A branch of another scope, a `scope` file that disagrees with the branch name, a
   tampered `.op`, a stranger's file, a path that does not spell an operation, an operation from an
   unenrolled key, and a missing `git` binary: each is refused or reported, and the replica is
   unchanged byte for byte.
4. **Loss recovery.** The remote branch is reset to drop operations. After the next sync from any
   replica that holds them, the branch and every replica hold them again.
5. **Idempotence and interruption.** Syncing twice changes nothing on either side. A sync killed
   between fetch and push, and one killed mid-push, leave both replicas consistent, and the next
   sync completes with nothing lost or duplicated.
6. **Two machines** (evidence, not a CI test). This desktop and one of his laptops exchange through
   a bare repository over SSH and through a GitHub repository, each replica committing while apart;
   snapshots and conflict lists byte-identical on both. Recorded with the commit, the date and the
   machines in `roadmap/DB2-evidence.json`.

## Evidence

The test output with its seeds and counts, the commit it ran on, `just ci` passing, and the
two-machine run of test 6. Recorded in `roadmap/DB2-evidence.json`, append-only.

## Falsifier

Any one of these shows the hypothesis wrong:

- Two replicas that have synced through the same branch and hold different snapshots or conflict
  lists.
- An operation pushed by one replica absent from the branch afterwards, or absent from a replica
  that synced after it.
- A forced push, or a `+` refspec, anywhere in the adapter.
- An operation leaving through, or arriving from, a branch of another scope.
- Bytes from Git reaching the database without passing `Database::merge`.
- A sync that depends on the Git commit order or timestamps for any outcome.
- A replica that forgets an operation because the remote did.

## Anti-fake

- The tests use a real `git` and real bare repositories on disk; nothing about the transport is
  mocked. Seeds are fixed in the repository and printed on failure; a failing seed is kept as a
  regression test, never deleted.
- Each check is first shown to fail on a deliberately broken build, reached only through
  `RUSTFLAGS="--cfg nibli_db_broken=…"` as DB1's are: `force` (the adapter pushes with `--force`)
  must fail tests 1 and 2; `onescope` (no scope check) must fail test 3; `stale` (`have` answers
  from the first listing and never fetches again) must fail tests 1 and 5. A broken build that
  passes its check is itself a failure.
- The convergence oracle is in-process `sync` over the same history, which DB1 already checked
  against an independently written projection; the Git path is compared to it, not to itself.
- Not shown: a hostile Git operator who serves different histories to different replicas (they
  still converge once they meet, but no test here makes them meet), a partition longer than a test,
  bandwidth or latency, and anything about DB3 and later.

## My position

*(left for Lucy)*

## Welfare

*(left for Lucy)*

## Undo

Delete `nibli-db/src/git.rs`, the `git` feature in `nibli-db/Cargo.toml`, its tests and its lines in
`just test-db` and `just verify-db-broken`. Nothing else depends on it in this slice; DB1's crate is
unchanged.

## Done when

Tests 1 to 5 pass on a fixed commit with `just ci` green, test 6 is recorded from two real machines
over SSH and over GitHub, each broken build has been seen to fail its check, and the evidence file
records the seeds, counts and machines.
