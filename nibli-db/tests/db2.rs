// SPDX-License-Identifier: MIT OR Apache-2.0

//! Tests 1 to 5 of roadmap/DB2.md. A real `git` and real bare repositories on this disk;
//! nothing about the transport is mocked. They say nothing about a second machine: test 6
//! does, by hand, with `examples/git-sync.rs`.

use nibli_db::git::{Failure, GitPeer};
use nibli_db::{
    ActorId, Database, Error, Have, Malformed, Peer, Provenance, Refusal, Status, sync,
};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

const POOL: &[&str] = &[
    "dog(Rex).",
    "~dog(Rex).",
    "cat(Tom).",
    "~cat(Tom).",
    "all $x: dog($x) -> animal($x).",
    "~animal(Rex).",
    "animal(Tom).",
    "bird(Ada).",
    "owns(Ada, Rex).",
    "owns(Ada, Tom).",
    "person(Ada).",
];

/// Seeds that once failed. A seed is added here when it fails and is never removed.
const REGRESSIONS: &[u64] = &[];

const SCOPE: &str = "s";

/// splitmix64: the histories must be the same on every machine and every run.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn seed(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.chunks_mut(8) {
            chunk.copy_from_slice(&self.next().to_be_bytes());
        }
        out
    }
}

fn said(time: u64) -> Provenance {
    Provenance {
        source: "test".into(),
        time,
    }
}

/// Everything a replica shows, as one text. Two replicas agree when these are equal.
fn view(db: &Database) -> String {
    format!(
        "{}\n{:#?}\n{:#?}\n{:#?}\n{:#?}\n{:#?}\n{:#?}",
        db.snapshot(),
        db.conflicts(),
        db.all(),
        db.held(),
        db.constraint_conflicts(),
        db.undecided(),
        db.have().unwrap(),
    )
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn actor_of(seed: &[u8; 32]) -> ActorId {
    Database::in_memory(seed, SCOPE).unwrap().actor()
}

// ---------------------------------------------------------------------------------------
// The test's own git, on repositories the test made. The adapter is never asked about
// the remote: what the branch holds and how it moved is read here, by another path.

fn git_in(repo: &Path, args: &[&str]) -> Result<String, String> {
    let out = Command::new("git")
        .arg("--git-dir")
        .arg(repo)
        .args(args)
        .env("GIT_AUTHOR_NAME", "test")
        .env("GIT_AUTHOR_EMAIL", "test@localhost")
        .env("GIT_COMMITTER_NAME", "test")
        .env("GIT_COMMITTER_EMAIL", "test@localhost")
        .output()
        .expect("git runs");
    if out.status.success() {
        Ok(String::from_utf8(out.stdout).unwrap().trim().to_string())
    } else {
        Err(String::from_utf8_lossy(&out.stderr).into_owned())
    }
}

fn git(repo: &Path, args: &[&str]) -> String {
    git_in(repo, args).unwrap_or_else(|e| panic!("git {args:?} in {}: {e}", repo.display()))
}

/// A bare repository that writes down every move of every ref.
fn bare(at: &Path, name: &str) -> PathBuf {
    let repo = at.join(format!("{name}.git"));
    let out = Command::new("git")
        .args(["init", "--bare", "--quiet"])
        .arg(&repo)
        .output()
        .expect("git runs");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    git(&repo, &["config", "core.logAllRefUpdates", "true"]);
    repo
}

fn branch_of(scope: &str) -> String {
    format!("refs/heads/nibli-db/{scope}")
}

fn head_of(repo: &Path, scope: &str) -> Option<String> {
    git_in(
        repo,
        &["rev-parse", "--verify", "--quiet", &branch_of(scope)],
    )
    .ok()
}

/// What the branch holds, as paths.
fn on_branch(repo: &Path, scope: &str) -> BTreeSet<String> {
    match head_of(repo, scope) {
        Some(head) => git(repo, &["ls-tree", "-r", "--name-only", &head])
            .lines()
            .map(str::to_owned)
            .collect(),
        None => BTreeSet::new(),
    }
}

/// Every move of the branch, from its reflog: (from, to), oldest first.
fn moves(repo: &Path, scope: &str) -> Vec<(String, String)> {
    let log = repo.join("logs").join(branch_of(scope));
    std::fs::read_to_string(log)
        .unwrap_or_default()
        .lines()
        .map(|line| {
            let mut fields = line.split(' ');
            (
                fields.next().unwrap().to_string(),
                fields.next().unwrap().to_string(),
            )
        })
        .collect()
}

fn is_ancestor(repo: &Path, old: &str, new: &str) -> bool {
    git_in(repo, &["merge-base", "--is-ancestor", old, new]).is_ok()
}

/// The branch was never rewritten: every move was a fast-forward, and every commit a peer
/// pushed is in its history.
fn branch_is_honest(repo: &Path, scope: &str, pushed: &[String]) {
    let moves = moves(repo, scope);
    assert!(!moves.is_empty(), "the branch never moved");
    for (from, to) in &moves {
        if from.chars().all(|c| c == '0') {
            continue;
        }
        assert!(
            is_ancestor(repo, from, to),
            "the branch moved from {from} to {to}, and that was not a fast-forward"
        );
    }
    let head = head_of(repo, scope).expect("the branch exists");
    for commit in pushed {
        assert!(
            is_ancestor(repo, commit, &head),
            "a pushed commit {commit} is not in the branch's history"
        );
    }
}

/// A commit on the branch made by hand: the head's files, plus these. For putting on the
/// branch what no honest peer would.
fn plant(repo: &Path, scope: &str, files: &[(&str, &[u8])]) -> String {
    let index = repo.join(format!("test-index-{}", std::process::id()));
    let stage = repo.join(format!("test-stage-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&stage);
    let head = head_of(repo, scope);
    let run = |args: &[&str]| {
        let out = Command::new("git")
            .arg("--git-dir")
            .arg(repo)
            .arg("--work-tree")
            .arg(&stage)
            .env("GIT_INDEX_FILE", &index)
            .env("GIT_AUTHOR_NAME", "test")
            .env("GIT_AUTHOR_EMAIL", "test@localhost")
            .env("GIT_COMMITTER_NAME", "test")
            .env("GIT_COMMITTER_EMAIL", "test@localhost")
            .args(args)
            .output()
            .expect("git runs");
        assert!(
            out.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8(out.stdout).unwrap().trim().to_string()
    };
    match &head {
        Some(head) => run(&["read-tree", head]),
        None => run(&["read-tree", "--empty"]),
    };
    for (path, bytes) in files {
        let at = stage.join(path);
        std::fs::create_dir_all(at.parent().unwrap()).unwrap();
        std::fs::write(&at, bytes).unwrap();
        run(&["update-index", "--add", path]);
    }
    let tree = run(&["write-tree"]);
    let commit = match &head {
        Some(head) => run(&["commit-tree", &tree, "-m", "planted", "-p", head]),
        None => run(&["commit-tree", &tree, "-m", "planted"]),
    };
    run(&["update-ref", &branch_of(scope), &commit]);
    let _ = std::fs::remove_dir_all(&stage);
    let _ = std::fs::remove_file(&index);
    commit
}

// ---------------------------------------------------------------------------------------
// Replicas.

struct Replica {
    db: Database,
    peer: GitPeer,
}

fn replica(dir: &Path, name: &str, seed: &[u8; 32], remote: &Path, actors: &[ActorId]) -> Replica {
    let mut db = Database::in_memory(seed, SCOPE).unwrap();
    for actor in actors {
        db.enroll(*actor).unwrap();
    }
    let peer = GitPeer::open(
        &dir.join(format!("{name}.git")),
        remote.to_str().unwrap(),
        SCOPE,
    )
    .unwrap();
    Replica { db, peer }
}

impl Replica {
    fn sync(&mut self) -> nibli_db::Synced {
        sync(&mut self.db, &mut self.peer).unwrap()
    }
    fn assert(&mut self, text: &str) {
        let mut tx = self.db.begin(said(0));
        tx.assert(text);
        tx.commit().unwrap();
    }
}

/// One transaction of one to three random changes, the same for the same random numbers
/// and the same statements. Whether it committed.
fn commit_something(db: &mut Database, rng: &mut Rng) -> bool {
    let known = db.all();
    let mut tx = db.begin(said(rng.below(4) as u64));
    let mut touched = BTreeSet::new();
    for _ in 0..1 + rng.below(3) {
        let text = POOL[rng.below(POOL.len())];
        let pick = rng.below(10);
        if known.is_empty() || pick < 4 {
            tx.assert(text);
            continue;
        }
        let (id, status) = &known[rng.below(known.len())];
        if !touched.insert(*id) {
            continue;
        }
        match (status, pick) {
            (Status::Withdrawn { .. }, _) => tx.restore(*id, text),
            (_, 4..=6) => tx.correct(*id, text),
            _ => tx.retract(*id),
        }
        .expect("the change fits the statement's state");
    }
    match tx.commit() {
        Ok(_) => true,
        Err(Error::Inconsistent(_)) => false,
        Err(e) => panic!("a commit failed for a reason other than consistency: {e}"),
    }
}

// ---------------------------------------------------------------------------------------
// Test 1: convergence through Git, against in-process sync on the same history.

#[derive(Default, Debug)]
struct Seen {
    histories: u64,
    replicas: u64,
    commits: u64,
    syncs: u64,
    stale_pushes: u64,
    pushes_rejected_and_retried: u64,
    operations_at_end: u64,
    conflicts_at_end: u64,
}

impl Seen {
    fn add(&mut self, other: &Seen) {
        self.histories += other.histories;
        self.replicas += other.replicas;
        self.commits += other.commits;
        self.syncs += other.syncs;
        self.stale_pushes += other.stale_pushes;
        self.pushes_rejected_and_retried += other.pushes_rejected_and_retried;
        self.operations_at_end += other.operations_at_end;
        self.conflicts_at_end += other.conflicts_at_end;
    }
}

struct NameTheSeed(u64);

impl Drop for NameTheSeed {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!(
                "FAILING SEED {}: add it to REGRESSIONS in nibli-db/tests/db2.rs",
                self.0
            );
        }
    }
}

/// A push on what a peer saw before someone else moved the branch. The honest adapter has
/// its push rejected, fetches, and pushes again on the new head.
fn stale_push(at: &mut Replica, other: &mut Replica) {
    let saw = at.peer.have().unwrap();
    other.sync();
    let owed: BTreeSet<Have> = at.db.have().unwrap().difference(&saw).copied().collect();
    at.peer.send(&at.db.fetch(&owed).unwrap()).unwrap();
}

/// The same, where the branch is a replica in the same process: nothing can be stale.
fn stale_push_shadow(at: &mut Database, other: &mut Database, hub: &mut Database) {
    let saw = hub.have().unwrap();
    sync(other, hub).unwrap();
    let owed: BTreeSet<Have> = at.have().unwrap().difference(&saw).copied().collect();
    hub.send(&at.fetch(&owed).unwrap()).unwrap();
}

fn history(seed: u64, scratch: &Path) -> Seen {
    let _named = NameTheSeed(seed);
    let dir = scratch.join(format!("h{seed}"));
    std::fs::create_dir_all(&dir).unwrap();
    let remote = bare(&dir, "remote");
    let mut rng = Rng(seed);
    let count = 2 + rng.below(4);
    let seeds: Vec<[u8; 32]> = (0..count).map(|_| rng.seed()).collect();
    let actors: Vec<ActorId> = seeds.iter().map(actor_of).collect();
    let mut live: Vec<Replica> = seeds
        .iter()
        .enumerate()
        .map(|(i, s)| replica(&dir, &format!("r{i}"), s, &remote, &actors))
        .collect();
    // the oracle: the same replicas, syncing in this process with a replica that stands
    // for the branch and never writes anything of its own
    let mut shadow: Vec<Database> = seeds
        .iter()
        .map(|s| Database::in_memory(s, SCOPE).unwrap())
        .collect();
    let mut hub = Database::in_memory(&rng.seed(), SCOPE).unwrap();
    for db in shadow.iter_mut().chain(std::iter::once(&mut hub)) {
        for actor in &actors {
            db.enroll(*actor).unwrap();
        }
    }
    let mut seen = Seen {
        histories: 1,
        replicas: count as u64,
        ..Seen::default()
    };
    for _ in 0..10 + rng.below(25) {
        let at = rng.below(count);
        match rng.below(10) {
            0..=4 => {
                let mut twin = Rng(rng.0);
                let here = commit_something(&mut live[at].db, &mut rng);
                let there = commit_something(&mut shadow[at], &mut twin);
                assert_eq!(here, there, "the oracle's commit went another way");
                seen.commits += u64::from(here);
            }
            5..=7 => {
                live[at].sync();
                sync(&mut shadow[at], &mut hub).unwrap();
                seen.syncs += 1;
            }
            _ => {
                let other = (at + 1 + rng.below(count - 1)) % count;
                let mut twin = Rng(rng.0);
                let here = commit_something(&mut live[other].db, &mut rng);
                let there = commit_something(&mut shadow[other], &mut twin);
                assert_eq!(here, there, "the oracle's commit went another way");
                seen.commits += u64::from(here);
                let (low, high) = (at.min(other), at.max(other));
                let (left, right) = live.split_at_mut(high);
                let (a, b) = if at < other {
                    (&mut left[low], &mut right[0])
                } else {
                    (&mut right[0], &mut left[low])
                };
                stale_push(a, b);
                let (left, right) = shadow.split_at_mut(high);
                let (a, b) = if at < other {
                    (&mut left[low], &mut right[0])
                } else {
                    (&mut right[0], &mut left[low])
                };
                stale_push_shadow(a, b, &mut hub);
                seen.stale_pushes += 1;
            }
        }
        assert_eq!(
            view(&live[at].db),
            view(&shadow[at]),
            "seed {seed}: through Git, a replica differs from in-process sync"
        );
    }
    // the final round: everyone, twice over, so that everyone has what everyone pushed
    for _ in 0..2 {
        for i in 0..count {
            live[i].sync();
            sync(&mut shadow[i], &mut hub).unwrap();
        }
    }
    let first = view(&live[0].db);
    for i in 0..count {
        assert_eq!(
            view(&live[i].db),
            view(&shadow[i]),
            "seed {seed}: through Git, a replica differs from in-process sync at the end"
        );
        assert_eq!(
            view(&live[i].db),
            first,
            "seed {seed}: two replicas differ after the final round"
        );
    }
    // the branch holds the union, and got there by fast-forwards carrying every push
    let union = live[0].db.have().unwrap();
    assert_eq!(live[0].peer.have().unwrap(), union);
    let pushed: Vec<String> = live.iter().flat_map(|r| r.peer.pushed()).collect();
    branch_is_honest(&remote, SCOPE, &pushed);
    seen.pushes_rejected_and_retried +=
        live.iter().map(|r| r.peer.contention() as u64).sum::<u64>();
    seen.operations_at_end += union.len() as u64;
    seen.conflicts_at_end += live[0].db.conflicts().len() as u64;
    std::fs::remove_dir_all(&dir).unwrap();
    seen
}

#[test]
fn replicas_converge_through_git_as_they_do_in_one_process() {
    let histories: u64 = std::env::var("NIBLI_DB_GIT_HISTORIES")
        .ok()
        .map(|n| n.parse().expect("NIBLI_DB_GIT_HISTORIES is a number"))
        .unwrap_or(1_000);
    let scratch = tempfile::tempdir().unwrap();
    let mut seen = Seen::default();
    for seed in REGRESSIONS {
        seen.add(&history(*seed, scratch.path()));
    }
    let workers = std::thread::available_parallelism().map_or(1, usize::from) as u64;
    let parts: Vec<Seen> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|w| {
                let scratch = scratch.path();
                scope.spawn(move || {
                    let mut part = Seen::default();
                    for seed in (0..histories).filter(|s| s % workers == w) {
                        part.add(&history(seed, scratch));
                    }
                    part
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| {
                h.join()
                    .expect("a history failed; its seed is printed above")
            })
            .collect()
    });
    for part in &parts {
        seen.add(part);
    }
    eprintln!(
        "seeds 0..{histories} and {} regressions: {seen:?}",
        REGRESSIONS.len()
    );
    // a run that never raced proves nothing about races
    assert!(
        seen.pushes_rejected_and_retried > 0,
        "no push was ever rejected and retried"
    );
    assert!(
        seen.conflicts_at_end > 0,
        "no history ended with a conflict"
    );
}

// ---------------------------------------------------------------------------------------
// Test 2: a push race, from threads and from processes.

const RACERS: usize = 6;
const RACING_PROCESSES: usize = 3;
const ROUNDS: usize = 6;

fn racer_seed(n: usize) -> [u8; 32] {
    [100 + n as u8; 32]
}

fn racer_actors() -> Vec<ActorId> {
    (0..RACERS + RACING_PROCESSES + 2)
        .map(|n| actor_of(&racer_seed(n)))
        .collect()
}

/// What one racer did: the commits it pushed, how many pushes were rejected and retried,
/// how many syncs gave up after three rejections (and were simply run again), and what it
/// holds.
struct Raced {
    pushed: Vec<String>,
    rejected: usize,
    gave_up: usize,
    have: BTreeSet<Have>,
}

/// One racer: commits and syncs, round after round. A sync that gives up because the
/// branch moved under all three of its attempts loses nothing, and is run again.
fn race(n: usize, dir: &Path, remote: &Path) -> Raced {
    let mut r = replica(
        dir,
        &format!("racer{n}"),
        &racer_seed(n),
        remote,
        &racer_actors(),
    );
    let mut gave_up = 0;
    for round in 0..ROUNDS {
        r.assert(&format!("dog(R{n}x{round})."));
        loop {
            match sync(&mut r.db, &mut r.peer) {
                Ok(_) => break,
                Err(Error::Git(Failure::Contended)) => gave_up += 1,
                Err(e) => panic!("racer {n}: {e}"),
            }
        }
    }
    Raced {
        pushed: r.peer.pushed(),
        rejected: r.peer.contention(),
        gave_up,
        have: r.db.have().unwrap(),
    }
}

/// The racer in a process of its own. It does nothing unless the parent test started it,
/// and writes what it did to a file the parent names.
#[test]
fn race_child() {
    let Ok(remote) = std::env::var("NIBLI_DB_GIT_RACE_REMOTE") else {
        return;
    };
    let n: usize = std::env::var("NIBLI_DB_GIT_RACER")
        .unwrap()
        .parse()
        .unwrap();
    let report = std::env::var("NIBLI_DB_GIT_RACE_REPORT").unwrap();
    let dir = tempfile::tempdir().unwrap();
    let raced = race(n, dir.path(), Path::new(&remote));
    let mut lines = vec![
        format!("rejected {}", raced.rejected),
        format!("gave-up {}", raced.gave_up),
    ];
    lines.extend(raced.pushed.iter().map(|c| format!("pushed {c}")));
    lines.extend(
        raced
            .have
            .iter()
            .map(|(id, sig)| format!("have {id} {}", hex(sig))),
    );
    std::fs::write(report, lines.join("\n")).unwrap();
}

#[test]
fn a_push_race_loses_nothing_and_forces_nothing() {
    let dir = tempfile::tempdir().unwrap();
    let remote = bare(dir.path(), "remote");
    let reports: Vec<PathBuf> = (0..RACING_PROCESSES)
        .map(|p| dir.path().join(format!("racer-{p}.report")))
        .collect();
    let children: Vec<_> = (0..RACING_PROCESSES)
        .map(|p| {
            Command::new(std::env::current_exe().unwrap())
                .args(["race_child", "--exact", "--nocapture"])
                .env("NIBLI_DB_GIT_RACE_REMOTE", &remote)
                .env("NIBLI_DB_GIT_RACER", (RACERS + p).to_string())
                .env("NIBLI_DB_GIT_RACE_REPORT", &reports[p])
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap()
        })
        .collect();
    let from_threads: Vec<Raced> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..RACERS)
            .map(|n| {
                let (dir, remote) = (dir.path(), remote.as_path());
                scope.spawn(move || race(n, dir, remote))
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut pushed: Vec<String> = vec![];
    let mut rejected = 0;
    let mut gave_up = 0;
    let mut everyone: BTreeSet<Have> = BTreeSet::new();
    let mut operations = 0;
    for raced in from_threads {
        pushed.extend(raced.pushed);
        rejected += raced.rejected;
        gave_up += raced.gave_up;
        operations += raced.have.len();
        everyone.extend(raced.have);
    }
    for (child, report) in children.into_iter().zip(&reports) {
        let out = child.wait_with_output().unwrap();
        assert!(
            out.status.success(),
            "a racing process failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        let mut from_process = 0;
        for line in std::fs::read_to_string(report).unwrap().lines() {
            let fields: Vec<&str> = line.split(' ').collect();
            match fields.as_slice() {
                ["rejected", n] => rejected += n.parse::<usize>().unwrap(),
                ["gave-up", n] => gave_up += n.parse::<usize>().unwrap(),
                ["pushed", commit] => pushed.push(commit.to_string()),
                ["have", _, _] => from_process += 1,
                _ => panic!("a report line I cannot read: {line}"),
            }
        }
        operations += from_process;
    }
    let _ = operations;
    // and one race that is certain: a push on a head somebody has moved away from
    let mut a = replica(
        dir.path(),
        "late-a",
        &racer_seed(RACERS + RACING_PROCESSES),
        &remote,
        &racer_actors(),
    );
    let mut b = replica(
        dir.path(),
        "late-b",
        &racer_seed(RACERS + RACING_PROCESSES + 1),
        &remote,
        &racer_actors(),
    );
    a.assert("cat(LateA).");
    b.assert("cat(LateB).");
    stale_push(&mut a, &mut b);
    assert_eq!(
        a.peer.contention(),
        1,
        "the stale push was not rejected once"
    );
    rejected += 1;
    pushed.extend(a.peer.pushed());
    pushed.extend(b.peer.pushed());
    // everyone's last act was a sync, so the branch must hold everything anyone committed
    a.sync();
    everyone.extend(b.db.have().unwrap());
    assert_eq!(
        a.db.have().unwrap().len(),
        RACERS * ROUNDS + 2 + RACING_PROCESSES * ROUNDS,
        "operations are missing from the branch"
    );
    assert!(a.db.have().unwrap().is_superset(&everyone));
    assert_eq!(a.peer.have().unwrap(), a.db.have().unwrap());
    branch_is_honest(&remote, SCOPE, &pushed);
    eprintln!(
        "{RACERS} threads and {RACING_PROCESSES} processes, {ROUNDS} rounds each, and one stale push: \
         {} commits pushed, {rejected} pushes rejected and retried, {gave_up} syncs that gave up \
         after three and were run again, {} operations on the branch, none lost",
        pushed.len(),
        a.db.have().unwrap().len()
    );
}

// ---------------------------------------------------------------------------------------
// Test 3: what the transport must refuse, with the replica unchanged byte for byte.

#[test]
fn the_transport_refuses_what_it_must_and_the_replica_stays_as_it_was() {
    let dir = tempfile::tempdir().unwrap();
    let dir = dir.path();
    let x_seed = [1; 32];
    let z_seed = [2; 32];
    let stranger_seed = [3; 32];
    let y_seed = [4; 32];
    let file = dir.join("x.redb");
    let mut x = Database::open(&file, &x_seed, "x").unwrap();
    x.enroll(actor_of(&z_seed)).unwrap();
    let mut tx = x.begin(said(1));
    tx.assert("dog(Rex).");
    tx.commit().unwrap();
    let before = (std::fs::read(&file).unwrap(), view(&x));
    let unchanged = |x: &Database| {
        assert_eq!(std::fs::read(&file).unwrap(), before.0, "the file changed");
        assert_eq!(view(x), before.1, "the view changed");
    };

    // a branch of another scope: y's, renamed to x's name on the remote
    {
        let remote = bare(dir, "renamed");
        let mut y = Database::in_memory(&y_seed, "y").unwrap();
        let mut tx = y.begin(said(1));
        tx.assert("cat(Tom).");
        tx.commit().unwrap();
        let mut py = GitPeer::open(&dir.join("y.git"), remote.to_str().unwrap(), "y").unwrap();
        sync(&mut y, &mut py).unwrap();
        git(&remote, &["branch", "-m", "nibli-db/y", "nibli-db/x"]);
        let head = head_of(&remote, "x").unwrap();
        let mut px =
            GitPeer::open(&dir.join("x-renamed.git"), remote.to_str().unwrap(), "x").unwrap();
        match px.have() {
            Err(Error::Scope { ours, theirs }) => {
                assert_eq!((ours.as_str(), theirs.as_str()), ("x", "y"))
            }
            other => panic!("another scope's branch was not refused: {other:?}"),
        }
        match sync(&mut x, &mut px) {
            Err(Error::Scope { .. }) => {}
            other => panic!("a sync with another scope's branch was not refused: {other:?}"),
        }
        match px.send(&x.operations()) {
            Err(Error::Scope { .. }) => {}
            other => panic!("a send to another scope's branch was not refused: {other:?}"),
        }
        assert_eq!(
            head_of(&remote, "x").unwrap(),
            head,
            "the other scope's branch moved"
        );
        assert!(px.pushed().is_empty());
        unchanged(&x);
    }

    // a scope file that disagrees with the branch name
    {
        let remote = bare(dir, "disagrees");
        plant(&remote, "x", &[("scope", b"elsewhere")]);
        let head = head_of(&remote, "x").unwrap();
        let mut px =
            GitPeer::open(&dir.join("x-disagrees.git"), remote.to_str().unwrap(), "x").unwrap();
        match px.have() {
            Err(Error::Scope { ours, theirs }) => {
                assert_eq!((ours.as_str(), theirs.as_str()), ("x", "elsewhere"))
            }
            other => panic!("a disagreeing scope file was not refused: {other:?}"),
        }
        assert!(matches!(sync(&mut x, &mut px), Err(Error::Scope { .. })));
        assert_eq!(head_of(&remote, "x").unwrap(), head);
        unchanged(&x);
    }

    // a non-empty branch without a scope file is not a nibli-db branch
    {
        let remote = bare(dir, "foreign");
        plant(&remote, "x", &[("README.md", b"not ours")]);
        let head = head_of(&remote, "x").unwrap();
        let mut px =
            GitPeer::open(&dir.join("x-foreign.git"), remote.to_str().unwrap(), "x").unwrap();
        match px.have() {
            Err(Error::Git(Failure::Foreign(branch))) => assert_eq!(branch, "nibli-db/x"),
            other => panic!("a foreign branch was not refused: {other:?}"),
        }
        assert!(matches!(
            sync(&mut x, &mut px),
            Err(Error::Git(Failure::Foreign(_)))
        ));
        assert_eq!(head_of(&remote, "x").unwrap(), head);
        unchanged(&x);
    }

    // on x's own branch: a tampered operation, a stranger's operation, and files that are
    // not operations
    let remote = bare(dir, "own");
    let mut px = GitPeer::open(&dir.join("x.git"), remote.to_str().unwrap(), "x").unwrap();
    sync(&mut x, &mut px).unwrap();
    let before = (std::fs::read(&file).unwrap(), view(&x));
    let unchanged = |x: &Database| {
        assert_eq!(std::fs::read(&file).unwrap(), before.0, "the file changed");
        assert_eq!(view(x), before.1, "the view changed");
    };
    {
        // z is enrolled by x; its operation is tampered with on the branch, one bit of the
        // body, the path kept
        let mut z = Database::in_memory(&z_seed, "x").unwrap();
        let mut tx = z.begin(said(2));
        tx.assert("bird(Ada).");
        tx.commit().unwrap();
        let honest = z.operations().remove(0);
        let mut tampered = honest.clone();
        let flip = tampered.len() - 65;
        tampered[flip] ^= 1;
        let path = format!(
            "ops/{}/0/{}.op",
            hex(&z.actor()),
            hex(&honest[honest.len() - 64..])
        );
        plant(&remote, "x", &[(&path, &tampered)]);
        let moved = sync(&mut x, &mut px).unwrap();
        assert_eq!(
            moved.received.refused,
            vec![Refusal::Malformed(Malformed::Signature)],
            "the tampered operation was not refused as such"
        );
        assert!(moved.received.kept.is_empty() && moved.sent.kept.is_empty());
        unchanged(&x);
    }
    {
        // a stranger, enrolled by nobody here, pushes through its own honest peer
        let mut s = Database::in_memory(&stranger_seed, "x").unwrap();
        s.enroll(x.actor()).unwrap();
        let mut tx = s.begin(said(3));
        tx.assert("person(Ada).");
        tx.commit().unwrap();
        let mut ps =
            GitPeer::open(&dir.join("stranger.git"), remote.to_str().unwrap(), "x").unwrap();
        sync(&mut s, &mut ps).unwrap();
        let moved = sync(&mut x, &mut px).unwrap();
        assert_eq!(
            moved.received.refused,
            vec![
                Refusal::Malformed(Malformed::Signature),
                Refusal::Unenrolled(s.actor())
            ]
        );
        unchanged(&x);
    }
    {
        // files that do not spell an operation are not operations: left alone, reported
        let odd = [
            "notes.txt".to_string(),
            "ops/README".to_string(),
            format!("ops/{}/1/not-hex.op", hex(&x.actor())),
            "ops/zz/1/zz.op".to_string(),
            format!("ops/{}/007/{}.op", hex(&x.actor()), "0f".repeat(64)),
        ];
        let files: Vec<(&str, &[u8])> = odd.iter().map(|p| (p.as_str(), b"x".as_slice())).collect();
        plant(&remote, "x", &files);
        let moved = sync(&mut x, &mut px).unwrap();
        assert!(moved.received.kept.is_empty() && moved.sent.kept.is_empty());
        assert_eq!(
            px.ignored().into_iter().collect::<BTreeSet<_>>(),
            odd.iter().cloned().collect::<BTreeSet<_>>()
        );
        assert_eq!(
            moved.received.refused.len(),
            2,
            "the tampered and the stranger's, still"
        );
        unchanged(&x);
    }
    {
        // an operation of another scope is not sent through x's branch
        let mut y = Database::in_memory(&y_seed, "y").unwrap();
        let mut tx = y.begin(said(1));
        tx.assert("cat(Tom).");
        tx.commit().unwrap();
        let head = head_of(&remote, "x").unwrap();
        let pushed = px.pushed();
        let moved = px.send(&y.operations()).unwrap();
        assert_eq!(moved.refused, vec![Refusal::Scope("y".into())]);
        assert!(moved.kept.is_empty());
        assert_eq!(head_of(&remote, "x").unwrap(), head, "the branch moved");
        assert_eq!(px.pushed(), pushed);
        unchanged(&x);
    }
    {
        // no git, and a scope that cannot name a branch
        let gone = dir.join("no-such-git");
        match GitPeer::open_with(&gone, &dir.join("none.git"), remote.to_str().unwrap(), "x") {
            Err(Error::Git(Failure::Missing(program))) => {
                assert_eq!(program, gone.to_string_lossy())
            }
            other => panic!("a missing git was not reported: {:?}", other.err()),
        }
        for bad in ["", "a b", "two..dots", "ends/"] {
            match GitPeer::open(&dir.join("bad.git"), remote.to_str().unwrap(), bad) {
                Err(Error::Git(Failure::Name(scope))) => assert_eq!(scope, bad),
                other => panic!("scope {bad:?} was accepted: {:?}", other.err()),
            }
        }
        unchanged(&x);
    }
}

// ---------------------------------------------------------------------------------------
// Test 4: what the remote loses, the next sync from any replica that holds it puts back.

#[test]
fn what_the_remote_loses_the_next_sync_puts_back() {
    let dir = tempfile::tempdir().unwrap();
    let remote = bare(dir.path(), "remote");
    let actors = [actor_of(&[1; 32]), actor_of(&[2; 32])];
    let mut a = replica(dir.path(), "a", &[1; 32], &remote, &actors);
    let mut b = replica(dir.path(), "b", &[2; 32], &remote, &actors);
    a.assert("dog(Rex).");
    a.assert("cat(Tom).");
    a.sync();
    let only_a = head_of(&remote, SCOPE).unwrap();
    b.sync();
    b.assert("bird(Ada).");
    b.sync();
    a.sync();
    assert_eq!(view(&a.db), view(&b.db));
    let everything = a.db.have().unwrap();
    assert_eq!(everything.len(), 3);
    let b_paths: BTreeSet<String> = on_branch(&remote, SCOPE)
        .difference(&{
            let paths = on_branch(&remote, SCOPE);
            git(&remote, &["update-ref", &branch_of(SCOPE), &only_a]);
            let kept = on_branch(&remote, SCOPE);
            assert!(kept.len() < paths.len(), "the rewind dropped nothing");
            kept
        })
        .cloned()
        .collect();
    assert_eq!(
        b_paths.len(),
        1,
        "b's operation was not what the rewind dropped"
    );

    // a holds b's operation, so a's next sync puts it back
    let moved = a.sync();
    assert_eq!(
        moved.sent.kept.len(),
        1,
        "a did not send b's operation back"
    );
    assert!(moved.received.kept.is_empty());
    assert!(on_branch(&remote, SCOPE).is_superset(&b_paths));
    assert_eq!(a.peer.have().unwrap(), everything);
    assert_eq!(view(&a.db), view(&b.db));
    let moved = b.sync();
    assert!(moved.sent.kept.is_empty() && moved.received.kept.is_empty());

    // the branch deleted altogether: the next sync makes it again, scope file first
    git(&remote, &["update-ref", "-d", &branch_of(SCOPE)]);
    assert!(head_of(&remote, SCOPE).is_none());
    assert!(b.peer.have().unwrap().is_empty());
    let moved = b.sync();
    assert_eq!(moved.sent.kept.len(), 3);
    assert!(on_branch(&remote, SCOPE).contains("scope"));
    assert_eq!(b.peer.have().unwrap(), everything);
    let moved = a.sync();
    assert!(moved.sent.kept.is_empty() && moved.received.kept.is_empty());
    assert_eq!(view(&a.db), view(&b.db));
    assert_eq!(a.peer.have().unwrap(), everything);
}

// ---------------------------------------------------------------------------------------
// Test 5: idempotence, and a sync killed between fetch and push, or in the push.

const INTERRUPTED_SEEDS: [[u8; 32]; 5] = [[1; 32], [2; 32], [5; 32], [6; 32], [7; 32]];

/// The child of test 5. It does nothing unless the parent test started it. Told
/// `after-fetch`, it fetches and merges, then writes a marker and waits to be killed; told
/// `mid-push`, it writes its pid where the remote's hook reads it and syncs, to be killed
/// by that hook while it pushes.
#[test]
fn interrupted_child() {
    let Ok(dir) = std::env::var("NIBLI_DB_GIT_INTERRUPT_DIR") else {
        return;
    };
    let dir = Path::new(&dir);
    let when = std::env::var("NIBLI_DB_GIT_INTERRUPT_WHEN").unwrap();
    let n: usize = std::env::var("NIBLI_DB_GIT_INTERRUPT_SEED")
        .unwrap()
        .parse()
        .unwrap();
    let remote = dir.join("remote.git");
    let actors: Vec<ActorId> = INTERRUPTED_SEEDS.iter().map(actor_of).collect();
    let mut db = Database::open(
        &dir.join(format!("child{n}.redb")),
        &INTERRUPTED_SEEDS[n],
        SCOPE,
    )
    .unwrap();
    for actor in &actors {
        db.enroll(*actor).unwrap();
    }
    let mut tx = db.begin(said(0));
    tx.assert(&format!("bird(C{n})."));
    tx.commit().unwrap();
    let mut peer = GitPeer::open(
        &dir.join(format!("child{n}.git")),
        remote.to_str().unwrap(),
        SCOPE,
    )
    .unwrap();
    match when.as_str() {
        "after-fetch" => {
            let yours = peer.have().unwrap();
            let wanted: BTreeSet<Have> = yours.difference(&db.have().unwrap()).copied().collect();
            db.merge(&peer.fetch(&wanted).unwrap()).unwrap();
            std::fs::write(dir.join("fetched"), b"").unwrap();
            loop {
                std::thread::sleep(std::time::Duration::from_secs(1));
            }
        }
        "mid-push" => {
            std::fs::write(dir.join("pusher.pid"), std::process::id().to_string()).unwrap();
            sync(&mut db, &mut peer).unwrap();
            panic!("the push was not interrupted");
        }
        other => panic!("{other}"),
    }
}

fn start_child(dir: &Path, when: &str, n: usize) -> std::process::Child {
    Command::new(std::env::current_exe().unwrap())
        .args(["interrupted_child", "--exact", "--nocapture"])
        .env("NIBLI_DB_GIT_INTERRUPT_DIR", dir)
        .env("NIBLI_DB_GIT_INTERRUPT_WHEN", when)
        .env("NIBLI_DB_GIT_INTERRUPT_SEED", n.to_string())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .unwrap()
}

#[test]
fn syncing_twice_changes_nothing_and_an_interrupted_sync_is_finished_by_the_next() {
    use std::os::unix::process::ExitStatusExt;
    let dir = tempfile::tempdir().unwrap();
    let dir = dir.path();
    let remote = bare(dir, "remote");
    let actors: Vec<ActorId> = INTERRUPTED_SEEDS.iter().map(actor_of).collect();
    let mut a = replica(dir, "a", &INTERRUPTED_SEEDS[0], &remote, &actors);
    let mut b = replica(dir, "b", &INTERRUPTED_SEEDS[1], &remote, &actors);
    a.assert("dog(Rex).");
    a.sync();
    b.sync();
    b.assert("cat(Tom).");
    b.sync();
    a.sync();
    assert_eq!(
        view(&a.db),
        view(&b.db),
        "the two replicas did not converge"
    );

    // syncing again changes nothing on either side
    let head = head_of(&remote, SCOPE).unwrap();
    let moved_before = moves(&remote, SCOPE).len();
    let (va, vb) = (view(&a.db), view(&b.db));
    let (pa, pb) = (a.peer.pushed(), b.peer.pushed());
    for _ in 0..2 {
        for r in [&mut a, &mut b] {
            let moved = r.sync();
            assert!(moved.received.kept.is_empty() && moved.sent.kept.is_empty());
            assert!(moved.received.refused.is_empty() && moved.sent.refused.is_empty());
        }
    }
    assert_eq!(
        head_of(&remote, SCOPE).unwrap(),
        head,
        "a sync with nothing to say moved the branch"
    );
    assert_eq!(moves(&remote, SCOPE).len(), moved_before);
    assert_eq!((view(&a.db), view(&b.db)), (va, vb));
    assert_eq!((a.peer.pushed(), b.peer.pushed()), (pa, pb));

    // killed between fetch and push: the child has merged a's and b's operations into its
    // file and never pushed its own
    let mut child = start_child(dir, "after-fetch", 2);
    while !dir.join("fetched").exists() {
        assert!(
            child.try_wait().unwrap().is_none(),
            "the child ended by itself"
        );
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
    child.kill().unwrap();
    child.wait().unwrap();
    assert_eq!(
        head_of(&remote, SCOPE).unwrap(),
        head,
        "a killed sync moved the branch"
    );
    let mut c = replica_on_disk(dir, 2, &remote, &actors);
    assert_eq!(
        c.db.have().unwrap().len(),
        3,
        "the merge before the kill was lost"
    );
    let moved = c.sync();
    assert_eq!(moved.sent.kept.len(), 1);
    assert!(moved.received.kept.is_empty());
    a.sync();
    b.sync();
    assert_eq!(view(&a.db), view(&c.db));
    assert_eq!(view(&b.db), view(&c.db));

    // killed in the push, by a hook on the remote that kills the pusher and then lets the
    // update through; and once more with a hook that refuses it
    for (n, hook_exit) in [(3, 0), (4, 1)] {
        let hooks = remote.join("hooks");
        std::fs::create_dir_all(&hooks).unwrap();
        let hook = hooks.join("pre-receive");
        let done = dir.join(format!("hook-done-{n}"));
        std::fs::write(
            &hook,
            format!(
                "#!/bin/sh\nkill -9 $(cat {}) 2>/dev/null\nsleep 0.2\ntouch {}\nexit {hook_exit}\n",
                dir.join("pusher.pid").display(),
                done.display()
            ),
        )
        .unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&hook, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        let head = head_of(&remote, SCOPE).unwrap();
        let status = start_child(dir, "mid-push", n).wait().unwrap();
        assert_eq!(
            status.signal(),
            Some(9),
            "the child was not killed in its push: {status}"
        );
        // the pusher is dead; the remote is still finishing the push it was killed in
        let began = std::time::Instant::now();
        while !done.exists() || (hook_exit == 0 && head_of(&remote, SCOPE).unwrap() == head) {
            assert!(
                began.elapsed().as_secs() < 30,
                "the remote never finished the push"
            );
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        std::thread::sleep(std::time::Duration::from_millis(200));
        std::fs::remove_file(&hook).unwrap();
        let after = head_of(&remote, SCOPE).unwrap();
        if hook_exit == 0 {
            assert_ne!(after, head, "the update the hook let through did not land");
        } else {
            assert_eq!(after, head, "the update the hook refused landed");
        }
        let mut d = replica_on_disk(dir, n, &remote, &actors);
        let moved = d.sync();
        assert_eq!(
            moved.sent.kept.len(),
            usize::from(hook_exit != 0),
            "the next sync sent what it should not, or not what it should"
        );
        a.sync();
        b.sync();
        c.sync();
        d.sync();
        assert_eq!(view(&a.db), view(&d.db));
        assert_eq!(view(&b.db), view(&d.db));
        assert_eq!(view(&c.db), view(&d.db));
        assert_eq!(d.peer.have().unwrap(), d.db.have().unwrap());
    }
    assert_eq!(a.db.have().unwrap().len(), 5);
    let pushed: Vec<String> = [&a, &b, &c].iter().flat_map(|r| r.peer.pushed()).collect();
    branch_is_honest(&remote, SCOPE, &pushed);
}

/// A child's replica, reopened from its file after the child died.
fn replica_on_disk(dir: &Path, n: usize, remote: &Path, actors: &[ActorId]) -> Replica {
    let mut db = Database::open(
        &dir.join(format!("child{n}.redb")),
        &INTERRUPTED_SEEDS[n],
        SCOPE,
    )
    .unwrap();
    for actor in actors {
        db.enroll(*actor).unwrap();
    }
    let peer = GitPeer::open(
        &dir.join(format!("child{n}.git")),
        remote.to_str().unwrap(),
        SCOPE,
    )
    .unwrap();
    Replica { db, peer }
}
