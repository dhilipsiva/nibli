// SPDX-License-Identifier: MIT OR Apache-2.0

//! The nine tests of roadmap/DB1.md. They run in one process and on one disk: they say
//! nothing about a network, a Git host or two real machines.

use nibli_db::{
    Batch, Change, Database, Error, Held, Malformed, Op, OpId, Peer, Provenance, Refusal, Status,
    sync,
};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

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
    fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in (1..items.len()).rev() {
            items.swap(i, self.below(i + 1));
        }
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

// ---------------------------------------------------------------------------------------
// Test 2: a second projection, written apart from the real one and as simply as possible.
// It shares no code with `State::of`: it reads only the public fields of the operations.

#[derive(PartialEq, Eq, Debug)]
enum Plain {
    Active(String),
    Withdrawn,
    Conflict(BTreeSet<OpId>),
}

type BatchKey = ([u8; 32], u64, u32);

struct Reference<'a> {
    ops: HashMap<OpId, &'a Op>,
    members: HashMap<BatchKey, Vec<&'a Op>>,
    verdict: HashMap<BatchKey, bool>,
    visiting: HashSet<BatchKey>,
}

fn batch_key(op: &Op) -> BatchKey {
    (op.id.actor, op.batch.first, op.batch.len)
}

impl<'a> Reference<'a> {
    fn applies(&mut self, key: BatchKey) -> bool {
        if let Some(v) = self.verdict.get(&key) {
            return *v;
        }
        if !self.visiting.insert(key) {
            return false;
        }
        let members = self.members[&key].clone();
        let mut ok = members.len() == key.2 as usize;
        'all: for op in &members {
            if !ok {
                break;
            }
            for p in &op.parents {
                let Some(parent) = self.ops.get(p).copied() else {
                    ok = false;
                    break 'all;
                };
                if parent.target != op.target
                    || (op.change == Change::Restore && parent.change != Change::Retract)
                {
                    ok = false;
                    break 'all;
                }
                let theirs = batch_key(parent);
                if theirs != key && !self.applies(theirs) {
                    ok = false;
                    break 'all;
                }
            }
        }
        self.visiting.remove(&key);
        self.verdict.insert(key, ok);
        ok
    }

    fn ancestors(&self, id: OpId, into: &mut BTreeSet<OpId>) {
        for p in &self.ops[&id].parents {
            if into.insert(*p) {
                self.ancestors(*p, into);
            }
        }
    }
}

/// What the operations say, and which of them do not count.
fn reference(ops: &[Op]) -> (BTreeMap<OpId, Plain>, BTreeSet<OpId>) {
    let mut r = Reference {
        ops: ops.iter().map(|op| (op.id, op)).collect(),
        members: HashMap::new(),
        verdict: HashMap::new(),
        visiting: HashSet::new(),
    };
    for op in ops {
        r.members.entry(batch_key(op)).or_default().push(op);
    }
    let mut applied = vec![];
    let mut held = BTreeSet::new();
    for op in ops {
        if r.applies(batch_key(op)) {
            applied.push(op);
        } else {
            held.insert(op.id);
        }
    }
    let mut by_target: BTreeMap<OpId, Vec<&Op>> = BTreeMap::new();
    for op in &applied {
        by_target.entry(op.target).or_default().push(op);
    }
    let mut out = BTreeMap::new();
    for (target, on_it) in by_target {
        let mut behind = BTreeSet::new();
        for op in &on_it {
            r.ancestors(op.id, &mut behind);
        }
        let heads: Vec<&&Op> = on_it.iter().filter(|op| !behind.contains(&op.id)).collect();
        let plain = match heads.as_slice() {
            [one] => match &one.payload {
                Some(text) => Plain::Active(text.clone()),
                None => Plain::Withdrawn,
            },
            many => Plain::Conflict(many.iter().map(|op| op.id).collect()),
        };
        out.insert(target, plain);
    }
    (out, held)
}

fn agrees_with_reference(db: &Database) {
    let ops: Vec<Op> = db
        .operations()
        .iter()
        .map(|bytes| Op::decode(bytes).expect("a kept operation decodes"))
        .collect();
    let (statements, held) = reference(&ops);
    let real: BTreeMap<OpId, Plain> = db
        .all()
        .into_iter()
        .map(|(id, status)| {
            let plain = match status {
                Status::Active { text, .. } => Plain::Active(text),
                Status::Withdrawn { .. } => Plain::Withdrawn,
                Status::Conflict { heads } => Plain::Conflict(heads.into_iter().collect()),
            };
            (id, plain)
        })
        .collect();
    assert_eq!(
        real, statements,
        "the two projections disagree on the statements"
    );
    let real_held: BTreeSet<OpId> = db.held().keys().copied().collect();
    assert_eq!(
        real_held, held,
        "the two projections disagree on what is held"
    );
}

// ---------------------------------------------------------------------------------------
// Tests 1, 2, 5 and 6: seeded random histories.

#[derive(Default, Debug)]
struct Seen {
    histories: u64,
    commits: u64,
    refused_commits: u64,
    deliveries: u64,
    held_midway: u64,
    conflicts_at_end: u64,
    constraint_conflicts_at_end: u64,
    resolutions: u64,
    snapshots_checked: u64,
}

impl Seen {
    fn add(&mut self, other: &Seen) {
        self.histories += other.histories;
        self.commits += other.commits;
        self.refused_commits += other.refused_commits;
        self.deliveries += other.deliveries;
        self.held_midway += other.held_midway;
        self.conflicts_at_end += other.conflicts_at_end;
        self.constraint_conflicts_at_end += other.constraint_conflicts_at_end;
        self.resolutions += other.resolutions;
        self.snapshots_checked += other.snapshots_checked;
    }
}

struct NameTheSeed(u64);

impl Drop for NameTheSeed {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!(
                "FAILING SEED {}: add it to REGRESSIONS in nibli-db/tests/db1.rs",
                self.0
            );
        }
    }
}

/// Tests 5 and 6 on one replica as it stands.
fn sound(db: &Database, seen: &mut Seen) {
    let snapshot = db.snapshot();
    let ast = nibli_kr::parse_checked(&snapshot).expect("the snapshot is nibli-kr");
    assert_eq!(ast.roots.len(), db.statements().len());
    db.engine().expect("the snapshot loads into the engine");
    let reasoned: BTreeSet<OpId> = db.statements().iter().map(|(id, _)| *id).collect();
    for conflict in db.conflicts() {
        assert!(conflict.heads.len() > 1);
        assert!(
            !reasoned.contains(&conflict.statement),
            "a conflicted statement is reasoned from"
        );
    }
    for id in db.constraint_conflicts().0 {
        assert!(
            !reasoned.contains(id),
            "a flagged statement is reasoned from"
        );
    }
    agrees_with_reference(db);
    seen.snapshots_checked += 1;
}

fn commit_something(db: &mut Database, rng: &mut Rng, seen: &mut Seen) {
    let known = db.all();
    let mut tx = db.begin(said(rng.below(4) as u64));
    let mut touched = BTreeSet::new();
    let mut resolves = 0;
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
        if matches!(status, Status::Conflict { .. }) {
            resolves += 1;
        }
        match (status, pick) {
            (Status::Withdrawn { .. }, _) => tx.restore(*id, text),
            (_, 4..=6) => tx.correct(*id, text),
            _ => tx.retract(*id),
        }
        .expect("the change fits the statement's state");
    }
    match tx.commit() {
        Ok(_) => {
            seen.commits += 1;
            seen.resolutions += resolves;
        }
        Err(Error::Inconsistent(_)) => seen.refused_commits += 1,
        Err(e) => panic!("a commit failed for a reason other than consistency: {e}"),
    }
}

/// Some of the operations, in any order, some of them twice.
fn some_of(mut ops: Vec<Vec<u8>>, rng: &mut Rng, all: bool) -> Vec<Vec<u8>> {
    if !all {
        ops.retain(|_| rng.below(2) == 0);
    }
    for i in 0..ops.len() {
        if rng.below(5) == 0 {
            ops.push(ops[i].clone());
        }
    }
    rng.shuffle(&mut ops);
    ops
}

fn history(seed: u64) -> Seen {
    let _named = NameTheSeed(seed);
    let mut seen = Seen {
        histories: 1,
        ..Seen::default()
    };
    let mut rng = Rng(seed);
    let count = 2 + rng.below(4);
    let seeds: Vec<[u8; 32]> = (0..count).map(|_| rng.seed()).collect();
    let mut replicas: Vec<Database> = seeds
        .iter()
        .map(|s| Database::in_memory(s, "history").unwrap())
        .collect();
    let actors: Vec<_> = replicas.iter().map(Database::actor).collect();
    for db in &mut replicas {
        for actor in &actors {
            db.enroll(*actor).unwrap();
        }
    }
    for _ in 0..10 + rng.below(25) {
        let at = rng.below(count);
        match rng.below(10) {
            0..=4 => commit_something(&mut replicas[at], &mut rng, &mut seen),
            5..=7 => {
                // a partial, reordered, duplicated delivery: the network at its worst
                let from = rng.below(count);
                let parcel = some_of(replicas[from].operations(), &mut rng, false);
                let merged = replicas[at].merge(&parcel).unwrap();
                assert!(merged.refused.is_empty() && merged.disowned.is_empty());
                seen.deliveries += 1;
            }
            _ => {
                let other = (at + 1 + rng.below(count - 1)) % count;
                let (low, high) = (at.min(other), at.max(other));
                let (left, right) = replicas.split_at_mut(high);
                sync(&mut left[low], &mut right[0]).unwrap();
                assert_eq!(left[low].have().unwrap(), right[0].have().unwrap());
                seen.deliveries += 1;
            }
        }
        if !replicas[at].held().is_empty() {
            seen.held_midway += 1;
        }
        sound(&replicas[at], &mut seen);
    }
    // everything reaches everyone, in an order and with repeats of each replica's own
    let everything: BTreeSet<Vec<u8>> = replicas.iter().flat_map(Database::operations).collect();
    for db in &mut replicas {
        let mut parcel = some_of(everything.iter().cloned().collect(), &mut rng, true);
        let rest = parcel.split_off(rng.below(parcel.len() + 1));
        db.merge(&parcel).unwrap();
        db.merge(&rest).unwrap();
    }
    let first = view(&replicas[0]);
    for db in &replicas {
        assert!(
            db.held().is_empty(),
            "an operation is still held after full delivery"
        );
        assert_eq!(
            view(db),
            first,
            "two replicas with the same operations differ"
        );
        sound(db, &mut seen);
    }
    seen.conflicts_at_end += replicas[0].conflicts().len() as u64;
    seen.constraint_conflicts_at_end += replicas[0].constraint_conflicts().0.len() as u64;
    seen
}

#[test]
fn replicas_converge_and_the_two_projections_agree() {
    for text in POOL {
        let ast = nibli_kr::parse_checked(text).unwrap_or_else(|e| panic!("{text}: {e:?}"));
        assert_eq!(ast.roots.len(), 1);
    }
    let histories: u64 = std::env::var("NIBLI_DB_HISTORIES")
        .ok()
        .map(|n| n.parse().expect("NIBLI_DB_HISTORIES is a number"))
        .unwrap_or(10_000);
    let mut seen = Seen::default();
    for seed in REGRESSIONS {
        seen.add(&history(*seed));
    }
    let workers = std::thread::available_parallelism().map_or(1, usize::from) as u64;
    let parts: Vec<Seen> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|w| {
                scope.spawn(move || {
                    let mut part = Seen::default();
                    for seed in (0..histories).filter(|s| s % workers == w) {
                        part.add(&history(seed));
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
    // a run that never met the hard cases proves nothing about them
    assert!(seen.held_midway > 0, "no history ever held an operation");
    assert!(
        seen.conflicts_at_end > 0,
        "no history ended with a conflict"
    );
    assert!(
        seen.constraint_conflicts_at_end > 0,
        "no history ended with a constraint conflict"
    );
    assert!(seen.resolutions > 0, "no history resolved a conflict");
    assert!(seen.refused_commits > 0, "no commit was ever refused");
}

// ---------------------------------------------------------------------------------------
// Test 6, directly: a clock must not pick a winner.

#[test]
fn concurrent_corrections_are_a_conflict_until_one_operation_follows_both() {
    let mut a = Database::in_memory(&[1; 32], "s").unwrap();
    let mut b = Database::in_memory(&[2; 32], "s").unwrap();
    a.enroll(b.actor()).unwrap();
    b.enroll(a.actor()).unwrap();
    let mut tx = a.begin(said(1));
    let rex = tx.assert("dog(Rex).");
    tx.commit().unwrap();
    sync(&mut a, &mut b).unwrap();

    let mut tx = a.begin(said(5));
    let by_a = tx.correct(rex, "cat(Rex).").unwrap();
    tx.commit().unwrap();
    let mut tx = b.begin(said(9));
    let by_b = tx.correct(rex, "bird(Rex).").unwrap();
    tx.commit().unwrap();
    sync(&mut a, &mut b).unwrap();

    for db in [&a, &b] {
        assert_eq!(db.snapshot(), "", "the later clock won");
        let conflicts = db.conflicts();
        assert_eq!(conflicts.len(), 1);
        assert_eq!(conflicts[0].statement, rex);
        let heads: BTreeSet<OpId> = conflicts[0].heads.iter().map(|h| h.0).collect();
        assert_eq!(heads, BTreeSet::from([by_a, by_b]));
    }
    assert_eq!(view(&a), view(&b));

    let mut tx = b.begin(said(0));
    tx.correct(rex, "dog(Rex).").unwrap();
    tx.commit().unwrap();
    sync(&mut a, &mut b).unwrap();
    for db in [&a, &b] {
        assert!(db.conflicts().is_empty());
        assert_eq!(db.snapshot(), "dog(Rex).\n");
    }
}

// ---------------------------------------------------------------------------------------
// Test 3: atomicity and durability under SIGKILL.

const CRASH_SEED: [u8; 32] = [9; 32];
const PER_BATCH: usize = 6;

fn crash_statement(batch: usize, part: usize) -> String {
    format!("dog(K{batch}p{part}).")
}

/// The child: commits batches for as long as it lives, and writes down each batch number
/// once its commit has returned. It does nothing unless the parent test started it.
#[test]
fn crash_child() {
    use std::io::Write;
    let Ok(dir) = std::env::var("NIBLI_DB_CRASH_DIR") else {
        return;
    };
    let dir = std::path::Path::new(&dir);
    let mut db = Database::open(&dir.join("db.redb"), &CRASH_SEED, "crash").unwrap();
    let mut returned = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(dir.join("returned"))
        .unwrap();
    let mut batch = db.all().len() / PER_BATCH;
    // A prior child may have committed a batch (redb synced it, so its commit
    // returned) and then been killed before appending that batch's line to
    // `returned`; this child resumes past it, so without a backfill the line is
    // never written and the witness drifts permanently below the committed count,
    // accumulating across the kills that share this directory. Every whole batch
    // already in the reopened DB had its commit durably complete (the parent's
    // held()/whole-batch/no-gap asserts enforce that), so record any the log is
    // missing before continuing. This keeps `batches <= returned + 1` a bound on
    // the single in-flight batch of THIS child, not an accumulation across restarts.
    {
        let logged: BTreeSet<usize> = std::fs::read_to_string(dir.join("returned"))
            .unwrap_or_default()
            .lines()
            .filter_map(|line| line.trim().parse().ok())
            .collect();
        for b in 0..batch {
            if !logged.contains(&b) {
                returned.write_all(format!("{b}\n").as_bytes()).unwrap();
            }
        }
        returned.sync_data().unwrap();
    }
    loop {
        let mut tx = db.begin(said(0));
        for part in 0..PER_BATCH {
            tx.assert(&crash_statement(batch, part));
        }
        tx.commit().unwrap();
        // One write syscall for the whole "N\n": writeln! emits the number and the
        // newline separately, so a kill between them leaves a newline-less partial
        // line that the next append fuses onto ("k" + "k+1\n" -> "kk+1\n"), losing a
        // line of the count for good. A single write_all of the formatted bytes is
        // atomic under SIGKILL.
        returned.write_all(format!("{batch}\n").as_bytes()).unwrap();
        returned.sync_data().unwrap();
        batch += 1;
    }
}

#[test]
fn a_killed_process_leaves_whole_batches_and_every_one_whose_commit_returned() {
    let kills: usize = std::env::var("NIBLI_DB_KILLS")
        .ok()
        .map(|n| n.parse().expect("NIBLI_DB_KILLS is a number"))
        .unwrap_or(500);
    let mut rng = Rng(3);
    let (mut returned_total, mut unreturned_kept, mut delays) = (0usize, 0usize, vec![]);
    let mut dir = tempfile::tempdir().unwrap();
    for kill in 0..kills {
        if kill % 20 == 0 {
            dir = tempfile::tempdir().unwrap();
        }
        let delay = 3 + rng.below(40) as u64;
        delays.push(delay);
        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["crash_child", "--exact", "--nocapture"])
            .env("NIBLI_DB_CRASH_DIR", dir.path())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap();
        std::thread::sleep(std::time::Duration::from_millis(delay));
        child.kill().unwrap(); // SIGKILL on Unix
        let status = child.wait().unwrap();
        assert!(!status.success(), "the child ended by itself: {status}");

        let db = Database::open(&dir.path().join("db.redb"), &CRASH_SEED, "crash").unwrap();
        assert!(
            db.held().is_empty(),
            "kill {kill}: part of a batch survived: {:?}",
            db.held()
        );
        let kept: BTreeSet<String> = db.statements().iter().map(|(_, t)| t.clone()).collect();
        assert_eq!(
            kept.len() % PER_BATCH,
            0,
            "kill {kill}: part of a batch survived"
        );
        let batches = kept.len() / PER_BATCH;
        for batch in 0..batches {
            for part in 0..PER_BATCH {
                assert!(
                    kept.contains(&crash_statement(batch, part)),
                    "kill {kill}: a gap"
                );
            }
        }
        let returned = std::fs::read_to_string(dir.path().join("returned")).unwrap_or_default();
        // the last line can be cut short by the kill; a batch counts as returned only whole
        let returned = returned.matches('\n').count();
        assert!(
            batches >= returned,
            "kill {kill}: {returned} commits returned and only {batches} batches are there"
        );
        assert!(
            batches <= returned + 1,
            "kill {kill}: a batch nobody committed"
        );
        unreturned_kept += batches - returned;
        if kill % 20 == 19 || kill + 1 == kills {
            returned_total += returned;
        }
    }
    eprintln!(
        "{kills} kills after {}..{} ms; {returned_total} commits returned and all were found; \
         {unreturned_kept} times a batch was whole on disk though its commit had not yet been \
         written down as returned",
        delays.iter().min().unwrap(),
        delays.iter().max().unwrap()
    );
    assert!(
        returned_total >= kills,
        "too few commits ran for the kills to mean anything"
    );
}

// ---------------------------------------------------------------------------------------
// Test 4: a refused batch changes nothing.

#[test]
fn a_refused_batch_leaves_the_file_as_it_was() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("db.redb");
    let mut db = Database::open(&path, &[4; 32], "s").unwrap();
    let mut tx = db.begin(said(0));
    let rex = tx.assert("dog(Rex).");
    tx.assert("derived_only(\"animal\").");
    tx.commit().unwrap();
    let before = (std::fs::read(&path).unwrap(), view(&db));

    type Attempt = fn(&mut nibli_db::Transaction<'_>, OpId);
    let attempts: [(&str, Attempt); 7] = [
        ("does not compile", |tx, _| {
            tx.assert("dog(Rex)");
        }),
        ("an unknown name", |tx, _| {
            tx.assert("zzqq(Rex).");
        }),
        ("two statements in one", |tx, _| {
            tx.assert("cat(Tom). bird(Ada).");
        }),
        ("contradicts a kept statement", |tx, _| {
            tx.assert("~dog(Rex).");
        }),
        ("breaks a declared constraint", |tx, _| {
            tx.assert("animal(Tom).");
        }),
        (
            "a correction that contradicts, after good statements",
            |tx, _| {
                tx.assert("cat(Tom).");
                let tom = tx.assert("bird(Tom).");
                tx.correct(tom, "~cat(Tom).").unwrap();
            },
        ),
        ("contradicts itself", |tx, rex| {
            tx.retract(rex).unwrap();
            tx.assert("bird(Ada).");
            tx.assert("~bird(Ada).");
        }),
    ];
    for (what, attempt) in attempts {
        let mut tx = db.begin(said(0));
        attempt(&mut tx, rex);
        let refused = tx.commit();
        assert!(
            matches!(refused, Err(Error::Statement(_) | Error::Inconsistent(_))),
            "{what}: {refused:?}"
        );
        assert_eq!(view(&db), before.1, "{what}: the state changed");
        assert!(
            std::fs::read(&path).unwrap() == before.0,
            "{what}: the file changed"
        );
    }
    // changes the state does not allow are refused before there is anything to commit
    let mut tx = db.begin(said(0));
    assert!(matches!(
        tx.restore(rex, "dog(Rex)."),
        Err(Error::Change(_))
    ));
    let nobody = OpId {
        actor: [0; 32],
        counter: 0,
    };
    assert!(matches!(tx.retract(nobody), Err(Error::Change(_))));
    // a transaction that is dropped is not a transaction
    tx.assert("cat(Tom).");
    drop(tx);
    assert_eq!(view(&db), before.1);
    assert!(std::fs::read(&path).unwrap() == before.0);

    // and the database still takes a good batch, and keeps it across a reopen
    let mut tx = db.begin(said(0));
    tx.assert("cat(Tom).");
    tx.commit().unwrap();
    let after = view(&db);
    drop(db);
    let db = Database::open(&path, &[4; 32], "s").unwrap();
    assert_eq!(view(&db), after);
    drop(db);
    assert!(matches!(
        Database::open(&path, &[4; 32], "other"),
        Err(Error::Open(_))
    ));
}

// ---------------------------------------------------------------------------------------
// Test 7: retract is never-asserted.

const BATTERY: &[&str] = &[
    "dog(Rex).",
    "animal(Rex).",
    "cat(Tom).",
    "animal(Tom).",
    "~dog(Rex).",
    "bird(Ada).",
    "owns(Ada, Rex).",
    "all $x: dog($x) -> animal($x).",
    "all $x: cat($x) -> animal($x).",
    "some $x: animal($x).",
    "some $x: owns(Ada, $x).",
];

fn answers(db: &Database) -> Vec<String> {
    let engine = db.engine().unwrap();
    BATTERY
        .iter()
        .map(|q| match engine.query_holds(q) {
            Ok(result) => nibli_engine::display_query_result(&result),
            Err(e) => format!("error: {e}"),
        })
        .collect()
}

#[test]
fn a_retracted_statement_answers_as_one_never_asserted() {
    let (mut retractions, mut distinct) = (0, BTreeSet::new());
    for seed in 0..300u64 {
        let _named = NameTheSeed(seed);
        let mut rng = Rng(seed ^ 0x7e7);
        let mut db = Database::in_memory(&[7; 32], "s").unwrap();
        let mut live: Vec<(OpId, &str)> = vec![];
        for _ in 0..4 + rng.below(12) {
            if !live.is_empty() && rng.below(3) == 0 {
                let (id, _) = live.remove(rng.below(live.len()));
                let mut tx = db.begin(said(0));
                tx.retract(id).unwrap();
                tx.commit().unwrap();
                retractions += 1;
                // a fresh database that was only ever told the survivors
                let mut fresh = Database::in_memory(&[8; 32], "s").unwrap();
                let mut tx = fresh.begin(said(0));
                for (_, text) in &live {
                    tx.assert(text);
                }
                tx.commit().unwrap();
                assert_eq!(db.snapshot(), fresh.snapshot());
                let got = answers(&db);
                assert_eq!(got, answers(&fresh));
                distinct.insert(got);
            } else {
                let text = POOL[rng.below(POOL.len())];
                let mut tx = db.begin(said(0));
                let id = tx.assert(text);
                if tx.commit().is_ok() {
                    live.push((id, text));
                }
            }
        }
    }
    eprintln!(
        "{retractions} retractions compared, {} distinct answer rows",
        distinct.len()
    );
    assert!(retractions > 300 && distinct.len() > 20);
}

// ---------------------------------------------------------------------------------------
// Test 8: refusals.

fn assertion(seed: &[u8; 32], counter: u64, scope: &str, text: &str) -> Op {
    let actor = Database::in_memory(seed, "any").unwrap().actor();
    let id = OpId { actor, counter };
    Op {
        id,
        scope: scope.into(),
        target: id,
        parents: vec![],
        change: Change::Assert,
        payload: Some(text.into()),
        provenance: said(0),
        batch: Batch {
            first: counter,
            len: 1,
        },
        signature: [0; 64],
    }
    .sign(seed)
}

#[test]
fn what_must_be_refused_is_refused() {
    let (writer, stranger) = ([11; 32], [12; 32]);
    let mut db = Database::in_memory(&[10; 32], "s").unwrap();
    let writer_actor = Database::in_memory(&writer, "s").unwrap().actor();
    db.enroll(writer_actor).unwrap();
    let empty = view(&db);

    // a forged signature: every single flipped bit of a good operation
    let good = assertion(&writer, 0, "s", "dog(Rex).").encode();
    for at in 0..good.len() {
        let mut forged = good.clone();
        forged[at] ^= 1;
        let merged = db.merge(&[forged]).unwrap();
        assert!(merged.kept.is_empty(), "a forgery was kept (byte {at})");
        assert_eq!(merged.refused.len(), 1);
    }
    // signed by someone else and claiming to be the writer
    let mut impostor = assertion(&stranger, 0, "s", "dog(Rex).");
    impostor.id.actor = writer_actor;
    impostor.target = impostor.id;
    let merged = db.merge(&[impostor.encode()]).unwrap();
    assert_eq!(
        merged.refused,
        vec![Refusal::Malformed(Malformed::Signature)]
    );
    // a key nobody enrolled
    let unknown = assertion(&stranger, 0, "s", "dog(Rex).");
    let merged = db.merge(&[unknown.encode()]).unwrap();
    assert_eq!(merged.refused, vec![Refusal::Unenrolled(unknown.id.actor)]);
    // another scope
    let merged = db
        .merge(&[assertion(&writer, 0, "elsewhere", "dog(Rex).").encode()])
        .unwrap();
    assert_eq!(merged.refused, vec![Refusal::Scope("elsewhere".into())]);
    // a payload that is not one statement, though well signed
    for text in ["zzqq(Rex).", "dog(Rex)", "dog(Rex). cat(Tom).", ""] {
        let merged = db
            .merge(&[assertion(&writer, 0, "s", text).encode()])
            .unwrap();
        assert!(
            matches!(
                merged.refused[..],
                [Refusal::Malformed(Malformed::Statement(_))]
            ),
            "{text}"
        );
    }
    // shapes that contradict themselves, though well signed
    let base = assertion(&writer, 0, "s", "dog(Rex).");
    let other = OpId {
        actor: writer_actor,
        counter: 7,
    };
    let bent: Vec<Op> = vec![
        Op {
            parents: vec![other],
            ..base.clone()
        },
        Op {
            target: other,
            ..base.clone()
        },
        Op {
            payload: None,
            ..base.clone()
        },
        Op {
            change: Change::Retract,
            ..base.clone()
        },
        Op {
            batch: Batch { first: 1, len: 1 },
            ..base.clone()
        },
        Op {
            batch: Batch { first: 0, len: 0 },
            ..base.clone()
        },
    ];
    for op in bent {
        let merged = db.merge(&[op.clone().sign(&writer).encode()]).unwrap();
        assert!(
            matches!(
                merged.refused[..],
                [Refusal::Malformed(Malformed::Shape(_))]
            ),
            "{op:?}"
        );
    }
    assert!(matches!(
        db.merge(&[vec![], good[..40].to_vec()]).unwrap().refused[..],
        [_, _]
    ));
    assert_eq!(view(&db), empty, "something refused left a trace");

    // an operation whose parent is missing is held, and appears nowhere until it arrives
    let mut source = Database::in_memory(&writer, "s").unwrap();
    let mut tx = source.begin(said(0));
    let rex = tx.assert("dog(Rex).");
    tx.commit().unwrap();
    let mut tx = source.begin(said(0));
    let correction = tx.correct(rex, "cat(Rex).").unwrap();
    tx.commit().unwrap();
    let ops: BTreeMap<OpId, Vec<u8>> = source
        .operations()
        .into_iter()
        .map(|bytes| (Op::decode(&bytes).unwrap().id, bytes))
        .collect();
    db.merge(&[ops[&correction].clone()]).unwrap();
    assert_eq!(db.held().get(&correction), Some(&Held::Waiting(rex)));
    assert_eq!(
        (db.snapshot(), db.all(), db.conflicts()),
        (String::new(), vec![], vec![])
    );
    db.merge(&[ops[&rex].clone()]).unwrap();
    assert!(db.held().is_empty());
    assert_eq!(db.snapshot(), "cat(Rex).\n");

    // half a transaction is held whole
    let mut tx = source.begin(said(0));
    let (one, two) = (tx.assert("bird(Ada)."), tx.assert("person(Ada)."));
    tx.commit().unwrap();
    let ops: BTreeMap<OpId, Vec<u8>> = source
        .operations()
        .into_iter()
        .map(|bytes| (Op::decode(&bytes).unwrap().id, bytes))
        .collect();
    db.merge(&[ops[&two].clone()]).unwrap();
    assert_eq!(db.held().get(&two), Some(&Held::Incomplete));
    assert_eq!(db.snapshot(), "cat(Rex).\n");
    db.merge(&[ops[&one].clone()]).unwrap();
    assert_eq!(db.snapshot(), "cat(Rex).\nbird(Ada).\nperson(Ada).\n");

    // a peer of another scope is refused before anything is asked of it or sent to it
    let mut elsewhere = Database::in_memory(&writer, "elsewhere").unwrap();
    assert!(matches!(
        sync(&mut db, &mut elsewhere),
        Err(Error::Scope { .. })
    ));
    assert!(elsewhere.operations().is_empty());
}

#[test]
fn an_id_signed_twice_counts_as_neither_whatever_the_order() {
    let writer = [11; 32];
    let first = assertion(&writer, 0, "s", "dog(Rex).").encode();
    let second = assertion(&writer, 0, "s", "cat(Rex).").encode();
    let mut views = vec![];
    for order in [[&first, &second], [&second, &first]] {
        let mut db = Database::in_memory(&[10; 32], "s").unwrap();
        db.enroll(Op::decode(&first).unwrap().id.actor).unwrap();
        db.merge(&[order[0].clone()]).unwrap();
        assert_eq!(db.statements().len(), 1);
        let merged = db.merge(&[order[1].clone()]).unwrap();
        assert_eq!(merged.disowned.len(), 1);
        assert_eq!(
            db.snapshot(),
            "",
            "one of two contents under one id was believed"
        );
        assert_eq!(db.disowned().len(), 1);
        // both are kept as evidence, and a repeat of either changes nothing
        assert_eq!(db.operations().len(), 2);
        assert_eq!(db.merge(&[first.clone(), second.clone()]).unwrap().known, 2);
        views.push(view(&db));
    }
    assert_eq!(views[0], views[1]);
}

// ---------------------------------------------------------------------------------------
// Test 9: two batches, each consistent alone, inconsistent together.

#[test]
fn a_merged_contradiction_is_reported_alike_and_reasoned_from_by_neither() {
    let mut a = Database::in_memory(&[21; 32], "s").unwrap();
    let mut b = Database::in_memory(&[22; 32], "s").unwrap();
    a.enroll(b.actor()).unwrap();
    b.enroll(a.actor()).unwrap();

    let mut tx = a.begin(said(0));
    let rule = tx.assert("all $x: dog($x) -> animal($x).");
    let rex = tx.assert("dog(Rex).");
    let ada = tx.assert("person(Ada).");
    tx.commit().unwrap();
    let mut tx = b.begin(said(0));
    let denial = tx.assert("~animal(Rex).");
    let tom = tx.assert("cat(Tom).");
    tx.commit().unwrap();
    sync(&mut a, &mut b).unwrap();

    assert_eq!(view(&a), view(&b));
    for db in [&a, &b] {
        let (flagged, problems) = db.constraint_conflicts();
        assert_eq!(flagged, &BTreeSet::from([rule, rex, denial]));
        assert!(!problems.is_empty());
        let reasoned: BTreeSet<OpId> = db.statements().iter().map(|(id, _)| *id).collect();
        assert_eq!(
            reasoned,
            BTreeSet::from([ada, tom]),
            "bystanders stay; the rest leave"
        );
        let engine = db.engine().unwrap();
        // (the denial itself cannot be asked this way: with no animal(Rex) left, the
        // engine's closed world answers `~animal(Rex).` TRUE whether or not it was said)
        for q in ["dog(Rex).", "animal(Rex)."] {
            let answer = nibli_engine::display_query_result(&engine.query_holds(q).unwrap());
            assert_ne!(answer, "TRUE", "{q} was reasoned from");
        }
    }
    // neither replica may add to the trouble; either may end it
    let mut tx = a.begin(said(0));
    tx.assert("~dog(Rex).");
    assert!(matches!(tx.commit(), Err(Error::Inconsistent(_))));
    let mut tx = b.begin(said(0));
    tx.retract(denial).unwrap();
    tx.commit().unwrap();
    sync(&mut a, &mut b).unwrap();
    assert_eq!(view(&a), view(&b));
    assert!(a.constraint_conflicts().0.is_empty());
    let engine = a.engine().unwrap();
    assert_eq!(
        nibli_engine::display_query_result(&engine.query_holds("animal(Rex).").unwrap()),
        "TRUE"
    );
}

#[test]
fn an_operation_survives_its_own_bytes() {
    let mut db = Database::in_memory(&[30; 32], "s").unwrap();
    let mut tx = db.begin(Provenance {
        source: "a note, with ünïcode".into(),
        time: u64::MAX,
    });
    let rex = tx.assert("dog(Rex).");
    tx.correct(rex, "cat(Rex).").unwrap();
    tx.retract(rex).unwrap();
    tx.restore(rex, "bird(Rex).").unwrap();
    tx.commit().unwrap();
    assert_eq!(db.snapshot(), "bird(Rex).\n");
    for bytes in db.operations() {
        assert_eq!(Op::decode(&bytes).unwrap().encode(), bytes);
    }
}
