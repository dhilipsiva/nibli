// SPDX-License-Identifier: MIT OR Apache-2.0

//! The Git transport of roadmap/DB2.md: a [`Peer`] that keeps one scope's operations as
//! files on one branch of any Git remote.
//!
//! The transport moves operations; it decides nothing. What a replica keeps, counts, flags
//! or reasons from is the database's business: every byte that comes through Git goes
//! through [`Database::merge`](crate::Database::merge), which decodes it, verifies its
//! signature and checks its scope and enrollment. Git's commit order and timestamps are not
//! used to decide anything, and the Git host is not trusted: it can delay or withhold
//! operations, and it cannot forge one, change one, or make a replica forget one it holds.
//!
//! **One branch per scope**, `nibli-db/<scope>`, with a `scope` file at the root of its
//! tree. **One file per operation content**, `ops/<actor>/<counter>/<signature>.op` in
//! lowercase hex, holding exactly [`Op::encode`]. The path spells the [`Have`] pair, so the
//! set of files is the set of operations; two writers touch disjoint paths or identical
//! bytes, and merging is set union on both sides. Pushes are never forced: a rejected push
//! is answered by a fetch, a new commit on the new head carrying the same files, and a new
//! push, three times, then an error that loses nothing, because the replica is its own
//! outbox. If the remote branch is rewritten and operations disappear from it, the next
//! `send` from any replica that holds them puts them back.
//!
//! The adapter drives the `git` command line. Authentication is Git's own (the SSH agent, a
//! credential helper); the adapter never sees a token and never prompts. It keeps a bare
//! clone as its local object store in a directory the caller names: put it beside the
//! database file, never inside the database's directory and never with the signing seed.
//! Git history can retain deleted content, so as in the rest of nibli-db, deletion is not
//! erasure.

use crate::db::{Error, Have, Merged, Peer, Refusal};
use crate::op::{ActorId, Op, OpId};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::fmt;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

/// A scope's branch is this, then the scope.
const PREFIX: &str = "nibli-db/";
/// The file at the root of the branch that holds the scope string.
const SCOPE_FILE: &str = "scope";
/// The directory the operations live under.
const OPS_DIR: &str = "ops";
/// How many times a push is tried before the branch is called contended.
const ATTEMPTS: usize = 3;

/// Why the Git transport could not do its work.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Failure {
    /// The `git` program could not be run: its name or path, as given.
    Missing(String),
    /// The scope cannot name a Git branch.
    Name(String),
    /// The branch holds files but no `scope` file: it is not a nibli-db branch.
    Foreign(String),
    /// The branch moved under every one of three attempts to push.
    Contended,
    /// A git command failed: at which stage, and what git said.
    Command { stage: &'static str, said: String },
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Failure::Missing(program) => write!(f, "{program:?} cannot be run"),
            Failure::Name(scope) => write!(f, "scope {scope:?} cannot name a branch"),
            Failure::Foreign(branch) => {
                write!(
                    f,
                    "{branch} holds files but no scope file: not a nibli-db branch"
                )
            }
            Failure::Contended => write!(f, "the branch moved under {ATTEMPTS} attempts to push"),
            Failure::Command { stage, said } => write!(f, "{stage} failed: {said}"),
        }
    }
}

impl std::error::Error for Failure {}

impl From<Failure> for Error {
    fn from(failure: Failure) -> Self {
        Error::Git(failure)
    }
}

/// The remote branch as it was when last looked at.
#[derive(Clone, Default)]
struct Seen {
    /// Its commit, if the branch exists.
    head: Option<String>,
    /// Every path on it: what need not be written again.
    paths: BTreeSet<String>,
    /// The paths that spell an operation.
    ops: BTreeSet<Have>,
    /// The paths that do not, `scope` aside: not operations, reported.
    ignored: Vec<String>,
}

/// A Git remote as a [`Peer`] of one scope. See the module documentation.
pub struct GitPeer {
    program: OsString,
    remote: String,
    scope: String,
    branch: String,
    dir: PathBuf,
    seen: RefCell<Option<Seen>>,
    pushed: Vec<String>,
    contention: usize,
}

impl GitPeer {
    /// Bind to `remote`'s branch of `scope`, with the bare clone at `clone` (created if it
    /// is not there yet). `remote` is anything `git fetch` and `git push` accept: an SSH or
    /// HTTPS URL, a path. `git` is looked for on `PATH`; its absence is an error here, not
    /// an empty peer later. The remote is not contacted until the first sync.
    pub fn open(clone: &Path, remote: &str, scope: &str) -> Result<Self, Error> {
        Self::open_with("git", clone, remote, scope)
    }

    /// [`open`](Self::open) with the `git` program named: a path, or another name on `PATH`.
    pub fn open_with(
        program: impl Into<OsString>,
        clone: &Path,
        remote: &str,
        scope: &str,
    ) -> Result<Self, Error> {
        let peer = GitPeer {
            program: program.into(),
            remote: remote.into(),
            scope: scope.into(),
            branch: format!("{PREFIX}{scope}"),
            dir: clone.to_path_buf(),
            seen: RefCell::new(None),
            pushed: vec![],
            contention: 0,
        };
        peer.run("version", peer.plain().arg("--version"), None)?;
        let (status, _, _) = peer.spawn(
            "check-ref-format",
            peer.plain()
                .arg("check-ref-format")
                .arg(format!("refs/heads/{}", peer.branch)),
            None,
        )?;
        if !status.success() {
            return Err(Failure::Name(scope.into()).into());
        }
        if !peer.dir.join("HEAD").is_file() {
            std::fs::create_dir_all(&peer.dir).map_err(|e| Failure::Command {
                stage: "init",
                said: format!("{}: {e}", peer.dir.display()),
            })?;
            peer.run(
                "init",
                peer.plain()
                    .args([
                        "-c",
                        "init.defaultBranch=nibli-db",
                        "init",
                        "--bare",
                        "--quiet",
                    ])
                    .arg(&peer.dir),
                None,
            )?;
        }
        Ok(peer)
    }

    /// The branch this peer reads and writes: `nibli-db/<scope>`.
    pub fn branch(&self) -> &str {
        &self.branch
    }

    /// The remote branch's commit when it was last looked at; `None` before the first look
    /// or when the branch does not exist.
    pub fn head(&self) -> Option<String> {
        self.seen.borrow().as_ref().and_then(|s| s.head.clone())
    }

    /// Paths seen on the branch that do not spell an operation, `scope` aside. They are
    /// not operations and are left alone.
    pub fn ignored(&self) -> Vec<String> {
        self.seen
            .borrow()
            .as_ref()
            .map(|s| s.ignored.clone())
            .unwrap_or_default()
    }

    /// The commits this peer has pushed, oldest first. Each is in the branch's history for
    /// as long as nobody rewrites the branch.
    pub fn pushed(&self) -> Vec<String> {
        self.pushed.clone()
    }

    /// How many pushes the remote rejected because the branch had moved, each answered by a
    /// fetch and a new attempt.
    pub fn contention(&self) -> usize {
        self.contention
    }

    /// A `git` command with nothing of the caller's Git environment and an identity of its
    /// own, never prompting.
    fn plain(&self) -> Command {
        let mut c = Command::new(&self.program);
        for var in [
            "GIT_DIR",
            "GIT_WORK_TREE",
            "GIT_INDEX_FILE",
            "GIT_OBJECT_DIRECTORY",
            "GIT_ALTERNATE_OBJECT_DIRECTORIES",
            "GIT_COMMON_DIR",
            "GIT_NAMESPACE",
        ] {
            c.env_remove(var);
        }
        c.env("GIT_TERMINAL_PROMPT", "0")
            .env("GIT_AUTHOR_NAME", "nibli-db")
            .env("GIT_AUTHOR_EMAIL", "nibli-db@localhost")
            .env("GIT_COMMITTER_NAME", "nibli-db")
            .env("GIT_COMMITTER_EMAIL", "nibli-db@localhost")
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        c
    }

    /// A `git` command on the clone.
    fn git(&self) -> Command {
        let mut c = self.plain();
        c.arg("--git-dir").arg(&self.dir);
        c
    }

    /// Run a command to its end, feeding it `input` if any. The status and both outputs.
    fn spawn(
        &self,
        stage: &'static str,
        cmd: &mut Command,
        input: Option<&[u8]>,
    ) -> Result<(ExitStatus, Vec<u8>, Vec<u8>), Error> {
        if input.is_some() {
            cmd.stdin(Stdio::piped());
        }
        let mut child = cmd.spawn().map_err(|e| {
            if e.kind() == std::io::ErrorKind::NotFound {
                Failure::Missing(self.program.to_string_lossy().into_owned())
            } else {
                Failure::Command {
                    stage,
                    said: e.to_string(),
                }
            }
        })?;
        let stdin = child.stdin.take();
        // the input is written from a thread of its own, so a command that answers while
        // it is still being fed cannot fill its pipe and stop
        let output = std::thread::scope(|scope| {
            let feeder = input.map(|bytes| {
                scope.spawn(move || {
                    let mut stdin = stdin.expect("a piped stdin was asked for");
                    stdin.write_all(bytes)
                })
            });
            let output = child.wait_with_output();
            if let Some(feeder) = feeder {
                let _ = feeder.join();
            }
            output
        })
        .map_err(|e| Failure::Command {
            stage,
            said: e.to_string(),
        })?;
        Ok((output.status, output.stdout, output.stderr))
    }

    /// Run a command that must succeed. Its standard output.
    fn run(
        &self,
        stage: &'static str,
        cmd: &mut Command,
        input: Option<&[u8]>,
    ) -> Result<Vec<u8>, Error> {
        let (status, out, err) = self.spawn(stage, cmd, input)?;
        if !status.success() {
            return Err(Failure::Command {
                stage,
                said: words(&err),
            }
            .into());
        }
        Ok(out)
    }

    /// Look at the remote branch as it is now, and keep what was seen. The honest build
    /// looks every time it is asked; the `stale` build of roadmap/DB2.md (Anti-fake) looks
    /// once and answers from that listing ever after.
    fn refresh(&self) -> Result<(), Error> {
        #[cfg(nibli_db_broken = "stale")]
        if self.seen.borrow().is_some() {
            return Ok(());
        }
        let full = format!("refs/heads/{}", self.branch);
        let (status, out, err) = self.spawn(
            "ls-remote",
            self.git()
                .args(["ls-remote", "--exit-code", &self.remote, &full]),
            None,
        )?;
        let advertised = match status.code() {
            Some(0) => Some(
                String::from_utf8_lossy(&out)
                    .split_whitespace()
                    .next()
                    .ok_or(Failure::Command {
                        stage: "ls-remote",
                        said: "no commit in the answer".into(),
                    })?
                    .to_string(),
            ),
            Some(2) => None,
            _ => {
                return Err(Failure::Command {
                    stage: "ls-remote",
                    said: words(&err),
                }
                .into());
            }
        };
        let mut seen = Seen::default();
        if let Some(sha) = advertised {
            let (known, _, _) = self.spawn(
                "cat-file",
                self.git()
                    .args(["cat-file", "-e", &format!("{sha}^{{commit}}")]),
                None,
            )?;
            let head = if known.success() {
                sha
            } else {
                self.run(
                    "fetch",
                    self.git()
                        .args(["fetch", "--quiet", "--no-tags", &self.remote, &full]),
                    None,
                )?;
                text(&self.run(
                    "rev-parse",
                    self.git().args(["rev-parse", "FETCH_HEAD"]),
                    None,
                )?)
            };
            let listing = self.run(
                "ls-tree",
                self.git()
                    .args(["ls-tree", "-r", "-z", "--name-only", &head]),
                None,
            )?;
            for path in listing.split(|b| *b == 0).filter(|p| !p.is_empty()) {
                let path = String::from_utf8_lossy(path).into_owned();
                match parse_path(&path) {
                    Some(have) => {
                        seen.ops.insert(have);
                    }
                    None if path == SCOPE_FILE => {}
                    None => seen.ignored.push(path.clone()),
                }
                seen.paths.insert(path);
            }
            self.identity(&head, &seen)?;
            seen.head = Some(head);
        }
        *self.seen.borrow_mut() = Some(seen);
        Ok(())
    }

    /// The branch must be a nibli-db branch of this scope before anything is read from it
    /// or written to it.
    #[cfg(not(nibli_db_broken = "onescope"))]
    fn identity(&self, head: &str, seen: &Seen) -> Result<(), Error> {
        if seen.paths.is_empty() {
            return Ok(());
        }
        if !seen.paths.contains(SCOPE_FILE) {
            return Err(Failure::Foreign(self.branch.clone()).into());
        }
        let theirs = self.run(
            "cat-file",
            self.git()
                .args(["cat-file", "blob", &format!("{head}:{SCOPE_FILE}")]),
            None,
        )?;
        let theirs = String::from_utf8_lossy(&theirs).into_owned();
        if theirs != self.scope {
            return Err(Error::Scope {
                ours: self.scope.clone(),
                theirs,
            });
        }
        Ok(())
    }

    /// The deliberately broken build of roadmap/DB2.md, Anti-fake: no scope is checked.
    #[cfg(nibli_db_broken = "onescope")]
    fn identity(&self, _head: &str, _seen: &Seen) -> Result<(), Error> {
        Ok(())
    }

    /// Make sure the branch has been looked at once.
    fn looked(&self) -> Result<Seen, Error> {
        if self.seen.borrow().is_none() {
            self.refresh()?;
        }
        Ok(self.seen.borrow().clone().expect("just looked"))
    }

    /// A commit on `head` (or a root commit) carrying the head's files and `fresh`.
    fn compose(
        &self,
        head: Option<&str>,
        present: &BTreeSet<String>,
        fresh: &[(&str, &[u8])],
    ) -> Result<String, Error> {
        static NONCE: AtomicU64 = AtomicU64::new(0);
        let nonce = format!(
            "{}-{}",
            std::process::id(),
            NONCE.fetch_add(1, Ordering::Relaxed)
        );
        let staging = self.dir.join(format!("nibli-db-staging-{nonce}"));
        let index = self.dir.join(format!("nibli-db-index-{nonce}"));
        let _clean = Scratch {
            staging: &staging,
            index: &index,
        };
        let place = |path: &str, bytes: &[u8]| -> Result<(), Error> {
            let at = staging.join(path);
            if let Some(parent) = at.parent() {
                std::fs::create_dir_all(parent).map_err(|e| failed("stage", e))?;
            }
            std::fs::write(&at, bytes).map_err(|e| failed("stage", e))
        };
        let mut written: Vec<&str> = vec![];
        if !present.contains(SCOPE_FILE) {
            place(SCOPE_FILE, self.scope.as_bytes())?;
            written.push(SCOPE_FILE);
        }
        for (path, bytes) in fresh {
            place(path, bytes)?;
            written.push(path);
        }
        let mut read = self.git();
        read.env("GIT_INDEX_FILE", &index).arg("read-tree");
        match head {
            Some(head) => read.arg(head),
            None => read.arg("--empty"),
        };
        self.run("read-tree", &mut read, None)?;
        let mut list = vec![];
        for path in &written {
            list.extend_from_slice(path.as_bytes());
            list.push(0);
        }
        self.run(
            "update-index",
            self.git()
                .env("GIT_INDEX_FILE", &index)
                .arg("--work-tree")
                .arg(&staging)
                .args(["update-index", "--add", "-z", "--stdin"]),
            Some(&list),
        )?;
        let tree = text(&self.run(
            "write-tree",
            self.git().env("GIT_INDEX_FILE", &index).arg("write-tree"),
            None,
        )?);
        let mut commit = self.git();
        commit.args(["commit-tree", &tree, "-m", &message(fresh)]);
        if let Some(head) = head {
            commit.args(["-p", head]);
        }
        Ok(text(&self.run("commit-tree", &mut commit, None)?))
    }

    /// Push `commit` to the branch, never by force. `Ok(false)` when the remote rejected it
    /// because the branch had moved; then what was seen is fresh again.
    fn push(&self, commit: &str, built_on: Option<&str>) -> Result<bool, Error> {
        let mut push = self.git();
        push.args(["push", "--quiet", "--no-verify"]);
        #[cfg(nibli_db_broken = "force")]
        push.arg("--force");
        push.arg(&self.remote)
            .arg(format!("{commit}:refs/heads/{}", self.branch));
        let (status, _, err) = self.spawn("push", &mut push, None)?;
        if status.success() {
            return Ok(true);
        }
        // a race or a real failure: the branch tells which
        let before = built_on.map(str::to_owned);
        self.refresh()?;
        if self.head() != before {
            return Ok(false);
        }
        Err(Failure::Command {
            stage: "push",
            said: words(&err),
        }
        .into())
    }
}

impl Peer for GitPeer {
    fn scope(&self) -> String {
        self.scope.clone()
    }

    fn have(&self) -> Result<BTreeSet<Have>, Error> {
        self.refresh()?;
        Ok(self.looked()?.ops)
    }

    fn fetch(&self, want: &BTreeSet<Have>) -> Result<Vec<Vec<u8>>, Error> {
        if want.is_empty() {
            return Ok(vec![]);
        }
        let Some(head) = self.looked()?.head else {
            return Ok(vec![]);
        };
        let mut asks = vec![];
        for have in want {
            asks.extend_from_slice(format!("{head}:{}\n", path_of(have)).as_bytes());
        }
        let out = self.run(
            "cat-file",
            self.git().args(["cat-file", "--batch"]),
            Some(&asks),
        )?;
        blobs(&out)
    }

    fn send(&mut self, operations: &[Vec<u8>]) -> Result<Merged, Error> {
        let mut report = Merged::default();
        let mut files: BTreeMap<String, (OpId, &[u8])> = BTreeMap::new();
        for bytes in operations {
            let op = match Op::decode(bytes) {
                Ok(op) => op,
                Err(e) => {
                    report.refused.push(Refusal::Malformed(e));
                    continue;
                }
            };
            #[cfg(not(nibli_db_broken = "onescope"))]
            if op.scope != self.scope {
                report.refused.push(Refusal::Scope(op.scope));
                continue;
            }
            files.insert(path_of(&(op.id, op.signature)), (op.id, bytes.as_slice()));
        }
        if files.is_empty() {
            return Ok(report);
        }
        for _ in 0..ATTEMPTS {
            let seen = self.looked()?;
            let fresh: Vec<(&str, &[u8])> = files
                .iter()
                .filter(|(path, _)| !seen.paths.contains(*path))
                .map(|(path, (_, bytes))| (path.as_str(), *bytes))
                .collect();
            if fresh.is_empty() {
                report.known = files.len();
                return Ok(report);
            }
            let commit = self.compose(seen.head.as_deref(), &seen.paths, &fresh)?;
            if !self.push(&commit, seen.head.as_deref())? {
                self.contention += 1;
                continue;
            }
            let mut now = seen;
            now.head = Some(commit.clone());
            now.paths.insert(SCOPE_FILE.into());
            for (path, _) in &fresh {
                now.paths.insert((*path).into());
                let have = parse_path(path).expect("a path this peer spelled");
                now.ops.insert(have);
                report.kept.push(have.0);
            }
            report.known = files.len() - fresh.len();
            *self.seen.borrow_mut() = Some(now);
            self.pushed.push(commit);
            return Ok(report);
        }
        Err(Failure::Contended.into())
    }
}

/// The staging directory and index of one commit, gone when it is done or abandoned.
struct Scratch<'a> {
    staging: &'a Path,
    index: &'a Path,
}

impl Drop for Scratch<'_> {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(self.staging);
        let _ = std::fs::remove_file(self.index);
    }
}

fn failed(stage: &'static str, e: std::io::Error) -> Error {
    Failure::Command {
        stage,
        said: e.to_string(),
    }
    .into()
}

/// What git said, trimmed and bounded. Never the content of an operation.
fn words(stderr: &[u8]) -> String {
    let said = String::from_utf8_lossy(stderr);
    let said = said.trim();
    if said.chars().count() > 600 {
        format!("{}…", said.chars().take(600).collect::<String>())
    } else {
        said.to_string()
    }
}

fn text(out: &[u8]) -> String {
    String::from_utf8_lossy(out).trim().to_string()
}

/// `nibli-db: <n> operations of <actor>`; the content is in the files, never here.
fn message(fresh: &[(&str, &[u8])]) -> String {
    let actors: BTreeSet<&str> = fresh
        .iter()
        .filter_map(|(path, _)| path.split('/').nth(1))
        .collect();
    let n = fresh.len();
    let s = if n == 1 { "" } else { "s" };
    match actors.iter().next() {
        Some(one) if actors.len() == 1 => format!("nibli-db: {n} operation{s} of {one}"),
        _ => format!("nibli-db: {n} operation{s} of {} actors", actors.len()),
    }
}

/// The blobs in a `cat-file --batch` answer, in order; what is missing is left out.
fn blobs(mut out: &[u8]) -> Result<Vec<Vec<u8>>, Error> {
    let bad = |what: &str| Failure::Command {
        stage: "cat-file",
        said: format!("an answer I cannot read: {what}"),
    };
    let mut found = vec![];
    while !out.is_empty() {
        let line = out
            .iter()
            .position(|b| *b == b'\n')
            .ok_or_else(|| bad("no header line"))?;
        let header = String::from_utf8_lossy(&out[..line]).into_owned();
        out = &out[line + 1..];
        let fields: Vec<&str> = header.split(' ').collect();
        match fields.as_slice() {
            [_, "missing"] | [_, "ambiguous"] => {}
            [_, kind, size] => {
                let size: usize = size.parse().map_err(|_| bad("the size"))?;
                if out.len() < size + 1 {
                    return Err(bad("a short object").into());
                }
                if *kind == "blob" {
                    found.push(out[..size].to_vec());
                }
                out = &out[size + 1..];
            }
            _ => return Err(bad(&header).into()),
        }
    }
    Ok(found)
}

/// Where an operation content lives on the branch.
fn path_of((id, signature): &Have) -> String {
    format!(
        "{OPS_DIR}/{}/{}/{}.op",
        hex(&id.actor),
        id.counter,
        hex(signature)
    )
}

/// The operation content a path names, if it names one in the one spelling there is.
fn parse_path(path: &str) -> Option<Have> {
    let mut parts = path.split('/');
    if parts.next()? != OPS_DIR {
        return None;
    }
    let actor: ActorId = unhex(parts.next()?)?.try_into().ok()?;
    let counter_text = parts.next()?;
    let counter: u64 = counter_text.parse().ok()?;
    if counter.to_string() != counter_text {
        return None;
    }
    let file = parts.next()?;
    if parts.next().is_some() {
        return None;
    }
    let signature: [u8; 64] = unhex(file.strip_suffix(".op")?)?.try_into().ok()?;
    Some((OpId { actor, counter }, signature))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Lowercase hex only: one spelling per content.
fn unhex(text: &str) -> Option<Vec<u8>> {
    if !text.len().is_multiple_of(2)
        || !text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return None;
    }
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).ok())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_path_spells_one_content_and_nothing_else_is_one() {
        let have = (
            OpId {
                actor: [0xab; 32],
                counter: 17,
            },
            [0x0f; 64],
        );
        let path = path_of(&have);
        assert_eq!(parse_path(&path), Some(have));
        assert_eq!(
            path,
            format!("ops/{}/17/{}.op", "ab".repeat(32), "0f".repeat(64))
        );
        for wrong in [
            "scope",
            "ops",
            "ops/README",
            &format!("ops/{}/17", "ab".repeat(32)),
            &format!("ops/{}/017/{}.op", "ab".repeat(32), "0f".repeat(64)),
            &format!("ops/{}/17/{}.op", "AB".repeat(32), "0f".repeat(64)),
            &format!("ops/{}/17/{}.op", "ab".repeat(32), "0f".repeat(63)),
            &format!("ops/{}/17/{}", "ab".repeat(32), "0f".repeat(64)),
            &format!("ops/{}/17/{}.op/more", "ab".repeat(32), "0f".repeat(64)),
            &format!("other/{}/17/{}.op", "ab".repeat(32), "0f".repeat(64)),
        ] {
            assert_eq!(parse_path(wrong), None, "{wrong}");
        }
    }

    #[test]
    fn a_batch_answer_is_read_and_a_missing_object_left_out() {
        let answer = b"abc blob 3\nxyz\nq missing\ndef tree 2\nzz\n";
        assert_eq!(blobs(answer).unwrap(), vec![b"xyz".to_vec()]);
        assert!(blobs(b"abc blob 9\nxyz\n").is_err());
    }
}
