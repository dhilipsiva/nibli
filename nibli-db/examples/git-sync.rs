// SPDX-License-Identifier: MIT OR Apache-2.0

//! Two machines, one Git remote: the hand tool of roadmap/DB2.md, test 6.
//!
//! ```text
//! NIBLI_DB_SEED_FILE=<seed> cargo run -p nibli-db --example git-sync -- \
//!     <db file> <clone dir> <remote> <scope> <command> [argument]
//!
//! commands:  actor               print this replica's actor (its public key)
//!            enroll <actor hex>  accept that actor's operations from now on
//!            assert <statement>  commit one nibli-kr statement
//!            sync                exchange operations with the remote's branch of the scope
//!            show                print the snapshot and the conflicts, with a fingerprint
//! ```
//!
//! The seed file holds this replica's Ed25519 secret key and is created with 32 random bytes
//! if it is not there. Keep it, like the clone directory, out of the database's directory.
//!
//! Two machines agree when `show` prints the same thing on both: compare the outputs with
//! `diff` or `sha256sum`; the fingerprint is only for a first look.

use nibli_db::git::GitPeer;
use nibli_db::{Database, Provenance, sync};
use std::io::Read;
use std::path::Path;

const USAGE: &str = "usage: git-sync <db file> <clone dir> <remote> <scope> \
                     actor | enroll <actor hex> | assert <statement> | sync | show \
                     (with NIBLI_DB_SEED_FILE set)";

fn main() {
    if let Err(e) = run() {
        eprintln!("git-sync: {e}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [file, clone, remote, scope, command, rest @ ..] = args.as_slice() else {
        return Err(USAGE.into());
    };
    let seed = seed()?;
    let mut db = Database::open(Path::new(file), &seed, scope)?;
    match (command.as_str(), rest) {
        ("actor", []) => println!("{}", hex(&db.actor())),
        ("enroll", [actor]) => {
            let actor: [u8; 32] = unhex(actor)?
                .try_into()
                .map_err(|_| "an actor is 32 bytes of hex")?;
            db.enroll(actor)?;
        }
        ("assert", [text]) => {
            let time = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0);
            let mut tx = db.begin(Provenance {
                source: "git-sync".into(),
                time,
            });
            let id = tx.assert(text);
            tx.commit()?;
            println!("{id}");
        }
        ("sync", []) => {
            let mut peer = GitPeer::open(Path::new(clone), remote, scope)?;
            let moved = sync(&mut db, &mut peer)?;
            println!(
                "received {} new, {} known, {} refused; sent {} new, {} known, {} refused; \
                 branch {} at {}",
                moved.received.kept.len(),
                moved.received.known,
                moved.received.refused.len(),
                moved.sent.kept.len(),
                moved.sent.known,
                moved.sent.refused.len(),
                peer.branch(),
                peer.head().unwrap_or_else(|| "nothing".into()),
            );
            for refusal in moved.received.refused.iter().chain(&moved.sent.refused) {
                eprintln!("refused: {refusal:?}");
            }
            for path in peer.ignored() {
                eprintln!("not an operation, left alone: {path}");
            }
        }
        ("show", []) => {
            let view = format!("{}\n{:#?}", db.snapshot(), db.conflicts());
            print!("{view}");
            println!("\nfingerprint {:016x}", fingerprint(view.as_bytes()));
        }
        _ => return Err(USAGE.into()),
    }
    Ok(())
}

/// The secret key from `NIBLI_DB_SEED_FILE`, made if it is not there.
fn seed() -> Result<[u8; 32], Box<dyn std::error::Error>> {
    let path = std::env::var_os("NIBLI_DB_SEED_FILE").ok_or(USAGE)?;
    let path = Path::new(&path);
    if !path.exists() {
        let mut fresh = [0u8; 32];
        std::fs::File::open("/dev/urandom")?.read_exact(&mut fresh)?;
        std::fs::write(path, fresh)?;
        eprintln!("made a new seed at {}; keep it secret", path.display());
    }
    std::fs::read(path)?
        .try_into()
        .map_err(|_| format!("{} is not 32 bytes", path.display()).into())
}

/// FNV-1a, 64 bits: enough to see two outputs differ, not to prove they are the same.
fn fingerprint(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325u64, |h, b| {
        (h ^ u64::from(*b)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(text: &str) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    if !text.len().is_multiple_of(2) {
        return Err("odd hex".into());
    }
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).map_err(Into::into))
        .collect()
}
