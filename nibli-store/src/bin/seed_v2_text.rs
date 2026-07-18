//! Test fixture generator: write a legacy v2 `NibliStore` database containing one
//! active `StoredAssertion::Text` row, for the `smoke-host-schema-v3-migration` gate.
//!
//! The host can no longer WRITE Text rows (they are migration-decode-only), so a raw
//! redb writer is the only way to produce the pre-v3 on-disk shape. Table names mirror
//! nibli-store's private `FACTS_TABLE` / `META_TABLE` (stable on-disk names).
//!
//! Usage: `seed_v2_text <db-path> <id> <text>`

use std::path::Path;

use nibli_store::{StoredAssertion, StoredFactRecord};
use redb::{Database, TableDefinition};

const FACTS: TableDefinition<u64, &[u8]> = TableDefinition::new("facts");
const META: TableDefinition<&str, &[u8]> = TableDefinition::new("metadata");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 4 {
        eprintln!("usage: seed_v2_text <db-path> <id> <text>");
        std::process::exit(2);
    }
    let path = &args[1];
    let id: u64 = args[2].parse().expect("id must be a u64");
    let text = &args[3];

    let record = StoredFactRecord {
        id,
        payload: postcard::to_allocvec(&StoredAssertion::Text(text.clone()))
            .expect("serialize Text assertion"),
        label: text.clone(),
        retracted: false,
        node_id: "seed".to_string(),
        hlc_timestamp: id,
        predicates: Vec::new(),
    };

    let db = Database::create(Path::new(path)).expect("create db");
    let txn = db.begin_write().expect("begin write");
    {
        let mut facts = txn.open_table(FACTS).expect("facts table");
        let bytes = postcard::to_allocvec(&record).expect("serialize record");
        facts.insert(id, bytes.as_slice()).expect("insert fact");
        let mut meta = txn.open_table(META).expect("meta table");
        let vb = postcard::to_allocvec(&2u32).expect("serialize version");
        meta.insert("schema_version", vb.as_slice())
            .expect("stamp v2");
    }
    txn.commit().expect("commit");
    eprintln!("seeded v2 Text row id={id} text={text:?} at {path}");
}
