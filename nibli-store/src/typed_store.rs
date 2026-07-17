//! Persistent fact store backed by redb.
//!
//! Stores compiled `StoredFact` values directly (no re-compilation on load).
//! The predicate index (relation → fact IDs) is loaded eagerly on open.
//! Individual facts are loaded lazily on first access per predicate.
//!
//! Critical invariant: never read a fact from disk unless backward chaining
//! or predicate lookup demands it.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use crate::StoreError;
use nibli_reason::fact_store::FactStore;
use nibli_reason::kb::StoredFact;
use redb::{Database, ReadableTable, TableDefinition};

const TYPED_FACTS_TABLE: TableDefinition<u64, &[u8]> = TableDefinition::new("typed_facts");
const TYPED_PRED_INDEX_TABLE: TableDefinition<&str, &[u8]> =
    TableDefinition::new("typed_pred_index");
const TYPED_META_TABLE: TableDefinition<&str, &[u8]> = TableDefinition::new("typed_meta");

/// On-disk schema version of the typed store (fact encoding = postcard of
/// `StoredFact`). Bump on any incompatible layout change; a mismatch fails
/// `open` closed (`StoreError::SchemaVersion`) instead of silently dropping
/// undecodable rows. Mirrors the sibling `NibliStore` guard.
const TYPED_SCHEMA_VERSION: u32 = 1;

/// Persistent `FactStore` backed by redb.
///
/// On open: loads the predicate index (relation → Vec<fact_id>) into memory.
/// On lookup: deserializes facts for the requested predicate on first access,
/// caches them in memory for subsequent lookups.
/// On insert: writes to redb immediately, updates in-memory cache + index.
pub struct RedbFactStore {
    db: Database,
    /// In-memory predicate index: relation → set of fact IDs on disk.
    pred_index: HashMap<String, Vec<u64>>,
    /// Cached facts per predicate (loaded lazily from disk) — the single
    /// in-memory authority; `all_facts()` iterates its buckets. (The old
    /// shape kept a second flat union set, deep-cloning every fact twice.)
    cache: HashMap<String, HashSet<StoredFact>>,
    /// Next fact ID (monotonic).
    next_id: u64,
}

impl RedbFactStore {
    /// Open or create a persistent typed fact store at the given path.
    ///
    /// Fails CLOSED (`StoreError`) on a schema-version mismatch or an
    /// undecodable persisted fact — a corrupt or incompatible store must never
    /// silently load a subset of its rows.
    pub fn open(path: &Path) -> Result<Self, StoreError> {
        let db = Database::create(path)?;

        // Ensure tables exist and check the schema version (mirrors NibliStore).
        {
            let txn = db.begin_write()?;
            {
                let _ = txn.open_table(TYPED_FACTS_TABLE)?;
                let _ = txn.open_table(TYPED_PRED_INDEX_TABLE)?;
                let mut meta = txn.open_table(TYPED_META_TABLE)?;

                let existing_version: Option<u32> = meta
                    .get("schema_version")?
                    .map(|g| postcard::from_bytes(g.value()))
                    .transpose()?;
                match existing_version {
                    Some(version) if version != TYPED_SCHEMA_VERSION => {
                        return Err(StoreError::SchemaVersion {
                            expected: TYPED_SCHEMA_VERSION,
                            found: version,
                        });
                    }
                    None => {
                        // Fresh store, or a pre-versioning store (whose layout
                        // IS version 1): stamp it.
                        let bytes = postcard::to_allocvec(&TYPED_SCHEMA_VERSION)?;
                        meta.insert("schema_version", bytes.as_slice())?;
                    }
                    _ => {} // Version matches.
                }
            }
            txn.commit()?;
        }

        // Eagerly load all facts into memory from disk.
        // (Lazy per-predicate loading reserved for WASI backend.)
        let mut cache: HashMap<String, HashSet<StoredFact>> = HashMap::new();
        let mut pred_index: HashMap<String, Vec<u64>> = HashMap::new();
        let mut max_id: u64 = 0;
        {
            let rtxn = db.begin_read()?;
            let table = rtxn.open_table(TYPED_FACTS_TABLE)?;
            for entry in table.iter()? {
                let (key, val) = entry?;
                let id = key.value();
                if id >= max_id {
                    max_id = id + 1;
                }
                // A row that no longer decodes is DATA LOSS, not noise: surface
                // it (the pre-guard code silently skipped it, masked only by
                // the caller's clear+rebuild).
                let fact = postcard::from_bytes::<StoredFact>(val.value()).map_err(|e| {
                    StoreError::Serialization(format!(
                        "typed store fact {id} failed to decode ({e}) — refusing to load a \
                         partial store"
                    ))
                })?;
                let relation = fact.relation().to_string();
                pred_index.entry(relation.clone()).or_default().push(id);
                cache.entry(relation).or_default().insert(fact);
            }
        }

        let count: usize = cache.values().map(HashSet::len).sum();
        if count > 0 {
            println!("[TypedStore] Loaded {} persisted facts", count);
        }

        Ok(Self {
            db,
            pred_index,
            cache,
            next_id: max_id,
        })
    }

    /// Persist the predicate index to disk.
    fn flush_pred_index(&self) -> Result<(), StoreError> {
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(TYPED_PRED_INDEX_TABLE)?;

            // Clear existing entries.
            let existing: Vec<String> = table
                .iter()?
                .filter_map(|e| e.ok().map(|(k, _)| k.value().to_string()))
                .collect();
            for key in &existing {
                table.remove(key.as_str())?;
            }

            // Write current index.
            for (relation, ids) in &self.pred_index {
                let bytes = postcard::to_allocvec(ids)?;
                table.insert(relation.as_str(), bytes.as_slice())?;
            }
        }
        txn.commit()?;
        Ok(())
    }

    /// Serialize one fact and commit it to the facts table.
    fn write_fact(&self, id: u64, fact: &StoredFact) -> Result<(), StoreError> {
        let bytes = postcard::to_allocvec(fact)?;
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(TYPED_FACTS_TABLE)?;
            table.insert(id, bytes.as_slice())?;
        }
        txn.commit()?;
        Ok(())
    }

    /// Drain both on-disk tables (the disk half of `clear`).
    fn clear_disk(&self) -> Result<(), StoreError> {
        let txn = self.db.begin_write()?;
        {
            let mut facts = txn.open_table(TYPED_FACTS_TABLE)?;
            let ids: Vec<u64> = facts
                .iter()?
                .filter_map(|e| e.ok().map(|(k, _)| k.value()))
                .collect();
            for id in ids {
                facts.remove(id)?;
            }
            let mut pred_idx = txn.open_table(TYPED_PRED_INDEX_TABLE)?;
            let keys: Vec<String> = pred_idx
                .iter()?
                .filter_map(|e| e.ok().map(|(k, _)| k.value().to_string()))
                .collect();
            for key in keys {
                pred_idx.remove(key.as_str())?;
            }
        }
        txn.commit()?;
        Ok(())
    }
}

impl FactStore for RedbFactStore {
    fn lookup_predicate(&self, relation: &str) -> Option<&HashSet<StoredFact>> {
        self.cache.get(relation)
    }

    fn contains(&self, fact: &StoredFact) -> bool {
        if let Some(set) = self.cache.get(fact.relation()) {
            set.contains(fact)
        } else {
            false
        }
    }

    fn insert(&mut self, fact: StoredFact) {
        let id = self.next_id;
        self.next_id += 1;

        // Write to redb. The `FactStore` trait's insert is infallible (the
        // reasoning core calls it on hot paths with no error channel), so a
        // disk-write failure cannot propagate — but it must NEVER be silent:
        // the fact stays queryable in memory while quietly not surviving a
        // restart. Log loudly with the fact id and cause.
        if let Err(e) = self.write_fact(id, &fact) {
            eprintln!(
                "[Persist Error] typed fact {id} ({}) was NOT written to disk: {e} — it remains \
                 in memory for this session but will not survive a restart",
                fact.relation()
            );
        }

        // Update in-memory index.
        let relation = fact.relation().to_string();
        self.pred_index
            .entry(relation.clone())
            .or_default()
            .push(id);

        // Update in-memory cache (the single in-memory copy).
        self.cache.entry(relation).or_default().insert(fact);

        // Periodically flush the predicate index (every 100 inserts).
        if id.is_multiple_of(100)
            && let Err(e) = self.flush_pred_index()
        {
            eprintln!("[Persist Error] predicate-index flush failed: {e}");
        }
    }

    fn clear(&mut self) {
        self.pred_index.clear();
        self.cache.clear();
        self.next_id = 0;

        // Clear disk tables. A failure here leaves the DISK holding facts the
        // MEMORY no longer has — they would resurrect on the next open. Loud.
        if let Err(e) = self.clear_disk() {
            eprintln!(
                "[Persist Error] clearing the on-disk typed store failed: {e} — stale facts may \
                 resurrect on the next open"
            );
        }
    }

    fn all_facts(&self) -> Box<dyn Iterator<Item = &StoredFact> + '_> {
        Box::new(self.cache.values().flatten())
    }

    fn len(&self) -> usize {
        self.cache.values().map(HashSet::len).sum()
    }

    fn remove(&mut self, fact: &StoredFact) -> bool {
        // Note: disk cleanup deferred to compaction. In-memory state is authoritative.
        match self.cache.get_mut(fact.relation()) {
            Some(set) => set.remove(fact),
            None => false,
        }
    }

    fn clone_box(&self) -> Box<dyn FactStore> {
        // For hypothetical reasoning on persistent stores, clone the in-memory
        // cache into an InMemoryFactStore (detached from disk). The hypothetical
        // KB operates purely in memory — no disk writes.
        let mut mem = nibli_reason::fact_store::InMemoryFactStore::new();
        for fact in self.cache.values().flatten() {
            mem.insert(fact.clone());
        }
        Box::new(mem)
    }
}

impl Drop for RedbFactStore {
    fn drop(&mut self) {
        // Flush predicate index on close. Drop has no error channel; the
        // failure must still be visible (the index is rebuilt from the facts
        // table on open, so this degrades startup, not correctness).
        if let Err(e) = self.flush_pred_index() {
            eprintln!("[Persist Error] predicate-index flush on close failed: {e}");
        }
    }
}

#[cfg(test)]
mod schema_guard_tests {
    use super::*;
    use nibli_reason::kb::GroundFact;
    use std::fs;

    fn temp_db_path(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join("nibli_typed_store_tests");
        fs::create_dir_all(&dir).unwrap();
        dir.join(format!("{name}.redb"))
    }

    fn cleanup(path: &Path) {
        let _ = fs::remove_file(path);
    }

    fn fact(relation: &str) -> StoredFact {
        StoredFact::Bare(GroundFact::new(
            relation,
            vec![nibli_reason::kb::GroundTerm::Constant("adam".to_string())],
        ))
    }

    #[test]
    fn fresh_store_is_stamped_and_reopens() {
        let path = temp_db_path("stamp_reopen");
        cleanup(&path);

        {
            let mut store = RedbFactStore::open(&path).unwrap();
            store.insert(fact("gerku"));
        }
        let store = RedbFactStore::open(&path).expect("same-version reopen must succeed");
        assert_eq!(store.len(), 1, "the persisted fact must reload");

        cleanup(&path);
    }

    #[test]
    fn schema_version_mismatch_fails_closed() {
        let path = temp_db_path("version_mismatch");
        cleanup(&path);

        // Stamp the store, then overwrite the version with a future one.
        drop(RedbFactStore::open(&path).unwrap());
        {
            let db = Database::create(&path).unwrap();
            let txn = db.begin_write().unwrap();
            {
                let mut meta = txn.open_table(TYPED_META_TABLE).unwrap();
                let bytes = postcard::to_allocvec(&(TYPED_SCHEMA_VERSION + 1)).unwrap();
                meta.insert("schema_version", bytes.as_slice()).unwrap();
            }
            txn.commit().unwrap();
        }

        match RedbFactStore::open(&path) {
            Err(StoreError::SchemaVersion { expected, found }) => {
                assert_eq!(expected, TYPED_SCHEMA_VERSION);
                assert_eq!(found, TYPED_SCHEMA_VERSION + 1);
            }
            Err(other) => panic!("expected SchemaVersion error, got {other}"),
            Ok(_) => panic!("expected SchemaVersion error, got a loaded store"),
        }

        cleanup(&path);
    }

    #[test]
    fn undecodable_fact_fails_closed_not_silently_dropped() {
        let path = temp_db_path("corrupt_fact");
        cleanup(&path);

        // A valid store with one good fact...
        {
            let mut store = RedbFactStore::open(&path).unwrap();
            store.insert(fact("gerku"));
        }
        // ...plus one raw garbage row.
        {
            let db = Database::create(&path).unwrap();
            let txn = db.begin_write().unwrap();
            {
                let mut facts = txn.open_table(TYPED_FACTS_TABLE).unwrap();
                facts
                    .insert(9999u64, [0xffu8, 0xff, 0xff, 0xff].as_slice())
                    .unwrap();
            }
            txn.commit().unwrap();
        }

        // Pre-guard behavior loaded 1 of 2 rows silently; now the whole open
        // fails closed with the offending id in the message.
        match RedbFactStore::open(&path) {
            Err(StoreError::Serialization(msg)) => {
                assert!(
                    msg.contains("9999") && msg.contains("refusing to load a partial store"),
                    "unexpected message: {msg}"
                );
            }
            Err(other) => panic!("expected Serialization error, got {other}"),
            Ok(_) => panic!("expected Serialization error, got a loaded store"),
        }

        cleanup(&path);
    }

    #[test]
    fn pre_versioning_store_is_adopted_as_v1() {
        let path = temp_db_path("adopt_legacy");
        cleanup(&path);

        // Simulate a store created before the schema guard: fact + index
        // tables with a valid row, but NO meta table.
        {
            let db = Database::create(&path).unwrap();
            let txn = db.begin_write().unwrap();
            {
                let mut facts = txn.open_table(TYPED_FACTS_TABLE).unwrap();
                let bytes = postcard::to_allocvec(&fact("gerku")).unwrap();
                facts.insert(0u64, bytes.as_slice()).unwrap();
                let _ = txn.open_table(TYPED_PRED_INDEX_TABLE).unwrap();
            }
            txn.commit().unwrap();
        }

        // The legacy layout IS version 1: open must adopt (stamp) and load it.
        let store = RedbFactStore::open(&path).expect("pre-versioning store must be adopted");
        assert_eq!(store.len(), 1);
        drop(store);
        // And the stamp must persist for the next open.
        assert!(RedbFactStore::open(&path).is_ok());

        cleanup(&path);
    }
}
