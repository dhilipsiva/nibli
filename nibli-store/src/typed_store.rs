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
use redb::{Database, ReadableTable, ReadableTableMetadata, TableDefinition};

const TYPED_FACTS_TABLE: TableDefinition<u64, &[u8]> = TableDefinition::new("typed_facts");
const TYPED_PRED_INDEX_TABLE: TableDefinition<&str, &[u8]> =
    TableDefinition::new("typed_pred_index");
const TYPED_META_TABLE: TableDefinition<&str, &[u8]> = TableDefinition::new("typed_meta");

/// On-disk schema version of the typed store (fact encoding = postcard of
/// `StoredFact`). Bump on any incompatible layout change; a mismatch fails
/// `open` closed (`StoreError::SchemaVersion`) instead of silently dropping
/// undecodable rows. Mirrors the sibling `NibliStore` guard.
const TYPED_SCHEMA_VERSION: u32 = 2;

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
    fn open_database(path: &Path) -> Result<Database, StoreError> {
        let db = Database::create(path)?;

        // Ensure tables exist and check the schema version (mirrors NibliStore).
        {
            let txn = db.begin_write()?;
            {
                let has_unversioned_rows = {
                    let facts = txn.open_table(TYPED_FACTS_TABLE)?;
                    let pred_index = txn.open_table(TYPED_PRED_INDEX_TABLE)?;
                    facts.len()? != 0 || pred_index.len()? != 0
                };
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
                        // An unversioned populated store has the original v1
                        // postcard layout. It cannot be adopted as v2: enum
                        // discriminants may decode as the wrong GroundTerm.
                        // Only a genuinely empty database may be initialized.
                        if has_unversioned_rows {
                            return Err(StoreError::SchemaVersion {
                                expected: TYPED_SCHEMA_VERSION,
                                found: 1,
                            });
                        }
                        let bytes = postcard::to_allocvec(&TYPED_SCHEMA_VERSION)?;
                        meta.insert("schema_version", bytes.as_slice())?;
                    }
                    _ => {} // Version matches.
                }
            }
            txn.commit()?;
        }

        Ok(db)
    }

    /// Open a disposable typed mirror, erase every encoded row, and stamp the
    /// current schema in one transaction.
    ///
    /// Unlike [`Self::open_database`], this does not require a matching schema
    /// stamp because the caller has an independent source of truth. The old
    /// fact bytes are removed without ever being deserialized. The clear and
    /// restamp are atomic so a failed rebuild cannot leave legacy bytes
    /// advertised as the current layout.
    fn open_database_for_rebuild(path: &Path) -> Result<Database, StoreError> {
        let db = Database::create(path)?;

        {
            let txn = db.begin_write()?;
            {
                let mut facts = txn.open_table(TYPED_FACTS_TABLE)?;
                let ids: Vec<u64> = facts
                    .iter()?
                    .map(|entry| entry.map(|(key, _)| key.value()))
                    .collect::<Result<_, _>>()?;
                for id in ids {
                    facts.remove(id)?;
                }

                let mut pred_index = txn.open_table(TYPED_PRED_INDEX_TABLE)?;
                let relations: Vec<String> = pred_index
                    .iter()?
                    .map(|entry| entry.map(|(key, _)| key.value().to_string()))
                    .collect::<Result<_, _>>()?;
                for relation in relations {
                    pred_index.remove(relation.as_str())?;
                }

                let mut meta = txn.open_table(TYPED_META_TABLE)?;
                let bytes = postcard::to_allocvec(&TYPED_SCHEMA_VERSION)?;
                meta.insert("schema_version", bytes.as_slice())?;
            }
            txn.commit()?;
        }

        Ok(db)
    }

    /// Open or create a persistent typed fact store at the given path.
    ///
    /// Fails CLOSED (`StoreError`) on a schema-version mismatch, an
    /// undecodable persisted fact, or an unsound opaque-abstraction marker — a
    /// corrupt or incompatible store must never silently load a subset of its
    /// rows. Valid opaque-abstraction-v1 markers with a non-canonical digest
    /// prefix are normalized from their complete key and rewritten durably.
    pub fn open(path: &Path) -> Result<Self, StoreError> {
        let db = Self::open_database(path)?;

        // Eagerly load all facts into memory from disk.
        // (Lazy per-predicate loading reserved for WASI backend.)
        let mut cache: HashMap<String, HashSet<StoredFact>> = HashMap::new();
        let mut pred_index: HashMap<String, Vec<u64>> = HashMap::new();
        let mut normalized_rows: Vec<(u64, StoredFact)> = Vec::new();
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
                let mut fact = postcard::from_bytes::<StoredFact>(val.value()).map_err(|e| {
                    StoreError::Serialization(format!(
                        "typed store fact {id} failed to decode ({e}) — refusing to load a \
                         partial store"
                    ))
                })?;
                nibli_reason::kb::validate_stored_fact_groundness(&fact).map_err(|e| {
                    StoreError::Serialization(format!(
                        "typed store fact {id} is not ground ({e}) — refusing to load a partial store"
                    ))
                })?;
                let persisted = fact.clone();
                nibli_reason::kb::canonicalize_stored_fact_abstraction_marker(&mut fact).map_err(
                    |e| {
                        StoreError::Serialization(format!(
                            "typed store fact {id} has an invalid opaque-abstraction identity \
                             ({e}) — refusing to load a partial store"
                        ))
                    },
                )?;
                if fact != persisted {
                    normalized_rows.push((id, fact.clone()));
                }
                let relation = fact.relation().to_string();
                pred_index.entry(relation.clone()).or_default().push(id);
                cache.entry(relation).or_default().insert(fact);
            }
        }

        if !normalized_rows.is_empty() {
            let txn = db.begin_write()?;
            {
                let mut table = txn.open_table(TYPED_FACTS_TABLE)?;
                for (id, fact) in &normalized_rows {
                    let bytes = postcard::to_allocvec(fact)?;
                    table.insert(*id, bytes.as_slice())?;
                }
            }
            txn.commit()?;
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

    /// Open the typed store as a disposable mirror, erase all existing rows
    /// without decoding them, and stamp the current schema version.
    ///
    /// This is intentionally destructive and is only correct when another
    /// durable registry is the source of truth and will immediately replay the
    /// active records. It lets the engine recover from legacy/corrupt mirror
    /// rows without weakening [`Self::open`]'s fail-closed contract for callers
    /// that treat the typed store itself as authoritative.
    pub fn open_for_rebuild(path: &Path) -> Result<Self, StoreError> {
        Ok(Self {
            db: Self::open_database_for_rebuild(path)?,
            pred_index: HashMap::new(),
            cache: HashMap::new(),
            next_id: 0,
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

    fn insert(&mut self, mut fact: StoredFact) {
        if let Err(e) = nibli_reason::kb::validate_stored_fact_groundness(&fact) {
            eprintln!("[Persist Error] rejected non-ground typed fact: {e}");
            return;
        }
        if let Err(e) = nibli_reason::kb::canonicalize_stored_fact_abstraction_marker(&mut fact) {
            eprintln!(
                "[Persist Error] rejected typed fact with invalid opaque-abstraction identity: \
                 {e}"
            );
            return;
        }
        let id = self.next_id;
        self.next_id += 1;

        // Write to redb. The `FactStore` trait's insert is infallible (the
        // reasoning core calls it on hot paths with no error channel), so a
        // disk-write failure cannot propagate — report it while keeping the
        // in-memory fact queryable. Native engine sessions rebuild this mirror
        // from their canonical assertion registry on reopen.
        if let Err(e) = self.write_fact(id, &fact) {
            eprintln!(
                "[Persist Error] typed fact {id} ({}) was NOT written to the mirror: {e} — it \
                 remains in memory; native engine reopen rebuilds from the canonical registry",
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

    fn valid_marker_with_digest(digest: &str) -> String {
        assert_eq!(digest.len(), 16);
        // event-kind + Predicate("p", []). The key grammar is independently
        // validated by nibli-types on open; this helper only supplies a valid
        // row with a controllable non-semantic digest prefix.
        let mut key = vec![0xa0, 0x10];
        key.extend_from_slice(&1_u64.to_be_bytes());
        key.push(b'p');
        key.extend_from_slice(&0_u64.to_be_bytes());
        let key_hex: String = key.iter().map(|byte| format!("{byte:02x}")).collect();
        format!("__abs_v1_{digest}_{key_hex}")
    }

    fn raw_insert(path: &Path, id: u64, fact: &StoredFact) {
        let db = Database::create(path).unwrap();
        let txn = db.begin_write().unwrap();
        {
            let mut facts = txn.open_table(TYPED_FACTS_TABLE).unwrap();
            let bytes = postcard::to_allocvec(fact).unwrap();
            facts.insert(id, bytes.as_slice()).unwrap();
        }
        txn.commit().unwrap();
    }

    fn stamp_schema(path: &Path, version: u32) {
        let db = Database::create(path).unwrap();
        let txn = db.begin_write().unwrap();
        {
            let mut meta = txn.open_table(TYPED_META_TABLE).unwrap();
            let bytes = postcard::to_allocvec(&version).unwrap();
            meta.insert("schema_version", bytes.as_slice()).unwrap();
        }
        txn.commit().unwrap();
    }

    fn read_schema(path: &Path) -> u32 {
        let db = Database::create(path).unwrap();
        let txn = db.begin_read().unwrap();
        let meta = txn.open_table(TYPED_META_TABLE).unwrap();
        let encoded = meta
            .get("schema_version")
            .unwrap()
            .expect("schema stamp must exist");
        postcard::from_bytes(encoded.value()).unwrap()
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
        stamp_schema(&path, TYPED_SCHEMA_VERSION + 1);

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
    fn v1_fails_closed_but_disposable_rebuild_wipes_and_restamps() {
        let path = temp_db_path("v1_rebuild");
        cleanup(&path);

        drop(RedbFactStore::open(&path).unwrap());
        {
            let db = Database::create(&path).unwrap();
            let txn = db.begin_write().unwrap();
            {
                // This row is deliberately not valid under either layout. A
                // successful rebuild proves it was erased, not decoded.
                let mut facts = txn.open_table(TYPED_FACTS_TABLE).unwrap();
                facts
                    .insert(41u64, [0xffu8, 0xff, 0xff, 0xff].as_slice())
                    .unwrap();
                let mut pred_index = txn.open_table(TYPED_PRED_INDEX_TABLE).unwrap();
                let ids = postcard::to_allocvec(&vec![41u64]).unwrap();
                pred_index.insert("legacy", ids.as_slice()).unwrap();
            }
            txn.commit().unwrap();
        }
        stamp_schema(&path, 1);

        match RedbFactStore::open(&path) {
            Err(StoreError::SchemaVersion { expected, found }) => {
                assert_eq!(expected, TYPED_SCHEMA_VERSION);
                assert_eq!(found, 1);
            }
            Err(other) => panic!("expected SchemaVersion error, got {other}"),
            Ok(_) => panic!("authoritative open must reject a v1 store"),
        }
        assert_eq!(read_schema(&path), 1, "a rejected open must not restamp v1");

        let rebuilt = RedbFactStore::open_for_rebuild(&path)
            .expect("a disposable mirror may discard v1 bytes without decoding them");
        assert!(rebuilt.is_empty());
        drop(rebuilt);
        assert_eq!(read_schema(&path), TYPED_SCHEMA_VERSION);
        assert!(RedbFactStore::open(&path).unwrap().is_empty());

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
    fn abstraction_rows_fail_closed_or_normalize_durably() {
        let path = temp_db_path("abstraction_identity");
        cleanup(&path);
        drop(RedbFactStore::open(&path).unwrap());

        raw_insert(&path, 7, &fact("__abs_0123456789abcdef"));
        match RedbFactStore::open(&path) {
            Err(StoreError::Serialization(msg)) => assert!(
                msg.contains("typed store fact 7")
                    && msg.contains("legacy hash-only opaque-abstraction marker"),
                "unexpected message: {msg}"
            ),
            Err(other) => panic!("expected Serialization error, got {other}"),
            Ok(_) => panic!("legacy hash-only marker must fail closed"),
        }

        // The engine's typed store is a disposable mirror. Its explicit
        // rebuild path must erase an invalid row without decoding it, after
        // which the ordinary authoritative open is clean again.
        let rebuilt = RedbFactStore::open_for_rebuild(&path).unwrap();
        assert!(rebuilt.is_empty());
        drop(rebuilt);
        assert!(RedbFactStore::open(&path).unwrap().is_empty());

        let forged = valid_marker_with_digest("0000000000000000");
        let mut expected = fact(&forged);
        nibli_reason::kb::canonicalize_stored_fact_abstraction_marker(&mut expected).unwrap();
        let canonical = expected.relation().to_string();
        assert_ne!(forged, canonical, "the test digest must be non-canonical");
        raw_insert(&path, 9, &fact(&forged));

        let normalized = RedbFactStore::open(&path).unwrap();
        assert!(normalized.lookup_predicate(&canonical).is_some());
        assert!(normalized.lookup_predicate(&forged).is_none());
        drop(normalized);

        // Reopen proves normalization was written back rather than existing
        // only in the first process's cache.
        let reopened = RedbFactStore::open(&path).unwrap();
        assert!(reopened.lookup_predicate(&canonical).is_some());
        assert!(reopened.lookup_predicate(&forged).is_none());
        drop(reopened);

        cleanup(&path);
    }

    #[test]
    fn direct_insert_rejects_legacy_abstraction_identity() {
        let path = temp_db_path("reject_legacy_insert");
        cleanup(&path);

        let mut store = RedbFactStore::open(&path).unwrap();
        store.insert(fact("__abs_0123456789abcdef"));
        assert!(store.is_empty(), "invalid marker must not enter the cache");
        drop(store);
        assert!(
            RedbFactStore::open(&path).unwrap().is_empty(),
            "invalid marker must not enter the disk store"
        );

        cleanup(&path);
    }

    #[test]
    fn populated_pre_versioning_store_fails_closed_until_rebuilt() {
        let path = temp_db_path("reject_unversioned_legacy");
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

        // The unversioned populated layout is known to be v1. Treating it as
        // v2 would let old postcard discriminants be misread as new terms.
        match RedbFactStore::open(&path) {
            Err(StoreError::SchemaVersion { expected, found }) => {
                assert_eq!(expected, TYPED_SCHEMA_VERSION);
                assert_eq!(found, 1);
            }
            Err(other) => panic!("expected SchemaVersion error, got {other}"),
            Ok(_) => panic!("populated pre-versioning store must fail closed"),
        }

        let rebuilt = RedbFactStore::open_for_rebuild(&path).unwrap();
        assert!(rebuilt.is_empty());
        drop(rebuilt);
        assert_eq!(read_schema(&path), TYPED_SCHEMA_VERSION);
        assert!(RedbFactStore::open(&path).unwrap().is_empty());

        cleanup(&path);
    }

    #[test]
    fn current_schema_rejects_persisted_compiler_only_terms() {
        let path = temp_db_path("reject_non_ground_v2");
        cleanup(&path);

        let non_ground = StoredFact::Bare(GroundFact::new(
            "p",
            vec![nibli_reason::kb::GroundTerm::PatternVar("x".to_string())],
        ));
        raw_insert(&path, 0, &non_ground);
        stamp_schema(&path, TYPED_SCHEMA_VERSION);

        match RedbFactStore::open(&path) {
            Err(StoreError::Serialization(message)) => {
                assert!(
                    message.contains("not ground"),
                    "unexpected error: {message}"
                );
                assert!(
                    message.contains("compiler-only"),
                    "unexpected error: {message}"
                );
            }
            Err(other) => panic!("expected Serialization error, got {other}"),
            Ok(_) => panic!("a persisted PatternVar must never enter the concrete fact store"),
        }

        let rebuilt = RedbFactStore::open_for_rebuild(&path).unwrap();
        assert!(rebuilt.is_empty());
        cleanup(&path);
    }
}
