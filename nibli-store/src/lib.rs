//! Persistent disk-backed knowledge base store for Nibli.
//!
//! Uses redb (pure Rust, ACID, embedded key-value store) with postcard
//! serialization. The store persists FactRecords to disk with soft-delete
//! (tombstone) retraction.

/// Persistent typed fact store (StoredFact → redb) with lazy loading.
pub mod typed_store;

use std::collections::HashMap;
use std::path::Path;

use redb::{Database, ReadableTable, ReadableTableMetadata, TableDefinition, WriteTransaction};
use serde::{Deserialize, Serialize};

// ─── redb table definitions ───────────────────────────────────────

const FACTS_TABLE: TableDefinition<u64, &[u8]> = TableDefinition::new("facts");
const PREDICATE_INDEX_TABLE: TableDefinition<&str, &[u8]> = TableDefinition::new("predicate_index");
const META_TABLE: TableDefinition<&str, &[u8]> = TableDefinition::new("metadata");

const SCHEMA_VERSION: u32 = 2;

// ─── Serializable mirror types ────────────────────────────────────

/// A logical term, mirroring WIT `logical-term` for serialization.
///
/// Still used by `StoredAssertion::Direct` (nibli-host's direct-fact injection path).
/// nibli-engine no longer mirrors the full logic graph here — it persists
/// `nibli_types::logic::LogicBuffer` directly (serde-derived) as the opaque payload.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum StoredLogicalTerm {
    Variable(String),
    Constant(String),
    Description(String),
    Unspecified,
    Number(f64),
}

/// A fact record persisted to disk.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StoredFactRecord {
    pub id: u64,
    /// Opaque payload — caller decides format.
    /// nibli-engine: postcard-serialized `nibli_types::logic::LogicBuffer`.
    /// nibli-host: postcard-serialized `StoredAssertion`.
    pub payload: Vec<u8>,
    /// Human-readable label (Lojban source or `:assert rel args`).
    pub label: String,
    /// Soft-delete (tombstone) flag.
    pub retracted: bool,
    /// Provenance: which node asserted this fact.
    pub node_id: String,
    /// Monotonic logical (HLC) clock, stamped per fact for ordering.
    pub hlc_timestamp: u64,
    /// Predicate names referenced by this fact for index rebuilds.
    #[serde(default)]
    pub predicates: Vec<String>,
}

fn decode_stored_fact_record(bytes: &[u8]) -> Result<StoredFactRecord, StoreError> {
    Ok(postcard::from_bytes(bytes)?)
}

/// Assertion type for nibli-host (WASM host) persistence.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StoredAssertion {
    /// LEGACY: Lojban source text — replayed by recompiling via the WIT
    /// `assert-text-with-id` (single composite fact, pre-split granularity).
    /// No longer written; kept so old databases replay unchanged.
    Text(String),
    /// Direct fact injection — replayed via `assert_fact`.
    Direct {
        relation: String,
        args: Vec<StoredLogicalTerm>,
    },
    /// A compiled single-root fact buffer (postcard-serialized
    /// `nibli_types::logic::LogicBuffer`, nested opaquely so this crate keeps
    /// no nibli-types dependency) — replayed recompile-free via the WIT
    /// `assert-buffer-with-id`. One record per root of a multi-`.i` assert.
    /// APPENDED variant: postcard discriminants are declaration-ordered, so
    /// `Text`=0 / `Direct`=1 stay stable and old rows decode unchanged (no
    /// SCHEMA_VERSION bump — existing row bytes are not reinterpreted).
    Buffer(Vec<u8>),
}

/// Store error type.
#[derive(Debug)]
pub enum StoreError {
    Io(String),
    Serialization(String),
    NotFound(u64),
    SchemaVersion { expected: u32, found: u32 },
}

impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StoreError::Io(msg) => write!(f, "I/O error: {msg}"),
            StoreError::Serialization(msg) => write!(f, "serialization error: {msg}"),
            StoreError::NotFound(id) => write!(f, "fact {id} not found"),
            StoreError::SchemaVersion { expected, found } => {
                write!(
                    f,
                    "schema version mismatch: expected {expected}, found {found}"
                )
            }
        }
    }
}

impl std::error::Error for StoreError {}

impl From<redb::Error> for StoreError {
    fn from(e: redb::Error) -> Self {
        StoreError::Io(e.to_string())
    }
}

impl From<redb::DatabaseError> for StoreError {
    fn from(e: redb::DatabaseError) -> Self {
        StoreError::Io(e.to_string())
    }
}

impl From<redb::TableError> for StoreError {
    fn from(e: redb::TableError) -> Self {
        StoreError::Io(e.to_string())
    }
}

impl From<redb::TransactionError> for StoreError {
    fn from(e: redb::TransactionError) -> Self {
        StoreError::Io(e.to_string())
    }
}

impl From<redb::StorageError> for StoreError {
    fn from(e: redb::StorageError) -> Self {
        StoreError::Io(e.to_string())
    }
}

impl From<redb::CommitError> for StoreError {
    fn from(e: redb::CommitError) -> Self {
        StoreError::Io(e.to_string())
    }
}

impl From<postcard::Error> for StoreError {
    fn from(e: postcard::Error) -> Self {
        StoreError::Serialization(e.to_string())
    }
}

// ─── NibliStore ───────────────────────────────────────────────────

/// Persistent fact store backed by redb.
pub struct NibliStore {
    db: Database,
    node_id: String,
    hlc: u64,
}

impl NibliStore {
    /// Open or create a store at the given path.
    pub fn open(path: &Path, node_id: String) -> Result<Self, StoreError> {
        let db = Database::create(path)?;

        // Ensure tables exist and check schema version.
        let txn = db.begin_write()?;
        {
            // Create tables if they don't exist.
            let _ = txn.open_table(FACTS_TABLE)?;
            let _ = txn.open_table(PREDICATE_INDEX_TABLE)?;
            let mut meta = txn.open_table(META_TABLE)?;

            // Check or set schema version.
            let existing_version: Option<u32> = meta
                .get("schema_version")?
                .map(|g| postcard::from_bytes(g.value()))
                .transpose()?;
            match existing_version {
                Some(version) if version != SCHEMA_VERSION => {
                    return Err(StoreError::SchemaVersion {
                        expected: SCHEMA_VERSION,
                        found: version,
                    });
                }
                None => {
                    let bytes = postcard::to_allocvec(&SCHEMA_VERSION)?;
                    meta.insert("schema_version", bytes.as_slice())?;
                }
                _ => {} // Version matches, no action needed.
            }
        }
        txn.commit()?;

        // Recover HLC from max fact timestamp.
        let hlc = {
            let rtxn = db.begin_read()?;
            let table = rtxn.open_table(FACTS_TABLE)?;
            let mut max_hlc = 0u64;
            for entry in table.iter()? {
                let (_, val) = entry?;
                let record = decode_stored_fact_record(val.value())?;
                if record.hlc_timestamp > max_hlc {
                    max_hlc = record.hlc_timestamp;
                }
            }
            max_hlc
        };

        Ok(Self { db, node_id, hlc })
    }

    /// Advance the HLC and return the new timestamp.
    fn tick(&mut self) -> u64 {
        self.hlc += 1;
        self.hlc
    }

    fn normalize_predicates<I, S>(predicates: I) -> Vec<String>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut normalized: Vec<String> = predicates
            .into_iter()
            .map(|pred| pred.as_ref().to_string())
            .collect();
        normalized.sort();
        normalized.dedup();
        normalized
    }

    fn rebuild_predicate_index(txn: &WriteTransaction) -> Result<(), StoreError> {
        let mut index_entries: HashMap<String, Vec<u64>> = HashMap::new();
        {
            let facts = txn.open_table(FACTS_TABLE)?;
            for entry in facts.iter()? {
                let (_, val) = entry?;
                let record = decode_stored_fact_record(val.value())?;
                if record.retracted {
                    continue;
                }
                for predicate in Self::normalize_predicates(record.predicates.iter()) {
                    index_entries.entry(predicate).or_default().push(record.id);
                }
            }
        }

        let mut pred_idx = txn.open_table(PREDICATE_INDEX_TABLE)?;
        let existing_keys: Vec<String> = pred_idx
            .iter()?
            .map(|e| e.map(|(k, _)| k.value().to_string()))
            .collect::<Result<_, _>>()?;
        for key in &existing_keys {
            pred_idx.remove(key.as_str())?;
        }

        let mut predicates: Vec<String> = index_entries.keys().cloned().collect();
        predicates.sort();
        for predicate in &predicates {
            let ids = index_entries.get(predicate).unwrap();
            let idx_bytes = postcard::to_allocvec(ids)?;
            pred_idx.insert(predicate.as_str(), idx_bytes.as_slice())?;
        }

        Ok(())
    }

    fn predicate_memberships_from_index(&self) -> Result<HashMap<u64, Vec<String>>, StoreError> {
        let rtxn = self.db.begin_read()?;
        let pred_idx = rtxn.open_table(PREDICATE_INDEX_TABLE)?;
        let mut memberships: HashMap<u64, Vec<String>> = HashMap::new();
        for entry in pred_idx.iter()? {
            let (pred, val) = entry?;
            let predicate = pred.value().to_string();
            let ids: Vec<u64> = postcard::from_bytes(val.value())?;
            for id in ids {
                memberships.entry(id).or_default().push(predicate.clone());
            }
        }
        for predicates in memberships.values_mut() {
            *predicates = Self::normalize_predicates(predicates.iter());
        }
        Ok(memberships)
    }

    /// Insert a new fact record.
    pub fn insert_fact(
        &mut self,
        id: u64,
        label: String,
        payload: Vec<u8>,
    ) -> Result<(), StoreError> {
        let ts = self.tick();
        let record = StoredFactRecord {
            id,
            payload,
            label,
            retracted: false,
            node_id: self.node_id.clone(),
            hlc_timestamp: ts,
            predicates: Vec::new(),
        };
        let bytes = postcard::to_allocvec(&record)?;

        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(FACTS_TABLE)?;
            table.insert(id, bytes.as_slice())?;
        }
        txn.commit()?;
        Ok(())
    }

    /// Permanently remove a fact record. Used to roll back failed local assertions.
    pub fn delete_fact(&mut self, id: u64) -> Result<(), StoreError> {
        let txn = self.db.begin_write()?;
        {
            let mut facts = txn.open_table(FACTS_TABLE)?;
            if facts.remove(id)?.is_none() {
                return Err(StoreError::NotFound(id));
            }
        }
        Self::rebuild_predicate_index(&txn)?;
        txn.commit()?;
        Ok(())
    }

    /// Insert a fact with predicate index entries.
    pub fn insert_fact_with_predicates(
        &mut self,
        id: u64,
        label: String,
        payload: Vec<u8>,
        predicates: &[&str],
    ) -> Result<(), StoreError> {
        let ts = self.tick();
        let record = StoredFactRecord {
            id,
            payload,
            label,
            retracted: false,
            node_id: self.node_id.clone(),
            hlc_timestamp: ts,
            predicates: Self::normalize_predicates(predicates.iter()),
        };
        let bytes = postcard::to_allocvec(&record)?;

        let txn = self.db.begin_write()?;
        {
            let mut facts = txn.open_table(FACTS_TABLE)?;
            facts.insert(id, bytes.as_slice())?;
        }
        Self::rebuild_predicate_index(&txn)?;
        txn.commit()?;
        Ok(())
    }

    /// Mark a fact as retracted (tombstone). Idempotent.
    pub fn retract_fact(&mut self, id: u64) -> Result<(), StoreError> {
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(FACTS_TABLE)?;
            // Read first, drop the guard, then mutate.
            let record_opt: Option<StoredFactRecord> = table
                .get(id)?
                .map(|g| decode_stored_fact_record(g.value()))
                .transpose()?;
            match record_opt {
                Some(mut record) => {
                    if !record.retracted {
                        record.retracted = true;
                        record.hlc_timestamp = self.tick();
                        let bytes = postcard::to_allocvec(&record)?;
                        table.insert(id, bytes.as_slice())?;
                    }
                }
                None => return Err(StoreError::NotFound(id)),
            }
        }
        Self::rebuild_predicate_index(&txn)?;
        txn.commit()?;
        Ok(())
    }

    /// Load all active (non-retracted) facts, ordered by ID.
    pub fn all_active_facts(&self) -> Result<Vec<StoredFactRecord>, StoreError> {
        let rtxn = self.db.begin_read()?;
        let table = rtxn.open_table(FACTS_TABLE)?;
        let mut results = Vec::new();
        for entry in table.iter()? {
            let (_, val) = entry?;
            let record = decode_stored_fact_record(val.value())?;
            if !record.retracted {
                results.push(record);
            }
        }
        Ok(results)
    }

    /// Load a single fact by ID.
    pub fn get_fact(&self, id: u64) -> Result<Option<StoredFactRecord>, StoreError> {
        let rtxn = self.db.begin_read()?;
        let table = rtxn.open_table(FACTS_TABLE)?;
        match table.get(id)? {
            Some(val) => {
                let record = decode_stored_fact_record(val.value())?;
                Ok(Some(record))
            }
            None => Ok(None),
        }
    }

    /// Get the highest fact ID stored (for counter recovery).
    pub fn max_fact_id(&self) -> Result<Option<u64>, StoreError> {
        let rtxn = self.db.begin_read()?;
        let table = rtxn.open_table(FACTS_TABLE)?;
        match table.last()? {
            Some((key, _)) => Ok(Some(key.value())),
            None => Ok(None),
        }
    }

    /// Return the next unused fact ID.
    pub fn next_fact_id(&self) -> Result<u64, StoreError> {
        match self.max_fact_id()? {
            Some(id) => id
                .checked_add(1)
                .ok_or_else(|| StoreError::Io("fact ID space exhausted".to_string())),
            None => Ok(0),
        }
    }

    /// Get the count of active (non-retracted) facts.
    pub fn active_fact_count(&self) -> Result<usize, StoreError> {
        let rtxn = self.db.begin_read()?;
        let table = rtxn.open_table(FACTS_TABLE)?;
        let mut count = 0;
        for entry in table.iter()? {
            let (_, val) = entry?;
            let record = decode_stored_fact_record(val.value())?;
            if !record.retracted {
                count += 1;
            }
        }
        Ok(count)
    }

    /// Get fact IDs for a given predicate name.
    pub fn facts_for_predicate(&self, pred: &str) -> Result<Vec<u64>, StoreError> {
        let rtxn = self.db.begin_read()?;
        let table = rtxn.open_table(PREDICATE_INDEX_TABLE)?;
        match table.get(pred)? {
            Some(val) => {
                let ids: Vec<u64> = postcard::from_bytes(val.value())?;
                Ok(ids)
            }
            None => Ok(Vec::new()),
        }
    }

    /// Clear all facts and indices. Used for `:reset`.
    pub fn clear(&mut self) -> Result<(), StoreError> {
        let txn = self.db.begin_write()?;
        {
            let mut facts = txn.open_table(FACTS_TABLE)?;
            // Collect keys first to avoid borrow conflict.
            let keys: Vec<u64> = facts
                .iter()?
                .map(|e| e.map(|(k, _)| k.value()))
                .collect::<Result<_, _>>()?;
            for key in keys {
                facts.remove(key)?;
            }

            let mut pred_idx = txn.open_table(PREDICATE_INDEX_TABLE)?;
            let pred_keys: Vec<String> = pred_idx
                .iter()?
                .map(|e| e.map(|(k, _)| k.value().to_string()))
                .collect::<Result<_, _>>()?;
            for key in &pred_keys {
                pred_idx.remove(key.as_str())?;
            }
        }
        txn.commit()?;
        self.hlc = 0;
        Ok(())
    }

    /// Export all facts (including retracted) for CRDT sync.
    pub fn export_all(&self) -> Result<Vec<StoredFactRecord>, StoreError> {
        let predicate_memberships = self.predicate_memberships_from_index()?;
        let rtxn = self.db.begin_read()?;
        let table = rtxn.open_table(FACTS_TABLE)?;
        let mut results = Vec::new();
        for entry in table.iter()? {
            let (_, val) = entry?;
            let mut record = decode_stored_fact_record(val.value())?;
            if let Some(predicates) = predicate_memberships.get(&record.id) {
                record.predicates =
                    Self::normalize_predicates(record.predicates.iter().chain(predicates.iter()));
            }
            results.push(record);
        }
        Ok(results)
    }

    /// Get the store's node ID.
    pub fn node_id(&self) -> &str {
        &self.node_id
    }

    /// Get the current DB path (not stored — caller tracks this).
    /// Returns the total number of fact records (including retracted).
    pub fn total_fact_count(&self) -> Result<usize, StoreError> {
        let rtxn = self.db.begin_read()?;
        let table = rtxn.open_table(FACTS_TABLE)?;
        Ok(table.len()? as usize)
    }

    /// Export all facts (including retracted) to a new redb file.
    pub fn export_to_file(&self, path: &Path) -> Result<usize, StoreError> {
        let facts = self.export_all()?;
        let target = NibliStore::open(path, self.node_id.clone())?;
        let txn = target.db.begin_write()?;
        {
            let mut table = txn.open_table(FACTS_TABLE)?;
            for fact in &facts {
                let bytes = postcard::to_allocvec(fact)?;
                table.insert(fact.id, bytes.as_slice())?;
            }
        }
        Self::rebuild_predicate_index(&txn)?;
        txn.commit()?;
        Ok(facts.len())
    }
}

// ─── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn temp_db_path(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join("nibli_store_tests");
        fs::create_dir_all(&dir).unwrap();
        dir.join(format!("{name}.redb"))
    }

    fn cleanup(path: &Path) {
        let _ = fs::remove_file(path);
    }

    #[test]
    fn test_open_and_insert() {
        let path = temp_db_path("open_insert");
        cleanup(&path);

        let mut store = NibliStore::open(&path, "test-node".into()).unwrap();
        store
            .insert_fact(1, "test fact".into(), b"payload1".to_vec())
            .unwrap();

        let fact = store.get_fact(1).unwrap().unwrap();
        assert_eq!(fact.id, 1);
        assert_eq!(fact.label, "test fact");
        assert_eq!(fact.payload, b"payload1");
        assert!(!fact.retracted);
        assert_eq!(fact.node_id, "test-node");

        cleanup(&path);
    }

    #[test]
    fn open_rejects_mismatched_schema_version() {
        let path = temp_db_path("schema_version_reject");
        cleanup(&path);

        // Simulate an older on-disk database by writing schema_version = 1
        // directly into the metadata table (the payload byte layout changed
        // when nibli-engine moved off the StoredLogicBuffer mirror, so v1 DBs
        // must be hard-rejected rather than silently misread).
        {
            let db = Database::create(&path).unwrap();
            let txn = db.begin_write().unwrap();
            {
                let mut meta = txn.open_table(META_TABLE).unwrap();
                let bytes = postcard::to_allocvec(&1u32).unwrap();
                meta.insert("schema_version", bytes.as_slice()).unwrap();
            }
            txn.commit().unwrap();
        }

        match NibliStore::open(&path, "test-node".into()) {
            Err(StoreError::SchemaVersion { expected, found }) => {
                assert_eq!(expected, SCHEMA_VERSION);
                assert_eq!(found, 1);
            }
            Err(other) => panic!("expected a SchemaVersion error, got: {other:?}"),
            Ok(_) => panic!("a stale schema version must be rejected"),
        }

        cleanup(&path);
    }

    #[test]
    fn test_retraction_filters() {
        let path = temp_db_path("retract_filter");
        cleanup(&path);

        let mut store = NibliStore::open(&path, "node".into()).unwrap();
        store.insert_fact(1, "a".into(), vec![1]).unwrap();
        store.insert_fact(2, "b".into(), vec![2]).unwrap();
        store.insert_fact(3, "c".into(), vec![3]).unwrap();

        store.retract_fact(2).unwrap();

        let active = store.all_active_facts().unwrap();
        assert_eq!(active.len(), 2);
        assert!(active.iter().all(|f| f.id != 2));

        // Retracted fact still in export_all.
        let all = store.export_all().unwrap();
        assert_eq!(all.len(), 3);

        cleanup(&path);
    }

    #[test]
    fn test_max_fact_id() {
        let path = temp_db_path("max_id");
        cleanup(&path);

        let mut store = NibliStore::open(&path, "node".into()).unwrap();
        assert_eq!(store.max_fact_id().unwrap(), None);

        store.insert_fact(5, "five".into(), vec![]).unwrap();
        store.insert_fact(10, "ten".into(), vec![]).unwrap();
        store.insert_fact(3, "three".into(), vec![]).unwrap();

        assert_eq!(store.max_fact_id().unwrap(), Some(10));

        cleanup(&path);
    }

    #[test]
    fn test_next_fact_id_and_delete_fact() {
        let path = temp_db_path("next_id_delete");
        cleanup(&path);

        let mut store = NibliStore::open(&path, "node".into()).unwrap();
        assert_eq!(store.next_fact_id().unwrap(), 0);

        store.insert_fact(0, "zero".into(), vec![0]).unwrap();
        store.insert_fact(2, "two".into(), vec![2]).unwrap();
        assert_eq!(store.next_fact_id().unwrap(), 3);

        store.delete_fact(2).unwrap();
        assert!(store.get_fact(2).unwrap().is_none());
        assert_eq!(store.next_fact_id().unwrap(), 1);

        cleanup(&path);
    }

    #[test]
    fn test_clear() {
        let path = temp_db_path("clear");
        cleanup(&path);

        let mut store = NibliStore::open(&path, "node".into()).unwrap();
        store.insert_fact(1, "a".into(), vec![1]).unwrap();
        store.insert_fact(2, "b".into(), vec![2]).unwrap();

        store.clear().unwrap();

        assert_eq!(store.all_active_facts().unwrap().len(), 0);
        assert_eq!(store.max_fact_id().unwrap(), None);

        cleanup(&path);
    }

    #[test]
    fn test_idempotent_retract() {
        let path = temp_db_path("idempotent");
        cleanup(&path);

        let mut store = NibliStore::open(&path, "node".into()).unwrap();
        store.insert_fact(1, "a".into(), vec![1]).unwrap();

        store.retract_fact(1).unwrap();
        store.retract_fact(1).unwrap(); // Second retraction is no-op.

        let fact = store.get_fact(1).unwrap().unwrap();
        assert!(fact.retracted);

        cleanup(&path);
    }

    #[test]
    fn test_retract_not_found() {
        let path = temp_db_path("not_found");
        cleanup(&path);

        let mut store = NibliStore::open(&path, "node".into()).unwrap();
        let err = store.retract_fact(999).unwrap_err();
        assert!(matches!(err, StoreError::NotFound(999)));

        cleanup(&path);
    }

    #[test]
    fn test_predicate_index() {
        let path = temp_db_path("pred_idx");
        cleanup(&path);

        let mut store = NibliStore::open(&path, "node".into()).unwrap();
        store
            .insert_fact_with_predicates(1, "a".into(), vec![1], &["gerku", "danlu"])
            .unwrap();
        store
            .insert_fact_with_predicates(2, "b".into(), vec![2], &["gerku"])
            .unwrap();
        store
            .insert_fact_with_predicates(3, "c".into(), vec![3], &["mlatu"])
            .unwrap();

        let dog_ids = store.facts_for_predicate("gerku").unwrap();
        assert_eq!(dog_ids, vec![1, 2]);

        let danlu_ids = store.facts_for_predicate("danlu").unwrap();
        assert_eq!(danlu_ids, vec![1]);

        let mlatu_ids = store.facts_for_predicate("mlatu").unwrap();
        assert_eq!(mlatu_ids, vec![3]);

        let empty = store.facts_for_predicate("blanu").unwrap();
        assert!(empty.is_empty());

        cleanup(&path);
    }

    #[test]
    fn test_retract_removes_fact_from_predicate_index() {
        let path = temp_db_path("pred_idx_retract");
        cleanup(&path);

        let mut store = NibliStore::open(&path, "node".into()).unwrap();
        store
            .insert_fact_with_predicates(1, "a".into(), vec![1], &["gerku"])
            .unwrap();
        store
            .insert_fact_with_predicates(2, "b".into(), vec![2], &["gerku"])
            .unwrap();

        store.retract_fact(1).unwrap();

        let dog_ids = store.facts_for_predicate("gerku").unwrap();
        assert_eq!(dog_ids, vec![2]);

        cleanup(&path);
    }

    #[test]
    fn test_stored_assertion_roundtrip() {
        let text_assertion = StoredAssertion::Text("ro lo gerku cu danlu".into());
        let bytes = postcard::to_allocvec(&text_assertion).unwrap();
        let decoded: StoredAssertion = postcard::from_bytes(&bytes).unwrap();
        match decoded {
            StoredAssertion::Text(s) => assert_eq!(s, "ro lo gerku cu danlu"),
            _ => panic!("expected Text variant"),
        }

        let direct_assertion = StoredAssertion::Direct {
            relation: "gerku".into(),
            args: vec![StoredLogicalTerm::Constant("adam".into())],
        };
        let bytes = postcard::to_allocvec(&direct_assertion).unwrap();
        let decoded: StoredAssertion = postcard::from_bytes(&bytes).unwrap();
        match decoded {
            StoredAssertion::Direct { relation, args } => {
                assert_eq!(relation, "gerku");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("expected Direct variant"),
        }

        // The appended Buffer variant round-trips its opaque payload, and —
        // discriminant stability — bytes written BEFORE the variant existed
        // still decode: Text=0 / Direct=1 are declaration-ordered postcard
        // tags, unchanged by the append.
        let buffer_assertion = StoredAssertion::Buffer(vec![1, 2, 3, 4]);
        let bytes = postcard::to_allocvec(&buffer_assertion).unwrap();
        let decoded: StoredAssertion = postcard::from_bytes(&bytes).unwrap();
        match decoded {
            StoredAssertion::Buffer(payload) => assert_eq!(payload, vec![1, 2, 3, 4]),
            _ => panic!("expected Buffer variant"),
        }
    }

    #[test]
    fn test_persistence_across_reopen() {
        let path = temp_db_path("reopen");
        cleanup(&path);

        {
            let mut store = NibliStore::open(&path, "node".into()).unwrap();
            store.insert_fact(1, "a".into(), vec![10]).unwrap();
            store.insert_fact(2, "b".into(), vec![20]).unwrap();
            store.retract_fact(2).unwrap();
        }

        // Reopen — data should survive.
        {
            let store = NibliStore::open(&path, "node".into()).unwrap();
            let active = store.all_active_facts().unwrap();
            assert_eq!(active.len(), 1);
            assert_eq!(active[0].id, 1);
            assert_eq!(active[0].payload, vec![10]);

            let retracted = store.get_fact(2).unwrap().unwrap();
            assert!(retracted.retracted);
        }

        cleanup(&path);
    }

    #[test]
    fn test_active_and_total_counts() {
        let path = temp_db_path("counts");
        cleanup(&path);

        let mut store = NibliStore::open(&path, "node".into()).unwrap();
        store.insert_fact(1, "a".into(), vec![]).unwrap();
        store.insert_fact(2, "b".into(), vec![]).unwrap();
        store.insert_fact(3, "c".into(), vec![]).unwrap();
        store.retract_fact(2).unwrap();

        assert_eq!(store.active_fact_count().unwrap(), 2);
        assert_eq!(store.total_fact_count().unwrap(), 3);

        cleanup(&path);
    }

    #[test]
    fn test_export_to_file() {
        let src_path = temp_db_path("export_src");
        let dst_path = temp_db_path("export_dst");
        cleanup(&src_path);
        cleanup(&dst_path);

        let mut store = NibliStore::open(&src_path, "node-a".into()).unwrap();
        store
            .insert_fact_with_predicates(1, "a".into(), vec![10], &["gerku"])
            .unwrap();
        store
            .insert_fact_with_predicates(2, "b".into(), vec![20], &["mlatu"])
            .unwrap();
        store.retract_fact(2).unwrap();

        let count = store.export_to_file(&dst_path).unwrap();
        assert_eq!(count, 2); // includes retracted

        let dst = NibliStore::open(&dst_path, "node-b".into()).unwrap();
        assert_eq!(dst.total_fact_count().unwrap(), 2);
        assert_eq!(dst.active_fact_count().unwrap(), 1);
        assert_eq!(dst.facts_for_predicate("gerku").unwrap(), vec![1]);
        assert!(dst.facts_for_predicate("mlatu").unwrap().is_empty());

        cleanup(&src_path);
        cleanup(&dst_path);
    }
}
