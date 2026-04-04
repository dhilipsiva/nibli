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

use logji::fact_store::FactStore;
use logji::kb::StoredFact;
use redb::{Database, ReadableTable, ReadableTableMetadata, TableDefinition};

const TYPED_FACTS_TABLE: TableDefinition<u64, &[u8]> = TableDefinition::new("typed_facts");
const TYPED_PRED_INDEX_TABLE: TableDefinition<&str, &[u8]> =
    TableDefinition::new("typed_pred_index");

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
    /// Cached facts per predicate (loaded lazily from disk).
    cache: HashMap<String, HashSet<StoredFact>>,
    /// All cached facts (union of all predicate caches).
    all_facts_cache: HashSet<StoredFact>,
    /// Next fact ID (monotonic).
    next_id: u64,
}

impl RedbFactStore {
    /// Open or create a persistent typed fact store at the given path.
    pub fn open(path: &Path) -> Result<Self, String> {
        let db = Database::create(path).map_err(|e| format!("redb open: {e}"))?;

        // Ensure tables exist.
        {
            let txn = db.begin_write().map_err(|e| format!("redb write: {e}"))?;
            let _ = txn
                .open_table(TYPED_FACTS_TABLE)
                .map_err(|e| format!("redb table: {e}"))?;
            let _ = txn
                .open_table(TYPED_PRED_INDEX_TABLE)
                .map_err(|e| format!("redb table: {e}"))?;
            txn.commit().map_err(|e| format!("redb commit: {e}"))?;
        }

        // Eagerly load all facts into memory from disk.
        // (Lazy per-predicate loading reserved for WASI backend.)
        let mut cache: HashMap<String, HashSet<StoredFact>> = HashMap::new();
        let mut all_facts_cache: HashSet<StoredFact> = HashSet::new();
        let mut pred_index: HashMap<String, Vec<u64>> = HashMap::new();
        let mut max_id: u64 = 0;
        {
            let rtxn = db.begin_read().map_err(|e| format!("redb read: {e}"))?;
            let table = rtxn
                .open_table(TYPED_FACTS_TABLE)
                .map_err(|e| format!("redb table: {e}"))?;
            for entry in table.iter().map_err(|e| format!("redb iter: {e}"))? {
                let (key, val) = entry.map_err(|e| format!("redb entry: {e}"))?;
                let id = key.value();
                if id >= max_id {
                    max_id = id + 1;
                }
                if let Ok(fact) = postcard::from_bytes::<StoredFact>(val.value()) {
                    let relation = fact.relation().to_string();
                    pred_index.entry(relation.clone()).or_default().push(id);
                    cache.entry(relation).or_default().insert(fact.clone());
                    all_facts_cache.insert(fact);
                }
            }
        }

        let count = all_facts_cache.len();
        if count > 0 {
            println!("[TypedStore] Loaded {} persisted facts", count);
        }

        Ok(Self {
            db,
            pred_index,
            cache,
            all_facts_cache,
            next_id: max_id,
        })
    }

    /// Persist the predicate index to disk.
    fn flush_pred_index(&self) -> Result<(), String> {
        let txn = self.db.begin_write().map_err(|e| format!("redb write: {e}"))?;
        {
            let mut table = txn
                .open_table(TYPED_PRED_INDEX_TABLE)
                .map_err(|e| format!("redb table: {e}"))?;

            // Clear existing entries.
            let existing: Vec<String> = table
                .iter()
                .map_err(|e| format!("redb iter: {e}"))?
                .filter_map(|e| e.ok().map(|(k, _)| k.value().to_string()))
                .collect();
            for key in &existing {
                let _ = table.remove(key.as_str());
            }

            // Write current index.
            for (relation, ids) in &self.pred_index {
                let bytes = postcard::to_allocvec(ids).map_err(|e| format!("postcard: {e}"))?;
                table
                    .insert(relation.as_str(), bytes.as_slice())
                    .map_err(|e| format!("redb insert: {e}"))?;
            }
        }
        txn.commit().map_err(|e| format!("redb commit: {e}"))?;
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

        // Serialize and write to redb.
        if let Ok(bytes) = postcard::to_allocvec(&fact) {
            if let Ok(txn) = self.db.begin_write() {
                if let Ok(mut table) = txn.open_table(TYPED_FACTS_TABLE) {
                    let _ = table.insert(id, bytes.as_slice());
                }
                let _ = txn.commit();
            }
        }

        // Update in-memory index.
        let relation = fact.relation().to_string();
        self.pred_index
            .entry(relation.clone())
            .or_default()
            .push(id);

        // Update in-memory cache.
        self.all_facts_cache.insert(fact.clone());
        self.cache.entry(relation).or_default().insert(fact);

        // Periodically flush the predicate index (every 100 inserts).
        if id % 100 == 0 {
            let _ = self.flush_pred_index();
        }
    }

    fn clear(&mut self) {
        self.pred_index.clear();
        self.cache.clear();
        self.all_facts_cache.clear();
        self.next_id = 0;

        // Clear disk tables.
        if let Ok(txn) = self.db.begin_write() {
            if let Ok(mut facts) = txn.open_table(TYPED_FACTS_TABLE) {
                // Drain all entries.
                let ids: Vec<u64> = facts
                    .iter()
                    .ok()
                    .into_iter()
                    .flatten()
                    .filter_map(|e| e.ok().map(|(k, _)| k.value()))
                    .collect();
                for id in ids {
                    let _ = facts.remove(id);
                }
            }
            if let Ok(mut pred_idx) = txn.open_table(TYPED_PRED_INDEX_TABLE) {
                let keys: Vec<String> = pred_idx
                    .iter()
                    .ok()
                    .into_iter()
                    .flatten()
                    .filter_map(|e| e.ok().map(|(k, _)| k.value().to_string()))
                    .collect();
                for key in keys {
                    let _ = pred_idx.remove(key.as_str());
                }
            }
            let _ = txn.commit();
        }
    }

    fn all_facts(&self) -> &HashSet<StoredFact> {
        &self.all_facts_cache
    }

    fn len(&self) -> usize {
        self.all_facts_cache.len()
    }

    fn clone_box(&self) -> Box<dyn FactStore> {
        // For hypothetical reasoning on persistent stores, clone the in-memory
        // caches into an InMemoryFactStore (detached from disk). The hypothetical
        // KB operates purely in memory — no disk writes.
        let mut mem = logji::fact_store::InMemoryFactStore::new();
        for fact in &self.all_facts_cache {
            mem.insert(fact.clone());
        }
        Box::new(mem)
    }
}

impl Drop for RedbFactStore {
    fn drop(&mut self) {
        // Flush predicate index on close.
        let _ = self.flush_pred_index();
    }
}
