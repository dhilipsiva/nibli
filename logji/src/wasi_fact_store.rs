//! WASI-compatible lazy-loading fact store.
//!
//! Uses `std::fs` (which maps to WASI filesystem syscalls on wasm32-wasip2).
//! Append-only facts log + predicate index + per-predicate LRU cache.
//!
//! Critical invariant: never read a fact from disk unless backward chaining
//! or predicate lookup demands it.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use crate::fact_store::{FactStore, InMemoryFactStore};
use crate::kb::StoredFact;

/// Maximum number of predicates kept in the LRU cache simultaneously.
const DEFAULT_MAX_CACHED_PREDICATES: usize = 64;

/// WASI-compatible lazy-loading fact store.
///
/// On open: loads the predicate index (relation → file offsets) into memory.
/// On lookup: deserializes facts for the requested predicate on first access,
/// caches them in an LRU cache for subsequent lookups.
/// On insert: appends to the facts log, updates in-memory index + cache.
pub struct WasiFactStore {
    /// Path to the data directory.
    dir: PathBuf,
    /// Predicate index: relation → Vec<offset in facts.bin>.
    pred_index: HashMap<String, Vec<u64>>,
    /// LRU cache: per-predicate fact sets, bounded by max_cached_predicates.
    cache: HashMap<String, HashSet<StoredFact>>,
    /// LRU order: most recently used at back, least recently used at front.
    lru_order: VecDeque<String>,
    /// Maximum predicates in cache.
    max_cached_predicates: usize,
    /// All facts seen so far (populated incrementally on insert + load_predicate).
    all_facts_set: HashSet<StoredFact>,
    /// Total fact count (maintained incrementally).
    fact_count: usize,
}

impl WasiFactStore {
    /// Open or create a WASI fact store at the given directory path.
    pub fn open(dir: &Path) -> Result<Self, String> {
        std::fs::create_dir_all(dir).map_err(|e| format!("mkdir: {e}"))?;

        let facts_path = dir.join("facts.bin");
        let index_path = dir.join("index.bin");

        // Ensure facts.bin exists.
        if !facts_path.exists() {
            File::create(&facts_path).map_err(|e| format!("create facts.bin: {e}"))?;
        }

        // Load predicate index.
        let (pred_index, fact_count) = if index_path.exists() {
            let mut data = Vec::new();
            File::open(&index_path)
                .and_then(|mut f| f.read_to_end(&mut data))
                .map_err(|e| format!("read index.bin: {e}"))?;
            if data.is_empty() {
                (HashMap::new(), 0)
            } else {
                let idx: HashMap<String, Vec<u64>> =
                    postcard::from_bytes(&data).map_err(|e| format!("decode index: {e}"))?;
                let count: usize = idx.values().map(|v| v.len()).sum();
                (idx, count)
            }
        } else {
            (HashMap::new(), 0)
        };

        let count = if fact_count > 0 {
            println!("[WasiStore] Loaded index: {} predicates, {} facts", pred_index.len(), fact_count);
            fact_count
        } else {
            0
        };

        Ok(Self {
            dir: dir.to_path_buf(),
            pred_index,
            cache: HashMap::new(),
            lru_order: VecDeque::new(),
            max_cached_predicates: DEFAULT_MAX_CACHED_PREDICATES,
            all_facts_set: HashSet::new(),
            fact_count: count,
        })
    }

    /// Load facts for a predicate from disk into the cache.
    fn load_predicate(&mut self, relation: &str) {
        if self.cache.contains_key(relation) {
            // Already cached — just touch LRU.
            self.touch_lru(relation);
            return;
        }

        let offsets = match self.pred_index.get(relation) {
            Some(o) => o.clone(),
            None => {
                self.cache.insert(relation.to_string(), HashSet::new());
                self.push_lru(relation);
                return;
            }
        };

        let facts_path = self.dir.join("facts.bin");
        let mut facts = HashSet::new();

        if let Ok(mut file) = File::open(&facts_path) {
            for &offset in &offsets {
                if file.seek(SeekFrom::Start(offset)).is_err() {
                    continue;
                }
                if let Some(fact) = read_fact_at_current_pos(&mut file) {
                    self.all_facts_set.insert(fact.clone());
                    facts.insert(fact);
                }
            }
        }

        self.cache.insert(relation.to_string(), facts);
        self.push_lru(relation);
    }

    fn touch_lru(&mut self, relation: &str) {
        self.lru_order.retain(|r| r != relation);
        self.lru_order.push_back(relation.to_string());
    }

    fn push_lru(&mut self, relation: &str) {
        self.lru_order.push_back(relation.to_string());
        // Evict if over capacity.
        while self.lru_order.len() > self.max_cached_predicates {
            if let Some(evicted) = self.lru_order.pop_front() {
                self.cache.remove(&evicted);
            }
        }
    }

    /// Flush the predicate index to disk.
    fn flush_index(&self) {
        let index_path = self.dir.join("index.bin");
        if let Ok(bytes) = postcard::to_allocvec(&self.pred_index) {
            if let Ok(mut f) = File::create(&index_path) {
                let _ = f.write_all(&bytes);
            }
        }
    }

}

/// Read a single fact entry from the current file position.
/// Format: [u32 rel_len][rel bytes][u32 fact_len][fact bytes]
fn read_fact_at_current_pos(file: &mut File) -> Option<StoredFact> {
    let mut len_buf = [0u8; 4];

    // Read relation length.
    file.read_exact(&mut len_buf).ok()?;
    let rel_len = u32::from_le_bytes(len_buf) as usize;
    let mut rel_buf = vec![0u8; rel_len];
    file.read_exact(&mut rel_buf).ok()?;
    // Skip relation string (we don't use it — the fact itself contains the relation).

    // Read fact length.
    file.read_exact(&mut len_buf).ok()?;
    let fact_len = u32::from_le_bytes(len_buf) as usize;
    let mut fact_buf = vec![0u8; fact_len];
    file.read_exact(&mut fact_buf).ok()?;

    postcard::from_bytes::<StoredFact>(&fact_buf).ok()
}

/// Write a single fact entry at the current file position.
/// Returns the offset where the entry was written.
fn write_fact_at_end(file: &mut File, fact: &StoredFact) -> Option<u64> {
    let offset = file.seek(SeekFrom::End(0)).ok()?;

    let rel = fact.relation();
    let rel_bytes = rel.as_bytes();
    file.write_all(&(rel_bytes.len() as u32).to_le_bytes()).ok()?;
    file.write_all(rel_bytes).ok()?;

    let fact_bytes = postcard::to_allocvec(fact).ok()?;
    file.write_all(&(fact_bytes.len() as u32).to_le_bytes()).ok()?;
    file.write_all(&fact_bytes).ok()?;

    Some(offset)
}

impl FactStore for WasiFactStore {
    fn lookup_predicate(&self, relation: &str) -> Option<&HashSet<StoredFact>> {
        // Check cache. If not cached, we need &mut self to load — but the trait
        // requires &self. Use the same pattern as the note in the trait: callers
        // should ensure loading. For now, return None for unloaded predicates.
        // The KB calls ensure_loaded() before queries.
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
        let facts_path = self.dir.join("facts.bin");
        if let Ok(mut file) = OpenOptions::new().append(true).create(true).open(&facts_path) {
            if let Some(offset) = write_fact_at_end(&mut file, &fact) {
                let rel = fact.relation().to_string();
                self.pred_index.entry(rel.clone()).or_default().push(offset);
                self.all_facts_set.insert(fact.clone());
                self.cache.entry(rel.clone()).or_default().insert(fact);
                self.touch_lru(&rel);
                self.fact_count += 1;

                // Flush index periodically.
                if self.fact_count % 100 == 0 {
                    self.flush_index();
                }
            }
        }
    }

    fn remove(&mut self, fact: &StoredFact) -> bool {
        let rel = fact.relation().to_string();
        let removed = if let Some(set) = self.cache.get_mut(&rel) {
            set.remove(fact)
        } else {
            false
        };
        if removed {
            self.fact_count = self.fact_count.saturating_sub(1);
            self.all_facts_set.remove(fact);
            // Note: fact remains in facts.bin (append-only). Compaction is deferred.
        }
        removed
    }

    fn clear(&mut self) {
        self.pred_index.clear();
        self.cache.clear();
        self.lru_order.clear();
        self.all_facts_set.clear();
        self.fact_count = 0;

        // Truncate disk files.
        let facts_path = self.dir.join("facts.bin");
        let index_path = self.dir.join("index.bin");
        if let Ok(f) = File::create(&facts_path) {
            drop(f);
        }
        if let Ok(f) = File::create(&index_path) {
            drop(f);
        }
    }

    fn all_facts(&self) -> &HashSet<StoredFact> {
        &self.all_facts_set
    }

    fn len(&self) -> usize {
        self.fact_count
    }

    fn clone_box(&self) -> Box<dyn FactStore> {
        // Clone to detached InMemoryFactStore (same as RedbFactStore).
        let mut mem = InMemoryFactStore::new();
        for fact in self.all_facts() {
            mem.insert(fact.clone());
        }
        Box::new(mem)
    }
}

impl Drop for WasiFactStore {
    fn drop(&mut self) {
        self.flush_index();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kb::{GroundFact, GroundTerm};

    fn temp_dir() -> PathBuf {
        let dir = std::env::temp_dir().join(format!("nibli_wasi_test_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        dir
    }

    fn make_fact(rel: &str, entity: &str) -> StoredFact {
        StoredFact::Bare(GroundFact::new(
            rel,
            vec![
                GroundTerm::Constant(entity.to_string()),
                GroundTerm::Unspecified,
            ],
        ))
    }

    #[test]
    fn test_wasi_store_insert_and_lookup() {
        let dir = temp_dir();
        let mut store = WasiFactStore::open(&dir).unwrap();
        let fact = make_fact("gerku", "adam");
        store.insert(fact.clone());

        // Must load predicate into cache for lookup.
        store.load_predicate("gerku");
        assert!(store.contains(&fact));
        assert_eq!(store.len(), 1);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_wasi_store_lazy_load() {
        let dir = temp_dir();

        // Insert and close.
        {
            let mut store = WasiFactStore::open(&dir).unwrap();
            store.insert(make_fact("gerku", "adam"));
            store.insert(make_fact("gerku", "bob"));
            store.insert(make_fact("mlatu", "carol"));
            store.flush_index();
        }

        // Reopen — facts should be on disk, index loaded.
        {
            let mut store = WasiFactStore::open(&dir).unwrap();
            assert_eq!(store.len(), 3);

            // Cache is empty — lookup returns None until loaded.
            assert!(store.lookup_predicate("gerku").is_none());

            // Load predicate lazily.
            store.load_predicate("gerku");
            let gerku_facts = store.lookup_predicate("gerku").unwrap();
            assert_eq!(gerku_facts.len(), 2);
            assert!(gerku_facts.contains(&make_fact("gerku", "adam")));
            assert!(gerku_facts.contains(&make_fact("gerku", "bob")));

            // mlatu not loaded yet.
            assert!(store.lookup_predicate("mlatu").is_none());
            store.load_predicate("mlatu");
            assert_eq!(store.lookup_predicate("mlatu").unwrap().len(), 1);
        }

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_wasi_store_contains() {
        let dir = temp_dir();
        let mut store = WasiFactStore::open(&dir).unwrap();
        let fact = make_fact("gerku", "adam");
        store.insert(fact.clone());
        store.load_predicate("gerku");
        assert!(store.contains(&fact));
        assert!(!store.contains(&make_fact("gerku", "bob")));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_wasi_store_remove() {
        let dir = temp_dir();
        let mut store = WasiFactStore::open(&dir).unwrap();
        let fact = make_fact("gerku", "adam");
        store.insert(fact.clone());
        store.load_predicate("gerku");
        assert!(store.contains(&fact));
        assert!(store.remove(&fact));
        assert!(!store.contains(&fact));
        assert_eq!(store.len(), 0);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_wasi_store_clone_box() {
        let dir = temp_dir();
        let mut store = WasiFactStore::open(&dir).unwrap();
        store.insert(make_fact("gerku", "adam"));
        store.insert(make_fact("mlatu", "bob"));

        let cloned = store.clone_box();
        assert_eq!(cloned.len(), 2);
        assert!(cloned.contains(&make_fact("gerku", "adam")));
        assert!(cloned.contains(&make_fact("mlatu", "bob")));

        let _ = std::fs::remove_dir_all(&dir);
    }
}
