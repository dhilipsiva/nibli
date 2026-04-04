//! Fact store abstraction for the reasoning engine.
//!
//! The `FactStore` trait decouples the KB from its storage backend.
//! `InMemoryFactStore` is the default (fast, bounded by available memory).
//! Persistent backends (e.g., redb) implement the same trait for lazy
//! on-demand loading from disk.

use std::collections::{HashMap, HashSet};

use crate::kb::StoredFact;

/// Abstract fact storage backend for the reasoning engine.
///
/// Implementations must maintain a predicate index (relation name → facts)
/// for O(1) amortized lookup on the hot path.
pub trait FactStore {
    /// Look up all facts for a given predicate relation.
    fn lookup_predicate(&self, relation: &str) -> Option<&HashSet<StoredFact>>;

    /// Check if a specific fact is asserted.
    fn contains(&self, fact: &StoredFact) -> bool;

    /// Insert a fact into the store.
    fn insert(&mut self, fact: StoredFact);

    /// Remove all facts (for reset/rebuild).
    fn clear(&mut self);

    /// Iterate over all stored facts.
    fn all_facts(&self) -> &HashSet<StoredFact>;

    /// Number of facts stored.
    fn len(&self) -> usize;

    /// Whether the store is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// In-memory fact store backed by HashSet + predicate index HashMap.
/// This is a direct extraction of the previous `typed_facts` +
/// `typed_predicate_facts` fields from `KnowledgeBaseInner`.
pub struct InMemoryFactStore {
    facts: HashSet<StoredFact>,
    predicate_index: HashMap<String, HashSet<StoredFact>>,
}

impl InMemoryFactStore {
    pub fn new() -> Self {
        Self {
            facts: HashSet::new(),
            predicate_index: HashMap::new(),
        }
    }
}

impl Default for InMemoryFactStore {
    fn default() -> Self {
        Self::new()
    }
}

impl FactStore for InMemoryFactStore {
    fn lookup_predicate(&self, relation: &str) -> Option<&HashSet<StoredFact>> {
        self.predicate_index.get(relation)
    }

    fn contains(&self, fact: &StoredFact) -> bool {
        if let Some(set) = self.predicate_index.get(fact.relation()) {
            set.contains(fact)
        } else {
            false
        }
    }

    fn insert(&mut self, fact: StoredFact) {
        let rel = fact.relation().to_string();
        self.predicate_index
            .entry(rel)
            .or_default()
            .insert(fact.clone());
        self.facts.insert(fact);
    }

    fn clear(&mut self) {
        self.facts.clear();
        self.predicate_index.clear();
    }

    fn all_facts(&self) -> &HashSet<StoredFact> {
        &self.facts
    }

    fn len(&self) -> usize {
        self.facts.len()
    }
}
