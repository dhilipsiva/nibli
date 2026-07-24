//! Decision cache keyed by policy version + call arguments + context hash.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use crate::decision::Decision;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct CacheKey {
    pub policy_version: String,
    pub agent: String,
    pub action: String,
    pub resource: String,
    pub context_hash: u64,
}

pub(crate) fn hash_context(context_kr: &str) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    context_kr.hash(&mut h);
    h.finish()
}

#[derive(Default)]
pub(crate) struct DecisionCache {
    map: HashMap<CacheKey, Decision>,
}

impl DecisionCache {
    pub fn get(&self, key: &CacheKey) -> Option<Decision> {
        self.map.get(key).cloned()
    }

    pub fn insert(&mut self, key: CacheKey, value: Decision) {
        self.map.insert(key, value);
    }

    pub fn clear(&mut self) {
        self.map.clear();
    }
}
