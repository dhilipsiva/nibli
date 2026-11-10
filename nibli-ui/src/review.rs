//! Tab-local human review. Nothing here is persisted or grants engine evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Snapshot {
    revision: u64,
    source: String,
    kr: String,
    build: String,
    profile: bool,
}

#[derive(Clone, Debug, Default)]
pub struct ReviewState {
    revision: u64,
    approved: Option<Snapshot>,
}

impl ReviewState {
    pub fn invalidate(&mut self) {
        self.revision = self
            .revision
            .checked_add(1)
            .expect("review revision overflow");
        self.approved = None;
    }

    pub fn snapshot(&self, source: &str, kr: &str, build: &str, profile: bool) -> Snapshot {
        Snapshot {
            revision: self.revision,
            source: source.into(),
            kr: kr.into(),
            build: build.into(),
            profile,
        }
    }

    pub fn approve(&mut self, snapshot: Snapshot) {
        self.approved = Some(snapshot);
    }

    pub fn is_approved(&self, snapshot: &Snapshot) -> bool {
        self.approved.as_ref() == Some(snapshot)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn review_is_exact_and_edit_then_revert_never_revives_it() {
        let mut state = ReviewState::default();
        let original = state.snapshot("a dog", "dog(Rex).", "build-a", false);
        state.approve(original.clone());
        assert!(state.is_approved(&original));
        for changed in [
            state.snapshot("a cat", "dog(Rex).", "build-a", false),
            state.snapshot("a dog", "cat(Rex).", "build-a", false),
            state.snapshot("a dog", "dog(Rex).", "build-b", false),
            state.snapshot("a dog", "dog(Rex).", "build-a", true),
        ] {
            assert!(!state.is_approved(&changed));
        }
        state.invalidate();
        state.invalidate();
        let reverted = state.snapshot("a dog", "dog(Rex).", "build-a", false);
        assert_ne!(
            original, reverted,
            "a late formalizer response must be discarded"
        );
        assert!(!state.is_approved(&reverted));
    }

    #[test]
    fn kb_and_query_reviews_are_independent() {
        let mut kb = ReviewState::default();
        let query = ReviewState::default();
        let snapshot = kb.snapshot("Rex is a dog", "dog(Rex).", "build", false);
        kb.approve(snapshot.clone());
        assert!(!query.is_approved(&snapshot));
        assert!(
            !ReviewState::default().is_approved(&snapshot),
            "reload starts unapproved"
        );
    }
}
