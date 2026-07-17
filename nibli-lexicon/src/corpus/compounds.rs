//! Curated compound predicates (the lujvo-concept successor) — HAND-AUTHORED,
//! sorted by name. A `+` compound resolves ONLY through this table (place
//! structures are conventional, never derived from the parts — the lujvo
//! reality); an undefined compound fails closed at resolve.
//!
//! Growing this table is the standard way to add a compound word: pick the
//! `a+b` spelling (head last), hand-author the places, record the source
//! lujvo when one exists.

use super::{CompoundEntry, CorpusTier};

pub(crate) static COMPOUNDS: &[CompoundEntry] = &[
    CompoundEntry {
        name: "computer+user",
        relation: "computer_user",
        source_lujvo: Some("sampli"),
        places: &["user", "computer", "purpose"],
        gloss: "computer user",
        template: Some("{x1} is a user of computer {x2} for purpose {x3}"),
        tier: CorpusTier::Curated,
    },
    CompoundEntry {
        name: "data+record",
        relation: "data_record",
        source_lujvo: Some("datnyvei"),
        places: &["record", "content", "medium"],
        gloss: "data record",
        template: Some("{x1} is a data record of {x2} on medium {x3}"),
        tier: CorpusTier::Curated,
    },
    CompoundEntry {
        name: "dog+house",
        relation: "dog_house",
        source_lujvo: Some("gerzda"),
        places: &["house", "dog"],
        gloss: "doghouse",
        template: Some("{x1} is a doghouse for {x2}"),
        tier: CorpusTier::Curated,
    },
];
