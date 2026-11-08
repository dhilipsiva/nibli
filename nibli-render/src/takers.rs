//! The event takers: the predicates that hold an event abstraction in one place and a party in
//! another, and the phrase each reads as ("is entitled to", "decides to"). One table for every
//! rendering path (the logic buffer, the proof summary, the rule reading), so a right reads the
//! same way wherever it is shown. `permitted` is the lexicon's swap of `permits`, so the event
//! sits in its first place and the party in its second.

pub(crate) struct EventTaker {
    pub(crate) relation: &'static str,
    pub(crate) event_place: usize,
    pub(crate) party_place: usize,
    pub(crate) phrase: &'static str,
}

pub(crate) const EVENT_TAKERS: &[EventTaker] = &[
    EventTaker {
        relation: "obliged",
        event_place: 2,
        party_place: 1,
        phrase: "is obligated to",
    },
    EventTaker {
        relation: "entitled",
        event_place: 2,
        party_place: 1,
        phrase: "is entitled to",
    },
    EventTaker {
        relation: "permits",
        event_place: 1,
        party_place: 2,
        phrase: "is permitted to",
    },
    EventTaker {
        relation: "decide",
        event_place: 2,
        party_place: 1,
        phrase: "decides to",
    },
];

pub(crate) fn event_taker(relation: &str) -> Option<&'static EventTaker> {
    EVENT_TAKERS.iter().find(|t| t.relation == relation)
}

/// The taker a relation names, flat (`entitled`) or as one of its role predicates (`entitled_x2`).
pub(crate) fn taker_of(relation: &str) -> Option<&'static EventTaker> {
    let base = match relation.rsplit_once("_x") {
        Some((b, n)) if n.parse::<usize>().is_ok() => b,
        _ => relation,
    };
    event_taker(base)
}
