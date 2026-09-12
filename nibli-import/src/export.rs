//! N-Triples export from TYPED facts — fail-closed.
//!
//! The EXPORTABLE FRAGMENT is exactly what [`crate::import_triples_raw`]
//! produces: arity-2 `Bare` facts over IRI-safe named constants and finite
//! numbers, emitted as one plain predicate triple per fact under the minted
//! stable base [`EXPORT_BASE`]
//! (`<base#subject> <base#relation> <base#object | "n"^^xsd:double> .`).
//! Everything the fragment cannot say in a triple is REFUSED with a reason,
//! never silently dropped: tense/deontic-wrapped facts (a triple carries no
//! flavor), arities other than 2 (RDF is subject–predicate–object),
//! engine-internal terms (Skolems, descriptions, unspecified places — an
//! event-decomposed KR fact refuses here by its Skolem event argument),
//! non-finite numbers, constants that are not IRI-local-name safe (refused
//! rather than lossy-encoded), and the relation local names the OWL importer
//! routes specially (`type`, `subClassOf` — a round trip would produce sort
//! declarations, not the fact back).
//!
//! Round trip: the emitted document re-imports through
//! [`crate::import_triples_raw`] to exactly the exported facts — the importer
//! keys on IRI LOCAL NAMES, so the minted base strips back off without
//! per-fact IRI provenance, and numbers ride `"n"^^xsd:double` (Rust's
//! shortest-round-trip `f64` formatting parses back to the same bits). The
//! facts are the CURRENT truth store — asserted and eagerly derived alike;
//! rules are not exported. Lines are sorted and deduplicated, so the document
//! is deterministic.

use nibli_engine::NibliEngine;
use nibli_reason::kb::{GroundFact, GroundTerm, StoredFact};

/// The minted stable namespace every exported IRI lives under.
pub const EXPORT_BASE: &str = "http://nibli.dev/kb#";

const XSD_DOUBLE: &str = "http://www.w3.org/2001/XMLSchema#double";

/// A fail-closed export: the pure N-Triples document plus the per-fact
/// refusals as `(fact display, reason)` pairs. `refused` is part of the
/// contract — a caller that shows only `document` is hiding the drop the
/// emitter refused to make silent.
#[derive(Debug)]
pub struct NTriplesExport {
    /// Valid N-Triples, one triple per line, sorted and deduplicated.
    pub document: String,
    /// Number of triples in `document`.
    pub exported: usize,
    /// Facts with no faithful triple form, each with its refusal reason.
    pub refused: Vec<(String, String)>,
}

/// Export the engine's current truth store as N-Triples, fail-closed.
///
/// The store holds the EVENT DECOMPOSITION (`rel(ev)` + `rel_xN(ev, argN)` —
/// every assertion path decomposes, `assert_fact_direct` included), so the
/// exporter first RE-PROJECTS each complete anchor+roles group back to its
/// surface tuple `rel(arg1, …, argN)` — the same lossless regrouping the ASP
/// oracle performs — and then maps each tuple onto a triple. Groups that
/// cannot be reconstructed (orphan roles, non-contiguous places) refuse, as
/// does every tuple outside the fragment.
pub fn export_ntriples(engine: &NibliEngine) -> NTriplesExport {
    let mut lines: Vec<String> = Vec::new();
    let mut refused: Vec<(String, String)> = Vec::new();
    let facts = match engine.kb().active_typed_facts() {
        Ok(facts) => facts,
        Err(error) => {
            return NTriplesExport {
                document: String::new(),
                exported: 0,
                refused: vec![("knowledge base".into(), error.to_string())],
            };
        }
    };
    let (tuples, structural_refusals) = project_surface_tuples(&facts);
    refused.extend(structural_refusals);
    for tuple in &tuples {
        match tuple_to_triple(tuple) {
            Ok(line) => lines.push(line),
            Err(reason) => refused.push((tuple_display(tuple), reason)),
        }
    }
    lines.sort();
    lines.dedup();
    refused.sort();
    let exported = lines.len();
    let mut document = lines.join("\n");
    if !document.is_empty() {
        document.push('\n');
    }
    NTriplesExport {
        document,
        exported,
        refused,
    }
}

/// Re-project the store's event decomposition to surface tuples, fail-closed.
///
/// - `rel(ev)` with a single Skolem argument is an ANCHOR; `rel_xN(ev, v)` is
///   a ROLE. A complete group (places contiguous from 1) projects to
///   `rel(v1, …, vk)`.
/// - A `Bare` fact with no Skolem arguments and no role suffix is already a
///   surface tuple and passes through unchanged.
/// - Everything else refuses with a reason: tense/deontic wrappers, orphan
///   roles (no anchor for their event), anchors whose role places have gaps,
///   and role-shaped or Skolem-bearing facts that fit no group.
pub fn project_surface_tuples(facts: &[StoredFact]) -> (Vec<GroundFact>, Vec<(String, String)>) {
    use std::collections::HashMap;
    let mut tuples: Vec<GroundFact> = Vec::new();
    let mut refused: Vec<(String, String)> = Vec::new();
    // ev-keyed groups: anchor relation + (place → value).
    type Ev = nibli_reason::kb::SkolemSymbol;
    let mut anchors: HashMap<Ev, Vec<String>> = HashMap::new();
    let mut roles: HashMap<Ev, Vec<(usize, GroundTerm)>> = HashMap::new();
    let mut orphans: Vec<&StoredFact> = Vec::new();

    for fact in facts {
        let StoredFact::Bare(g) = fact else {
            refused.push((
                fact_display(fact),
                "tense/deontic-wrapped fact: a triple carries no flavor, so exporting it \
                 would silently strip the wrapper"
                    .to_string(),
            ));
            continue;
        };
        match (role_place(&g.relation), g.args.as_slice()) {
            // Anchor: rel(ev).
            (None, [GroundTerm::Skolem(ev)]) => {
                anchors.entry(*ev).or_default().push(g.relation.clone());
            }
            // Role: rel_xN(ev, value).
            (Some((_, place)), [GroundTerm::Skolem(ev), value]) => {
                roles.entry(*ev).or_default().push((place, value.clone()));
            }
            // Flat surface tuple: no Skolems anywhere, no role suffix. The
            // same trailing-Unspecified trim as the projected path.
            (None, args) if !args.iter().any(|a| matches!(a, GroundTerm::Skolem(_))) => {
                let mut args = args.to_vec();
                while matches!(args.last(), Some(GroundTerm::Unspecified)) {
                    args.pop();
                }
                tuples.push(GroundFact::new(g.relation.clone(), args));
            }
            _ => orphans.push(fact),
        }
    }

    for (ev, anchor_rels) in &anchors {
        let mut places = roles.remove(ev).unwrap_or_default();
        places.sort_by_key(|(n, _)| *n);
        let contiguous = places.iter().enumerate().all(|(i, (n, _))| *n == i + 1);
        for rel in anchor_rels {
            if !contiguous {
                refused.push((
                    format!("{rel}(…)"),
                    format!(
                        "role places {:?} are not contiguous from 1 — the surface tuple \
                         cannot be reconstructed",
                        places.iter().map(|(n, _)| *n).collect::<Vec<_>>()
                    ),
                ));
                continue;
            }
            // Trim the TRAILING run of Unspecified places: direct injection
            // pads to the corpus arity (`knows(bob, adam)` stores
            // `knows_x3/_x4(ev, Unspecified)`), and the padding is arity
            // bookkeeping, not content. An INTERIOR Unspecified still refuses
            // at the tuple mapper — that one is a real elided argument.
            let mut args: Vec<GroundTerm> = places.iter().map(|(_, v)| v.clone()).collect();
            while matches!(args.last(), Some(GroundTerm::Unspecified)) {
                args.pop();
            }
            tuples.push(GroundFact::new(rel.clone(), args));
        }
    }
    // Roles whose event had no anchor.
    for (_, orphan_roles) in roles {
        for (place, value) in orphan_roles {
            refused.push((
                format!("…_x{place}(…, {value:?})"),
                "role fact whose event has no anchor — the surface tuple cannot be \
                 reconstructed"
                    .to_string(),
            ));
        }
    }
    for fact in orphans {
        refused.push((
            fact_display(fact),
            "Skolem-bearing fact that fits no anchor+roles group (nested witness or \
             role-shaped anchor) — engine-internal, no faithful triple form"
                .to_string(),
        ));
    }
    (tuples, refused)
}

/// `rel_xN` → `(base, N)`; anything else → `None`.
fn role_place(relation: &str) -> Option<(&str, usize)> {
    let (base, digits) = relation.rsplit_once("_x")?;
    if base.is_empty() || digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    digits.parse::<usize>().ok().map(|n| (base, n))
}

/// Map ONE stored fact — treated as an ALREADY-PROJECTED surface tuple — onto
/// its N-Triples line, or say exactly why it has none. Public so the refusal
/// classes are unit-testable shape by shape; [`export_ntriples`] runs the
/// event-decomposition projection first and feeds [`tuple_to_triple`].
pub fn fact_to_triple(fact: &StoredFact) -> Result<String, String> {
    let StoredFact::Bare(g) = fact else {
        return Err(
            "tense/deontic-wrapped fact: a triple carries no flavor, so exporting it \
             would silently strip the wrapper"
                .to_string(),
        );
    };
    tuple_to_triple(g)
}

/// Map one projected surface tuple onto its N-Triples line, fail-closed.
pub fn tuple_to_triple(g: &GroundFact) -> Result<String, String> {
    if g.args.len() != 2 {
        return Err(format!(
            "arity {}: RDF is subject–predicate–object, only 2-place facts map onto a triple",
            g.args.len()
        ));
    }
    let rel = local_name_safe(&g.relation, "relation")?;
    if rel == "type" || rel == "subClassOf" {
        return Err(format!(
            "relation `{rel}` collides with the OWL importer's rdf:type/rdfs:subClassOf \
             routing — a round trip would produce sort declarations, not this fact"
        ));
    }
    let subject = match &g.args[0] {
        GroundTerm::Constant(c) => local_name_safe(c, "subject")?,
        other => {
            return Err(format!(
                "subject {other:?} has no IRI form (only named constants can be subjects)"
            ));
        }
    };
    let object = match &g.args[1] {
        GroundTerm::Constant(c) => format!("<{EXPORT_BASE}{}>", local_name_safe(c, "object")?),
        GroundTerm::Number(bits) => {
            let n = f64::from_bits(*bits);
            if !n.is_finite() {
                return Err(format!("non-finite number {n} has no RDF literal form"));
            }
            format!("\"{n}\"^^<{XSD_DOUBLE}>")
        }
        other => {
            return Err(format!(
                "object {other:?} has no RDF term form (Skolems, descriptions, and \
                 unspecified places are engine-internal)"
            ));
        }
    };
    Ok(format!(
        "<{EXPORT_BASE}{subject}> <{EXPORT_BASE}{rel}> {object} ."
    ))
}

/// Strict IRI-local-name check: `[A-Za-z0-9_-]+`. Refuses rather than
/// lossy-encodes — a percent-encoded name would not survive the importer's
/// local-name extraction unchanged.
fn local_name_safe(s: &str, role: &str) -> Result<String, String> {
    if s.is_empty() {
        return Err(format!("{role} is empty — no IRI local name"));
    }
    if s.chars()
        .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
    {
        Ok(s.to_string())
    } else {
        Err(format!(
            "{role} {s:?} is not IRI-local-name safe ([A-Za-z0-9_-]) — refusing rather \
             than lossy-encoding"
        ))
    }
}

fn fact_display(fact: &StoredFact) -> String {
    tuple_display(fact.inner())
}

fn tuple_display(g: &GroundFact) -> String {
    let args = g
        .args
        .iter()
        .map(|a| format!("{a:?}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}({args})", g.relation)
}
