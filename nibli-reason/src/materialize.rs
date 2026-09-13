//! Stratum-ordered materialisation: saturate the extension of a relation bottom-up
//! so negation-as-failure becomes a LOOKUP instead of an exhaustive proof attempt.
//!
//! # Why this module exists
//!
//! `~p(x)` is answered by trying to prove `p(x)` and failing ([`crate::reasoning`]'s
//! `NotNode` arm, the flat negated-condition inversion, and `eval_negated_exists_group`
//! all bottom out in `check_predicate_in_kb_typed`). When `p` is concluded by a wide
//! multi-variable rule, each negated occurrence pays for a domain cartesian.
//!
//! Stratification already tells us that cannot be necessary: `check_stratification`
//! ([`crate::rules`]) proves a valid stratum ordering EXISTS — negated relations can be
//! completed before the relations that read them. The engine used that ordering only to
//! REJECT unstratifiable programs and then threw the assignment away. This module keeps
//! it and evaluates with it.
//!
//! # Why the obvious version does not work
//!
//! The compiled program is not function-free Datalog. Neo-Davidsonian decomposition
//! means `false($x)` compiles to `∃ev. false(ev) ∧ false_x1(ev, $x)`, and an `∃` in a
//! rule consequent under a `∀` becomes a DEPENDENT SKOLEM FUNCTION in the head
//! ([`crate::rules`]'s `dependent_skolems` / `skolem_fn_registry`). Essentially every
//! `∀`-rule therefore has a function symbol in its head, so a naive bottom-up fixpoint
//! is not guaranteed to terminate — and an eligibility rule of "no Skolem heads" would
//! admit nothing at all.
//!
//! The escape is the same one `nibli-verify`'s ASP translator takes to keep clingo's
//! grounding finite: REGROUP the decomposition back to function-free surface atoms.
//! `∃ev. rel(ev) ∧ rel_x1(ev,a1) ∧ … ∧ rel_xN(ev,aN)` projects to `rel(a1,…,aN)`,
//! which is sound here because an event variable has no cross-atom identity — it only
//! ties the roles of ONE atom together. Eliminating it keeps the Herbrand base finite,
//! so saturation terminates: no rule can invent a term.
//!
//! That projection is deliberately REIMPLEMENTED here rather than shared with
//! `nibli-verify/src/asp.rs`. The ASP oracle checks this engine's NAF verdicts against
//! clingo's perfect model; an oracle that shared its regrouping code with the engine it
//! checks would stop being independent exactly where NAF soundness is decided. The two
//! implementations can drift — and the clingo differential is what fires when they do.
//!
//! # Fail-closed
//!
//! Everything here is an OPTIMISATION with one unsound failure mode: if a saturation
//! under-derives, `~p(x)` flips from FALSE to a wrong TRUE. So a relation is admitted
//! only when every rule that can conclude it is provably projectable and every relation
//! beneath it is admitted too ([`eligible_relations`]). Anything not admitted is simply
//! absent from the completed set and keeps today's backward-chaining behaviour exactly.

use std::collections::{HashMap, HashSet};

use crate::kb::{
    GroundTerm, KnowledgeBaseInner, NegatedExistsGroup, StoredFact, UniversalRuleRecord,
    is_abstraction_marker,
};

/// Stratum 0 is the EDB / pure-positive layer. A relation read under `~` by a stratum-`n`
/// rule sits at stratum `< n`, so its extension is complete before that rule is evaluated.
pub(super) type Strata = HashMap<String, usize>;

/// Assign every relation in the dependency graph a stratum index.
///
/// The condensation of [`crate::rules::compute_sccs`] is a DAG (SCCs are maximal, so no
/// cycle survives contraction). Label each component by the longest path into it,
/// counting a negative edge as +1 and a positive edge as +0 — the textbook stratification.
/// Members of one SCC share a stratum by construction, which is exactly right: a positive
/// cycle is evaluated as one mutually-recursive block.
///
/// TOTALITY. This terminates and produces a finite label for every node precisely when
/// `check_stratification` returned `Ok` — a negative edge inside an SCC would make the
/// "+1 within a component" demand unsatisfiable, and that is the case the engine already
/// rejects at rule-registration time. Since the graph on a live KB has always passed that
/// check, this cannot fail; it is nonetheless written to be total on ANY graph (a negative
/// intra-SCC edge is absorbed rather than looped on), because a panic here would turn a
/// read-side optimisation into a crash.
///
/// Determinism: `compute_sccs` already sorts its node scan, each node's neighbour list,
/// and each component's members, so the partition is canonical regardless of `HashMap`
/// layout or rule-registration order. The relaxation below is order-independent anyway
/// (it iterates to a fixpoint), so the labelling is reproducible run to run.
pub(super) fn compute_strata(graph: &HashMap<String, Vec<(String, bool)>>) -> Strata {
    let sccs = crate::rules::compute_sccs(graph);

    // node → its component index.
    let mut comp_of: HashMap<&str, usize> = HashMap::new();
    for (i, scc) in sccs.iter().enumerate() {
        for node in scc {
            comp_of.insert(node.as_str(), i);
        }
    }

    // Condensation edges, carrying the strongest (negative wins) label between components.
    // Self-edges are dropped: an intra-SCC edge cannot raise the stratum of its own
    // component, and a negative one is the unstratifiable case the registration gate
    // already refused.
    let mut cond_edges: Vec<Vec<(usize, bool)>> = vec![Vec::new(); sccs.len()];
    for (head, deps) in graph {
        let Some(&h) = comp_of.get(head.as_str()) else {
            continue;
        };
        for (dep, is_neg) in deps {
            let Some(&d) = comp_of.get(dep.as_str()) else {
                continue;
            };
            if d != h {
                // Edge head → dep means "head reads dep", so dep must be no LATER
                // than head; store it as a constraint on `h` keyed by `d`.
                cond_edges[h].push((d, *is_neg));
            }
        }
    }

    // Longest-path relaxation to a fixpoint. Bounded by |components| passes: each pass
    // either raises at least one label or the labels are stable, and no label can exceed
    // the number of components (a strictly longer chain would revisit a component, which
    // the condensation makes impossible).
    let mut level: Vec<usize> = vec![0; sccs.len()];
    for _ in 0..=sccs.len() {
        let mut changed = false;
        for h in 0..sccs.len() {
            for &(d, is_neg) in &cond_edges[h] {
                let want = level[d] + usize::from(is_neg);
                if want > level[h] {
                    level[h] = want;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    let mut out = Strata::new();
    for (i, scc) in sccs.iter().enumerate() {
        for node in scc {
            out.insert(node.clone(), level[i]);
        }
    }
    out
}

/// Why a relation was NOT admitted for materialisation. Surfaced by
/// `KnowledgeBase::materialization_report` — without it a knowledge base cannot tell
/// whether it actually got the lookup, only that its query is still slow.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ineligible {
    /// A rule concluding it has a Skolem function surviving the event projection —
    /// the head invents a term, so saturation may not terminate.
    SkolemHead(String),
    /// A rule's conditions do not partition into per-atom role groups (an event
    /// variable is shared across groups, or appears in an individual position), so the
    /// `∃ev` projection would change what the rule means.
    NotProjectable(String),
    /// A head variable does not occur in a positive body literal, so the rule is not
    /// range-restricted and its saturation is not finite.
    NotRangeRestricted(String),
    /// A condition dispatches to the compute backend / arithmetic. Its domain is not
    /// enumerable, so its extension is not a finite set to saturate.
    ComputeCondition(String),
    /// A RULE TEMPLATE carries a tense or deontic flavour. The v1 projection
    /// has no flavor dimension and would erase that distinction.
    Flavoured(String),
    /// A STORED FACT of this relation carries a flavour. Distinct from `Flavoured` so the
    /// report cannot tell a reader to go looking for a `past` in a rule when it is in the
    /// data (or vice versa) — different place, different repair.
    FlavouredFact,
    /// The KB has a non-empty `du`-equivalence, so fact lookup is modulo union-find and
    /// a plain set-membership test would miss equivalent variants.
    Equality,
    /// A `~P` restrictor group that does not project cleanly.
    NegatedGroup(String),
    /// Admitted on its own merits, but something it depends on was not.
    DependsOn(String),
    /// The stored facts skip a role place (`rel_x1` present, `rel_x2` missing), so there
    /// is no whole surface atom to project.
    RoleGap,
    /// Stored facts of this relation disagree on how many role places they carry, so
    /// there is no single surface arity to probe against.
    ArityClash,
    /// An abstraction TYPING relation (`__abs_<id>` or the `event(·)` anchor beside it).
    /// The projection eliminates the referent, so these carry no surface extension —
    /// refused rather than omitted so they cannot be mistaken for pure EDB.
    AbstractionTyping,
}

impl Ineligible {
    /// One-line explanation, for `materialization_report`.
    pub fn reason(&self) -> String {
        match self {
            Ineligible::SkolemHead(r) => {
                format!("rule '{r}' has a Skolem function in its head after projection")
            }
            Ineligible::NotProjectable(r) => {
                format!("rule '{r}' conditions do not partition into per-atom role groups")
            }
            Ineligible::NotRangeRestricted(r) => {
                format!("rule '{r}' is not range-restricted (a head variable is unbound)")
            }
            Ineligible::ComputeCondition(r) => {
                format!("rule '{r}' has a compute-backend condition (domain not enumerable)")
            }
            Ineligible::Flavoured(r) => {
                format!("rule '{r}' carries a tense/deontic flavour (not reproduced in v1)")
            }
            Ineligible::FlavouredFact => {
                "a stored fact of it carries a tense/deontic flavour (not reproduced in v1)"
                    .to_string()
            }
            Ineligible::Equality => {
                "the KB has `=` equivalence classes (lookup is modulo union-find)".to_string()
            }
            Ineligible::NegatedGroup(r) => {
                format!("rule '{r}' has a `~` restrictor group that does not project cleanly")
            }
            Ineligible::DependsOn(d) => format!("depends on '{d}', which is not materialisable"),
            Ineligible::RoleGap => {
                "its stored facts skip a role place — no whole surface atom to project".to_string()
            }
            Ineligible::ArityClash => {
                "its stored facts disagree on arity — no single surface shape to probe".to_string()
            }
            Ineligible::AbstractionTyping => {
                "an abstraction typing marker — the projection eliminates its referent".to_string()
            }
        }
    }
}

// ─── The event projection ─────────────────────────────────────────────────────
//
// Neo-Davidsonian decomposition turns a surface atom into an anchor plus one role
// atom per place, all sharing a fresh event term:
//
//     teaches(Esa, Fin).
//       ⇒ teaches(ev) ∧ teaches_x1(ev, esa) ∧ teaches_x2(ev, fin) ∧ teaches_x3..x5(ev, _)
//
// and in a rule head the event term is a dependent Skolem FUNCTION
// (`SkolemFn("sk_12", x__v2)`), which is exactly what would make a bottom-up fixpoint
// invent terms forever. Projecting the event away — keeping only the role VALUES —
// restores a function-free atom `teaches#(esa, fin, _, _, _)` over a fixed finite
// domain, so saturation terminates.
//
// The projection is sound only while the event variable has no cross-atom identity:
// it must tie the roles of ONE atom together and appear nowhere else. Every check
// below exists to enforce that, and to REFUSE (never silently mistranslate) when it
// does not hold.

/// A projected atom: a surface relation and its role values, event eliminated.
/// Values may contain `PatternVar`s when this came from a rule template.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Atom {
    pub(super) relation: String,
    pub(super) values: Vec<GroundTerm>,
}

/// Why a projection was refused. Carried into [`Ineligible`] by the caller, which
/// knows the rule label.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ProjectErr {
    /// An atom is neither an anchor `R(ev)` nor a role `R_xN(ev, v)`.
    NotRoleShaped,
    /// A group has no anchor atom, so we cannot name the surface relation.
    NoAnchor,
    /// Role places are not the contiguous run `x1..xN`.
    GappedRoles,
    /// The event term occurs in a role VALUE — it has cross-atom identity, so
    /// eliminating it would change what the rule means.
    EventEscapes,
    /// Two anchors share one event term (`R(ev) ∧ S(ev)`) — same objection.
    AmbiguousAnchor,
    /// A tense/deontic flavour that the v1 projection cannot represent.
    Flavoured,
    /// A `SkolemFn`/`DepPair` survives in a role value (not just the event slot).
    SkolemInValue,
}

/// The surface relation a decomposed predicate name belongs to: `teaches_x2` and the
/// anchor `teaches` both answer `"teaches"`.
pub(super) fn surface_relation(name: &str) -> &str {
    split_role(name).map(|(b, _)| b).unwrap_or(name)
}

/// Split a role predicate name into `(base, place)`: `teaches_x2` → `("teaches", 2)`.
/// Returns `None` for a name that is not role-shaped. A genuine corpus relation
/// literally named `foo_x1` cannot be mistaken for a role of `foo`, because a group is
/// only formed when the ANCHOR `foo(ev)` shares the same event term.
fn split_role(name: &str) -> Option<(&str, usize)> {
    let (base, idx) = name.rsplit_once("_x")?;
    if base.is_empty() {
        return None;
    }
    let place: usize = idx.parse().ok()?;
    if place == 0 {
        None
    } else {
        Some((base, place))
    }
}

/// True for a term the projection must never leave in a value position.
fn is_function_term(t: &GroundTerm) -> bool {
    matches!(t, GroundTerm::SkolemFn(_, _) | GroundTerm::DepPair(_, _))
}

/// Project a set of decomposed atoms into surface atoms, one per event group.
///
/// Returns the projected atoms in a deterministic order (by relation, then by the
/// order their anchor appeared), or the first structural objection found. Atoms that
/// are FLAT (no event group — e.g. the `equals` built-in) are returned separately, so
/// the caller can decide whether it knows how to evaluate them.
#[allow(clippy::type_complexity)]
fn project_atoms(atoms: &[StoredFact]) -> Result<(Vec<Atom>, Vec<StoredFact>), ProjectErr> {
    project_atoms_inner(atoms).map(|(atoms, flat, _)| (atoms, flat))
}

/// As [`project_atoms`], additionally returning the ABSTRACTION MARKER relations that were
/// suppressed. The caller must refuse those explicitly — see [`ProjectedRule::suppressed`].
fn project_atoms_inner(
    atoms: &[StoredFact],
) -> Result<(Vec<Atom>, Vec<StoredFact>, Vec<String>), ProjectErr> {
    // Every atom must be Bare: v1 does not encode Past/Present/Future or deontic
    // wrappers, and dropping one would change the rule. (This is also what keeps the GDPR-style
    // `obliged(every X, event { … })` / `permitted(…)` rules out — they compile to
    // Obligatory/Permitted stored facts, so only the plain `entitled` shape reaches the
    // abstraction handling below.)
    if atoms.iter().any(|a| !matches!(a, StoredFact::Bare(_))) {
        return Err(ProjectErr::Flavoured);
    }

    // ── ABSTRACTION PRE-PASS ──
    //
    // `entitled(every person, event { P() }).` compiles to a head carrying an abstraction
    // referent: `event(sk_1(x))` and `__abs_<id>(sk_1(x))` — TWO arity-1 atoms on one
    // event term — plus `entitled_x2(sk_3(x), sk_1(x))`, the referent in a role VALUE.
    // Untreated those are `AmbiguousAnchor` and `SkolemInValue`, which is why every
    // abstraction-bearing rule was outside the saturation.
    //
    // The identity that crosses compiles is the marker RELATION NAME, not any term: it is
    // `__abs_v1_<digest>_<lossless-key>`, byte-identical wherever the same kind+body
    // appears. The digest is non-semantic; the engine matches the complete marker rather
    // than re-deriving content. So the referent projects to the marker name as an opaque CONSTANT — the
    // same move `nibli-verify/src/asp.rs`'s `abs_const_of` makes for clingo, reimplemented
    // here rather than shared so the oracle stays independent.
    //
    // Collapsing `sk_1(adam)` and `sk_1(bel)` onto one constant is sound ONLY while the
    // referent is used by exactly one role atom; more than one would be genuine cross-atom
    // identity that the collapse would erase. Enforced below, as asp.rs enforces it.
    let mut abs_const: HashMap<&GroundTerm, String> = HashMap::new();
    let mut suppressed: Vec<String> = Vec::new();
    for a in atoms {
        let gf = a.inner();
        if gf.args.len() == 1
            && gf
                .relation
                .starts_with(crate::kb::ABSTRACTION_MARKER_PREFIX)
        {
            abs_const.insert(&gf.args[0], gf.relation.clone());
            suppressed.push(gf.relation.clone());
        }
    }
    if !abs_const.is_empty() {
        // The referent may fill at most one role slot across the whole atom set.
        for (referent, _) in abs_const.iter() {
            let uses = atoms
                .iter()
                .filter(|a| {
                    let gf = a.inner();
                    gf.args.len() == 2 && &gf.args[1] == *referent
                })
                .count();
            if uses > 1 {
                return Err(ProjectErr::EventEscapes);
            }
        }
        // The `event(·)` typing anchor rides in the same bucket and is suppressed with it.
        for a in atoms {
            let gf = a.inner();
            if gf.args.len() == 1
                && abs_const.contains_key(&gf.args[0])
                && !gf
                    .relation
                    .starts_with(crate::kb::ABSTRACTION_MARKER_PREFIX)
            {
                suppressed.push(gf.relation.clone());
            }
        }
    }
    let referent_const = |t: &GroundTerm| -> Option<GroundTerm> {
        abs_const.get(t).map(|m| GroundTerm::Constant(m.clone()))
    };

    // Bucket by event term (argument 0). `order` keeps first-seen order so the output
    // is reproducible without sorting by a term type that has no natural key.
    let mut anchor_of: HashMap<&GroundTerm, &str> = HashMap::new();
    let mut roles_of: HashMap<&GroundTerm, Vec<(usize, &GroundTerm, &str)>> = HashMap::new();
    let mut order: Vec<&GroundTerm> = Vec::new();
    let mut flat: Vec<StoredFact> = Vec::new();

    for a in atoms {
        let gf = a.inner();
        // Suppress the whole marker bucket — both `__abs_<id>(ref)` and the `event(ref)`
        // typing anchor. It is abstraction TYPING, not a surface atom.
        if gf.args.len() == 1 && abs_const.contains_key(&gf.args[0]) {
            continue;
        }
        match gf.args.len() {
            1 => {
                let ev = &gf.args[0];
                if anchor_of.insert(ev, gf.relation.as_str()).is_some() {
                    return Err(ProjectErr::AmbiguousAnchor);
                }
                if !roles_of.contains_key(ev) {
                    order.push(ev);
                    roles_of.entry(ev).or_default();
                }
            }
            2 => match split_role(&gf.relation) {
                Some((_, place)) => {
                    let ev = &gf.args[0];
                    if !roles_of.contains_key(ev) {
                        order.push(ev);
                    }
                    roles_of.entry(ev).or_default().push((
                        place,
                        &gf.args[1],
                        gf.relation.as_str(),
                    ));
                }
                // An arity-2 non-role atom is FLAT (`equals(a, b)`), not part of any
                // event group.
                None => flat.push(a.clone()),
            },
            // Arity 0 or ≥3 is not a decomposed shape at all.
            _ => flat.push(a.clone()),
        }
    }

    let mut out = Vec::with_capacity(order.len());
    for ev in order {
        let Some(&base) = anchor_of.get(ev) else {
            return Err(ProjectErr::NoAnchor);
        };
        let mut roles = roles_of.remove(ev).unwrap_or_default();
        // Every role must belong to THIS anchor's relation.
        for (_, _, rel) in &roles {
            match split_role(rel) {
                Some((b, _)) if b == base => {}
                _ => return Err(ProjectErr::NotRoleShaped),
            }
        }
        roles.sort_by_key(|(place, _, _)| *place);
        // Contiguous x1..xN, no gaps, no duplicates.
        for (i, (place, _, _)) in roles.iter().enumerate() {
            if *place != i + 1 {
                return Err(ProjectErr::GappedRoles);
            }
        }
        let mut values = Vec::with_capacity(roles.len());
        for (_, v, _) in roles {
            // The event must not leak into a value: that would be cross-atom identity,
            // which the projection cannot preserve.
            if v == ev {
                return Err(ProjectErr::EventEscapes);
            }
            // An abstraction referent in a value slot becomes its opaque marker constant.
            // This is what dissolves the `SkolemInValue` refusal for `entitled_x2`.
            if let Some(c) = referent_const(v) {
                values.push(c);
                continue;
            }
            if is_function_term(v) {
                return Err(ProjectErr::SkolemInValue);
            }
            values.push(v.clone());
        }
        out.push(Atom {
            relation: base.to_string(),
            values,
        });
    }
    suppressed.sort();
    suppressed.dedup();
    Ok((out, flat, suppressed))
}

/// Project a `~P` restrictor group. Its templates are one event group by construction
/// (`detect_negated_exists_group` only admits that shape), so exactly one atom must
/// come out and nothing may be left flat.
fn project_negated_group(group: &NegatedExistsGroup) -> Result<Atom, ProjectErr> {
    let (mut atoms, flat) = project_atoms(&group.conditions)?;
    if atoms.len() != 1 || !flat.is_empty() {
        return Err(ProjectErr::NotRoleShaped);
    }
    Ok(atoms.remove(0))
}

/// A rule rewritten as function-free surface Datalog. `None` for any rule the
/// projection refuses — the caller turns that into an [`Ineligible`] with the reason.
pub(super) struct ProjectedRule {
    pub(super) label: String,
    /// Positive body atoms, joined left to right.
    pub(super) positive: Vec<Atom>,
    /// Constant/previously-bound positions, computed once with the rule plan.
    bound_positions: Vec<Vec<usize>>,
    /// Necessary constant-only matches, checked before allocating join frames.
    constant_probes: Vec<(usize, Vec<usize>, Vec<GroundTerm>)>,
    /// Negated body atoms, checked by lookup once the positives have bound everything.
    pub(super) negative: Vec<Atom>,
    /// Flat built-in conditions we know how to decide, with their negation flag.
    /// Today this is exactly `equals` (see [`BUILTIN_RELATIONS`]).
    pub(super) builtins: Vec<(StoredFact, bool)>,
    /// Head atoms — one per conclusion group. A rule may conclude several relations.
    pub(super) head: Vec<Atom>,
    /// Abstraction TYPING relations the projection suppressed — the `__abs_<id>` marker
    /// and the `event(·)` anchor riding in its bucket.
    ///
    /// These MUST be refused explicitly by the caller, never merely omitted. `is_edb` is
    /// `!rules.contains_key && !refused.contains_key`, and `saturate` marks an EDB relation
    /// complete straight from its (empty) seed — so a suppressed marker left unrefused
    /// would answer `~event(x)` TRUE where backward chaining derives `event(sk_1(adam))`
    /// from the rule and answers FALSE. A definitive wrong verdict.
    pub(super) suppressed: Vec<String>,
}

/// Flat conditions the saturator can decide itself, without a stored extension.
/// `equals` is decidable from the term structure alone (reflexivity), and the
/// union-find path is excluded separately by [`Ineligible::Equality`], so a plain
/// structural comparison is exact here.
const BUILTIN_RELATIONS: &[&str] = &[nibli_types::relations::IDENTITY];

fn is_builtin(rel: &str) -> bool {
    BUILTIN_RELATIONS.contains(&rel)
}

/// Specialize an already-admitted projection using positive scalar equalities.
/// Keep every equality as an executable condition, including conflicts, and
/// rewrite all its variable uses together. Range/shape checks must run FIRST:
/// a constant equality does not make an otherwise unbound rule admissible.
fn specialize_fixed_values(
    positive: &mut [Atom],
    negative: &mut [Atom],
    head: &mut [Atom],
    builtins: &mut [(StoredFact, bool)],
) -> Vec<bool> {
    let mut fixed = HashMap::new();
    for (fact, negated) in builtins.iter() {
        if *negated || fact.relation() != nibli_types::relations::IDENTITY {
            continue;
        }
        let (name, value) = match fact.inner().args.as_slice() {
            [GroundTerm::PatternVar(name), value] | [value, GroundTerm::PatternVar(name)] => {
                (name, value)
            }
            _ => continue,
        };
        if matches!(
            value,
            GroundTerm::Constant(_)
                | GroundTerm::Description(_)
                | GroundTerm::Number(_)
                | GroundTerm::Unspecified
        ) {
            fixed.entry(name.clone()).or_insert_with(|| value.clone());
        }
    }
    if fixed.is_empty() {
        return Vec::new();
    }
    let replace = |value: &mut GroundTerm| {
        if let GroundTerm::PatternVar(name) = value
            && let Some(constant) = fixed.get(name)
        {
            *value = constant.clone();
            true
        } else {
            false
        }
    };
    let mut promoted = vec![false; positive.len()];
    for (index, atom) in positive.iter_mut().enumerate() {
        for value in &mut atom.values {
            promoted[index] |= replace(value);
        }
    }
    for atom in negative.iter_mut().chain(head.iter_mut()) {
        for value in &mut atom.values {
            replace(value);
        }
    }
    for (fact, _) in builtins {
        if !fact
            .inner()
            .args
            .iter()
            .any(|value| matches!(value, GroundTerm::PatternVar(name) if fixed.contains_key(name)))
        {
            continue;
        }
        let mut grounded = fact.inner().clone();
        for value in &mut grounded.args {
            replace(value);
        }
        *fact = StoredFact::with_tense_from(grounded, fact);
    }
    promoted
}

/// Rewrite one compiled rule as function-free surface Datalog.
pub(super) fn project_rule(rule: &UniversalRuleRecord) -> Result<ProjectedRule, Ineligible> {
    let label = rule.label.clone();
    let flav = |e: ProjectErr| -> Ineligible {
        match e {
            ProjectErr::Flavoured => Ineligible::Flavoured(label.clone()),
            ProjectErr::SkolemInValue => Ineligible::SkolemHead(label.clone()),
            _ => Ineligible::NotProjectable(label.clone()),
        }
    };

    // Split the conditions into the positively- and negatively-flagged halves FIRST:
    // a flat negated literal and a positive one project identically, but they must not
    // be merged into one event group by accident.
    let mut pos_conds: Vec<StoredFact> = Vec::new();
    let mut neg_conds: Vec<StoredFact> = Vec::new();
    for (i, c) in rule.typed_conditions.iter().enumerate() {
        if rule.negated_condition_indices.contains(&i) {
            neg_conds.push(c.clone());
        } else {
            pos_conds.push(c.clone());
        }
    }

    let (mut positive, pos_flat) = project_atoms(&pos_conds).map_err(&flav)?;
    let (neg_flat_atoms, neg_flat) = project_atoms(&neg_conds).map_err(&flav)?;

    let mut builtins: Vec<(StoredFact, bool)> = Vec::new();
    for (f, negated) in pos_flat
        .into_iter()
        .map(|f| (f, false))
        .chain(neg_flat.into_iter().map(|f| (f, true)))
    {
        if !is_builtin(f.relation()) {
            // A flat condition we cannot decide — most often a compute predicate,
            // whose domain is not enumerable.
            //
            // NOTE the reach of this check: it sees only FLAT conditions. A numeric
            // comparison written at the surface (`greater($n, 15)`) is event-decomposed,
            // so it takes the event-group path in `project_atoms` and projects as an
            // ORDINARY atom — it never arrives here. Were such a rule registrable, the
            // saturator would then call `greater` EDB, seed it empty, and mark that empty
            // extension complete, so `~greater(…)` would read as definitively TRUE. It is
            // unreachable only because `validate_no_operational_comparisons` refuses the
            // rule at assertion ingress. If that guard is ever relaxed, this check must be
            // taught the decomposed shape FIRST.
            return Err(Ineligible::ComputeCondition(label.clone()));
        }
        builtins.push((f, negated));
    }

    let mut negative = neg_flat_atoms;
    for g in &rule.negated_exists_groups {
        match project_negated_group(g) {
            Ok(a) => negative.push(a),
            Err(ProjectErr::Flavoured) => return Err(Ineligible::Flavoured(label)),
            Err(_) => return Err(Ineligible::NegatedGroup(label)),
        }
    }

    // The head. `project_atoms` rejects a `SkolemFn` in a VALUE position but not in the
    // event slot, which is exactly right: the dependent Skolem that every `∀`-rule head
    // carries lives in the event slot and is what the projection eliminates.
    let (mut head, head_flat, suppressed) =
        project_atoms_inner(&rule.typed_conclusions).map_err(&flav)?;
    if !head_flat.is_empty() || head.is_empty() {
        return Err(Ineligible::NotProjectable(label));
    }
    // A rule that DERIVES a built-in would invalidate the built-in evaluator below,
    // which decides `equals` from term structure alone. Refuse rather than evaluate a
    // relation two different ways in one saturation.
    if head.iter().any(|a| is_builtin(&a.relation)) {
        return Err(Ineligible::NotProjectable(label));
    }

    // RANGE RESTRICTION. Every variable in a head value, in a negated atom, or in a
    // built-in must be bound by a positive body atom — otherwise the rule ranges over
    // terms the saturation never enumerates and its extension would be under-derived,
    // which is the one way this optimisation can turn a NAF FALSE into a wrong TRUE.
    let mut bound: HashSet<&str> = HashSet::new();
    for a in &positive {
        for v in &a.values {
            if let GroundTerm::PatternVar(n) = v {
                bound.insert(n.as_str());
            }
        }
    }
    let unbound = |vals: &[GroundTerm]| -> bool {
        vals.iter()
            .any(|v| matches!(v, GroundTerm::PatternVar(n) if !bound.contains(n.as_str())))
    };
    if head.iter().any(|a| unbound(&a.values))
        || negative.iter().any(|a| unbound(&a.values))
        || builtins
            .iter()
            .any(|(f, _)| unbound(f.inner().args.as_slice()))
    {
        return Err(Ineligible::NotRangeRestricted(label));
    }

    let promoted = specialize_fixed_values(&mut positive, &mut negative, &mut head, &mut builtins);
    let mut constant_probes: Vec<_> = positive
        .iter()
        .enumerate()
        .filter_map(|(index, atom)| {
            let positions: Vec<_> = atom
                .values
                .iter()
                .enumerate()
                .filter(|(_, value)| !matches!(value, GroundTerm::PatternVar(_)))
                .map(|(position, _)| position)
                .collect();
            if positions.is_empty() {
                return None;
            }
            let key = positions
                .iter()
                .map(|&position| atom.values[position].clone())
                .collect();
            Some((index, positions, key))
        })
        .collect();
    if !promoted.is_empty() {
        // A record-kind or mode equality is usually more selective than the
        // shared authority/field prefixes. Reorder only necessary prechecks,
        // never the executable joins or their binding order.
        constant_probes.sort_by_key(|(index, _, _)| !promoted[*index]);
    }
    Ok(ProjectedRule {
        label,
        bound_positions: bound_positions(&positive),
        constant_probes,
        positive,
        negative,
        builtins,
        head,
        suppressed,
    })
}

/// Every distinct rule in the KB, once. `universal_rules` indexes the SAME `Arc` under
/// every relation the rule concludes, so a naive iteration would visit a multi-headed
/// rule several times.
pub(super) fn distinct_rules(
    inner: &KnowledgeBaseInner,
) -> Vec<&std::sync::Arc<UniversalRuleRecord>> {
    let mut seen: HashSet<*const UniversalRuleRecord> = HashSet::new();
    let mut keys: Vec<&String> = inner.universal_rules.keys().collect();
    keys.sort();
    let mut out = Vec::new();
    for k in keys {
        for r in &inner.universal_rules[k] {
            if seen.insert(std::sync::Arc::as_ptr(r)) {
                out.push(r);
            }
        }
    }
    out
}

/// The outcome of the eligibility analysis: which surface relations may be saturated,
/// and why each of the others may not.
pub(super) struct Eligibility {
    pub(super) eligible: HashSet<String>,
    pub(super) refused: HashMap<String, Ineligible>,
    /// The projected form of every rule that survived, keyed by head relation.
    pub(super) rules: HashMap<String, Vec<std::sync::Arc<ProjectedRule>>>,
    /// First-seen distinct dependencies per head, projected from exactly the
    /// same positive/negative atoms as the executable rules. No quoted edges.
    pub(super) dependencies: HashMap<String, Vec<String>>,
    pub(super) negatively_read: HashSet<String>,
}

/// Rule-only planning survives ordinary fact insertions and can be shared by
/// independent snapshots. Stored-fact shape checks still run in `seed_edb` on
/// every new or resumed materialization.
pub(super) struct MaterializationPlan {
    eligibility: Eligibility,
    strata: Strata,
    pub(super) domain: crate::domain::DomainPlan,
}

pub(super) fn materialization_plan(
    inner: &KnowledgeBaseInner,
) -> std::sync::Arc<MaterializationPlan> {
    if let Some(plan) = inner.materialization_plan.borrow().as_ref() {
        return std::sync::Arc::clone(plan);
    }
    let plan = std::sync::Arc::new(MaterializationPlan {
        eligibility: eligible_relations(inner),
        strata: compute_strata(&inner.pred_dep_graph),
        domain: crate::domain::DomainPlan::new(inner),
    });
    *inner.materialization_plan.borrow_mut() = Some(std::sync::Arc::clone(&plan));
    plan
}

/// Decide which surface relations can be saturated bottom-up.
///
/// Two passes. First, project every rule: a rule that refuses poisons every relation it
/// concludes. Second, close DOWNWARD — a relation stays eligible only while every
/// relation its surviving rules read is itself eligible, pure EDB, or a built-in. The
/// closure is a shrinking fixpoint, so it is order-independent and terminates.
pub(super) fn eligible_relations(inner: &KnowledgeBaseInner) -> Eligibility {
    let mut refused: HashMap<String, Ineligible> = HashMap::new();
    let mut rules: HashMap<String, Vec<std::sync::Arc<ProjectedRule>>> = HashMap::new();

    // The `du` union-find makes fact lookup modulo equivalence classes; a plain
    // set-membership test on a projected tuple would miss an equivalent variant, so a
    // NAF answered by lookup could wrongly report "no witness". Refuse the whole KB.
    if !inner.equivalence_parent.is_empty() {
        for r in distinct_rules(inner) {
            for c in &r.typed_conclusions {
                refused.insert(c.relation().to_string(), Ineligible::Equality);
            }
        }
        return Eligibility {
            eligible: HashSet::new(),
            refused,
            rules,
            dependencies: HashMap::new(),
            negatively_read: HashSet::new(),
        };
    }

    for r in distinct_rules(inner) {
        match project_rule(r) {
            Ok(pr) => {
                // Abstraction TYPING relations the projection suppressed are REFUSED, not
                // omitted. `is_edb` is "no rule and not refused", and `saturate` marks an
                // EDB relation complete straight from its seed — so an omitted marker
                // would be complete over an EMPTY extension, and `~event(x)` would answer
                // TRUE where backward chaining derives `event(sk_1(adam))` from this very
                // rule and answers FALSE. A definitive wrong verdict, silently.
                for rel in &pr.suppressed {
                    refused
                        .entry(rel.clone())
                        .or_insert(Ineligible::AbstractionTyping);
                }
                let pr = std::sync::Arc::new(pr);
                for h in &pr.head {
                    rules
                        .entry(h.relation.clone())
                        .or_default()
                        .push(pr.clone());
                }
            }
            Err(why) => {
                // Name every relation this rule could have concluded. The conclusion
                // templates are decomposed, so the surface name is the anchor's — but a
                // refused projection may not have found one, so fall back to stripping
                // the role suffix.
                for c in &r.typed_conclusions {
                    let rel = split_role(c.relation())
                        .map(|(b, _)| b.to_string())
                        .unwrap_or_else(|| c.relation().to_string());
                    refused.entry(rel).or_insert_with(|| why.clone());
                }
            }
        }
    }

    // Plan relation-level reads once. Wide rules often repeat the same relation
    // hundreds of times with different constant discriminators; that matters to
    // execution, but not to dependency reachability or completion requirements.
    let mut dependencies = HashMap::new();
    let mut negatively_read = HashSet::new();
    for (head, head_rules) in &rules {
        let mut seen = HashSet::new();
        let mut reads = Vec::new();
        for pr in head_rules {
            for dep in pr.positive.iter().chain(pr.negative.iter()) {
                if seen.insert(dep.relation.as_str()) {
                    reads.push(dep.relation.clone());
                }
            }
            negatively_read.extend(pr.negative.iter().map(|dep| dep.relation.clone()));
        }
        dependencies.insert(head.clone(), reads);
    }

    // Candidate set: every relation with at least one surviving rule, minus the refused.
    let mut eligible: HashSet<String> = rules
        .keys()
        .filter(|r| !refused.contains_key(*r))
        .cloned()
        .collect();

    // A relation is pure EDB when nothing can DERIVE it: no surviving rule concludes it
    // AND no refused rule concluded it either. The second half is load-bearing — a
    // relation whose only rule failed to project has no entry in `rules`, and calling
    // that EDB would silently read just its asserted facts and miss every derived one,
    // which is exactly the under-derivation that turns a NAF FALSE into a wrong TRUE.
    fn is_edb(
        rel: &str,
        rules: &HashMap<String, Vec<std::sync::Arc<ProjectedRule>>>,
        refused: &HashMap<String, Ineligible>,
    ) -> bool {
        !rules.contains_key(rel) && !refused.contains_key(rel)
    }

    // Downward closure to a fixpoint. Bounded by |eligible| passes: each pass either
    // removes at least one relation or stops.
    loop {
        let mut drop_rel: Option<(String, String)> = None;
        'outer: for rel in &eligible {
            for dep in dependencies.get(rel).into_iter().flatten() {
                if eligible.contains(dep) || is_edb(dep, &rules, &refused) {
                    continue;
                }
                drop_rel = Some((rel.clone(), dep.clone()));
                break 'outer;
            }
        }
        match drop_rel {
            Some((rel, dep)) => {
                eligible.remove(&rel);
                refused.entry(rel).or_insert(Ineligible::DependsOn(dep));
            }
            None => break,
        }
    }

    Eligibility {
        eligible,
        refused,
        rules,
        dependencies,
        negatively_read,
    }
}

// ─── Saturation ───────────────────────────────────────────────────────────────

/// Extensions of the projected relations: surface relation → set of role-value tuples.
pub(super) type Extensions = HashMap<String, HashSet<Vec<GroundTerm>>>;

/// Test-only accounting for the combinatorial work performed while joining projected
/// rule bodies. The release build keeps this as a zero-sized type, so profiling hooks
/// cannot become part of the runtime cost or public API.
#[derive(Clone, Default)]
pub(super) struct MaterializationWork {
    #[cfg(test)]
    tuple_bind_attempts: HashMap<String, usize>,
    #[cfg(test)]
    positive_presence_checks: usize,
    /// How many times this saturation was folded forward incrementally rather
    /// than recomputed. Resets with the `Materialized` it lives in, so a value
    /// of zero after a mutation means the fixpoint was rebuilt from scratch.
    /// The only observable that separates "resumed" from "recomputed" — both
    /// answer identically, which is exactly why a verdict test cannot see the
    /// difference and this counter has to exist.
    #[cfg(test)]
    resumes: usize,
}

impl MaterializationWork {
    #[inline]
    fn note_positive_presence_check(&mut self) {
        #[cfg(test)]
        {
            self.positive_presence_checks += 1;
        }
    }

    #[cfg(test)]
    pub(super) fn positive_presence_checks(&self) -> usize {
        self.positive_presence_checks
    }

    #[inline]
    fn note_tuple_bind_attempt(&mut self, _rule: &ProjectedRule) {
        #[cfg(test)]
        for head in &_rule.head {
            *self
                .tuple_bind_attempts
                .entry(head.relation.clone())
                .or_default() += 1;
        }
    }

    #[inline]
    fn note_resume(&mut self) {
        #[cfg(test)]
        {
            self.resumes += 1;
        }
    }

    #[cfg(test)]
    pub(super) fn resumes(&self) -> usize {
        self.resumes
    }

    #[cfg(test)]
    pub(super) fn tuple_bind_attempts(&self, relation: &str) -> usize {
        self.tuple_bind_attempts
            .get(relation)
            .copied()
            .unwrap_or_default()
    }
}

/// Total derived-tuple budget for one saturation.
///
/// Saturation is an OPTIMISATION. A KB whose least model is enormous would spend more
/// time saturating than the backward search it replaces, so the budget is a
/// stop-loss, not a correctness device: exceeding it abandons the stratum and leaves
/// its relations INCOMPLETE, which means every NAF over them falls back to today's
/// path. Deliberately generous — the shipped corpora derive in the hundreds.
const MAX_MATERIALIZED_TUPLES: usize = crate::domain::MAX_INFERENCE_RECORDS;

/// The result of a saturation: which relations were completed, their extensions, and
/// why each of the others was not.
#[derive(Clone)]
pub(super) struct Materialized {
    pub(super) ext: Extensions,
    pub(super) complete: HashSet<String>,
    pub(super) refused: HashMap<String, Ineligible>,
    /// Projected arity per relation — how many role places its tuples carry.
    pub(super) arity: HashMap<String, usize>,
    /// Query roots whose dependency cones are represented by this cache. A later query
    /// unions its missing roots and recomputes that cumulative cone; treating any
    /// partial cache as globally complete would strand the positive fast path.
    pub(super) requested: HashSet<String>,
    /// Every SURFACE relation this saturation's extensions can depend on — the
    /// dependency closure of `requested` over the eligible rules, positive AND
    /// negated deps alike. A stored fact whose surface relation is outside this
    /// set cannot change any extension here, which is what lets an insert about
    /// an unrelated relation leave the saturation standing
    /// (`invalidate_materialization_for_insert`). `complete` is always a subset,
    /// so a relation outside the cone also carries no completeness claim.
    pub(super) cone: HashSet<String>,
    /// Relations read under NEGATION by any eligible rule. Growth through a
    /// negated condition SHRINKS the model, so an insert into one of these can
    /// never be folded in incrementally — it invalidates outright.
    pub(super) negatively_read: HashSet<String>,
    /// In-cone relations whose stored extension may have gained tuples since
    /// this saturation was built. Empty = clean; non-empty means the next query
    /// must fold the delta in (`resume_with_delta`) before reading it.
    pub(super) grew: HashSet<String>,
    pub(super) work: MaterializationWork,
}

impl Materialized {
    pub(super) fn empty() -> Self {
        Materialized {
            ext: Extensions::new(),
            complete: HashSet::new(),
            refused: HashMap::new(),
            arity: HashMap::new(),
            requested: HashSet::new(),
            cone: HashSet::new(),
            negatively_read: HashSet::new(),
            grew: HashSet::new(),
            work: MaterializationWork::default(),
        }
    }

    /// May a probe of `arity` role places read this relation's extension as complete?
    ///
    /// The arity check is not belt-and-braces. A probe with FEWER places than the stored
    /// tuples would miss every tuple and read as "nothing derived" — but the engine's own
    /// group check only tests the atoms the template actually carries, so it WOULD find
    /// that witness. That mismatch is a wrong definitive NAF TRUE. KR text cannot produce
    /// it (arity is fixed by the corpus), but `nibli-import` and the programmatic API can,
    /// so the guard is structural rather than trusting the front-end.
    ///
    /// An EMPTY extension records no arity and answers at every width — "nothing derived"
    /// is correct however many places the probe carries, and that is the case the whole
    /// optimisation turns on (`~false($t)` when nobody has been voided).
    pub(super) fn is_complete_for(&self, relation: &str, arity: usize) -> bool {
        self.complete.contains(relation) && self.arity.get(relation).is_none_or(|&a| a == arity)
    }

    /// Membership in a COMPLETE extension. The caller must have checked
    /// [`Self::is_complete_for`] first — an absent relation here is "nothing derived",
    /// not "not saturated", and confusing the two is how a NAF gets a wrong TRUE.
    pub(super) fn contains(&self, relation: &str, tuple: &[GroundTerm]) -> bool {
        self.ext
            .get(relation)
            .is_some_and(|set| set.contains(tuple))
    }
}

/// Project the fact store into surface tuples — the EDB seed.
///
/// Returns the seed plus the set of relations that carry a tense/deontic flavour
/// anywhere in the store. Those are excluded rather than refusing the whole KB: a
/// flavoured `past P(x)` and a bare `P(x)` are DIFFERENT facts to the engine, and a
/// projection that dropped the flavour would merge them.
fn seed_edb(inner: &KnowledgeBaseInner) -> (Extensions, HashMap<String, Ineligible>) {
    let mut anchors: HashSet<(String, GroundTerm)> = HashSet::new();
    let mut roles: HashMap<(String, GroundTerm), Vec<(usize, GroundTerm)>> = HashMap::new();
    // Relation -> why its stored facts cannot be projected. Three distinct causes share
    // this map, and they must NOT share a message: a flavour, a role-index gap, and an
    // arity clash are different repairs, and a report that called all three "tense" would
    // send the reader looking for a `past` that is not there.
    let mut unseedable: HashMap<String, Ineligible> = HashMap::new();

    for f in inner.fact_store.all_facts() {
        let gf = f.inner();
        let bare = matches!(f, StoredFact::Bare(_));
        match gf.args.len() {
            1 => {
                if !bare {
                    unseedable.insert(gf.relation.clone(), Ineligible::FlavouredFact);
                    continue;
                }
                anchors.insert((gf.relation.clone(), gf.args[0].clone()));
            }
            2 => {
                if let Some((base, place)) = split_role(&gf.relation) {
                    if !bare {
                        unseedable.insert(base.to_string(), Ineligible::FlavouredFact);
                        continue;
                    }
                    roles
                        .entry((base.to_string(), gf.args[0].clone()))
                        .or_default()
                        .push((place, gf.args[1].clone()));
                }
                // A flat arity-2 fact (`equals`) is not a projected relation.
            }
            _ => {}
        }
    }

    let mut ext = Extensions::new();
    for (rel, ev) in anchors {
        if unseedable.contains_key(&rel) {
            continue;
        }
        let mut rs = roles.remove(&(rel.clone(), ev)).unwrap_or_default();
        rs.sort_by_key(|(p, _)| *p);
        // Contiguous x1..xN. A gap means the store holds a partially-retracted or
        // hand-built decomposition we cannot read as one surface atom — skip the group
        // and mark the relation flavoured-style ineligible via the caller's checks
        // rather than inventing a tuple with a hole in it.
        if rs.iter().enumerate().any(|(i, (p, _))| *p != i + 1) {
            unseedable.insert(rel, Ineligible::RoleGap);
            continue;
        }
        let tuple: Vec<GroundTerm> = rs.into_iter().map(|(_, v)| v).collect();
        ext.entry(rel).or_default().insert(tuple);
    }
    // ARITY AGREEMENT. Two stored atoms of one relation with different place counts mean
    // there is no single surface arity to project onto, so a probe of either width would
    // silently miss the other width's tuples. KR text cannot spell this (arity comes from
    // the corpus), but RDF import and the programmatic API can — exclude the relation.
    for (rel, tuples) in &ext {
        let mut widths = tuples.iter().map(Vec::len);
        let first = widths.next().unwrap_or(0);
        if widths.any(|w| w != first) {
            unseedable.insert(rel.clone(), Ineligible::ArityClash);
        }
    }
    // A relation found to be gap-shaped or arity-clashing after some of its tuples were
    // already seeded must not keep those partial tuples.
    for rel in unseedable.keys() {
        ext.remove(rel);
    }
    (ext, unseedable)
}

/// Bind a projected atom's template values against a concrete tuple, EXTENDING
/// `bindings` IN PLACE. Every key this call inserts is pushed onto `trail`, in
/// insertion order.
///
/// THE CALLER MUST UNWIND ON EVERY PATH, INCLUDING `false`. A mismatch is detected
/// MID-SCAN, so earlier places of the same tuple may already have bound; leaving them
/// behind carries one candidate's bindings into the next, which is how this join comes
/// to derive a tuple no rule licenses — or, more quietly, to MISS one because a stale
/// binding fails an equality check the next tuple should have passed.
///
/// Binding SEQUENTIALLY, against the live map, is load-bearing and not an accident of
/// the old implementation. A template may repeat a variable: `p($x, $x)` against
/// `(a, b)` must bind `$x = a` at place 1 and then REJECT at place 2. Deciding the whole
/// template against a snapshot of the entry bindings — the obvious "test first, extend
/// only on success" shape — sees `$x` unbound twice and accepts, over-deriving. Pinned
/// by `a_repeated_variable_in_one_atom_matches_only_equal_pairs`.
///
/// A key-only trail is sufficient because a binding is only ever INSERTED, never
/// overwritten: the `Some(_)` arm below leaves the existing value alone. If an
/// overwriting arm is ever added, this trail must become
/// `Vec<(&str, Option<GroundTerm>)>` and RESTORE the previous value rather than remove
/// the key.
///
/// `trail` borrows the variable NAMES out of `template`, which lives in the `Arc`d
/// [`ProjectedRule`] for the whole walk — not out of `bindings`, whose owned `String`
/// keys the unwind frees.
#[must_use]
fn bind_tuple<'p>(
    template: &'p [GroundTerm],
    tuple: &[GroundTerm],
    bindings: &mut HashMap<String, GroundTerm>,
    trail: &mut Vec<&'p str>,
) -> bool {
    if template.len() != tuple.len() {
        return false;
    }
    for (t, v) in template.iter().zip(tuple.iter()) {
        match t {
            GroundTerm::PatternVar(n) => match bindings.get(n) {
                Some(prev) if prev != v => return false,
                Some(_) => {}
                None => {
                    bindings.insert(n.clone(), v.clone());
                    trail.push(n.as_str());
                }
            },
            other if other == v => {}
            _ => return false,
        }
    }
    true
}

/// Substitute bindings into a template value list. Returns `None` if any variable is
/// still unbound — range restriction should make that unreachable, so it is a
/// fail-closed assertion rather than an expected path.
fn ground_values(
    template: &[GroundTerm],
    bindings: &HashMap<String, GroundTerm>,
) -> Option<Vec<GroundTerm>> {
    template
        .iter()
        .map(|t| match t {
            GroundTerm::PatternVar(n) => bindings.get(n).cloned(),
            other => Some(other.clone()),
        })
        .collect()
}

/// Decide a flat built-in condition under the current bindings.
///
/// Only `equals` today. Eligibility guarantees an empty `du` union-find, so identity is
/// exactly structural equality — the same answer `check_predicate_in_kb_typed`'s
/// reflexivity arm gives, with no equivalence classes to consult.
fn builtin_holds(fact: &StoredFact, bindings: &HashMap<String, GroundTerm>) -> Option<bool> {
    let gf = fact.inner();
    if gf.relation != nibli_types::relations::IDENTITY {
        return None;
    }
    let args = ground_values(&gf.args, bindings)?;
    // A `du` atom is arity 2 in the flat shape the engine stores; anything else is not
    // the identity predicate we know how to decide.
    if args.len() != 2 {
        return None;
    }
    Some(args[0] == args[1])
}

/// Per-level join index for [`eval_rule`]'s walk: the template positions of
/// `positive[i]` that are BOUND on entry (constants, plus variables bound by an
/// earlier positive atom — statically derivable from the templates alone), and a
/// lazily built bucket map over the level's source extension keyed by the values
/// at those positions.
///
/// A pure PRE-FILTER: `bind_tuple` still re-checks every position on every
/// candidate, so the index may only skip tuples it can PROVE `bind_tuple` would
/// reject (a different value at a bound position, or an arity too short to carry
/// one) — soundness never depends on the bound-position analysis, only the
/// speedup does, and an unexpectedly unbound "bound" variable falls open to the
/// full scan. Maps are shared across levels and rules in one immutable round;
/// full and delta extensions have separate keys. Constants can index level 0
/// too: its map is shared by other rules with the same relation/key positions.
struct LevelIndex<'e> {
    bound_positions: Vec<usize>,
    map: Option<std::sync::Arc<TupleIndex<'e>>>,
}

type TupleIndex<'e> = HashMap<Vec<GroundTerm>, Vec<&'e Vec<GroundTerm>>>;
type RoundIndexes<'e> = HashMap<(String, Vec<usize>, bool), std::sync::Arc<TupleIndex<'e>>>;

fn shared_tuple_index<'e>(
    tuples: &'e HashSet<Vec<GroundTerm>>,
    relation: &str,
    positions: &[usize],
    from_delta: bool,
    indexes: &mut RoundIndexes<'e>,
) -> std::sync::Arc<TupleIndex<'e>> {
    let key = (relation.to_owned(), positions.to_vec(), from_delta);
    std::sync::Arc::clone(indexes.entry(key).or_insert_with(|| {
        let mut map: TupleIndex<'e> = HashMap::new();
        for tuple in tuples {
            // A short tuple cannot pass the ordinary binder's arity check.
            if let Some(key) = positions
                .iter()
                .map(|&p| tuple.get(p).cloned())
                .collect::<Option<Vec<_>>>()
            {
                map.entry(key).or_default().push(tuple);
            }
        }
        std::sync::Arc::new(map)
    }))
}

/// The positions of `positive[i]`'s template bound when the walk reaches level
/// `i`: constants always, and pattern variables that occur in an earlier
/// positive atom. (A variable repeated within atom `i` itself binds DURING
/// `bind_tuple`, not on entry — correctly excluded.)
fn bound_positions(positive: &[Atom]) -> Vec<Vec<usize>> {
    let mut earlier_vars: HashSet<&str> = HashSet::new();
    let mut result = Vec::with_capacity(positive.len());
    for atom in positive {
        result.push(
            atom.values
                .iter()
                .enumerate()
                .filter(|(_, v)| match v {
                    GroundTerm::PatternVar(n) => earlier_vars.contains(n.as_str()),
                    _ => true,
                })
                .map(|(position, _)| position)
                .collect(),
        );
        for v in &atom.values {
            if let GroundTerm::PatternVar(n) = v {
                earlier_vars.insert(n.as_str());
            }
        }
    }
    result
}

/// Evaluate one projected rule, appending every head tuple it derives.
///
/// `delta_pos` is the semi-naive marker: when `Some(i)`, positive atom `i` is joined
/// against `delta` (the tuples discovered in the previous round) instead of the full
/// extension, so a round only re-derives what the previous round could have enabled.
/// When `None` the rule is evaluated against the full extensions (the seeding round).
///
/// Join levels are INDEXED on their statically bound positions
/// (see [`LevelIndex`]): a transitive-closure shape that scanned O(|R|²) tuples
/// per round now touches O(|R| · fanout).
fn eval_rule<'e>(
    pr: &ProjectedRule,
    ext: &'e Extensions,
    delta: &'e Extensions,
    delta_pos: Option<usize>,
    out: &mut Vec<(String, Vec<GroundTerm>)>,
    work: &mut MaterializationWork,
    shared_indexes: &mut RoundIndexes<'e>,
) {
    // Every positive conjunct needs a tuple. In particular, a late constant
    // discriminator can reject the rule before any earlier cartesian join.
    // These are necessary conditions only: the unchanged binder still checks
    // arity, repeated variables and all cross-atom bindings for every survivor.
    // Try fixed-value discriminators first: one miss can exclude a wide rule
    // without visiting every remaining relation in its positive body.
    for (i, positions, key) in &pr.constant_probes {
        let atom = &pr.positive[*i];
        let from_delta = delta_pos == Some(*i);
        let source = if from_delta { delta } else { ext };
        work.note_positive_presence_check();
        let Some(tuples) = source
            .get(&atom.relation)
            .filter(|tuples| !tuples.is_empty())
        else {
            return;
        };
        let index = shared_tuple_index(
            tuples,
            &atom.relation,
            positions,
            from_delta,
            shared_indexes,
        );
        if !index.contains_key(key) {
            return;
        }
    }
    for (i, atom) in pr.positive.iter().enumerate() {
        let source = if delta_pos == Some(i) { delta } else { ext };
        work.note_positive_presence_check();
        if source.get(&atom.relation).is_none_or(HashSet::is_empty) {
            return;
        }
    }
    // ONE binding map for the whole walk, extended and unwound in place.
    //
    // It used to be an owned `HashMap` cloned per candidate tuple per join level, which
    // profiled as ~63% of a real workload's runtime — the deep copy, plus the malloc,
    // free and drop_glue it dragged behind it — against ~5% for the join logic itself.
    // Nothing here changes WHICH tuples are visited or in what order; only where the
    // bindings live.
    //
    // Deliberately NOT hoisted out of `eval_rule` into the fixpoint loop. `HashMap::new`
    // does not allocate, the cost this removes was per-CANDIDATE rather than per-call,
    // and a buffer reused across the rule / `delta_pos` / round loops would leak
    // bindings between rules — where a slot means a different variable — which is a far
    // worse failure than the one being fixed.
    #[allow(clippy::too_many_arguments)]
    fn walk<'p, 'e>(
        pr: &'p ProjectedRule,
        ext: &'e Extensions,
        delta: &'e Extensions,
        delta_pos: Option<usize>,
        i: usize,
        bindings: &mut HashMap<String, GroundTerm>,
        trail: &mut Vec<&'p str>,
        out: &mut Vec<(String, Vec<GroundTerm>)>,
        work: &mut MaterializationWork,
        indexes: &mut [LevelIndex<'e>],
        shared_indexes: &mut RoundIndexes<'e>,
    ) {
        if i == pr.positive.len() {
            // Built-ins first: they are the cheapest and often the most selective
            // (`~($a = $b)` cuts the diagonal out of a self-join).
            for (f, negated) in &pr.builtins {
                match builtin_holds(f, bindings) {
                    Some(holds) if holds != *negated => {}
                    // Either the built-in fails, or we could not decide it. An
                    // undecidable built-in must kill the derivation, never be assumed
                    // true: this saturation's whole value is that a MISSING tuple means
                    // "not derivable".
                    _ => return,
                }
            }
            // Negated atoms: a lookup into a strictly-lower, already-complete stratum.
            for n in &pr.negative {
                let Some(t) = ground_values(&n.values, bindings) else {
                    return;
                };
                if ext.get(&n.relation).is_some_and(|s| s.contains(&t)) {
                    return;
                }
            }
            for h in &pr.head {
                if let Some(t) = ground_values(&h.values, bindings) {
                    out.push((h.relation.clone(), t));
                }
            }
            return;
        }
        let atom = &pr.positive[i];
        let source = if delta_pos == Some(i) { delta } else { ext };
        let Some(tuples) = source.get(&atom.relation) else {
            return;
        };
        // Indexed path: a level whose template has statically
        // bound positions visits only the bucket matching the current
        // bindings' key values. `take()`/restore instead of borrowing the map
        // across the recursion — levels strictly increase, so this level's map
        // is never needed while it is out.
        if !indexes[i].bound_positions.is_empty() {
            let key: Option<Vec<GroundTerm>> = indexes[i]
                .bound_positions
                .iter()
                .map(|&p| match &atom.values[p] {
                    GroundTerm::PatternVar(n) => bindings.get(n.as_str()).cloned(),
                    constant => Some(constant.clone()),
                })
                .collect();
            if let Some(key) = key {
                if indexes[i].map.is_none() {
                    indexes[i].map = Some(shared_tuple_index(
                        tuples,
                        &atom.relation,
                        &indexes[i].bound_positions,
                        delta_pos == Some(i),
                        shared_indexes,
                    ));
                }
                let map = indexes[i].map.take().expect("index map was just built");
                if let Some(bucket) = map.get(&key) {
                    for tuple in bucket {
                        try_tuple(
                            pr,
                            ext,
                            delta,
                            delta_pos,
                            i,
                            tuple,
                            bindings,
                            trail,
                            out,
                            work,
                            indexes,
                            shared_indexes,
                        );
                    }
                }
                indexes[i].map = Some(map);
                return;
            }
            // A "bound" variable was unbound at entry — unreachable by the
            // analysis, but fail OPEN to the full scan rather than dropping
            // derivations.
        }
        for tuple in tuples {
            try_tuple(
                pr,
                ext,
                delta,
                delta_pos,
                i,
                tuple,
                bindings,
                trail,
                out,
                work,
                indexes,
                shared_indexes,
            );
        }
    }

    /// One candidate tuple at level `i` — bind, recurse, unwind. INVARIANT:
    /// exactly ONE unwind site, and no `return`, `?`, `break` or `continue`
    /// may sit between the `bind_tuple` call and it. The frame's bindings must
    /// be identical on exit — which the old owned-map version gave for free,
    /// and which this has to maintain.
    #[allow(clippy::too_many_arguments)]
    fn try_tuple<'p, 'e>(
        pr: &'p ProjectedRule,
        ext: &'e Extensions,
        delta: &'e Extensions,
        delta_pos: Option<usize>,
        i: usize,
        tuple: &[GroundTerm],
        bindings: &mut HashMap<String, GroundTerm>,
        trail: &mut Vec<&'p str>,
        out: &mut Vec<(String, Vec<GroundTerm>)>,
        work: &mut MaterializationWork,
        indexes: &mut [LevelIndex<'e>],
        shared_indexes: &mut RoundIndexes<'e>,
    ) {
        let atom = &pr.positive[i];
        work.note_tuple_bind_attempt(pr);

        #[cfg(debug_assertions)]
        let before = bindings.clone();

        let mark = trail.len();
        if bind_tuple(&atom.values, tuple, bindings, trail) {
            walk(
                pr,
                ext,
                delta,
                delta_pos,
                i + 1,
                bindings,
                trail,
                out,
                work,
                indexes,
                shared_indexes,
            );
        }
        // UNCONDITIONAL, and outside the `if` on purpose: `bind_tuple` binds as it
        // scans and can reject at any place, so the `false` path has bindings to undo
        // too. Never write this as an `else`.
        for n in trail.drain(mark..) {
            bindings.remove(n);
        }

        #[cfg(debug_assertions)]
        debug_assert_eq!(
            *bindings, before,
            "the undo trail left frame {i} of rule '{}' altered",
            pr.label
        );
    }
    let mut bindings: HashMap<String, GroundTerm> = HashMap::new();
    let mut trail: Vec<&str> = Vec::new();
    let mut indexes: Vec<LevelIndex> = pr
        .bound_positions
        .iter()
        .map(|positions| LevelIndex {
            bound_positions: positions.clone(),
            map: None,
        })
        .collect();
    walk(
        pr,
        ext,
        delta,
        delta_pos,
        0,
        &mut bindings,
        &mut trail,
        out,
        work,
        &mut indexes,
        shared_indexes,
    );
    debug_assert!(
        bindings.is_empty() && trail.is_empty(),
        "every binding must be unwound by the time the walk returns"
    );
}

/// Saturate `targets` and everything they depend on, stratum by stratum.
///
/// This is the whole point of the module: when it returns, every relation in
/// `complete` has its FULL extension in `ext`, so `~p(x)` is answered by asking whether
/// a tuple is in a set — no proof attempt, no depth bound, no domain cartesian.
/// One stratum's semi-naive fixpoint, shared by the full [`saturate`] and the
/// incremental [`resume_with_delta`].
///
/// `initial_delta` EMPTY means "compute this stratum from scratch": round 0
/// evaluates every rule against the full extensions (which already hold the EDB
/// seed plus every completed lower stratum), and later rounds join each rule once
/// per positive position against the previous round's delta, so a tuple
/// combination is only revisited when one of its inputs is new.
///
/// A NON-EMPTY `initial_delta` means "this stratum's inputs just grew by exactly
/// these tuples": the round-0 full evaluation — the expensive part, and the whole
/// reason a recompute costs what it does — is SKIPPED, and the loop starts at the
/// delta rounds. That is sound only for monotone growth, which is why the caller
/// must have excluded every relation read under negation before getting here.
///
/// Returns everything newly derived (so a caller can carry it to higher strata),
/// or `None` if the tuple budget was exhausted.
fn semi_naive_stratum(
    stratum_rules: &[&std::sync::Arc<ProjectedRule>],
    ext: &mut Extensions,
    initial_delta: Extensions,
    budget: &mut usize,
    work: &mut MaterializationWork,
) -> Option<Extensions> {
    let resuming = initial_delta.values().any(|s| !s.is_empty());
    let mut delta = initial_delta;
    let mut round = if resuming { 1usize } else { 0 };
    let mut all_derived: Extensions = Extensions::new();
    loop {
        let mut produced: Vec<(String, Vec<GroundTerm>)> = Vec::new();
        // These maps borrow exactly this round's immutable full/delta tuples.
        // Drop them before installing newly produced tuples below.
        let mut shared_indexes = RoundIndexes::new();
        for pr in stratum_rules {
            if round == 0 {
                eval_rule(
                    pr,
                    ext,
                    &delta,
                    None,
                    &mut produced,
                    work,
                    &mut shared_indexes,
                );
            } else {
                for pos in 0..pr.positive.len() {
                    // Skip positions whose relation gained nothing last round —
                    // the join would be over an empty delta.
                    if delta
                        .get(&pr.positive[pos].relation)
                        .is_none_or(HashSet::is_empty)
                    {
                        continue;
                    }
                    eval_rule(
                        pr,
                        ext,
                        &delta,
                        Some(pos),
                        &mut produced,
                        work,
                        &mut shared_indexes,
                    );
                }
            }
        }
        drop(shared_indexes);
        let mut next: Extensions = Extensions::new();
        let mut overflowed = false;
        for (rel, tuple) in produced {
            if ext.get(&rel).is_some_and(|s| s.contains(&tuple)) {
                continue;
            }
            if *budget == 0 {
                overflowed = true;
                break;
            }
            if next.entry(rel).or_default().insert(tuple) {
                *budget -= 1;
            }
        }
        if overflowed {
            return None;
        }
        let grew = next.values().any(|s| !s.is_empty());
        for (rel, set) in &next {
            ext.entry(rel.clone())
                .or_default()
                .extend(set.iter().cloned());
            all_derived
                .entry(rel.clone())
                .or_default()
                .extend(set.iter().cloned());
        }
        delta = next;
        if !grew {
            return Some(all_derived);
        }
        round += 1;
    }
}

/// INCREMENTAL RE-SATURATION: fold the stored tuples that arrived since this
/// saturation was built into it, instead of recomputing the whole fixpoint.
///
/// Returns `false` when anything at all looks unlike plain monotone growth, and
/// the caller then drops the cache and recomputes — every refusal below is a
/// fall-back to today's behaviour, never a weakened claim:
///
/// * a `du` equivalence exists (the global equality guard),
/// * the delta can REACH a relation read under NEGATION anywhere in the program.
///   Growth through a negated condition SHRINKS the model, so it is not monotone
///   — and reachability is the load-bearing word: it is not enough to check the
///   delta's own relations. `judge` inserted under
///   `judge -> clean` / `person & ~clean -> free` is not itself negatively read,
///   but one derivation step later `clean` is, and `free` must then LOSE a tuple
///   that a monotone fold can only keep. So the refusal closes forward over the
///   rules from the delta and refuses if that closure touches `negatively_read`,
/// * a relation this saturation completed can no longer be seeded (a `past`
///   fact, a role gap, an arity clash arrived with the delta),
/// * a delta tuple's arity disagrees with the projected arity, or
/// * the fixpoint exhausts its tuple budget.
///
/// In debug builds the result is verified against a full recompute — see the
/// `debug_assert` at the end, which makes every test in the suite a check of
/// this function.
fn resume_with_delta(
    inner: &KnowledgeBaseInner,
    elig: &Eligibility,
    strata: &Strata,
    m: &mut Materialized,
) -> bool {
    if !inner.equivalence_parent.is_empty() {
        return false;
    }
    // Re-seed from the store. This is O(store) and cheap next to the fixpoint —
    // which is the part being skipped.
    let (seed, unseedable) = seed_edb(inner);
    for rel in &m.complete {
        if unseedable.contains_key(rel) {
            return false;
        }
    }

    // The delta: stored tuples this saturation has never seen.
    let mut delta: Extensions = Extensions::new();
    for (rel, tuples) in &seed {
        if !m.cone.contains(rel) {
            continue;
        }
        for tuple in tuples {
            if m.ext.get(rel).is_some_and(|s| s.contains(tuple)) {
                continue;
            }
            if m.arity.get(rel).is_some_and(|a| *a != tuple.len()) {
                return false;
            }
            delta.entry(rel.clone()).or_default().insert(tuple.clone());
        }
    }
    if delta.values().all(HashSet::is_empty) {
        // Nothing actually new (a duplicate assertion, or a fact the rules had
        // already derived): the extensions stand as they are.
        m.grew.clear();
        m.work.note_resume();
        return true;
    }

    // NON-MONOTONE REACHABILITY. A fold may only ADD tuples, so it is sound only
    // while nothing the delta can reach is read under `~`. Close forward over the
    // rules — `dep -> heads that read dep` — starting from the delta's own
    // relations, and refuse if that closure meets `negatively_read`. Checking only
    // the delta relations (which is what this did until 2026-08-17) catches the
    // one-hop case and misses every longer one: a delta that is not itself negated
    // can still grow a relation that is, one derivation step later, and the rule
    // reading `~` of it must then LOSE a conclusion the fold would keep.
    if !m.negatively_read.is_empty() {
        let mut readers: HashMap<&str, Vec<&str>> = HashMap::new();
        for (head, dependencies) in &elig.dependencies {
            for dep in dependencies {
                readers.entry(dep.as_str()).or_default().push(head.as_str());
            }
        }
        let mut seen: HashSet<&str> = HashSet::new();
        let mut stack: Vec<&str> = delta.keys().map(String::as_str).collect();
        while let Some(rel) = stack.pop() {
            if !seen.insert(rel) {
                continue;
            }
            if m.negatively_read.contains(rel) {
                return false;
            }
            for next in readers.get(rel).into_iter().flatten() {
                stack.push(next);
            }
        }
    }

    for (rel, tuples) in &delta {
        m.ext
            .entry(rel.clone())
            .or_default()
            .extend(tuples.iter().cloned());
    }

    // Walk the strata that can see the delta, carrying each level's derivations
    // upward. Levels below the lowest changed one cannot be affected: their rules
    // read only strictly lower strata, which did not move.
    let lowest = delta
        .keys()
        .map(|rel| strata.get(rel).copied().unwrap_or(0))
        .min()
        .unwrap_or(0);
    let mut by_stratum: Vec<(usize, &String)> = m
        .complete
        .iter()
        .map(|rel| (strata.get(rel).copied().unwrap_or(0), rel))
        .filter(|(level, _)| *level >= lowest)
        .collect();
    by_stratum.sort();

    let mut budget = MAX_MATERIALIZED_TUPLES;
    let mut carried = delta;
    let mut idx = 0usize;
    while idx < by_stratum.len() {
        let level = by_stratum[idx].0;
        let mut rels: Vec<&String> = Vec::new();
        while idx < by_stratum.len() && by_stratum[idx].0 == level {
            rels.push(by_stratum[idx].1);
            idx += 1;
        }
        let mut stratum_rules: Vec<&std::sync::Arc<ProjectedRule>> = Vec::new();
        let mut seen: HashSet<*const ProjectedRule> = HashSet::new();
        for rel in &rels {
            for pr in elig.rules.get(*rel).into_iter().flatten() {
                if seen.insert(std::sync::Arc::as_ptr(pr)) {
                    stratum_rules.push(pr);
                }
            }
        }
        if stratum_rules.is_empty() {
            continue;
        }
        let Some(derived) = semi_naive_stratum(
            &stratum_rules,
            &mut m.ext,
            carried.clone(),
            &mut budget,
            &mut m.work,
        ) else {
            return false;
        };
        for (rel, tuples) in derived {
            carried.entry(rel).or_default().extend(tuples);
        }
    }
    m.grew.clear();
    m.work.note_resume();

    // The metamorphic property this whole function must satisfy, checked on every
    // debug-build query: resuming from a delta agrees with recomputing from
    // scratch. Cheap to state, and it turns the entire test suite — plus the
    // interleaved ON/OFF differential — into a gate on the incremental path.
    #[cfg(debug_assertions)]
    {
        let fresh = saturate(inner, elig, strata, &m.requested);
        debug_assert_eq!(
            m.complete, fresh.complete,
            "resumed completeness disagrees with a full recompute"
        );
        for rel in &fresh.complete {
            debug_assert_eq!(
                m.ext.get(rel),
                fresh.ext.get(rel),
                "resumed extension for '{rel}' disagrees with a full recompute"
            );
        }
    }
    true
}

pub(super) fn saturate(
    inner: &KnowledgeBaseInner,
    elig: &Eligibility,
    strata: &Strata,
    targets: &HashSet<String>,
) -> Materialized {
    // EQUALITY GUARD — repeated here, not only in `eligible_relations`.
    //
    // `eligible_relations` refuses every RULE-derived relation when a `du` union-find
    // exists, but that is not enough on its own: the loop below also marks a rule-less
    // EDB relation complete straight from its seed, and a seed is a set of stored tuples
    // with no equivalence expansion. With `Ara = Bel` and a stored `rotten(Bel)`, the
    // seed for `rotten` omits `rotten(Ara)` — so `~rotten(Ara)` would look like "no
    // witness" and answer TRUE where backward chaining, which expands equivalence
    // variants in `typed_fact_is_stored`, correctly answers FALSE. That is a WRONG
    // definitive verdict, the exact failure this module must never produce.
    //
    // (Caught by `equality_classes_refuse_the_whole_kb`, which is why that test asserts
    // on the verdicts and not merely on the report.)
    if !inner.equivalence_parent.is_empty() {
        let mut refused = elig.refused.clone();
        for rel in targets {
            refused.entry(rel.clone()).or_insert(Ineligible::Equality);
        }
        return Materialized {
            ext: Extensions::new(),
            complete: HashSet::new(),
            refused,
            arity: HashMap::new(),
            requested: targets.clone(),
            // The equality guard saturates nothing, so no insert is ever
            // irrelevant to it — an empty cone keeps every insert invalidating.
            cone: HashSet::new(),
            negatively_read: HashSet::new(),
            grew: HashSet::new(),
            work: MaterializationWork::default(),
        };
    }

    let (mut ext, unseedable) = seed_edb(inner);
    let mut refused = elig.refused.clone();
    for (rel, why) in &unseedable {
        refused.entry(rel.clone()).or_insert_with(|| why.clone());
    }

    // Dependency closure of the targets over eligible relations. A target that is not
    // eligible simply never enters, and its NAF keeps today's behaviour.
    let mut wanted: HashSet<String> = HashSet::new();
    let mut stack: Vec<String> = targets.iter().cloned().collect();
    stack.sort();
    while let Some(rel) = stack.pop() {
        if unseedable.contains_key(&rel) || !wanted.insert(rel.clone()) {
            continue;
        }
        for dep in elig.dependencies.get(&rel).into_iter().flatten() {
            stack.push(dep.clone());
        }
    }
    // Only relations we are actually allowed to saturate.
    let saturable: HashSet<&String> = wanted
        .iter()
        .filter(|r| elig.eligible.contains(*r))
        .collect();

    // Ascending stratum order. A relation with no rules is EDB: already seeded, so it
    // is complete the moment we know nothing can derive more of it.
    let mut by_stratum: Vec<(usize, String)> = wanted
        .iter()
        .map(|r| (strata.get(r).copied().unwrap_or(0), r.clone()))
        .collect();
    by_stratum.sort();

    let mut complete: HashSet<String> = HashSet::new();
    let mut budget = MAX_MATERIALIZED_TUPLES;
    let mut work = MaterializationWork::default();
    let mut idx = 0usize;
    while idx < by_stratum.len() {
        let level = by_stratum[idx].0;
        let mut rels: Vec<&String> = Vec::new();
        while idx < by_stratum.len() && by_stratum[idx].0 == level {
            rels.push(&by_stratum[idx].1);
            idx += 1;
        }

        // Every rule concluding a relation in this stratum, once.
        // Pass 1 — EDB. A relation nothing can derive is complete the moment its seed is
        // in, and it must be settled BEFORE the dependency check below, because a derived
        // relation in this same stratum may read it.
        for rel in &rels {
            if unseedable.contains_key(*rel) || saturable.contains(*rel) {
                continue;
            }
            if !elig.rules.contains_key(*rel) && !refused.contains_key(*rel) {
                complete.insert((*rel).clone());
            }
        }

        // Pass 2 — the derived relations of this stratum.
        let mut derived_here: Vec<&String> = rels
            .iter()
            .filter(|rel| !unseedable.contains_key(**rel) && saturable.contains(**rel))
            .copied()
            .collect();

        // Pass 3 — DEPENDENCY CHECK, and the reason this loop is three passes.
        //
        // `eligible_relations` closed downward over relations it could not PROJECT, but a
        // relation can also become unusable later, when `seed_edb` refuses its stored
        // facts (a `past` fact, a role gap, an arity clash). Those refusals are invisible
        // to the eligibility analysis, so without this pass a rule reading `~rotten` would
        // still be saturated while `rotten`'s extension was ABSENT — and an absent
        // extension reads as "nothing derived", so the negated condition passes and the
        // head is derived for everyone. That is a definitive wrong TRUE, and it is exactly
        // what the ON/OFF differential caught on `mat_seed4` / `mat_seed35`.
        //
        // A dependency is acceptable if it is already complete (a lower stratum, or the
        // EDB pass above) or is being computed alongside us in this stratum's fixpoint.
        // Shrinking to a fixpoint: dropping one relation can invalidate another.
        loop {
            let mut drop_idx: Option<(usize, String)> = None;
            'scan: for (i, rel) in derived_here.iter().enumerate() {
                for dep in elig.dependencies.get(*rel).into_iter().flatten() {
                    if complete.contains(dep) || derived_here.contains(&dep) {
                        continue;
                    }
                    drop_idx = Some((i, dep.clone()));
                    break 'scan;
                }
            }
            match drop_idx {
                Some((i, dep)) => {
                    let rel = derived_here.remove(i);
                    refused
                        .entry(rel.clone())
                        .or_insert(Ineligible::DependsOn(dep));
                }
                None => break,
            }
        }

        let mut stratum_rules: Vec<&std::sync::Arc<ProjectedRule>> = Vec::new();
        let mut seen: HashSet<*const ProjectedRule> = HashSet::new();
        for rel in &derived_here {
            for pr in elig.rules.get(*rel).into_iter().flatten() {
                if seen.insert(std::sync::Arc::as_ptr(pr)) {
                    stratum_rules.push(pr);
                }
            }
        }
        if derived_here.is_empty() {
            continue;
        }

        // Semi-naive fixpoint for this stratum, seeded with an EMPTY delta so it
        // opens with the full round-0 evaluation (see `semi_naive_stratum`).
        let derived = semi_naive_stratum(
            &stratum_rules,
            &mut ext,
            Extensions::new(),
            &mut budget,
            &mut work,
        );
        let overflowed = derived.is_none();

        if overflowed {
            // Stop-loss. Leave this stratum's relations INCOMPLETE — and every later
            // stratum too, since their negated lookups would read a partial extension.
            for rel in derived_here {
                refused
                    .entry(rel.clone())
                    .or_insert_with(|| Ineligible::DependsOn("the materialisation budget".into()));
            }
            break;
        }
        for rel in derived_here {
            complete.insert(rel.clone());
        }
    }

    // Anything wanted but never completed is reported, so `materialization_report` can
    // say why a query is still paying for a proof search.
    for rel in &wanted {
        if !complete.contains(rel) {
            refused
                .entry(rel.clone())
                .or_insert_with(|| Ineligible::DependsOn("an unsaturated dependency".into()));
        }
    }

    // One projected arity per relation, taken from its saturated tuples.
    //
    // Recorded ONLY when tuples exist and agree on a width. An EMPTY extension records
    // nothing, and that is deliberate rather than a gap: "nothing derived" is the answer
    // at every width, and it is also the most important case the optimisation has —
    // `~false($t)` when nobody has been voided is exactly an empty extension, and it must
    // answer TRUE, not fall back. A DISAGREEING width records nothing either, and the
    // relation loses its `complete` status below: there is no single surface arity to
    // probe against, so a probe of one width would silently miss the other's tuples.
    let mut arity: HashMap<String, usize> = HashMap::new();
    let mut clashing: HashSet<String> = HashSet::new();
    for (rel, tuples) in &ext {
        let mut widths = tuples.iter().map(Vec::len);
        let Some(first) = widths.next() else { continue };
        if widths.all(|w| w == first) {
            arity.insert(rel.clone(), first);
        } else {
            clashing.insert(rel.clone());
        }
    }
    let complete: HashSet<String> = complete
        .into_iter()
        .filter(|rel| !clashing.contains(rel))
        .collect();
    for rel in &clashing {
        refused
            .entry(rel.clone())
            .or_insert_with(|| Ineligible::Flavoured(format!("mixed arities for '{rel}'")));
    }

    // Every relation any eligible rule reads under `~`. An insert into one of
    // these is NOT monotone growth, so `resume_with_delta` must refuse it.
    let negatively_read = elig.negatively_read.clone();

    Materialized {
        ext,
        complete,
        refused,
        arity,
        requested: targets.clone(),
        // `wanted` IS the dependency closure (positive and negated deps both
        // pushed above), which is exactly what an insert has to fall outside of
        // to be irrelevant to these extensions.
        cone: wanted,
        negatively_read,
        grew: HashSet::new(),
        work,
    }
}

/// Every surface relation occurring under a `NotNode` in a compiled buffer — the
/// query-side half of the materialisation target set.
///
/// Deliberately over-approximating: it collects every predicate reachable from any
/// negation, not just the immediate ones. Naming a relation that turns out not to need
/// saturating costs a little work; MISSING one only costs the optimisation, and neither
/// can change a verdict. The memo is keyed on `(node, polarity)` — a compiled buffer
/// is a DAG (`<->`/`xor` share subtrees between both polarities), so a node first
/// reached positively must still be re-walked when a negation reaches it later.
pub(super) fn collect_negated_relations(
    buffer: &nibli_types::logic::LogicBuffer,
    out: &mut HashSet<String>,
) {
    use nibli_types::logic::LogicNode;
    fn walk(
        buffer: &nibli_types::logic::LogicBuffer,
        id: u32,
        under_not: bool,
        out: &mut HashSet<String>,
        seen: &mut HashSet<(u32, bool)>,
    ) {
        if !seen.insert((id, under_not)) {
            return;
        }
        let Some(node) = buffer.nodes.get(id as usize) else {
            return;
        };
        match node {
            LogicNode::Predicate((rel, _)) | LogicNode::ComputeNode((rel, _)) => {
                if under_not {
                    out.insert(surface_relation(rel).to_string());
                }
            }
            LogicNode::NotNode(inner) => walk(buffer, *inner, true, out, seen),
            LogicNode::AndNode((l, r)) => {
                walk(buffer, *l, under_not, out, seen);
                if !is_abstraction_marker(buffer, *l) {
                    walk(buffer, *r, under_not, out, seen);
                }
            }
            LogicNode::OrNode((l, r)) => {
                walk(buffer, *l, under_not, out, seen);
                walk(buffer, *r, under_not, out, seen);
            }
            LogicNode::ExistsNode((_, body))
            | LogicNode::ForAllNode((_, body))
            | LogicNode::CountNode((_, _, body)) => walk(buffer, *body, under_not, out, seen),
            LogicNode::PastNode(b)
            | LogicNode::PresentNode(b)
            | LogicNode::FutureNode(b)
            | LogicNode::ObligatoryNode(b)
            | LogicNode::PermittedNode(b) => walk(buffer, *b, under_not, out, seen),
        }
    }
    for &root in &buffer.roots {
        // A fresh `seen` per root: sub-buffers share one node arena
        // (`LogicBuffer::split_roots`), so a node reachable from two roots under
        // different polarity must be visited for each.
        walk(buffer, root, false, out, &mut HashSet::new());
    }
}

/// Every surface relation reachable from a compiled buffer's query roots — the target
/// set for the POSITIVE fast path.
///
/// Unlike [`collect_negated_relations`] this ignores polarity: a positive query over a
/// saturable relation should hit the lookup too, and a relation named here that turns out
/// not to be saturable is simply dropped by the eligibility filter. Traversing from roots
/// is load-bearing: split buffers share an arena with unreachable sibling statements, and
/// opaque abstraction content is encoded into a marker rather than evaluated as actuality.
pub(super) fn collect_query_relations(
    buffer: &nibli_types::logic::LogicBuffer,
    out: &mut HashSet<String>,
) {
    use nibli_types::logic::LogicNode;

    fn walk(
        buffer: &nibli_types::logic::LogicBuffer,
        id: u32,
        out: &mut HashSet<String>,
        seen: &mut HashSet<u32>,
    ) {
        if !seen.insert(id) {
            return;
        }
        let Some(node) = buffer.nodes.get(id as usize) else {
            return;
        };
        match node {
            LogicNode::Predicate((rel, _)) => {
                out.insert(surface_relation(rel).to_string());
            }
            LogicNode::ComputeNode(_) => {}
            LogicNode::AndNode((left, right)) => {
                walk(buffer, *left, out, seen);
                if !is_abstraction_marker(buffer, *left) {
                    walk(buffer, *right, out, seen);
                }
            }
            LogicNode::OrNode((left, right)) => {
                walk(buffer, *left, out, seen);
                walk(buffer, *right, out, seen);
            }
            LogicNode::NotNode(inner)
            | LogicNode::ExistsNode((_, inner))
            | LogicNode::ForAllNode((_, inner))
            | LogicNode::CountNode((_, _, inner))
            | LogicNode::PastNode(inner)
            | LogicNode::PresentNode(inner)
            | LogicNode::FutureNode(inner)
            | LogicNode::ObligatoryNode(inner)
            | LogicNode::PermittedNode(inner) => walk(buffer, *inner, out, seen),
        }
    }

    for &root in &buffer.roots {
        walk(buffer, root, out, &mut HashSet::new());
    }
}

/// Whether any relation reachable from this query's positive roots reads a negative
/// dependency. Such cones are materialised before backward chaining because NAF needs a
/// complete extension and is the workload the fast path exists to accelerate. Purely
/// positive cones stay lazy until the ordinary proof path cannot decide the query.
pub(super) fn query_cone_has_negative_dependency(
    buffer: &nibli_types::logic::LogicBuffer,
    graph: &HashMap<String, Vec<(String, bool)>>,
) -> bool {
    let mut pending = HashSet::new();
    collect_query_relations(buffer, &mut pending);
    let mut seen = HashSet::new();
    while let Some(relation) = pending.iter().next().cloned() {
        pending.remove(&relation);
        if !seen.insert(relation.clone()) {
            continue;
        }
        let Some(dependencies) = graph.get(&relation) else {
            continue;
        };
        for (dependency, negative) in dependencies {
            if *negative {
                return true;
            }
            if !seen.contains(dependency) {
                pending.insert(dependency.clone());
            }
        }
    }
    false
}

/// Extend the cumulative materialisation cache with these surface-relation roots.
///
/// This is shared by top-level query planning and the backward-chainer's lazy
/// positive-subgoal fallback. The cache represents the union of every requested
/// root until KB mutation; adding one root recomputes that union rather than
/// replacing earlier completed extensions.
pub(super) fn ensure_materialized_targets(
    inner: &KnowledgeBaseInner,
    targets: &HashSet<String>,
) -> bool {
    if !inner.materialization {
        return false;
    }

    // Fold any pending in-cone growth in FIRST, before anything reads these
    // extensions — including the `targets.is_subset` fast path below, which
    // would otherwise serve a cache that is missing the newest tuples. A resume
    // that refuses drops the cache, and the recompute below rebuilds it.
    let dirty = inner
        .materialized
        .borrow()
        .as_ref()
        .is_some_and(|m| !m.grew.is_empty());
    if dirty {
        let plan = materialization_plan(inner);
        // Taken OUT for the duration: `resume_with_delta`'s debug verification
        // recomputes through `saturate`, and nothing may read a half-folded cache.
        let mut taken = inner.materialized.borrow_mut().take();
        let resumed = taken
            .as_mut()
            .is_some_and(|m| resume_with_delta(inner, &plan.eligibility, &plan.strata, m));
        if resumed {
            *inner.materialized.borrow_mut() = taken;
        }
    }

    if targets.is_empty() {
        if inner.materialized.borrow().is_none() {
            *inner.materialized.borrow_mut() = Some(Materialized::empty());
        }
        return false;
    }

    // Re-read AFTER the resume attempt: a refused resume left `None` here, and
    // must fall through to the recompute rather than report a cache hit.
    let previous_targets = inner
        .materialized
        .borrow()
        .as_ref()
        .map(|materialized| materialized.requested.clone())
        .unwrap_or_default();
    if let Some(materialized) = inner.materialized.borrow_mut().as_mut() {
        if targets.is_subset(&previous_targets) {
            return false;
        }
        // A root already completed as a dependency needs no second saturation.
        // Retain it in the requested union for later mutation/recompute paths.
        // Refused or unfinished dependencies never satisfy this shortcut.
        if targets.is_subset(&materialized.complete) {
            materialized.requested.extend(targets.iter().cloned());
            return false;
        }
    }

    let mut cumulative = targets.clone();
    cumulative.extend(previous_targets);
    let plan = materialization_plan(inner);
    let materialized = saturate(inner, &plan.eligibility, &plan.strata, &cumulative);
    *inner.materialized.borrow_mut() = Some(materialized);
    true
}

/// Project a `~P` group under a rule's current bindings into a ground surface tuple —
/// the probe [`crate::reasoning::eval_negated_exists_group`] uses to replace its
/// candidate sweep with a set membership test.
///
/// Returns `None` whenever the shortcut does not apply (unprojectable group, a value
/// still unbound, a flavour), and the caller then takes the ordinary search path. Never
/// guesses.
pub(super) fn probe_negated_group(
    group: &NegatedExistsGroup,
    bindings: &HashMap<String, GroundTerm>,
) -> Option<(String, Vec<GroundTerm>)> {
    let atom = project_negated_group(group).ok()?;
    let tuple = ground_values(&atom.values, bindings)?;
    if tuple.iter().any(|t| matches!(t, GroundTerm::PatternVar(_))) {
        return None;
    }
    Some((atom.relation, tuple))
}

/// Exact candidate restriction for a single-variable witness rule whose whole
/// positive body is one completed unary relation. This is only a filter: the
/// ordinary witness evaluator must still bind and prove every retained case.
pub(super) fn complete_unary_condition_members(
    inner: &KnowledgeBaseInner,
    rule: &crate::kb::UniversalRuleRecord,
    variable: &str,
) -> Option<HashSet<GroundTerm>> {
    if !inner.materialization
        || !inner.positive_lookup.get()
        || !rule.negated_condition_indices.is_empty()
        || !rule.negated_exists_groups.is_empty()
    {
        return None;
    }
    let (projected, flat) = project_atoms(&rule.typed_conditions).ok()?;
    if projected.len() != 1 || !flat.is_empty() {
        return None;
    }
    let atom = &projected[0];
    if atom.values != [GroundTerm::PatternVar(variable.to_owned())] {
        return None;
    }
    let materialized = inner.materialized.borrow();
    let complete = materialized.as_ref()?;
    if !complete.grew.is_empty() || !complete.is_complete_for(&atom.relation, 1) {
        return None;
    }
    Some(
        complete
            .ext
            .get(&atom.relation)
            .into_iter()
            .flatten()
            .map(|tuple| tuple[0].clone())
            .collect(),
    )
}

/// Project one rule's complete positive antecedent into a ground surface tuple.
/// Returns `None` for multiple surface atoms, flat/equality conditions, flavours,
/// negation (screened by the caller), or any surviving unbound value. A successful
/// projection is exact, so a complete materialised extension can replace the
/// event-witness search without weakening the rule.
pub(super) fn probe_positive_rule_conditions(
    conditions: &[StoredFact],
    bindings: &HashMap<String, GroundTerm>,
) -> Option<(String, Vec<GroundTerm>)> {
    let (mut projected, flat) = project_atoms(conditions).ok()?;
    if projected.len() != 1 || !flat.is_empty() {
        return None;
    }
    let atom = projected.remove(0);
    let tuple = ground_values(&atom.values, bindings)?;
    if tuple
        .iter()
        .any(|term| matches!(term, GroundTerm::PatternVar(_)))
    {
        return None;
    }
    Some((atom.relation, tuple))
}

/// Project a POSITIVE `∃ev. rel(ev) ∧ rel_x1(ev,a) ∧ …` buffer subtree into a ground
/// surface tuple — the probe `check_formula_holds_core`'s `ExistsNode` arm uses to answer
/// from a complete extension instead of sweeping candidates.
///
/// The negated twin ([`probe_negated_group`]) starts from a rule's already-compiled
/// `NegatedExistsGroup`; this one starts from raw buffer nodes, so it must do its own
/// flattening — and that flattening has to REFUSE, not drop.
///
/// # Why the obvious helper is wrong
///
/// `rules::collect_ground_facts` has exactly this signature shape and looks reusable. It
/// is not. It is the ASSERT-path walker: an `Or`/`Not` conjunct silently contributes
/// nothing (its `build_stored_fact_from_node` returns `None`), and an `∃` whose variable
/// is unbound vanishes. Dropping a conjunct WEAKENS the goal, so the projected tuple is
/// more general than the query was — and a hit then answers TRUE for something the full
/// conjunction makes FALSE. That is fail-OPEN, the one direction this module exists to
/// prevent. Hence the explicit `_ => return None` below, modelled on
/// `compute::try_evaluate_numeric_group`'s flattener.
pub(super) fn probe_positive_group(
    buffer: &nibli_types::logic::LogicBuffer,
    body_id: u32,
    exists_var: &str,
    subs: &HashMap<String, GroundTerm>,
) -> Option<(String, Vec<GroundTerm>)> {
    use nibli_types::logic::LogicNode;

    // Flatten the And-tree, REFUSING anything that is not And/Predicate. A `ComputeNode`
    // is refused too: its relation is never saturated (`Ineligible::ComputeCondition`), so
    // admitting it could only produce a tuple for a relation with no complete extension.
    let mut conjuncts: Vec<u32> = Vec::new();
    let mut stack = vec![body_id];
    while let Some(id) = stack.pop() {
        match buffer.nodes.get(id as usize)? {
            LogicNode::AndNode((l, r)) => {
                stack.push(*l);
                stack.push(*r);
            }
            LogicNode::Predicate(_) => conjuncts.push(id),
            _ => return None,
        }
    }
    if conjuncts.is_empty() {
        return None;
    }

    // The event variable must NOT already be bound: this arm is the existential probe, and
    // a bound `ev` means the caller is asking about one specific event, which the
    // projection cannot answer (it eliminated event identity).
    if subs.contains_key(exists_var) {
        return None;
    }

    // Build one `StoredFact` per conjunct with the event variable left as a PatternVar, so
    // `project_atoms` can bucket by it exactly as it does for a rule template.
    let mut ev_subs = subs.clone();
    ev_subs.insert(
        exists_var.to_string(),
        GroundTerm::PatternVar(exists_var.to_string()),
    );
    let mut atoms: Vec<StoredFact> = Vec::with_capacity(conjuncts.len());
    for id in conjuncts {
        atoms.push(crate::rules::build_stored_fact_from_node(
            buffer, id, &ev_subs, None,
        )?);
    }

    // One event group, nothing left flat — the same acceptance `project_negated_group`
    // demands. Anything else (two groups, a stray `equals`) is not a single relation's
    // extension and must fall through to the ordinary search.
    let (mut projected, flat) = project_atoms(&atoms).ok()?;
    if projected.len() != 1 || !flat.is_empty() {
        return None;
    }
    let atom = projected.remove(0);
    let tuple = ground_values(&atom.values, subs)?;
    if tuple.iter().any(|t| matches!(t, GroundTerm::PatternVar(_))) {
        return None;
    }
    Some((atom.relation, tuple))
}

#[cfg(test)]
mod strata_tests {
    use super::*;

    fn g(edges: &[(&str, &str, bool)]) -> HashMap<String, Vec<(String, bool)>> {
        let mut m: HashMap<String, Vec<(String, bool)>> = HashMap::new();
        for (h, d, n) in edges {
            m.entry(h.to_string())
                .or_default()
                .push((d.to_string(), *n));
        }
        m
    }

    #[test]
    fn edb_only_graph_is_all_stratum_zero() {
        let s = compute_strata(&g(&[("b", "a", false), ("c", "b", false)]));
        assert_eq!(s.get("a"), Some(&0));
        assert_eq!(s.get("b"), Some(&0));
        assert_eq!(s.get("c"), Some(&0));
    }

    #[test]
    fn a_negative_edge_raises_the_reader_one_stratum() {
        // reward ⟵ ~false : `false` must be complete before `reward` is evaluated.
        let s = compute_strata(&g(&[
            ("reward", "false", true),
            ("false", "capture", false),
        ]));
        assert_eq!(s.get("capture"), Some(&0));
        assert_eq!(s.get("false"), Some(&0));
        assert_eq!(s.get("reward"), Some(&1));
    }

    #[test]
    fn negative_edges_stack_along_a_chain() {
        let s = compute_strata(&g(&[("c", "b", true), ("b", "a", true)]));
        assert_eq!(s.get("a"), Some(&0));
        assert_eq!(s.get("b"), Some(&1));
        assert_eq!(s.get("c"), Some(&2));
    }

    #[test]
    fn the_longest_negative_path_wins_not_the_first_found() {
        // d reads c (positive) and a (negative); c reads b (negative) reads a (negative).
        // The long way round is 2 negative hops, so d must sit at stratum 2, not 1.
        let s = compute_strata(&g(&[
            ("d", "c", false),
            ("d", "a", true),
            ("c", "b", true),
            ("b", "a", true),
        ]));
        assert_eq!(s.get("a"), Some(&0));
        assert_eq!(s.get("d"), Some(&2));
    }

    #[test]
    fn a_positive_cycle_shares_one_stratum() {
        // Mutual positive recursion is ONE evaluation block, not a chain.
        let s = compute_strata(&g(&[
            ("p", "q", false),
            ("q", "p", false),
            ("r", "p", true),
        ]));
        assert_eq!(s.get("p"), s.get("q"));
        assert_eq!(s.get("r"), Some(&(s["p"] + 1)));
    }

    /// A leaf predicate is an edge TARGET but never a graph key. `compute_sccs` includes
    /// edge targets in its node set, so it must still get a stratum — otherwise the
    /// eligibility closure would treat every EDB relation as unknown and admit nothing.
    #[test]
    fn condition_only_leaf_predicates_are_labelled() {
        let s = compute_strata(&g(&[("head", "leaf", false)]));
        assert_eq!(s.get("leaf"), Some(&0));
    }

    /// Totality guard: the registration gate rejects this shape, but a panic in a
    /// read-side optimisation would be far worse than a meaningless-but-finite label.
    #[test]
    fn a_negative_self_loop_terminates_rather_than_diverging() {
        let s = compute_strata(&g(&[("p", "p", true)]));
        assert_eq!(s.get("p"), Some(&0));
    }

    /// `saturate` orders its work by `(stratum, relation name)`, so the saturation
    /// sequence is byte-reproducible across runs and processes regardless of HashMap
    /// layout. That ordering is only meaningful if the labels themselves are stable.
    #[test]
    fn labels_are_stable_across_repeated_computation() {
        let graph = g(&[("c", "b", true), ("b", "a", true), ("z", "a", false)]);
        let first = compute_strata(&graph);
        for _ in 0..8 {
            assert_eq!(compute_strata(&graph), first);
        }
        let mut order: Vec<(usize, &str)> = first.iter().map(|(k, v)| (*v, k.as_str())).collect();
        order.sort();
        assert_eq!(order, vec![(0, "a"), (0, "z"), (1, "b"), (2, "c")]);
    }
}
