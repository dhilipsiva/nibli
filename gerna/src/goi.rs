//! `go'i` pro-bridi resolution: rewrites a freshly parsed gerna AST in place so a
//! `go'i` ("repeat the previous bridi") is replaced by the antecedent bridi's
//! selbri + sumti. Pure `nibli_types::ast` manipulation with no smuni/logji
//! dependency, SHARED by the stateful lasna WASM `Session` and the native
//! `nibli-engine` embedding so both resolve `go'i` identically against their own
//! prior-bridi [`BridiSnapshot`] state. Call [`resolve_go_i`] between
//! `gerna::parse_checked` and `smuni::compile_from_gerna_ast`, then snapshot the
//! resolved antecedent with [`extract_bridi_snapshot`].

use nibli_types::ast as gerna_ast;
use std::collections::{HashMap, HashSet};

/// A self-contained clone of a full bridi (its sentence + selbri + sumti
/// subtrees), storable across calls. All indices are internal to the snapshot's
/// own vecs; `root` is a SENTENCE id (the antecedent bridi) so a bare `go'i`
/// can repeat the whole previous predication — relation AND sumti — not just the
/// selbri.
#[derive(Clone)]
pub struct BridiSnapshot {
    pub selbris: Vec<gerna_ast::Selbri>,
    pub sumtis: Vec<gerna_ast::Sumti>,
    pub sentences: Vec<gerna_ast::Sentence>,
    pub root: u32,
}

// ─── Selbri snapshot: extract & graft subtrees for cross-call go'i ───

/// Extract the self-contained full-bridi subtree rooted at the SENTENCE
/// `sentence_id` from `ast` (relation + every head/tail term sumti, preserving
/// tense/negation/attitudinal). `visit_sentence` already deep-clones a `Simple`
/// bridi, so this is a thin wrapper over it.
pub fn extract_bridi_snapshot(ast: &gerna_ast::AstBuffer, sentence_id: u32) -> BridiSnapshot {
    let mut snap = BridiSnapshot {
        selbris: Vec::new(),
        sumtis: Vec::new(),
        sentences: Vec::new(),
        root: 0,
    };
    let mut sm = HashMap::new();
    let mut um = HashMap::new();
    let mut tm = HashMap::new();
    snap.root = visit_sentence(ast, sentence_id, &mut snap, &mut sm, &mut um, &mut tm);
    snap
}

fn visit_selbri(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    snap: &mut BridiSnapshot,
    sm: &mut HashMap<u32, u32>,
    um: &mut HashMap<u32, u32>,
    tm: &mut HashMap<u32, u32>,
) -> u32 {
    if let Some(&mapped) = sm.get(&id) {
        return mapped;
    }
    let new_id = snap.selbris.len() as u32;
    sm.insert(id, new_id);
    snap.selbris.push(gerna_ast::Selbri::Root(String::new())); // placeholder
    let mapped = match &ast.selbris[id as usize] {
        gerna_ast::Selbri::Root(n) => gerna_ast::Selbri::Root(n.clone()),
        gerna_ast::Selbri::Compound(p) => gerna_ast::Selbri::Compound(p.clone()),
        gerna_ast::Selbri::Tanru((m, h)) => {
            let nm = visit_selbri(ast, *m, snap, sm, um, tm);
            let nh = visit_selbri(ast, *h, snap, sm, um, tm);
            gerna_ast::Selbri::Tanru((nm, nh))
        }
        gerna_ast::Selbri::Converted((c, i)) => {
            let ni = visit_selbri(ast, *i, snap, sm, um, tm);
            gerna_ast::Selbri::Converted((*c, ni))
        }
        gerna_ast::Selbri::Negated(i) => {
            let ni = visit_selbri(ast, *i, snap, sm, um, tm);
            gerna_ast::Selbri::Negated(ni)
        }
        gerna_ast::Selbri::Grouped(i) => {
            let ni = visit_selbri(ast, *i, snap, sm, um, tm);
            gerna_ast::Selbri::Grouped(ni)
        }
        gerna_ast::Selbri::WithArgs((core, args)) => {
            let nc = visit_selbri(ast, *core, snap, sm, um, tm);
            let na: Vec<u32> = args
                .iter()
                .map(|&a| visit_sumti(ast, a, snap, sm, um, tm))
                .collect();
            gerna_ast::Selbri::WithArgs((nc, na))
        }
        gerna_ast::Selbri::Connected((l, c, r)) => {
            let nl = visit_selbri(ast, *l, snap, sm, um, tm);
            let nr = visit_selbri(ast, *r, snap, sm, um, tm);
            gerna_ast::Selbri::Connected((nl, c.clone(), nr))
        }
        gerna_ast::Selbri::Abstraction((k, s)) => {
            let ns = visit_sentence(ast, *s, snap, sm, um, tm);
            gerna_ast::Selbri::Abstraction((*k, ns))
        }
    };
    snap.selbris[new_id as usize] = mapped;
    new_id
}

fn visit_sumti(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    snap: &mut BridiSnapshot,
    sm: &mut HashMap<u32, u32>,
    um: &mut HashMap<u32, u32>,
    tm: &mut HashMap<u32, u32>,
) -> u32 {
    if let Some(&mapped) = um.get(&id) {
        return mapped;
    }
    let new_id = snap.sumtis.len() as u32;
    um.insert(id, new_id);
    snap.sumtis.push(gerna_ast::Sumti::Unspecified); // placeholder
    let mapped = match &ast.sumtis[id as usize] {
        gerna_ast::Sumti::ProSumti(s) => gerna_ast::Sumti::ProSumti(s.clone()),
        gerna_ast::Sumti::Description((g, sid)) => {
            let ns = visit_selbri(ast, *sid, snap, sm, um, tm);
            gerna_ast::Sumti::Description((*g, ns))
        }
        gerna_ast::Sumti::Name(s) => gerna_ast::Sumti::Name(s.clone()),
        gerna_ast::Sumti::QuotedLiteral(s) => gerna_ast::Sumti::QuotedLiteral(s.clone()),
        gerna_ast::Sumti::Unspecified => gerna_ast::Sumti::Unspecified,
        gerna_ast::Sumti::Tagged((t, inner)) => {
            let ni = visit_sumti(ast, *inner, snap, sm, um, tm);
            gerna_ast::Sumti::Tagged((*t, ni))
        }
        gerna_ast::Sumti::ModalTagged((mt, inner)) => {
            let ni = visit_sumti(ast, *inner, snap, sm, um, tm);
            let nmt = match mt {
                gerna_ast::ModalTag::Fixed(b) => gerna_ast::ModalTag::Fixed(*b),
                gerna_ast::ModalTag::Fio(sid) => {
                    let ns = visit_selbri(ast, *sid, snap, sm, um, tm);
                    gerna_ast::ModalTag::Fio(ns)
                }
            };
            gerna_ast::Sumti::ModalTagged((nmt, ni))
        }
        gerna_ast::Sumti::Restricted((inner, rc)) => {
            let ni = visit_sumti(ast, *inner, snap, sm, um, tm);
            let ns = visit_sentence(ast, rc.body_sentence, snap, sm, um, tm);
            gerna_ast::Sumti::Restricted((
                ni,
                gerna_ast::RelClause {
                    kind: rc.kind,
                    body_sentence: ns,
                },
            ))
        }
        gerna_ast::Sumti::Number(n) => gerna_ast::Sumti::Number(*n),
        gerna_ast::Sumti::Connected((l, c, neg, r)) => {
            let nl = visit_sumti(ast, *l, snap, sm, um, tm);
            let nr = visit_sumti(ast, *r, snap, sm, um, tm);
            gerna_ast::Sumti::Connected((nl, c.clone(), *neg, nr))
        }
        gerna_ast::Sumti::QuantifiedDescription((count, g, sid)) => {
            let ns = visit_selbri(ast, *sid, snap, sm, um, tm);
            gerna_ast::Sumti::QuantifiedDescription((*count, *g, ns))
        }
    };
    snap.sumtis[new_id as usize] = mapped;
    new_id
}

fn visit_sentence(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    snap: &mut BridiSnapshot,
    sm: &mut HashMap<u32, u32>,
    um: &mut HashMap<u32, u32>,
    tm: &mut HashMap<u32, u32>,
) -> u32 {
    if let Some(&mapped) = tm.get(&id) {
        return mapped;
    }
    let new_id = snap.sentences.len() as u32;
    tm.insert(id, new_id);
    // placeholder
    snap.sentences
        .push(gerna_ast::Sentence::Simple(gerna_ast::Bridi {
            relation: 0,
            head_terms: vec![],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        }));
    let mapped = match &ast.sentences[id as usize] {
        gerna_ast::Sentence::Simple(b) => {
            let nr = visit_selbri(ast, b.relation, snap, sm, um, tm);
            let nh: Vec<u32> = b
                .head_terms
                .iter()
                .map(|&s| visit_sumti(ast, s, snap, sm, um, tm))
                .collect();
            let nt: Vec<u32> = b
                .tail_terms
                .iter()
                .map(|&s| visit_sumti(ast, s, snap, sm, um, tm))
                .collect();
            gerna_ast::Sentence::Simple(gerna_ast::Bridi {
                relation: nr,
                head_terms: nh,
                tail_terms: nt,
                negated: b.negated,
                tense: b.tense,
                attitudinal: b.attitudinal,
            })
        }
        gerna_ast::Sentence::Connected((c, l, r)) => {
            let nl = visit_sentence(ast, *l, snap, sm, um, tm);
            let nr = visit_sentence(ast, *r, snap, sm, um, tm);
            gerna_ast::Sentence::Connected((c.clone(), nl, nr))
        }
        gerna_ast::Sentence::Prenex((vars, body)) => {
            let nb = visit_sentence(ast, *body, snap, sm, um, tm);
            gerna_ast::Sentence::Prenex((vars.clone(), nb))
        }
    };
    snap.sentences[new_id as usize] = mapped;
    new_id
}

/// Graft a snapshot into an existing AstBuffer, consuming it. Returns the new
/// SENTENCE (bridi) root index. Mutates indices in place then moves nodes via
/// `append` — zero cloning.
pub fn graft_snapshot(ast: &mut gerna_ast::AstBuffer, snap: &mut BridiSnapshot) -> u32 {
    let sb = ast.selbris.len() as u32;
    let ub = ast.sumtis.len() as u32;
    let tb = ast.sentences.len() as u32;
    for s in &mut snap.selbris {
        rebase_selbri_inplace(s, sb, ub, tb);
    }
    for s in &mut snap.sumtis {
        rebase_sumti_inplace(s, sb, ub, tb);
    }
    for s in &mut snap.sentences {
        rebase_sentence_inplace(s, sb, ub, tb);
    }
    // `root` is a SENTENCE id, so it rebases by the sentence base (`tb`).
    let root = snap.root + tb;
    ast.selbris.append(&mut snap.selbris);
    ast.sumtis.append(&mut snap.sumtis);
    ast.sentences.append(&mut snap.sentences);
    root
}

fn rebase_selbri_inplace(s: &mut gerna_ast::Selbri, sb: u32, ub: u32, tb: u32) {
    match s {
        gerna_ast::Selbri::Root(_) | gerna_ast::Selbri::Compound(_) => {}
        gerna_ast::Selbri::Tanru((m, h)) => {
            *m += sb;
            *h += sb;
        }
        gerna_ast::Selbri::Converted((_, i)) => {
            *i += sb;
        }
        gerna_ast::Selbri::Negated(i) | gerna_ast::Selbri::Grouped(i) => {
            *i += sb;
        }
        gerna_ast::Selbri::WithArgs((core, args)) => {
            *core += sb;
            for a in args.iter_mut() {
                *a += ub;
            }
        }
        gerna_ast::Selbri::Connected((l, _, r)) => {
            *l += sb;
            *r += sb;
        }
        gerna_ast::Selbri::Abstraction((_, sent)) => {
            *sent += tb;
        }
    }
}

fn rebase_sumti_inplace(s: &mut gerna_ast::Sumti, sb: u32, ub: u32, tb: u32) {
    match s {
        gerna_ast::Sumti::ProSumti(_)
        | gerna_ast::Sumti::Name(_)
        | gerna_ast::Sumti::QuotedLiteral(_)
        | gerna_ast::Sumti::Unspecified
        | gerna_ast::Sumti::Number(_) => {}
        gerna_ast::Sumti::Description((_, sid)) => {
            *sid += sb;
        }
        gerna_ast::Sumti::Tagged((_, i)) => {
            *i += ub;
        }
        gerna_ast::Sumti::ModalTagged((mt, i)) => {
            if let gerna_ast::ModalTag::Fio(sid) = mt {
                *sid += sb;
            }
            *i += ub;
        }
        gerna_ast::Sumti::Restricted((i, rc)) => {
            *i += ub;
            rc.body_sentence += tb;
        }
        gerna_ast::Sumti::Connected((l, _, _, r)) => {
            *l += ub;
            *r += ub;
        }
        gerna_ast::Sumti::QuantifiedDescription((_, _, sid)) => {
            *sid += sb;
        }
    }
}

fn rebase_sentence_inplace(s: &mut gerna_ast::Sentence, sb: u32, ub: u32, tb: u32) {
    match s {
        gerna_ast::Sentence::Simple(b) => {
            b.relation += sb;
            for i in b.head_terms.iter_mut() {
                *i += ub;
            }
            for i in b.tail_terms.iter_mut() {
                *i += ub;
            }
        }
        gerna_ast::Sentence::Connected((_, l, r)) => {
            *l += tb;
            *r += tb;
        }
        gerna_ast::Sentence::Prenex((_, body)) => {
            *body += tb;
        }
    }
}

/// Map a bridi's head+tail term ids to place positions (x1=0, x2=1, …) using the
/// SAME positional FA rule as smuni's `compile_bridi`: an untagged term fills the
/// next free place; a `Sumti::Tagged((tag, inner))` sets the place to
/// `tag.to_index()` and stores the INNER id (the tag is stripped — the merged
/// bridi is positional), resuming after it.
fn place_map(
    sumtis: &[gerna_ast::Sumti],
    head: &[u32],
    tail: &[u32],
    arity_bound: Option<usize>,
) -> Result<Vec<Option<u32>>, String> {
    let mut places: Vec<Option<u32>> = Vec::new();
    let mut next = 0usize;
    for &t in head.iter().chain(tail.iter()) {
        let (place, id, tag) = match &sumtis[t as usize] {
            gerna_ast::Sumti::Tagged((tag, inner)) => (tag.to_index(), *inner, Some(*tag)),
            _ => {
                while next < places.len() && places[next].is_some() {
                    next += 1;
                }
                (next, t, None)
            }
        };
        // FAIL CLOSED on a TAGGED place beyond the relation's arity, mirroring smuni's
        // authoritative guard: the merge strips tags to positional, so smuni would
        // otherwise SILENTLY DROP the over-arity term. Only tagged terms are checked
        // (smuni silently drops untagged over-arity for non-`du`, so the merge does too);
        // `arity_bound` is None for the antecedent and for dictionary-less callers.
        if let (Some(tg), Some(a)) = (tag, arity_bound) {
            if place >= a {
                return Err(format!(
                    "Place tag `{}` targets place x{}, but the selbri only has {} place(s); \
                     the tagged term cannot be placed.",
                    tg.name(),
                    place + 1,
                    a
                ));
            }
        }
        if place >= places.len() {
            places.resize(place + 1, None);
        }
        if places[place].is_some() {
            // FAIL CLOSED, mirroring smuni's authoritative compiler: a tag re-targeting
            // an already-filled place (`fe X fe Y go'i`) would last-win and silently drop
            // the earlier term. Only reachable for a `Tagged` term — an untagged term
            // always advances `next` to a free slot.
            return Err(format!(
                "Place tag `{}` targets place x{}, which is already filled; \
                 the same place cannot be set twice.",
                tag.map(|t| t.name()).unwrap_or(""),
                place + 1
            ));
        }
        places[place] = Some(id);
        next = place + 1;
    }
    Ok(places)
}

/// Resolve a Simple bridi's go'i (when its relation selbri is `Root("go'i")`)
/// against the antecedent identified by `current`. BARE go'i (`go'i` / `? go'i`,
/// no own sumti/tense/negation/attitudinal) repeats the WHOLE antecedent bridi;
/// a PARTIAL go'i (`do go'i`, `na go'i`, `pu go'i`) merges per place — the go'i's
/// supplied places override, unsupplied places inherit from the antecedent, and
/// tense/negation/attitudinal are overridden only when the go'i supplies them.
/// The antecedent's term ids are already valid in `ast.sumtis` (grafted from a
/// snapshot or a live in-buffer sentence), so the merge is pure id-selection — no
/// rebasing. Does NOT touch `current` (the caller owns antecedent advancement);
/// no-op if the bridi is not a go'i.
fn resolve_simple_bridi_go_i(
    ast: &mut gerna_ast::AstBuffer,
    sentence_idx: usize,
    current: &Option<u32>,
    arity_of: &dyn Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    let gerna_ast::Sentence::Simple(mut bridi) = ast.sentences[sentence_idx].clone() else {
        return Ok(());
    };
    let is_go_i =
        matches!(&ast.selbris[bridi.relation as usize], gerna_ast::Selbri::Root(n) if n == "go'i");
    if !is_go_i {
        return Ok(());
    }
    let antecedent_sid =
        current.ok_or_else(|| "go'i has no antecedent (no previous assertion)".to_string())?;
    let antecedent = match &ast.sentences[antecedent_sid as usize] {
        gerna_ast::Sentence::Simple(b) => b.clone(),
        _ => return Err("go'i antecedent is not a simple bridi".to_string()),
    };

    let bare = bridi.head_terms.is_empty()
        && bridi.tail_terms.is_empty()
        && bridi.tense.is_none()
        && !bridi.negated
        && bridi.attitudinal.is_none();
    if bare {
        ast.sentences[sentence_idx] = gerna_ast::Sentence::Simple(antecedent);
        return Ok(());
    }

    // Per-place merge: overlay the go'i's supplied places over the antecedent's.
    // `place_map` fails closed on a duplicate FA place AND (for the go'i side) on a
    // tagged place beyond the antecedent relation's arity. The antecedent side is
    // already valid, so it's unbounded. The relation's arity comes from the caller's
    // dictionary lookup; a non-`Root` relation (tanru/compound) has no simple arity → None.
    let ant_arity = match &ast.selbris[antecedent.relation as usize] {
        gerna_ast::Selbri::Root(name) => arity_of(name),
        _ => None,
    };
    let ant = place_map(
        &ast.sumtis,
        &antecedent.head_terms,
        &antecedent.tail_terms,
        None,
    )?;
    let goi = place_map(&ast.sumtis, &bridi.head_terms, &bridi.tail_terms, ant_arity)?;
    let n = ant.len().max(goi.len());
    let mut head_terms = Vec::with_capacity(n);
    for i in 0..n {
        let id = goi
            .get(i)
            .copied()
            .flatten()
            .or_else(|| ant.get(i).copied().flatten())
            .unwrap_or_else(|| {
                // A place neither side supplies becomes a fresh `zo'e` so smuni's
                // positional counter stays aligned.
                let uid = ast.sumtis.len() as u32;
                ast.sumtis.push(gerna_ast::Sumti::Unspecified);
                uid
            });
        head_terms.push(id);
    }
    bridi.relation = antecedent.relation;
    bridi.head_terms = head_terms;
    bridi.tail_terms = vec![];
    bridi.negated = antecedent.negated || bridi.negated;
    bridi.tense = bridi.tense.or(antecedent.tense);
    bridi.attitudinal = bridi.attitudinal.or(antecedent.attitudinal);
    ast.sentences[sentence_idx] = gerna_ast::Sentence::Simple(bridi);
    Ok(())
}

/// Resolve go'i references in a single TOP-LEVEL sentence, advancing `current`.
fn resolve_sentence_go_i(
    ast: &mut gerna_ast::AstBuffer,
    sentence_idx: usize,
    current: &mut Option<u32>,
    arity_of: &dyn Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    match ast.sentences[sentence_idx].clone() {
        gerna_ast::Sentence::Simple(_) => {
            // Resolve this bridi's own top-level go'i (bare → whole antecedent;
            // partial → per-place merge).
            resolve_simple_bridi_go_i(ast, sentence_idx, &*current, arity_of)?;
            // Descend into NESTED positions (abstraction / relative-clause bodies)
            // and resolve any go'i there, reading `current` as the PRIOR top-level
            // antecedent — so `mi klama .i mi nelci lo nu go'i` resolves the nested
            // go'i to `klama(mi)`, not to this sentence. Descend BEFORE advancing
            // `current`. This descent ALSO resolves a SELBRI-position go'i (`sutra
            // go'i` in a tanru) via `resolve_selbri_go_i` → the antecedent relation.
            let (relation, terms): (u32, Vec<u32>) = match &ast.sentences[sentence_idx] {
                gerna_ast::Sentence::Simple(b) => (
                    b.relation,
                    b.head_terms.iter().chain(&b.tail_terms).copied().collect(),
                ),
                _ => unreachable!(),
            };
            let mut seen = std::collections::HashSet::new();
            resolve_selbri_go_i(ast, relation, &*current, &mut seen, arity_of)?;
            for t in terms {
                resolve_sumti_go_i(ast, t, &*current, &mut seen, arity_of)?;
            }
            // The resolved bridi becomes the antecedent for the next go'i —
            // `mi klama .i do go'i .i go'i` chains the resolved `klama(do)`.
            *current = Some(sentence_idx as u32);
            Ok(())
        }
        gerna_ast::Sentence::Connected((_, left_idx, right_idx)) => {
            resolve_sentence_go_i(ast, left_idx as usize, current, arity_of)?;
            resolve_sentence_go_i(ast, right_idx as usize, current, arity_of)?;
            Ok(())
        }
        gerna_ast::Sentence::Prenex((_, body_idx)) => {
            resolve_sentence_go_i(ast, body_idx as usize, current, arity_of)?;
            Ok(())
        }
    }
}

/// Mutating twin of `selbri_reaches_go_i`: descend a selbri and resolve any go'i.
/// A SELBRI-position go'i (a bare `Root("go'i")` in a tanru, `sutra go'i`) becomes
/// the antecedent's RELATION selbri; a nested SENTENCE-position go'i (an
/// abstraction body, `lo nu go'i`) is resolved by recursing. Reads `current`
/// (never advances it). Clone-then-recurse to dodge the `&mut ast[i]` borrow;
/// `seen` cycle-guards.
fn resolve_selbri_go_i(
    ast: &mut gerna_ast::AstBuffer,
    id: u32,
    current: &Option<u32>,
    seen: &mut std::collections::HashSet<(u8, u32)>,
    arity_of: &dyn Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    if !seen.insert((1, id)) {
        return Ok(());
    }
    match ast.selbris[id as usize].clone() {
        gerna_ast::Selbri::Root(n) if n == "go'i" => {
            // SELBRI-position go'i (a tanru arm, `mi sutra go'i`): replace it with
            // the antecedent bridi's RELATION selbri. The antecedent is already in
            // the live buffer (grafted at dispatch / a live sentence), so its
            // relation subtree's child indices are valid — copy the top node,
            // sharing the subtree exactly as the bare-bridi case copies the
            // antecedent bridi. After `mi klama`, `mi sutra go'i` → `mi sutra klama`.
            let antecedent_sid = current
                .ok_or_else(|| "go'i has no antecedent (no previous assertion)".to_string())?;
            let ant_relation = match &ast.sentences[antecedent_sid as usize] {
                gerna_ast::Sentence::Simple(b) => b.relation,
                _ => return Err("go'i antecedent is not a simple bridi".to_string()),
            };
            let cloned = ast.selbris[ant_relation as usize].clone();
            ast.selbris[id as usize] = cloned;
        }
        gerna_ast::Selbri::Root(_) | gerna_ast::Selbri::Compound(_) => {}
        gerna_ast::Selbri::Tanru((m, h)) => {
            resolve_selbri_go_i(ast, m, current, seen, arity_of)?;
            resolve_selbri_go_i(ast, h, current, seen, arity_of)?;
        }
        gerna_ast::Selbri::Converted((_, i))
        | gerna_ast::Selbri::Negated(i)
        | gerna_ast::Selbri::Grouped(i) => resolve_selbri_go_i(ast, i, current, seen, arity_of)?,
        gerna_ast::Selbri::WithArgs((core, args)) => {
            resolve_selbri_go_i(ast, core, current, seen, arity_of)?;
            for a in args {
                resolve_sumti_go_i(ast, a, current, seen, arity_of)?;
            }
        }
        gerna_ast::Selbri::Connected((l, _, r)) => {
            resolve_selbri_go_i(ast, l, current, seen, arity_of)?;
            resolve_selbri_go_i(ast, r, current, seen, arity_of)?;
        }
        gerna_ast::Selbri::Abstraction((_, s)) => {
            resolve_nested_sentence_go_i(ast, s, current, seen, arity_of)?;
        }
    }
    Ok(())
}

/// Mutating twin of `sumti_reaches_go_i`: descend a sumti and resolve any nested
/// SENTENCE-position go'i (a relative-clause body, `poi go'i`). Reads `current`.
fn resolve_sumti_go_i(
    ast: &mut gerna_ast::AstBuffer,
    id: u32,
    current: &Option<u32>,
    seen: &mut std::collections::HashSet<(u8, u32)>,
    arity_of: &dyn Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    if !seen.insert((2, id)) {
        return Ok(());
    }
    match ast.sumtis[id as usize].clone() {
        gerna_ast::Sumti::Description((_, sid))
        | gerna_ast::Sumti::QuantifiedDescription((_, _, sid)) => {
            resolve_selbri_go_i(ast, sid, current, seen, arity_of)?;
        }
        gerna_ast::Sumti::Tagged((_, i)) => resolve_sumti_go_i(ast, i, current, seen, arity_of)?,
        gerna_ast::Sumti::ModalTagged((mt, i)) => {
            if let gerna_ast::ModalTag::Fio(sid) = mt {
                resolve_selbri_go_i(ast, sid, current, seen, arity_of)?;
            }
            resolve_sumti_go_i(ast, i, current, seen, arity_of)?;
        }
        gerna_ast::Sumti::Restricted((i, rc)) => {
            resolve_sumti_go_i(ast, i, current, seen, arity_of)?;
            resolve_nested_sentence_go_i(ast, rc.body_sentence, current, seen, arity_of)?;
        }
        gerna_ast::Sumti::Connected((l, _, _, r)) => {
            resolve_sumti_go_i(ast, l, current, seen, arity_of)?;
            resolve_sumti_go_i(ast, r, current, seen, arity_of)?;
        }
        gerna_ast::Sumti::ProSumti(_)
        | gerna_ast::Sumti::Name(_)
        | gerna_ast::Sumti::QuotedLiteral(_)
        | gerna_ast::Sumti::Unspecified
        | gerna_ast::Sumti::Number(_) => {}
    }
    Ok(())
}

/// Mutating twin of `sentence_reaches_go_i` for a NESTED sentence (abstraction /
/// relative-clause body): resolve its Simple bridi's go'i (reading `current`,
/// never advancing it) and recurse into its selbri + terms (handles
/// `lo nu lo nu go'i`).
fn resolve_nested_sentence_go_i(
    ast: &mut gerna_ast::AstBuffer,
    id: u32,
    current: &Option<u32>,
    seen: &mut std::collections::HashSet<(u8, u32)>,
    arity_of: &dyn Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    if !seen.insert((0, id)) {
        return Ok(());
    }
    match ast.sentences[id as usize].clone() {
        gerna_ast::Sentence::Simple(_) => {
            resolve_simple_bridi_go_i(ast, id as usize, current, arity_of)?;
            let (relation, terms): (u32, Vec<u32>) = match &ast.sentences[id as usize] {
                gerna_ast::Sentence::Simple(b) => (
                    b.relation,
                    b.head_terms.iter().chain(&b.tail_terms).copied().collect(),
                ),
                _ => unreachable!(),
            };
            resolve_selbri_go_i(ast, relation, current, seen, arity_of)?;
            for t in terms {
                resolve_sumti_go_i(ast, t, current, seen, arity_of)?;
            }
        }
        gerna_ast::Sentence::Connected((_, l, r)) => {
            resolve_nested_sentence_go_i(ast, l, current, seen, arity_of)?;
            resolve_nested_sentence_go_i(ast, r, current, seen, arity_of)?;
        }
        gerna_ast::Sentence::Prenex((_, body)) => {
            resolve_nested_sentence_go_i(ast, body, current, seen, arity_of)?;
        }
    }
    Ok(())
}

/// Walk all root sentences and resolve any go'i references.
/// Skips snapshot grafting entirely if no go'i is present in the parsed text.
///
/// `arity_of` looks up a relation's place count so a partial go'i whose FA tag
/// targets a place beyond the antecedent relation's arity fails closed (mirroring
/// smuni's authoritative guard) instead of being silently dropped after the merge
/// strips tags. `gerna::goi` has no dictionary, so the caller supplies the lookup;
/// callers without one use [`resolve_go_i`] (no arity bound).
pub fn resolve_go_i_with_arity(
    ast: &mut gerna_ast::AstBuffer,
    last_snapshot: &mut Option<BridiSnapshot>,
    arity_of: &dyn Fn(&str) -> Option<usize>,
) -> Result<Option<u32>, String> {
    let has_go_i = ast
        .selbris
        .iter()
        .any(|s| matches!(s, gerna_ast::Selbri::Root(n) if n == "go'i"));
    let mut current: Option<u32> = if has_go_i {
        // Graft from a CLONE: `graft_snapshot` rebases + drains its vecs via
        // `Vec::append`. Without the clone, a second `? go'i` would graft the
        // drained husk, producing an out-of-bounds index → a WASM component
        // trap. Cloning keeps the stored snapshot intact, so go'i is idempotent
        // across calls.
        last_snapshot
            .as_ref()
            .map(|snap| graft_snapshot(ast, &mut snap.clone()))
    } else {
        None
    };
    for i in 0..ast.roots.len() {
        let root_idx = ast.roots[i] as usize;
        resolve_sentence_go_i(ast, root_idx, &mut current, arity_of)?;
    }
    // Defensive backstop: every reachable go'i position — top-level, partial,
    // abstraction / relative-clause body, AND selbri-position (a tanru arm) — is
    // resolved above; a resolved go'i leaves only an unreachable residual node. A
    // go'i still REACHABLE here would mean a future AST variant was added to the
    // `*_reaches_go_i` walks but not the `resolve_*` twins (the arm-for-arm mirror
    // broke). Compiling a stray go'i as a literal predicate is silently wrong, so
    // reject rather than miscompile.
    if has_go_i {
        let mut seen = HashSet::new();
        for &root in &ast.roots {
            if sentence_reaches_go_i(ast, root, &mut seen) {
                return Err(
                    "go'i in an unsupported position — the resolver did not descend \
                            into it (a `*_reaches_go_i` / `resolve_*` mismatch). This \
                            should not occur for any currently-supported construct."
                        .to_string(),
                );
            }
        }
    }
    Ok(current)
}

/// Resolve go'i references WITHOUT a beyond-arity place bound — for callers that
/// have no dictionary (lasna unit tests, in-browser/native modes that already
/// validate arity in smuni). The duplicate-place guard still applies. Production
/// callers with a dictionary use [`resolve_go_i_with_arity`].
pub fn resolve_go_i(
    ast: &mut gerna_ast::AstBuffer,
    last_snapshot: &mut Option<BridiSnapshot>,
) -> Result<Option<u32>, String> {
    resolve_go_i_with_arity(ast, last_snapshot, &|_| None)
}

/// Read-only reachability walk: does any `Selbri::Root("go'i")` remain REACHABLE
/// from sentence `id`, following the exact edges the compiler will follow? Used
/// to fail closed on go'i the resolver does not descend into. The `(tag, id)`
/// key disambiguates the three index spaces and guards against rel-clause /
/// connective re-entry. Match arms mirror `rebase_*` (the nested-index ground
/// truth) exactly — no `_` wildcard, so a new AST variant forces a revisit.
fn sentence_reaches_go_i(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    seen: &mut std::collections::HashSet<(u8, u32)>,
) -> bool {
    if !seen.insert((0, id)) {
        return false;
    }
    match &ast.sentences[id as usize] {
        gerna_ast::Sentence::Simple(b) => {
            selbri_reaches_go_i(ast, b.relation, seen)
                || b.head_terms
                    .iter()
                    .chain(&b.tail_terms)
                    .any(|&s| sumti_reaches_go_i(ast, s, seen))
        }
        gerna_ast::Sentence::Connected((_, l, r)) => {
            sentence_reaches_go_i(ast, *l, seen) || sentence_reaches_go_i(ast, *r, seen)
        }
        gerna_ast::Sentence::Prenex((_, body)) => sentence_reaches_go_i(ast, *body, seen),
    }
}

fn selbri_reaches_go_i(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    seen: &mut std::collections::HashSet<(u8, u32)>,
) -> bool {
    if !seen.insert((1, id)) {
        return false;
    }
    match &ast.selbris[id as usize] {
        gerna_ast::Selbri::Root(n) => n == "go'i",
        gerna_ast::Selbri::Compound(_) => false,
        gerna_ast::Selbri::Tanru((m, h)) => {
            selbri_reaches_go_i(ast, *m, seen) || selbri_reaches_go_i(ast, *h, seen)
        }
        gerna_ast::Selbri::Converted((_, i))
        | gerna_ast::Selbri::Negated(i)
        | gerna_ast::Selbri::Grouped(i) => selbri_reaches_go_i(ast, *i, seen),
        gerna_ast::Selbri::WithArgs((core, args)) => {
            selbri_reaches_go_i(ast, *core, seen)
                || args.iter().any(|&a| sumti_reaches_go_i(ast, a, seen))
        }
        gerna_ast::Selbri::Connected((l, _, r)) => {
            selbri_reaches_go_i(ast, *l, seen) || selbri_reaches_go_i(ast, *r, seen)
        }
        gerna_ast::Selbri::Abstraction((_, s)) => sentence_reaches_go_i(ast, *s, seen),
    }
}

fn sumti_reaches_go_i(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    seen: &mut std::collections::HashSet<(u8, u32)>,
) -> bool {
    if !seen.insert((2, id)) {
        return false;
    }
    match &ast.sumtis[id as usize] {
        gerna_ast::Sumti::Description((_, sid))
        | gerna_ast::Sumti::QuantifiedDescription((_, _, sid)) => {
            selbri_reaches_go_i(ast, *sid, seen)
        }
        gerna_ast::Sumti::Tagged((_, i)) => sumti_reaches_go_i(ast, *i, seen),
        gerna_ast::Sumti::ModalTagged((mt, i)) => {
            let fio_hit =
                matches!(mt, gerna_ast::ModalTag::Fio(sid) if selbri_reaches_go_i(ast, *sid, seen));
            fio_hit || sumti_reaches_go_i(ast, *i, seen)
        }
        gerna_ast::Sumti::Restricted((i, rc)) => {
            sumti_reaches_go_i(ast, *i, seen) || sentence_reaches_go_i(ast, rc.body_sentence, seen)
        }
        gerna_ast::Sumti::Connected((l, _, _, r)) => {
            sumti_reaches_go_i(ast, *l, seen) || sumti_reaches_go_i(ast, *r, seen)
        }
        gerna_ast::Sumti::ProSumti(_)
        | gerna_ast::Sumti::Name(_)
        | gerna_ast::Sumti::QuotedLiteral(_)
        | gerna_ast::Sumti::Unspecified
        | gerna_ast::Sumti::Number(_) => false,
    }
}
