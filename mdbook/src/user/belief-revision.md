# Belief revision

Nibli's conclusions are never stored — they are re-derived from the current
facts on every query. Retract a fact and everything that depended on it
dissolves; nothing has to be manually un-concluded. This page covers the
mechanics on both runtime surfaces.

**Sources:** [GUARANTEES — Retraction Model](https://github.com/dhilipsiva/nibli/blob/main/GUARANTEES.md),
`nibli-host` REPL (`nibli-host/src/main.rs`), and the retraction metamorphic
differential (`nibli-verify/src/retract_diff.rs`, part of `just verify-soundness`).

## The guarantee: retract ≡ never-asserted

Retraction has **one path — rebuild**: the fact's registry record is marked
retracted and the knowledge base is rebuilt by replaying the surviving records.
Equivalence classes, indexes, and the quantifier domain are all re-derived, so
a KB after a retraction answers **byte-identically** to a fresh engine that
never saw the fact.

This is not just documented — it is checked metamorphically at scale: the
retraction differential generates seeded random programs mixing ground facts,
rules, identity links, and stratified negation, retracts random earlier
statements, and requires the engine to agree with a never-asserted twin on a
battery of ground *and* quantified queries after every retraction.

## In the host REPL

Facts get ids at assert time (`[Fact #N] …`, in file order under `:load`).
List and retract by id:

```text
:facts
[Facts] 24 active fact(s):
...

:retract 21
[Retract] Fact #21 retracted. KB rebuilt.
```

Re-query and the verdicts reflect the surviving facts only. With the durable
store attached, the retraction persists as a tombstone — provenance is kept,
and a replay never resurrects the fact.

Use `:facts --all` to inspect retained assertion records with `active` or
`withdrawn` status. The default `:facts` still lists active statements only.
Withdrawn records retain their ID and label across reopening a saved knowledge
base; their obsolete payloads are not recompiled. This is retained assertion
metadata, not a complete chronology of changes. `:reset` clears both sets.

A single `assert_text` call commits every root together or leaves the prior
knowledge base unchanged. Separate input lines remain separate calls. A storage
commit with an uncertain outcome retires the live session until the database is
reopened, so subsequent queries cannot certify an uncertain state.

Two worked, engine-checked demos:

- [GDPR walkthrough](gdpr-walkthrough.md) — withdraw consent (`:retract 21`):
  the lawful basis flips FALSE and the right to erasure flips TRUE.
- [Drug-interactions walkthrough](ddi-walkthrough.md) — discontinue the
  inhibitor (`:retract 4`) or the drug (`:retract 10`): the alert dissolves;
  in the second case the drug-level risk deliberately stays TRUE.

## Verdicts that rest on an absence

Retraction interacts with negation-as-failure: a claim like *“no lawful basis
remains”* becomes TRUE precisely because a search found nothing. The engine
discloses this — such proofs carry the `naf_dependent` flag, and query results
distinguish a deduced FALSE from `UNKNOWN (naf-dependent)` states. See
[What Nibli guarantees](guarantees.md).

## In the playground: edit and re-query

The browser playground has no `:retract` command — it does not need one. The
**nibli KR pane is the knowledge base**, and every query rebuilds a fresh
engine from that pane, so belief revision is *edit-and-re-query*: delete (or
`#`-comment) the fact's line, run the claim again, and the verdict reflects
the edited KB. That is the same "retract ≡ never-asserted" semantics, achieved
by construction.

The preset examples load read-only. To revise one, switch to **Custom** mode
and paste the corpus in from the repo root (e.g.
[`gdpr.nibli`](https://github.com/dhilipsiva/nibli/blob/main/gdpr.nibli),
[`drug-interactions.nibli`](https://github.com/dhilipsiva/nibli/blob/main/drug-interactions.nibli)
— `#` comment lines are skipped at assert time), then comment out
`approves(Adam).` or `uses(Adam, Varfarin).` and re-run the preset claims from
the walkthroughs.
