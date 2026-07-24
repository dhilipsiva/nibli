# What Nibli guarantees

Derived from the engine [README](https://github.com/dhilipsiva/nibli/blob/main/README.md) and [GUARANTEES.md](https://github.com/dhilipsiva/nibli/blob/main/GUARANTEES.md). The full contract text lives in those files; this page is a short operator summary.

## One surface language

Nibli has **one** front-end language: **nibli KR** (predicate-call surface: `dog(Adam).`, `animal(every dog).`). Name resolution is **fail-closed**: an unknown word is a compile error, never an arity-guessed new predicate. Normative spec: [NIBLI_KR.md](https://github.com/dhilipsiva/nibli/blob/main/NIBLI_KR.md).

## Soundness (relative to what you asserted)

The engine never returns **TRUE** for a formula that does not follow from the asserted facts and compiled rules, **given a correct implementation**. A TRUE answer comes with a formal proof trace. Bugs would be deterministic and testable — not stochastic fabrication.

This is **not** omniscience: change the premises and the verdict can change.

## Closed world and closed domain

Inference assumes:

- **Closed world** — a fact you did not assert is taken to be *false*, not unknown.
- **Closed domain** — quantifiers range only over entities the knowledge base knows.

## Four-valued outcomes

How to read a query result (product README wording):

| Verdict | Meaning |
|---------|---------|
| **TRUE** | A proof exists from your premises (facts + rules + trusted backend results). |
| **FALSE** | *Not derivable* from those premises. This is **not** a proof of ¬P. |
| **UNKNOWN** | The search could not decide (e.g. a cycle, incomplete knowledge, or negation over an undecided sub-goal). |

Hosts may also surface **resource** limits (fuel / memory / depth) as a separate non-answer when the budget is hit — see host/`NIBLI_*` env and [GUARANTEES.md](https://github.com/dhilipsiva/nibli/blob/main/GUARANTEES.md).

## Trusted compute backend

Results from the **external compute backend** (`exponential`, `logarithm`, or predicates you register) are a **trusted oracle**, not a derivation: a `true` reply is auto-asserted mid-query. Built-in arithmetic (`product` / `sum` / `quotient`) is local. Any conclusion that passes through the backend is only as sound as that oracle.

## Where the full story lives

- [GUARANTEES.md](https://github.com/dhilipsiva/nibli/blob/main/GUARANTEES.md) — differential oracles (Vampire / clingo), Lean proofs, determinism, mutation baseline.
- [LOGIC_IR.md](https://github.com/dhilipsiva/nibli/blob/main/LOGIC_IR.md) — the FOL intermediate form the reasoner consumes.
- CI: `just ci`, `just verify-soundness`, `just verify-proofs`.
