# Session summary — 2026-09-03

**Question asked:** is nibli a good fit for data-flow / logic-flow analysis of
computer programs? Then: how would an adjudication layer over Soufflé and CodeQL
actually work, is it better than not using nibli, and should nibli have recursion
support?

**Status:** two commits on `main` (`e4e5a90`, `619ea1d`). This file is untracked
and deliberately uncommitted.

---

## 1. The headline finding

Nibli cannot be a data-flow analysis engine, and the reason is measurable rather
than philosophical. It *can* be the policy layer above one.

Everything below was measured on this box (release profile), not reasoned about.

### Recursion is exponential

The textbook closure rule — the atom of every data-flow analysis, since
reachability, def-use, points-to and taint propagation are all closures:

```nibli-kr
all $a, $b, $c: earlier($a,$b) & earlier($b,$c) -> earlier($a,$c).
```

Forward query `earlier(N0, Nn).` over an n-edge chain:

| n | 5 | 6 | 8 | 10 | 12 | 15 |
|---|---|---|---|---|---|---|
| time | 0.21 s | 0.35 s | 1.14 s | 4.81 s | 18.3 s | >60 s |

~3.3–4.2× per two edges added. Materialisation is **not** engaged:
`NIBLI_MATERIALIZE=1` vs `=0` at n=12 measured 17.69 s vs 17.25 s.

### The same query's FALSE twin is fast

On the *same* knowledge base, `earlier(Nn, N0).` goes non-definitive, so the cone
**is** saturated:

- n=12: **0.11 s** against 18.3 s for the TRUE direction — 160×
- n=25: 0.72 s (325 closure tuples)
- n=50: 6.0 s (1,275 tuples)
- n=100: 47.2 s (5,050 tuples)
- n=200: >240 s (20,100 tuples)

Control: loading 200 facts with no rule is 0.10 s flat at every size, so all of
the above is rule evaluation.

**Derivation rate on the saturated path: ~100–210 tuples/s.** Soufflé is 10⁶–10⁷.

### Non-recursive adjudication is comfortable

Same engine, non-recursive policy rules over analyzer facts:

| flows | facts | time | peak RSS |
|---|---|---|---|
| 100 | 256 | 0.10 s | 7 MB |
| 2,000 | 5,006 | 0.20 s | 54 MB |
| 10,000 | 25,006 | 1.20 s | 254 MB |
| 30,000 | 75,006 | 3.80 s | 764 MB |
| 60,000 | 150,006 | 8.31 s | 1.5 GB |

Linear in time, ~10 KB/fact — **memory binds before time does.**

### Root cause: a request policy, not a missing algorithm

Stratum-ordered materialisation evaluates recursive SCCs bottom-up with
semi-naive joins and level indexing, and handles the closure rule correctly. It
is simply never asked: a purely positive cone is requested only when exact
reasoning stays non-definitive (GUARANTEES § Completeness), and a positive
reachability goal resolves definitively.

Nothing in `ci` had ever paid for this — the shipped corpora chain 2–4 hops and
`pins/temporal-order.nibli` closes over five.

---

## 2. The same trap without recursion

This is the part that bit me mid-session and is the most transferable lesson.

A purely **positive** rule set shows the identical asymmetry. In the adjudication
example, `authorized(F1, …)` returning FALSE — the finding, the case a pipeline
cares about — is an exhaustive search:

| flows | `authorized(...)` FALSE | `warns(Gate, ...)` TRUE |
|---|---|---|
| 500 | 0.90 s | 0.10 s |
| 2,000 | 19.2 s | 0.20 s |
| 10,000 | — | 1.20 s |

Fixed by deriving the finding under negation instead of reading clearance:

```nibli-kr
all $f, $d, $s, $o, $r: carries($f, $d, $s, $o, $r) & ~authorized($f, Release, $s) -> warns(Gate, $f, $s).
```

That requests the cone and answers the same question ~190× faster at 500 flows.
Stating it over *clearance* rather than over evidence is what preserves the
fail-closed reading: a flow whose sink the analyzer never classified is not
cleared, so it warns.

**Rule of thumb: ask for the finding, not the clearance.** The engine gives no
signal that one phrasing is the cheap one.

---

## 3. What was built

### `examples/adjudication/` (commit `e4e5a90`, corrected in `619ea1d`)

A worked, self-verifying pipeline: Soufflé/CodeQL compute the flows, nibli
decides what they mean. 14 content pins, green.

| File | Role |
|---|---|
| `policy.nibli` | Reviewed policy + trust boundary |
| `facts.nibli` | Generated analyzer output (committed sample) |
| `policy.pins.nibli` | Content pins — live `policy.nibli` as fixture via `--kb` |
| `extract.py` | Soufflé/CodeQL tabular output → escaped KR facts |
| `README.md` | Architecture, measurements, limits |

Three properties make it *adjudication* rather than a second analyzer, each
verified with a negative control:

1. `derived_only("authorized")` — the analyzer cannot state a conclusion.
2. `admits(...)` — the analyzer cannot widen the vocabulary; an unreviewed
   output relation fails the load.
3. `certify_text` → `ProofEnvelope`, checked by the KB-independent
   `validate_envelope`.

### `just bench-closure` (commit `619ea1d`)

Release-profile bench, self-generating KBs. Three families: forward (the cliff,
with growth ratios), backward (the saturated path), and clearance-vs-finding (the
same trap without recursion). The source for any recursion-cost figure.

### GUARANTEES § Disclosed Sharp Edges (commit `619ea1d`)

New entry disclosing the cost cliff, with the re-open trigger: extend the
materialisation request policy to cones containing a recursive SCC.

---

## 4. Two defects found while building

Neither was reachable by internal test-writing; both came from building a real
pipeline.

**KR injection via analyzer identifiers.** Analyzer columns carry names from the
code under analysis, so whoever can name a file in the analyzed repo chooses
those bytes. A crafted name could close a quoted term and append
`permits(Review, …, Waiver).` to clear its own finding — and `permits` is
admitted vocabulary, so the `admits` closure does not catch it. `extract.py` now
escapes backslash/quote and *refuses* control characters. `flow:5` carries a live
injection attempt, pinned to stay a finding, with a positive control proving the
pin isn't vacuous.

**A wrong scaling claim in my own commit.** `e4e5a90` shipped a purely positive
fail-closed policy while quoting a table measured on an earlier NAF-bearing
draft. The bench caught it because it exercised the shipped policy rather than
the scratch one. Corrected in `619ea1d`.

---

## 5. Verdicts

### Should nibli have recursion support?

It has recursion; the question is whether to make it competitive. Two separable
defects, opposite answers:

- **Fix the trigger policy.** The machinery already works — same rule, same KB,
  the FALSE direction saturates in 0.11 s while TRUE takes 18.3 s. Extending the
  request to recursive SCCs would move n=15 from ">60 s" to under a second.
  Worth doing even if nobody does data-flow with nibli: the cliff is already live
  in shipped content (`pins/temporal-order.nibli`), and an undisclosed
  exponential in the most natural rule shape in logic programming is a bad
  property for a project selling predictability. **Disclosure landed this
  session regardless.**
- **Don't chase the constant factor.** ~100–200 tuples/s is a data-structure
  problem, and fixing it means competing head-on with a system that compiles to
  C++. Nibli's differentiators — proof envelope, Lean proofs, differential
  gates, readable surface — get no better from winning a Datalog benchmark.
- **If the trigger fix proves insufficient:** a *declared* closure form (the KB
  states "this relation is the transitive closure of that one", the engine uses
  a purpose-built algorithm and refuses the general case loudly). Gives users the
  one recursive shape they need, no silent cliff, no commitment to being a
  general Datalog engine.

### Is nibli worth using for vulnerability analysis?

The deciding question: **who reads the output, and would they ever check the
derivation?**

- Team reading it in a PR → **don't**. The envelope is dead weight; you pay the
  vocabulary tax and the silent performance traps for an artifact nobody opens.
- External auditor / regulator / customer security team → the differentiator is
  real. "Here is the derivation, validate it yourself" is a materially different
  claim from "our scanner said so."

**Recommendation: keep nibli off the critical path of the scanning pipeline; use
it for the sign-off layer** (release attestation, waiver justification) — dozens
of facts, external audience, well inside the envelope.

**Alternatives, honestly ranked for this purpose:**

| Option | Verdict |
|---|---|
| **OPA/Rego + Conftest** | The pragmatic default. Mature, hireable, SARIF-aware, decision logs. Ceiling: the log records the answer, not a checkable derivation. |
| **Hand-rolled Python** | Correct choice under ~500 lines of policy with no external auditor. |
| **Soufflé for policy too** | Zero new infrastructure, but analysis bugs and policy bugs become indistinguishable — defeats the point of a layer. |
| **clingo/ASP** | Underrated: weak constraints can rank/minimize findings, which neither Rego nor nibli can express. Specialist skill, no proof artifact. |
| **Cedar** | Mechanized Lean spec, rigorous in the same spirit, but principal/action/resource authz — too narrow. Worth reading for scoping. |
| **Z3/SMT** | Wrong tool. Entailment over ground facts, not satisfiability. |

**The caveat that survives any choice:** nibli guarantees the derivation, not the
premises. Nearly all error in vulnerability analysis lives in Soufflé's
approximations and CodeQL's sanitizer models. A perfect proof over a wrong
sanitizer model is a confidently wrong "cleared", and the envelope will make it
look *more* authoritative. The layer's contribution is making premises explicit
and reviewable — not making them true.

**The strongest case for using it here is dogfooding**, and it should be named as
such: two real defects surfaced in one session. If the goal is to make nibli
good, keep building on it. If the goal is to ship a pipeline this quarter, use
OPA and revisit.

---

## 6. Open items

- **Not run:** full `just ci` after `619ea1d` (15–25 min). `verify-adjudication`,
  `cargo fmt --check`, and clippy on the new bin are green; the rest is unverified.
- **Scope note:** `verify-adjudication` was wired into `ci` — a small deliberate
  scope expansion, easy to back out.
- **Unmeasured:** `query_find_text` enumeration ("list every flow that warns").
  All scaling figures above are ground queries.
- **Unmeasured:** graph topologies other than a linear chain. The exponent is
  characteristic of that shape, not a general law.
- **The gating language feature** for this use case remains user-authored `pred`
  declarations (NIBLI_KR §14.1) — a compile error today. Only 66 of 1,356 corpus
  entries are `Curated` tier with hand-verified places.
