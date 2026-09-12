Revised version is in the file. The critique behind it, in priority order:

**1. It gates work, then demands everything at once.** Seven decision gates and Gate 7 says "do not expand domain coverage until earlier gates pass" — but the deliverables list asks for full four-domain capability matrices, 26 deliverables, 8 spikes and a 40-example corpus in a single pass. §15 says build the corpus before freezing the grammar; §8 asks for the syntax sketch in the same breath. Anything answering this in one shot will be uniformly thin, and the anti-handwaving rules make that *worse* — they push toward confident-sounding operational definitions rather than admitted gaps. I split it into five stages with hard stop points, keeping your section numbers.

**2. "Try to falsify this hypothesis" is unenforceable.** You'll get falsification theatre. I replaced it with six pre-registered kill criteria (F1–F6) that must be committed to before the spikes run, each tied to a specific spike and a specific observation. I also added a ninth spike — an adversarial resource test — because F6 (bounded failure under a hostile theory) has no spike in your version.

**3. Three things are inputs, not findings, and their absence makes downstream sections unanswerable:**
- **Target license and distribution model.** If the product is permissively licensed and linkable, GPL-family solvers — much of mature CAS, optimization and quantum chemistry — are forced to subprocess/container. That decides §10's integration modes before any research happens.
- **Named users with real competency questions.** Without them the coverage matrix is bounded by nothing, and the operational definition of "comprehensive" is a sophisticated way of not confronting that.
- **Latency model.** "Orchestrator" implies scheduling, cancellation, partial results and incremental recompute. None of it appears. 10ms vs 10 hours is an architectural input.

**4. No prior art.** This is the largest omission. **Modelica** isn't mentioned once — acausal equation-based declarative modeling with a first-class unit system and DAE index reduction, in production for two decades, and the closest existing thing to your physics/chemistry core. Also absent: **SED-ML and the COMBINE archive** (the existing community answer to "describe a simulation so it replays"), **CWL/Nextflow/Snakemake** (which already solve containerised solver orchestration with provenance — a real chunk of §10 may be re-implementation), Wolfram, KeYmaera X, and the OpenMath/Content MathML and OWL-science-ontology programmes as *failed* universalisms. I added §0.6 requiring a direct answer to "why doesn't this exist, and why is each prior attempt not it."

**5. §12's receipt doesn't defend against §13's threats.** §13 lists cache poisoning and replay-with-different-binaries; a plaintext receipt with no signature, no timestamp, no actor and no schema version detects neither. Either sign it / chain it, or move those threats out of §13 — don't leave them listed and unmitigated.

**6. The result taxonomy mixes three axes into one enum.** `unknown` and `backend_unavailable` aren't alternatives to each other. I split it into verdict (`proved`/`disproved`/`supported`/`refuted`/`conflicting`/`unknown`/`out_of_regime`) × disposition. Two specifics: `invalid` is ambiguous between invalid input, invalid model and invalid inference — split it; and the `disproved`/`refuted` distinction (logical vs. empirical) is implied but never stated, so a researcher can guess wrong.

**Terms your prompt uses undefined, in violation of its own anti-handwaving rule:** *decision-grade, materially different, narrowly adapted, clean* (spike 2), *fail closed*, *semantic fidelity over superficial uniformity*, *semantically misleading spike*, *leakage from Nibli's global vocabulary assumptions*, *trusted computing base* (used without naming the property protected), and *actively maintained* implied by the §11 table. You define "comprehensive" and "auditable" rigorously and then leave nine others floating. I defined all of them in §0.5. Separately, **exact/approximate is a binary in your §10 and §11 tables and shouldn't be** — interval arithmetic, certified numerics and uncharacterised approximation don't fit two buckets. I made it a five-level scale; collapsing "rigorous enclosure" and "error estimate" is the standard failure here.

**Domain gaps worth adding:** genomic coordinates without assembly + base convention + strand (the single most common bioinformatics reproducibility failure — absent entirely); HGNC symbol drift; tautomers and protonation state, plus InChI's actual limits rather than treating it as canonical; CODATA version pinning and the 2019 SI redefinition making some constants exact and others measured; finite fields/modular arithmetic for exact linear algebra and certificate checking; charts and atlases if frames are handled honestly; ISO 80000, Zarr, SPDX.

**The best thing in your prompt is the vertical slice, and it's under-specified.** I supplied numbers designed so that (a) the limiting reagent is genuinely ambiguous at ~1σ, so a system that picks one silently fails; (b) T and P are shared across both gas conversions, making the correlated-uncertainty case bite; (c) ideal-gas deviation for CO₂ is ~0.6%, comparable to the measurement uncertainty, so the silent-approximation rule has teeth; (d) undeclared water vapour is ~3% of pressure, larger than every stated error bar. And I made the **Crabtree effect** explicit rather than accidental: aerobic fermentation in *S. cerevisiae* means the observations should be inconsistent with complete respiration, which is exactly the case where validity regimes, the `disproved`/`refuted` split and non-generalisation all do work simultaneously. Your last negative case gestures at this; it deserves to be the centrepiece.

---

**Remaining disagreement, stated rather than smoothed over:** I don't think the four-domain scope survives contact. Every prior attempt at one formal substrate across mathematics, physics, chemistry and biology either narrowed, degenerated into a taxonomy with no computational semantics, or survived only as a proprietary monolith. The coverage-matrix definition of "comprehensive" is a genuinely good move, but it manages the symptom. I added §0.2 requiring a defence of the scope before any coverage work, with "narrow to one domain pair for v1" as an explicitly acceptable outcome — and added "what evidence would mean not building this at all" alongside your existing "what would overturn the recommendation," since you ask the second and never the first.

# Research prompt — Auditable Scientific Model Compiler and Solver Orchestrator

**Revision 2.** Changes from rev. 1 are marked `[NEW]`, `[CHANGED]` or `[MOVED]` in section headers so the two can be diffed.

---

## 0. How to use this prompt `[NEW]`

This prompt describes a research programme, not a single output. Attempting all deliverables in one pass produces a document that is uniformly shallow and confidently wrong in places — the exact failure the anti-handwaving rules exist to prevent.

Work in five stages. **Stop at the end of each stage and report before continuing.** Do not begin a later stage's work early, even if it seems easy.

| Stage | Covers | Gate before proceeding |
|---|---|---|
| A | §0.1 inputs, §1 product boundary, §2 epistemology, §0.6 prior art | Gate 0 |
| B | §3 shared semantics, §4–§7 domain requirements | Gate 1 |
| C | §8 compiler architecture, §9 Nibli reuse audit + spikes | Gate 2 |
| D | §10 solver protocol, §11 ecosystem, §12 receipts, §13 security | Gates 3, 5 |
| E | §14 vertical slice, §15 verification corpus | Gates 4, 6 |

**Tagging.** Tag every substantive claim inline, at the point it is made, with one of:
`[local-fact]` `[external-fact]` `[inference]` `[proposal]` `[open]` `[evidence-incomplete]`
The evidence ledger is derived from these tags, not written separately. An untagged claim is a defect.

**Budget honesty.** If a section cannot be completed at the depth this prompt demands within the effort available, say so explicitly, state what was covered and what was not, and stop. Do not pad. A short section marked incomplete is worth more than a long one that is uniformly `[inference]`.

**Self-assessment.** End every section with two lines: *Confidence* (high / medium / low, with the reason) and *Largest unverified assumption in this section*.

**Required disagreement.** `[NEW]` Every stage report must contain a section titled **"Where this prompt is wrong."** Argue against the framing, scope, definitions or constraints given here. "Nothing to add" is not an acceptable entry; if you genuinely find no objection, explain what you tested the framing against.

---

## 0.1 Inputs you must have before starting `[NEW]`

These are **constraints on the research, not findings of it**. Rev. 1 left them implicit, which makes several downstream questions unanswerable. If any is unknown, say so at the top of the Stage A report and state the assumption you proceeded under.

1. **Target license of the new product**, and whether it will be distributed as a library, a self-hosted service, a hosted service, or all three.
   This decides §10 and §11 outright. If the product is permissively licensed and distributed as a linkable library, then GPL-family solvers — which includes a large share of mature computer algebra, optimization and quantum-chemistry software — cannot be linked in-process and are forced to subprocess, container or service boundaries. Do not present integration-mode recommendations without this input fixed.
2. **Named users and their jobs.** Three to five real people or roles, each with two competency questions they would actually ask this week. Without these, the capability matrix is bounded by nothing and "comprehensive" reverts to "large."
3. **Interaction and latency model.** Is a query interactive (sub-second to seconds), batch-with-wait (minutes), or a submitted job (hours to days)? This is an architectural input, not a performance detail: it decides in-process vs. job queue vs. distributed scheduler, whether partial results and incremental recomputation are required, and whether caching is an optimization or load-bearing.
4. **Team size and horizon** for the first release.
5. **Schema and ontology governance.** Who curates, publishes, versions and deprecates the scientific vocabularies? A system that fails closed on undeclared vocabulary has a vocabulary supply chain, and that supply chain is a recurring operational cost, not a one-time architecture decision. Name the owner or mark it `[open]` as a first-class product risk.

---

## 1. Role

Act as lead researcher and architect for a scientific-computing platform written primarily in Rust.

The proposed product is an **auditable scientific model compiler and solver orchestrator** with a human-readable, Nibli-KR-like declarative surface, intended to support modeling and computation across mathematics, physics, chemistry and biology through:

- typed declarative knowledge representation;
- exact logical inference;
- symbolic mathematics;
- numerical computation and simulation;
- domain-specific engines;
- empirical data and evidence;
- explicit uncertainty;
- complete provenance and reproducibility receipts.

The existing Nibli engine may be reusable as a component, particularly as a finite logical inference and proof kernel. Determine this from evidence; assume neither reuse nor rejection.

Your task is research and architecture. Do not begin production implementation — with the two exceptions in §0.3.

---

## 0.2 Scope challenge — answer this before anything else `[NEW]`

Every prior attempt at a unified formal representation spanning mathematics, physics, chemistry and biology has either narrowed to one domain, degenerated into a taxonomy with no computational semantics, or survived only as a proprietary monolith. Before defining coverage, produce a defence of the four-domain scope that addresses:

- Which pair of domains generates the most value from being in one system, and how much of the value is lost by shipping only that pair?
- What specifically is different now — in tooling, standards maturity, or user demand — that did not hold for the prior attempts surveyed in §0.6?
- What is the smallest scope for v1 that still requires the architecture you will recommend? If the recommended architecture is not required by that smaller scope, the architecture is over-built.

An acceptable outcome of Stage A is **"narrow to one domain pair for v1."** State this plainly if the evidence supports it.

---

## 0.3 Workspace and evidence boundary `[CHANGED]`

The current Nibli checkout is `/home/dhilipsiva/projects/dhilipsiva/nibli`, running under Ubuntu on WSL2 with tools supplied by its Nix flake.

Before analysis:

1. Read the repository's `AGENTS.md`.
2. Record: repository path; branch; exact commit SHA; dirty worktree state (`git status --porcelain`, verbatim); toolchain versions (`rustc --version`, `cargo --version`, flake lock revision); inspection date.
3. Use native Linux paths.
4. Run repository commands only through the documented Nix development shell.
5. Treat source code and executable tests as stronger evidence than prose. Where prose and code disagree, record both and treat the disagreement as a finding.
6. Do not modify Nibli production code, commit, push, or alter branches.
7. Put feasibility spikes in an isolated temporary workspace and report exactly what was created and executed, including the commands verbatim.
8. Do not inspect the separate book/manuscript checkout unless a specific research question requires it; if it does, state which question and why.

**Citation format for Nibli claims.** `[CHANGED]` Every claim about Nibli must cite `path/to/file.rs:symbol` and, where the claim is behavioural, the name of a test that demonstrates it. Anchor all citations to the recorded commit SHA. "The engine appears to…" without a symbol is not evidence.

Inspect at least: `README.md`, `NIBLI_KR.md`, `LOGIC_IR.md`, `GUARANTEES.md`, `Cargo.toml`, `wit/world.wit`, `nibli-kr`, `nibli-lexicon`, `nibli-semantics`, `nibli-reason`, `nibli-engine`, `nibli-types`, `nibli-protocol`, `nibli-session`, `nibli-store`, `nibli-render`, `nibli-pipeline`, `nibli-host`, `nibli-wasm`, `nibli-verify`, `proofs`, `pins`.

Use primary sources for external systems: official specifications, maintainer documentation, repositories, papers, and license texts. Record exact versions and access dates. Mark unresolved claims `[evidence-incomplete]`.

**Implementation boundary.** `[NEW]` Rev. 1 forbade implementation while requiring eight executed spikes and a forty-example corpus. Resolving that:

- **Spikes are throwaway.** Temporary workspace, deleted after the report, referenced only by transcript.
- **The verification corpus is a durable asset and should be built and kept.** It is specification, not implementation, and per §15 it must exist before the grammar or common IR is frozen.
- **Everything else is forbidden.** No crates, no partial compiler, no plugin runtime.

---

## 0.4 Objective

Produce a decision-grade architecture and execution blueprint answering:

> How should we build a Rust-owned, auditable scientific model compiler and solver orchestrator with a Nibli-KR-like surface, while preserving the distinct semantics of mathematics, physics, chemistry, biology, empirical evidence, uncertainty and numerical computation?

**"Decision-grade"** `[NEW]` means: a technical lead who did not do the research can (a) approve or reject the recommendation, (b) start the first three implementation tasks without asking a follow-up question, and (c) identify which future observation would reverse the decision. Anything that does not serve one of those three is out of scope for the report.

Explicitly decide between at least:

1. Extend or fork Nibli into the shared scientific core.
2. Build a new scientific compiler and use Nibli as one logic backend.
3. Build an independent system with an optional Nibli adapter.
4. Buy or wrap an existing system (see §0.6) rather than building a core at all. `[NEW]`
5. Another materially different architecture if evidence supports it.

**"Materially different"** `[NEW]` means the architectures differ in at least two of: what is inside the trusted computing base; where the semantic authority for units and types lives; the process/memory boundary between compiler and solvers; the ownership of the surface language. Two arrangements of the same components with different box labels are one architecture.

### Leading hypothesis and pre-registered falsification criteria `[CHANGED]`

The hypothesis to test — not assume — is:

> Build a new typed scientific semantic core and use Nibli, unchanged or narrowly adapted, as a `LogicKernel` for finite logical obligations whose semantics match Nibli's guarantees.

Rev. 1 said "try to falsify this hypothesis," which invites falsification theatre. Instead, **commit to these criteria before running the spikes.** The hypothesis is falsified if any one holds:

- **F1.** Introducing a user-defined scientific predicate through a public Nibli API requires editing `nibli-lexicon` or any other Nibli crate source. (Spike 2.)
- **F2.** Nibli's closed-world semantics cannot be scoped to a declared theory snapshot without either (a) changing Nibli's evaluation semantics, or (b) producing an answer that is correct inside Nibli and wrong in the platform's open-world reading. (Spike 4.)
- **F3.** A Nibli proof or proof envelope loses information required by the receipt schema in §12 — specifically, if the assumptions actually used cannot be recovered from the proof object. (Spike 5.)
- **F4.** The compute contract cannot return a structured typed value with units and uncertainty, only Booleans or untyped scalars, and extending it requires forking. (Spikes 6 and 7.)
- **F5.** Round-tripping typed scientific terms through opaque logical identifiers is not injective — two distinct scientific terms collide, or a term cannot be reconstructed from its identifier.
- **F6.** Nibli's resource limits cannot bound a hostile or pathological theory, i.e. a bounded call can still hang or exhaust memory.

**"Narrowly adapted"** `[NEW]` means: changes confined to additive public API surface, no change to evaluation semantics, no change to existing call sites, and upstreamable as a non-breaking minor version. Anything else is a fork; call it a fork.

State, for each F-criterion, the exact observation that would trigger it, before you look.

---

## 0.5 Required definitions

### "Comprehensive"

Not "contains a large vocabulary" and not "has plugins." Define it operationally through a coverage matrix. For every capability, distinguish:

- representable in the surface language;
- statically validated;
- natively evaluated;
- delegated to a typed backend;
- imported as externally trusted evidence;
- planned but unsupported;
- deliberately outside scope.

Bound the matrix by the competency questions from §0.1(2), not by the union of four sciences.

Distinguish at least these workflows: logical derivation; theorem proving; exact symbolic computation; approximate numerical computation; equation and constraint solving; optimization; deterministic simulation; stochastic simulation; parameter estimation; statistical inference; empirical-data lookup; annotation and ontology mapping; model comparison; consistency checking; explanation and provenance.

### "Auditable"

A result is auditable only if the system can identify: the original source statement; its canonical typed representation; schemas, ontologies, models and datasets used; explicit and implicit assumptions; units, frames, conditions and validity regime; chosen execution plan; solver identity and exact version; solver inputs and configuration; proof, certificate, witness, or explicit trusted-computation classification; uncertainty and numerical error model; source and artifact hashes; random seeds and resource limits; warnings, conflicts and unsupported portions; replay instructions.

Provenance alone is not scientific validity. Internal consistency is not empirical confirmation. A numerical result is not automatically a theorem.

### "Fail closed" `[NEW]`

Rev. 1 used this term throughout and defined it only by example. Define it as an observable contract, and hold the design to it:

- No result artifact is emitted at all — not a partial one, not one with a warning field set.
- The error carries a source span, a machine-readable code, and the specific undeclared or ambiguous entity.
- The process exit status distinguishes *rejected input* from *internal error* from *backend unavailable*.
- No default is silently substituted for a missing unit, frame, model, precision, approximation or solver.

State which of the seventeen compiler stages in §8 can fail closed and which cannot, and why.

### "Exact" versus "approximate" `[CHANGED]`

Rev. 1 treats this as a binary in the §10 and §11 tables. It is not. Use a five-level classification and require every solver row to pick one:

1. **Exact** — result is the mathematically correct value in an exact representation (rationals, algebraic numbers, symbolic forms).
2. **Enclosed** — result is a rigorous enclosure that provably contains the true value (interval arithmetic, validated numerics, certified ODE solvers).
3. **Estimated with error model** — approximate, with a defensible quantitative error estimate whose assumptions are stated.
4. **Approximate, uncharacterised** — approximate, no rigorous or defensible error bound.
5. **Opaque** — the backend does not disclose enough to classify it.

Levels 4 and 5 must be visually distinct in every rendered result. Collapsing 2 and 3 is the most common error in this area.

### "Nibli-KR-like"

A surface-design requirement, not a requirement to inherit Nibli's semantics. Investigate retaining: readable predicate calls; named argument places; explicit quantifiers and variables; declarative rules; fail-closed name resolution; deterministic compilation; clear errors; proof-oriented explanations.

Do not assume that Nibli's existing vocabulary, event decomposition, function-free FOL, closed-world semantics, numeric representation or compute interface are suitable as universal scientific semantics.

### "Trusted computing base" `[NEW]`

Rev. 1 asks for a TCB inventory without naming the property being protected. Define the TCB separately for each of these properties, because they have different boundaries:

- **Soundness** — components whose failure could cause a false claim to be reported as `proved` or `supported`.
- **Integrity** — components whose compromise could alter a result or receipt undetectably.
- **Confidentiality** — components with access to private datasets.
- **Availability** — out of scope for v1 unless §0.1(3) says otherwise; state this explicitly.

### "Semantic fidelity" `[NEW]`

Rev. 1's instruction to "prefer semantic fidelity over superficial uniformity" needs a test. Use this one: an encoding loses fidelity if a well-formed operation in the source domain (differentiation of a function, atom-mapping of a reaction, contraction of a tensor index) cannot be expressed as a total, type-checked operation in the IR, but requires either an escape hatch, an untyped string, or a convention enforced only by documentation.

---

## 0.6 Prior art — required before any architecture work `[NEW]`

Rev. 1 surveys components (§11) but never asks whether the product already exists or why prior attempts failed. This is the largest omission. Survey at least the following from primary sources, and for each state: what it does that this product would do; why it is not sufficient; and if it once had wider ambitions, why it narrowed.

**Equation-based declarative modeling**
- Modelica and the Modelica Language Specification; OpenModelica; Dymola. Acausal equation-based modeling with a first-class unit system, DAE index reduction and a large standard library, in production for two decades. This is the closest existing thing to the physics and chemistry core proposed here and rev. 1 does not mention it once. Explain specifically what it lacks — likely provenance, evidence typing and logical inference — and whether extending it is cheaper than building.
- Julia's ModelingToolkit and the SciML ecosystem; Acausal modeling with symbolic-numeric compilation.

**Unified scientific computation**
- Wolfram Language / Mathematica: the existing proprietary answer to "one system across mathematics, physics, chemistry, biology." Its curated data layer is the closest analogue to the "imported database assertion" category. Account for it honestly.
- SageMath as the open aggregation attempt, and what its integration model cost.

**Formal mathematics and physics**
- Lean 4 and mathlib; Isabelle/HOL, including its physical-units and quantity libraries; Coq/Rocq. Determine where the boundary sits between "we state a theorem" and "we prove it."
- KeYmaera X for hybrid-systems verification — the working example of theorem proving applied to physical models.

**Systems biology and reproducible simulation**
- SBML, and critically **SED-ML** (simulation experiment description) and the **COMBINE archive** — omitted from rev. 1's standards list and directly on point, since they are the existing community answer to "describe a simulation so it can be replayed."
- COPASI, PySB, BioModels.

**Workflow, provenance and reproducibility**
- Common Workflow Language, Nextflow, Snakemake, WDL. These already solve orchestration, containerised solver invocation, and provenance capture for exactly the kind of heterogeneous pipeline in §10. Determine what fraction of §10 is a re-implementation.
- W3C PROV, RO-Crate, WholeTale, Nix and Guix as reproducibility substrates.

**Failed universalisms — required** `[NEW]`
- OpenMath and Content MathML as attempts at a universal mathematical interchange semantics; report adoption honestly.
- The Semantic Web / OWL science-ontology programme: substantial investment, limited computational payoff. State what this product does differently, in mechanism, not in aspiration.

Conclude §0.6 with a direct answer to: **"Why does this not exist already, and what is the specific reason each prior attempt is not the answer?"** If the honest answer is "it does exist and is called Modelica plus a provenance layer," say so.

---

## 1. Product boundary

Determine the concrete user jobs the product performs. Answer:

- Is it primarily a modeling language, compiler, theorem prover, scientific notebook, workflow engine, reproducibility system, or orchestrator? Pick one primary identity; the others are secondary or absent.
- What belongs in the first-party Rust core?
- What remains an external domain engine?
- What is inside each TCB from §0.5?
- Which operations must fail closed, per the §0.5 contract?
- What is explicitly outside the first release?
- What does each result status claim, and what does it not claim?

### Result taxonomy `[CHANGED]`

Rev. 1's twelve statuses mix three orthogonal axes into one enum: an epistemic verdict about the claim; a statement about the system's ability to answer; and a numerical outcome. `unknown` and `backend_unavailable` are not alternatives to each other. Restructure as an outcome plus a typed reason:

**Axis 1 — verdict** (what is claimed about the proposition):
- `proved` — established by a checkable proof object under declared axioms.
- `disproved` — its negation is `proved`. Logical, not empirical.
- `supported` — empirical evidence is consistent with it, under a stated model and stated statistical criterion.
- `refuted` — empirical evidence is inconsistent with it, under a stated model and stated statistical criterion. Empirical, not logical. **State the `disproved` / `refuted` distinction explicitly in the report**; rev. 1 implies it but a reader can guess wrong.
- `conflicting` — sourced claims disagree and no resolution policy applies.
- `unknown` — the question is well-formed and in scope, but not settled by available evidence and computation.
- `out_of_regime` `[NEW]` — the question is well-formed, but falls outside the declared validity regime of every applicable model. Distinct from `unknown`: the system knows why it cannot answer.

**Axis 2 — disposition** (why no verdict was produced):
- `invalid_input` — rejected at compile time. Rev. 1's bare `invalid` is ambiguous between invalid input, invalid model and invalid inference; split it.
- `invalid_model` — the model itself failed validation (unbalanced reaction, dimensional inconsistency, unsatisfiable constraints).
- `unsupported` — representable but not evaluable by this system; names the missing capability.
- `resource_exhausted` — hit a declared budget; names which one.
- `backend_unavailable` — the required solver could not be reached; names it and its version constraint.
- `non_convergent` — the numerical method failed to converge; reports the residual and iteration count.
- `numerically_indeterminate` — converged, but the result is not distinguishable from an alternative within the error model.

Do not conflate: absence with negation; `FALSE` with scientific impossibility; unsupported with unknown; solver failure with a negative result; model inconsistency with empirical falsification.

---

## 2. Scientific epistemology and evidence

Keep these categories structurally distinct: definition; axiom; theorem; hypothesis; model law; assumption; approximation; observation; measurement; imported database assertion; dataset; logically derived result; exact computed result; approximate computed result; simulation result; statistical inference; expert annotation; external citation.

Determine:

- how conflicting sourced claims coexist;
- how theories and contexts isolate contradictions;
- whether any paraconsistent behaviour is needed, and if so where the boundary of the paraconsistent region sits;
- how claims change across schema, model and dataset versions;
- how model applicability is represented;
- how a claim records organism, tissue, strain, frame, time, pressure, temperature, protocol or other relevant context;
- how closure is explicitly declared for a complete finite relation;
- how open-world semantics remain the default for empirical science;
- **who is permitted to declare closure, and what stops a wrong closure declaration from silently producing false negatives.** `[NEW]` This is an authoring-side integrity question, not a security one, and rev. 1 does not ask it.

Separate, and do not collapse into a single confidence score: logical truth status; measurement uncertainty; numerical error; stochastic variability; parameter uncertainty; structural/model uncertainty; source or evidence quality.

**Also decide:** `[NEW]` are large language models in scope anywhere in this system — literature extraction, schema suggestion, natural-language query? Rev. 1 forbids LLM output becoming evidence without deterministic validation but never says whether LLMs are present at all. Decide it; if they are in scope, they need a trust tier in §10 and a validation rule.

---

## 3. Shared semantics and domain-specific semantics

Determine whether the system uses: one universal IR; one shared semantic envelope containing several domain IRs; a small common claim/evidence model plus independently typed obligation languages; or another design.

Apply the §0.5 fidelity test rather than a general preference.

Evaluate the common layer for: user-defined types and sorts; namespaced identifiers; relations; typed functions; constants and variables; quantifiers and binders; equations and inequalities; exact and approximate equality; assumptions and theory scopes; units and physical dimensions; contexts and validity regimes; evidence and provenance; artifact references; query and solver obligations.

Do not encode functions, equations, tensors or molecular graphs as generic predicates merely to preserve a single IR.

---

## 4. Mathematics requirements `[CHANGED]`

Research the minimum representations needed for:

- integers, rationals, algebraic numbers;
- **arbitrary-precision rationals distinct from arbitrary-precision floating point** (MPFR-style), with the rounding mode and precision as part of the type, not a global setting;
- **modular arithmetic and finite fields** `[NEW]` — required for fraction-free and modular exact linear algebra, and for several certificate-checking schemes; omitted from rev. 1;
- intervals and validated numerics;
- complex numbers;
- symbolic expressions;
- functions and binders;
- sets and sequences;
- equations and inequalities;
- sums, products, limits, derivatives, integrals;
- matrices, tensors and linear operators;
- algebraic structures;
- rewrite systems;
- constraint solving;
- theorem statements and proof terms.

Determine where first-order logic suffices and where higher-order or dependent-type reasoning becomes necessary. Be specific: name the competency question that first requires it.

Compare: native exact arithmetic; SMT integration; proof-assistant integration; computer-algebra systems; independently checkable certificates; opaque symbolic-computation backends.

A broad mathematical language must not pretend that Nibli's existing logical fragment covers modern mathematics. State plainly which fragment it does cover.

---

## 5. Physics requirements `[CHANGED]`

Research representations for: dimensioned quantities; affine and logarithmic units; vectors, tensors and spinors; **manifolds, charts and atlases** `[NEW]` (if coordinate systems and frames are to be handled honestly, charts are the correct representation and "coordinate system" is a fixed-chart special case); **differential forms** `[NEW]`; coordinate systems and reference frames; transformations; states and observables; systems and subsystems; spacetime events; fields; symmetries and representations; equations of motion; initial and boundary conditions; approximation regimes; classical, quantum, statistical and continuum models; ODE, PDE and stochastic simulation; parameter scale and renormalization scheme where applicable.

**Physical constants** `[NEW]`: constants are versioned sourced evidence, not literals. Pin the CODATA release explicitly and treat a CODATA version change as a cache-invalidating input. Distinguish exactly-defined SI constants from measured ones with uncertainty — the 2019 SI redefinition made several exact, and code that treats them uniformly is wrong.

Determine what can be: statically validated; symbolically transformed; exactly solved; numerically solved; delegated to specialised physics software; represented only as imported evidence.

---

## 6. Chemistry requirements `[CHANGED]`

Research representations for: elements and isotopes; atoms and formal charge; molecular graphs; bond types and aromaticity; stereochemistry; **tautomers and protonation state** `[NEW]`; chemical species versus molecule instances; substances, mixtures and phases; reactions and atom mapping; exact stoichiometry; catalysts and conditions; equilibrium; kinetics; thermodynamics; spectra; quantum-chemistry calculations; provenance of measured chemical properties.

Determine which chemical identity and interchange standards to support, and whether each is a canonical identifier, an import format, or a presentation form.

**Do not treat InChI as unconditionally canonical.** `[NEW]` Account explicitly for its known limits — tautomer normalisation behaviour, stereo-layer coverage, and the standard-versus-non-standard distinction. Aromaticity perception differs between toolkits and is a live source of identity disagreement; state which perception model is normative and what happens when two importers disagree. This is what the "ambiguous chemical identity" negative case in §14 must actually exercise.

---

## 7. Biology requirements `[CHANGED]`

Research representations for: sequences and sequence features; genes, transcripts and proteins as distinct entities; variants and haplotypes; molecular complexes; cells, tissues, organs and organisms; taxonomy; strains and cell lines; pathways and interaction networks; genotype and phenotype; homology; development and spatial context; populations and cohorts; assays and experimental protocols; statistical and bioinformatics workflows.

**Reference and coordinate versioning** `[NEW]` — omitted from rev. 1 and the single most common reproducibility failure in bioinformatics. Any genomic coordinate is meaningless without: assembly (GRCh37 / GRCh38 / T2T-CHM13), coordinate base (0-based half-open vs. 1-based inclusive), and strand. Make these mandatory components of the type, not annotations. A coordinate without an assembly must fail closed.

**Identifier instability** `[NEW]` — HGNC gene symbols are renamed, Ensembl and RefSeq identifiers are versioned and retired, and taxonomy identifiers are merged. Decide whether the system pins versioned accessions, resolves symbols at compile time and records the resolution, or refuses symbols entirely. This is the biological analogue of the ontology-version negative case and should appear in §14.

Biological rules are often contextual, statistical, defeasible and exception-rich. Do not default them to universal exact implications.

Large sequences, alignments, images and datasets should normally be external typed artifacts referenced by the KR, not millions of logical facts. State the threshold and the mechanism.

---

## 8. Language and compiler architecture

Specify the required stages and their invariants: parsing with complete source spans; syntax version detection; namespace and import resolution; schema and ontology resolution; type and shape inference; unit and dimension checking; context and validity-regime validation; desugaring; canonicalization; capability analysis; lowering to logical, symbolic, numeric or domain obligations; execution-plan construction; solver invocation; result validation; provenance-DAG construction; result rendering; receipt generation.

For each stage state: its input type; its output type; the invariant it establishes; whether it can fail closed per §0.5; and what a downstream stage may therefore assume.

Research syntax only after stabilising semantics. Produce a provisional syntax sketch covering: schema and namespace declarations; types; relations; functions; quantities and units; equations; observations; assumptions; models and validity conditions; data and artifact references; rules; queries; explicit closure declarations; solver or trust policies where unavoidable.

Show accepted and rejected syntax. Show how at least three representative source statements lower through every stage — one from the vertical slice in §14, one mathematical, one biological with a versioned coordinate.

**Sequencing note.** `[CHANGED]` §15 requires the verification corpus before the grammar is frozen. The syntax produced here is a *sketch to be attacked by the corpus*, explicitly not a candidate for freezing. Say so in the deliverable.

---

## 9. Nibli reuse audit

Inspect current code, tests and public interfaces. Audit separately: parser and executable grammar; lexicon and name resolution; AST; semantic compiler; logical IR; event decomposition; equality; quantifiers; negation and stratification; closed-world and closed-domain behaviour; rule indexing and materialisation; proof traces and proof envelopes; query, find, count and aggregate APIs; compute dispatch; session state; persistence; retraction; resource limits; WIT/component boundary; Wasmtime host; browser/WASM surfaces; native embedding API; testing, differential oracles and Lean proofs; packaging, API stability and licensing.

For every candidate asset produce a row of:

| Asset | File:symbol @ commit | Test evidence | Current contract | Scientific requirement | Gap | Reuse mode | Coupling risk | Required spike | Decision |
|---|---|---|---|---|---|---|---|---|---|

`[CHANGED]` Every row needs a file-and-symbol citation; every behavioural claim in "Current contract" needs a named test. A row without both is `[evidence-incomplete]` and cannot support a reuse decision.

Reuse dispositions: reuse unchanged; wrap behind stable adapter; extract and generalize; fork; reuse testing or architectural patterns only; reject.

Test whether Nibli can safely act as a `LogicKernel` with: a declared finite theory snapshot; explicitly scoped closed-world semantics; custom scientific predicates; no leakage from Nibli's global vocabulary assumptions; typed terms lowered into opaque but stable logical identifiers; proof results convertible into the platform's evidence graph; deterministic replay; resource-bounded failure; no authority to inject arbitrary scientific claims.

**"No leakage" needs an observable test.** `[NEW]` Propose one before the spike. Suggested form: construct two theory snapshots that share a predicate name but nothing else, evaluate a query against each in the same process, and assert the results are identical to evaluating each in a fresh process. If they differ, leakage exists.

### Spikes `[CHANGED]`

Each spike must state, before running: its hypothesis; the exact commands; the observation that counts as success; the observation that triggers an F-criterion from §0.4.

1. Embed `nibli-engine` unchanged and execute a finite classification rule.
2. Attempt user-defined scientific vocabulary through current text APIs. **"Clean" means: no edits to Nibli crate source; no reliance on undocumented behaviour; no string escapes to smuggle structure through a name.** `[NEW]`
3. Compare text, raw-IR and imported-fact paths on the same input; report semantic and performance differences.
4. Determine whether open-world behaviour can be layered outside Nibli without falsifying its results.
5. Convert a Nibli proof or proof envelope into the proposed evidence format; report exactly what is lost.
6. Route a grounded external computation through the current compute contract.
7. Identify changes required for structured outputs rather than Boolean checks.
8. Evaluate whether a WIT component boundary suffices or native embedding is required.
9. **`[NEW]` Adversarial resource test.** Feed a pathological theory (deep recursion, large cross-product, wide arity) under a declared limit and confirm bounded failure rather than hang or OOM. This is F6 and rev. 1 has no spike for it.

**"Semantically misleading spike"** `[NEW]` means: the spike returns a success signal while the underlying semantics differ from what the platform requires — typically a closed-world answer that reads as an open-world one, or a `FALSE` that means "not derivable" being consumed as "known false." A misleading spike is stronger evidence against reuse than a failing one, because it will not be caught later.

---

## 10. Solver orchestration

Define a typed solver protocol.

**Capability declaration:** supported obligation language and version; accepted input and output schemas; the §0.5 exact/approximate level; soundness or validation claims; certificate support; determinism limitations; supported numeric types and precision; unit and uncertainty support; platform and resource requirements; security and sandbox requirements.

**Request:** canonical obligation; theory/model snapshot; typed input values; assumptions; units and contexts; required precision or tolerance; resource budget; random seed; trust policy; expected output schema.

**Response:** status (per §1's two axes); typed outputs; proof, certificate or witness; uncertainty and error estimate; assumptions actually used; approximations applied; warnings; partial or unsupported portions; solver identity and version; executable or container hash; input snapshot hash; timing and resource consumption; replay information.

A solver must not invent undeclared claim types. Returned claims must conform to schemas declared before invocation.

### Trust tiers `[CHANGED]`

Rev. 1's list conflates *how strongly a result was verified* with *what kind of thing it is*. "Imported empirical evidence" is not a verification tier of a computation. Use two axes:

**Verification strength:** kernel-checked proof; independently checkable certificate; differentially verified across independent implementations; deterministic trusted computation; stochastic trusted computation (seeded); unverified assertion.

**Evidence provenance:** derived internally; computed by a declared external solver; imported from a versioned database; asserted by a named human expert; extracted by a non-deterministic process (including any LLM, per §2).

A result carries one value on each axis. A database import is `unverified assertion × imported from versioned database` — which is a perfectly respectable position and is not the same as an unverified internal computation.

### Boundaries

Research native Rust, C ABI, subprocess, WIT/WASI component, container and service boundaries against the license constraint from §0.1(1). Do not use Rust's unstable dynamic-library ABI as the public plugin contract.

Rust owns the compiler, validation, planning, evidence and trust boundary. Do not require mature scientific solvers to be rewritten in Rust, and do not describe wrapped external solvers as Rust components.

**Scheduling.** `[NEW]` Per §0.1(3), state whether obligations are executed synchronously, queued, or distributed; whether partial results are surfaced; and whether an obligation can be cancelled. "Orchestrator" without a scheduling model is a name, not a design.

---

## 11. External ecosystem and standards survey `[CHANGED]`

Evaluate candidates from primary sources for: theorem proving and proof checking; SMT; computer algebra; exact and interval arithmetic; linear algebra; optimization; numerical integration; ODE/PDE solving; stochastic simulation; uncertainty propagation; units and dimensional analysis; molecular graphs and cheminformatics; chemical reaction formats; thermodynamics and kinetics; sequence and variant processing; biological ontologies; pathway and systems-biology models; columnar scientific data and large artifact storage; provenance and reproducibility metadata.

Standards to assess, including but not limited to: SI and UCUM; **ISO 80000** `[NEW]`; QUDT; SMT-LIB; OpenMath and Content MathML; InChI, RInChI and common molecular formats; OBO, OWL/RDF, SBML, **SED-ML**, **COMBINE archive** `[NEW]`, SBGN, BioPAX; FASTA, VCF and **the reference-assembly registry** `[NEW]`; W3C PROV, RO-Crate, **DataCite and FAIR** `[NEW]`; Arrow, Parquet, HDF5, NetCDF, **Zarr** `[NEW]`; **SPDX** `[NEW]` for machine-readable licensing given §0.1(1); WIT/WASI.

Determine each standard's proper role, semantic fit, license, versioning model and implementation burden. Do not assume adoption.

| Capability | Candidate/version | Language | Integration mode | Exact/approx level (§0.5) | Certificate | Determinism limits | WASM suitability | License + SPDX id | Maintenance evidence | Decision |
|---|---|---|---|---|---|---|---|---|---|---|

**Maintenance evidence** `[NEW]` means observable facts: date of last release, commit frequency over 24 months, number of distinct committers, and whether a security policy exists. Not "actively maintained."

Do not recommend a Rust crate merely because it is written in Rust.

---

## 12. Audit receipts and reproducibility `[CHANGED]`

Define an immutable execution receipt containing: **receipt schema version** `[NEW]`; source hash; canonical-IR hash; compiler version; schema and ontology versions; dataset and artifact hashes; model-package version; assumptions; closure and trust policies; units, frames and environmental conditions; execution plan; rejected plan alternatives; solver identities and versions; solver binary, package or container hashes; exact inputs and outputs; proof, certificate, witness or trust classification (both axes, §10); numerical tolerances; **tolerance bounds declared before execution** `[NEW]`; precision and rounding mode; uncertainty model; random seeds; platform information; resource limits; warnings and conflicts; citations; replay command or procedure; **wall-clock timestamp and clock source** `[NEW]`; **actor identity, if the system is multi-user** `[NEW]`.

**Integrity.** `[NEW]` Rev. 1's receipt does not defend against rev. 1's own threat model. §13 lists cache poisoning and replay-with-different-binaries; a plain-text receipt with no signature detects neither. Decide and justify: is the receipt signed? Is there an append-only log or transparency mechanism? Is the hash chain over the provenance DAG or only over leaf artifacts? If the answer is "the receipt is advisory and integrity is out of scope for v1," state that explicitly and remove the corresponding threats from §13 rather than leaving them unmitigated.

State precisely what the receipt proves and what it does not.

**Cache keys and invalidation.** Any change to a semantic input, schema, model, dataset, solver version, numeric policy or trust policy must invalidate affected results. Specify: what is in the key; how transitive invalidation propagates through the provenance DAG; and what happens to a cached result whose solver version is no longer obtainable.

**Floating-point reproducibility.** `[CHANGED]` Gate 6 in rev. 1 permits "explicitly justified numerical bounds," which invites post-hoc justification. Bounds must be declared in the receipt *before* execution and the replay test compares against the declared bound. A replay that stays within a bound invented after seeing the result is not a passing replay.

---

## 13. Security and trust-boundary research `[CHANGED]`

Threat model covering: malicious or compromised solver plugins; malformed model files; adversarial datasets; arbitrary claim injection; command and argument injection through process adapters; unsafe FFI; path traversal and artifact replacement; resource exhaustion; solver nontermination; network access; untrusted deserialization; supply-chain compromise; malicious ontology imports; cache poisoning; replay with different binaries; leakage of private datasets.

Add: `[NEW]`

- **Honest-but-buggy solver.** A solver that returns plausible, wrong results without malice. This is the highest-probability threat in the list and rev. 1 addresses it only implicitly through differential testing. Give it an explicit mitigation and state its cost.
- **Authoring-side integrity.** A legitimate user declaring a false closure, an unsound assumption, or a mis-scoped validity regime. Not adversarial, and not preventable by sandboxing; determine whether review, signing or provenance display is the answer.

For each threat state: the asset, the attacker capability assumed, the mitigation, the residual risk, and which of the four TCBs in §0.5 the mitigation lives in.

Define which components require sandboxing and whether WASI, processes, containers or remote services provide the necessary boundary — noting that WASI's boundary is memory-safety-plus-capability, not resource-limit enforcement, and that a hostile solver's nontermination is a scheduler problem, not a sandbox problem.

---

## 14. Required cross-domain vertical slice `[CHANGED]`

Rev. 1 states the scenario but supplies no numbers, so the negative cases have no bite. Use the following worked scenario. **Verify the arithmetic yourself and adjust as needed, but preserve the intended epistemic structure noted after each value.**

### Declared model

`complete_aerobic_respiration`: C₆H₁₂O₆ + 6 O₂ → 6 CO₂ + 6 H₂O

### Measured inputs

| Quantity | Value | Note |
|---|---|---|
| Glucose supplied | 1.80 ± 0.02 g | M = 180.156 g/mol → 9.99 ± 0.11 mmol |
| O₂ supplied | 1.50 ± 0.03 L | measured at stated T, P |
| Temperature | 298.15 ± 0.5 K | shared between all gas conversions |
| Pressure | 101.325 ± 0.5 kPa | shared between all gas conversions |
| CO₂ evolved (observed) | 0.95 ± 0.02 L | at same T, P |
| O₂ consumed (observed) | 24 ± 1 mmol | |

### Four properties this scenario is designed to exercise

1. **The limiting reagent is genuinely ambiguous.** O₂ supplied ≈ 61.3 ± 1.2 mmol; O₂ required by the model ≈ 59.9 ± 0.7 mmol. These overlap at roughly one standard deviation. The correct output is not "glucose is limiting" — it is a statement that the determination is not resolved at the stated uncertainty, with the margin reported. A system that picks one silently has failed.
2. **T and P are correlated across conversions.** Both the O₂ and the CO₂ volume-to-moles conversions use the same T and P. Treating them as independent misstates the uncertainty on the respiratory quotient. This is the concrete instance of rev. 1's "correlated uncertainty incorrectly treated as independent" case.
3. **The ideal-gas assumption is a quantifiable error, not a formality.** For CO₂ at 298 K and 101 kPa the compressibility factor is roughly 0.994 — a ~0.6% deviation, comparable to the stated measurement uncertainties. Silently selecting ideal-gas behaviour introduces an error of the same magnitude as the thing being measured. This is the concrete instance of "do not silently select an approximation."
4. **Missing context is quantitatively fatal.** Saturated water vapour at 298.15 K contributes roughly 3.2 kPa — about 3% of total pressure, larger than every stated uncertainty. If the model does not declare whether gas volumes are dry or water-saturated, the result is wrong by more than its error bars. This is what "missing required context must fail closed" actually protects against.

### The epistemically interesting outcome `[NEW]`

The observations are **inconsistent** with complete aerobic respiration. Predicted CO₂ under the model is roughly 1.47 ± 0.02 L against 0.95 ± 0.02 L observed, and predicted O₂ consumption roughly 59.9 mmol against 24 mmol observed.

The scientifically correct conclusion is *not* that respiration is false. *S. cerevisiae* exhibits the **Crabtree effect** — aerobic fermentation at high glucose concentration, producing ethanol and CO₂ through a route the declared model does not contain. The correct verdict is `refuted` for *this model under these conditions*, with a warning that the declared model's validity regime (low glucose) may not have been met, and explicitly **not** a universal biological claim.

Rev. 1 gestured at this in its final negative case. Make it the centrepiece: it is the best thing in the scenario, because it is the case where provenance, validity regimes and the `disproved`/`refuted` distinction all do real work simultaneously.

### The slice must exercise

Mathematics (exact linear balancing, correlated uncertainty arithmetic); physics (units, dimensions, gas-law conversion, CODATA-pinned R); chemistry (composition, atom and charge conservation, stoichiometry); biology (organism, strain, metabolic regime, environmental context); logic (consequences under an explicitly declared model); evidence (measured inputs and sourced constants); orchestration (at least two distinct solver capabilities); auditability (a complete replayable receipt).

### Required negative cases

Dimensionally invalid input; unbalanced reaction; undeclared predicate or type; ambiguous chemical identity (use a tautomer or aromaticity-perception disagreement, per §6); missing pressure or temperature; missing water-vapour declaration; missing model assumption; incompatible ontology version; **genomic coordinate without an assembly, and a renamed gene symbol** `[NEW]`, per §7; correlated uncertainty incorrectly treated as independent; conflicting measurements; unavailable solver; solver timeout; numerical non-convergence; stale cache after a solver-version change; untrusted solver attempting to inject a new claim; **cached result whose solver version can no longer be obtained** `[NEW]`; observation inconsistent with this model but not falsely generalized into a universal biological conclusion.

---

## 15. Verification strategy

Build at least: 20 accepted examples; 20 fail-closed or rejection examples; one complete cross-domain vertical slice.

Require: parser fuzzing; round-trip tests; type, shape and dimension property tests; metamorphic tests; differential tests against independent solvers; certificate-checker tests; golden execution-receipt tests; deterministic-replay tests; cache-invalidation tests; adapter fault injection; backend disagreement tests; resource-exhaustion tests; corrupted-artifact tests.

Develop this corpus before freezing the surface grammar or common IR. Per §0.3 it is a durable asset, not a spike.

**`[NEW]`** For each rejection example, record the expected error code and the expected source span. A rejection test that only asserts "an error occurred" does not test fail-closed behaviour.

---

## Research methodology

1. Establish the §0.1 inputs, or record the assumptions used in their place.
2. Establish local Nibli provenance.
3. Survey prior art (§0.6) and answer the "why does this not exist" question.
4. Answer the scope challenge (§0.2).
5. Define coverage levels and user competency questions.
6. Build accepted and rejected examples.
7. Inspect Nibli's actual implementation and tests.
8. Survey external systems from primary sources.
9. Develop at least three materially different architectures, per §0.4's definition.
10. Define concrete data contracts for every architectural arrow.
11. Run minimal isolated spikes where documentation is insufficient, with pre-declared success and F-criteria.
12. Attack each architecture using the hardest examples.
13. Tag every conclusion inline per §0.
14. Build a requirement → design → test traceability matrix.
15. Make a recommendation and state what evidence would overturn it — both the architecture recommendation and the build/don't-build recommendation.

Parallel domain research is encouraged; one lead architect integrates and resolves semantic conflicts.

---

## Deliverables

Grouped by stage. Produce each stage's deliverables and stop.

**Stage A** — §0.1 input record or assumptions; prior-art survey and the "why does this not exist" answer; scope defence or narrowing recommendation; product promise and non-goals; operational definition of comprehensive coverage; capability matrix bounded by competency questions; epistemology and two-axis result taxonomy.

**Stage B** — shared semantic-envelope proposal; domain-IR boundaries; per-domain requirement analyses (§4–§7); fidelity-test results for the proposed encoding.

**Stage C** — compiler pipeline and per-stage invariants; provisional syntax sketch with accepted and rejected examples; three worked lowerings; Nibli reuse audit with file, symbol and test evidence; spike results including F-criteria outcomes; Rust crate/module decomposition.

**Stage D** — solver capability, request, response and failure schemas; two-axis trust model; external ecosystem and standards comparison; four TCB inventories; security threat model; complete audit-receipt schema with a worked example and an integrity decision.

**Stage E** — cross-domain vertical-slice specification; accepted and rejected verification corpus; phased implementation dependency graph; ten initial implementation tasks in dependency order with exit criteria; risk register; ADRs for expensive or irreversible choices; unresolved questions and experiments; derived evidence ledger.

**Every stage** — executive summary, confidence self-assessment, and the "Where this prompt is wrong" section.

Use Rust traits or data-structure sketches where they eliminate ambiguity; label all pseudocode provisional.

---

## Decision gates

For every gate state: required evidence; measurable pass/fail criteria; consequence of failure; work that must not begin before passage.

**Gate 0 — Scope coherence.** Pass only if: comprehensive has a bounded capability matrix tied to named competency questions; non-goals are explicit; the two-axis result taxonomy is complete; and the four-domain scope has been defended or narrowed.

**Gate 1 — Semantic viability.** Pass only if representative cross-domain cases can be represented without semantic overloading or lost context, judged by the §0.5 fidelity test.

**Gate 2 — Nibli reuse.** Pass only if the disposition is supported by code-level evidence with file:symbol citations and by spikes whose F-criteria were declared in advance. Outcomes remain: embed unchanged; wrap; extract/generalize; fork; patterns only; reject.

**Gate 3 — Solver protocol.** Pass only if the protocol distinguishes formal proof; exact computation; enclosed computation; estimated computation with error model; uncharacterised approximation; simulation; statistical inference; empirical evidence; opaque trusted output — on both trust axes.

**Gate 4 — Vertical slice.** Pass only if the yeast scenario runs end-to-end, emits a complete replayable receipt, **reports the limiting-reagent ambiguity rather than resolving it silently**, and returns `refuted`-for-this-model without generalizing.

**Gate 5 — Extensibility.** Pass only if a materially different solver can be added without modifying unrelated compiler semantics or hard-coding a domain route. Demonstrate with a specific second solver, not an argument.

**Gate 6 — Reproducibility.** Pass only if pinned re-execution reproduces exact results, or stays within numerical bounds **declared in the receipt before execution**.

**Gate 7 — Expansion.** Do not expand domain coverage until earlier gates pass.

---

## Anti-handwaving rules

Do not use these terms without operational definitions and evidence: comprehensive; supports; integrates; deterministic; auditable; reproducible; verified; safe; scalable; extensible; interoperable; **decision-grade; materially different; narrowly adapted; clean; fail closed; semantic fidelity; leakage; actively maintained** `[NEW]` — all of which rev. 1 used undefined and §0.5 now defines.

Additionally:

- Every architectural arrow needs a typed data contract and failure semantics.
- Every solver result must declare what is trusted, on both axes.
- Do not call a result a proof without a checkable proof object or certificate.
- Do not claim floating-point determinism without specifying platform, implementation, reduction order and tolerance.
- Do not claim reproducibility without an executable replay procedure.
- Do not hide unsupported operations behind a generic plugin interface.
- Do not confuse unit checking with uncertainty propagation.
- Do not confuse independent uncertainty with correlated uncertainty. `[NEW]`
- Do not confuse a rigorous enclosure with an error estimate. `[NEW]`
- Do not confuse provenance with correctness.
- Do not confuse provenance with integrity — a receipt nobody can verify is documentation. `[NEW]`
- Do not confuse model consistency with empirical confirmation.
- Do not silently select an approximation, model, solver, unit convention, reference assembly or coordinate base. `[NEW]`
- Do not allow LLM output to become scientific evidence without deterministic validation, and state whether LLMs are in scope at all.
- Do not require every external solver to be rewritten in Rust.
- Do not claim external solvers are Rust components; describe the Rust-owned boundary accurately.
- Do not invent benchmarks, schedules or performance figures.
- Every Nibli claim requires file:symbol at a recorded commit, plus a named test for behavioural claims.
- Every external claim requires a primary source with version and access date.
- Mark insufficient evidence `[evidence-incomplete]` and do not reason onward from it without saying so.

---

## Final acceptance test

A skeptical technical reader must be able to answer:

- What exactly does the product promise?
- What does it explicitly refuse?
- **Why does this not already exist, and why is Modelica / Wolfram / SBML+SED-ML / CWL not the answer?** `[NEW]`
- What does "comprehensive" mean operationally, and what bounds the matrix?
- Which semantics are shared? Which remain domain-specific?
- Which Nibli code is reused, through what stable boundary, and why is that reuse semantically safe?
- **Which pre-declared falsification criterion came closest to firing?** `[NEW]`
- How does a source statement become a solver request?
- Why was a particular solver selected — and what license constraint shaped that choice? `[NEW]`
- What is inside each of the four trusted computing bases?
- What does a returned result establish, and what does it not?
- How are unknown, out-of-regime, unsupported, failed and conflicting results distinguished?
- How is an execution reproduced, and how would anyone detect a forged receipt? `[NEW]`
- **What does a typical query cost, in wall-clock time and in compute?** `[NEW]`
- **Who maintains the domain schemas in year three, and what does that cost?** `[NEW]`
- What is the smallest defensible implementation sequence?
- What evidence would change the architecture recommendation — and what evidence would mean not building this at all? `[NEW]`

If any answer depends on "the plugin handles it," "the system supports it," or another undefined abstraction, the research is incomplete.
