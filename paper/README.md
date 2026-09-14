# Nibli research artifact

This directory contains the paper **Nibli: Auditable Symbolic Reasoning with
Bounded Evaluation and Retractable Premises**, its experiment sources, and the
observations used to generate its quantitative claims. The draft author is
**dhilipsiva**; no affiliation is asserted. The proposed arXiv category is
**cs.AI**. Submission and endorsement contact are outside this artifact.

Start with [the paper](nibli-paper.pdf). [counts.json](generated/counts.json)
gives the outcome totals; [summary.csv](generated/summary.csv) gives every
aggregate cell, including cutoffs and definitive coverage.
[claims.json](research/claims.json) maps claims to their evidence and
states the boundaries of that evidence.

## Environment and baseline

The engine baseline is `158e3b0cdeeb09d26ae9e87dd3d5487ab945c2ca` in
[dhilipsiva/nibli](https://github.com/dhilipsiva/nibli). The artifact adds a
private benchmark binary, a paper shell, recipes, and research files. It makes
no changes to engine algorithms or WIT interfaces. The measured source identity
is the complete content fingerprint in `protocol.freeze.json`, together with
the benchmark executable hash. This is a recorded working-tree revision, not
an invented Git commit. `Cargo.lock` and `flake.lock` fix the dependency inputs.

Run commands from the engine repository root, inside the Nix paper shell:

```sh
nix develop --extra-experimental-features nix-command \
  --extra-experimental-features flakes .#paper
```

The shell includes the ordinary engine verification tools, compiled Soufflé,
wasm-pack, GNU time, LaTeX, and Python plotting dependencies. The initial Nix
and Cargo fetches require network access. Measured executions use local inputs
and no external compute backend. The recorded machine, WSL2 kernel, visible
memory, CPU affinity, runtime versions, executable paths, and release profile
are in `results/evaluation/environment.json`. No exclusive CPU reservation or
control over the Windows host's background activity is claimed.

## Rebuild the paper from archived observations

```sh
just paper-build
just paper-package
```

`paper-build` checks the completed observation ledger, regenerates CSV data,
tables, and figures, audits certificate source citations, and builds the PDF
twice in clean directories. It requires identical PDF bytes, resolved
references, no overfull boxes, and 12–15 pages of main text. References and
appendices follow the main text. The report is `build/build-report.json`.

`paper-package` also verifies the upload sources in a clean extraction. Its
outputs are `dist/nibli-arxiv-source.tar.gz` and
`dist/nibli-research-artifact.tar.gz`, with SHA-256 manifests. The first is a
typesetting bundle, not an upload or a submission. `dist/submission-metadata.json`
contains the title, author, category, and expanded abstract. The abstract uses
ASCII with supported accent notation and is checked against the 1,920-character
limit in [arXiv's metadata instructions](https://info.arxiv.org/help/prep.html).
The second archive is an overlay
for the exact engine baseline and contains input snapshots, raw observations,
proof envelopes, persistent snapshots, and reproduction instructions.

## Required checks and the pilot

```sh
just paper-check
just paper-smoke
python3 paper/scripts/run.py freeze
```

The default output directories already contain the archived evidence.
`paper-smoke` and evaluation refuse to overwrite existing output. To run an
additional pilot without changing the frozen record:

```sh
just paper-driver
python3 paper/scripts/run.py smoke --output paper/results/local-pilot
python3 paper/scripts/run.py check --output paper/results/local-checks
```

The checks require the solvers, Lean, persistence tests, and WebAssembly tools
to be present. Required missing-tool skips fail the check. Native reasoner and
engine integration suites, the existing differential soundness and compiler
seam gates, adjudication pins, persistence gates, and the complete Wasmtime/Node
gate are run. `results/checks/checks.json` records the exact commands and log
paths. Some repository tests are ordinarily marked ignored; the required host
smoke recipes explicitly invoke their ignored integration tests. The report
does not claim every optional repository test ran.

The pilot validates each adapter with hand-derived positive and negative
cases, both reachability directions, policy support alternatives, and a
persistent update sequence. The protocol was frozen only after a successful
pilot of the exact source and executable. `research/harness-history.md`
records the harness corrections made before that freeze.

## Collect a new result series

When the rebuilt executable has the same hash as the original freeze:

```sh
python3 paper/scripts/run.py evaluate --output paper/results/local-evaluation
python3 paper/scripts/analyze.py --results paper/results/local-evaluation \
  --output paper/generated-local
```

This uses the frozen matrix and refuses an existing output directory. A build
on another machine or checkout path can have different executable bytes. In
that case, preserve the original freeze and create a new one after a new pilot:

```sh
mv paper/protocol.freeze.json paper/protocol.original.freeze.json
python3 paper/scripts/run.py freeze --smoke paper/results/local-pilot/smoke.json
python3 paper/scripts/run.py evaluate --output paper/results/local-evaluation
```

Do this in a separate reproduction checkout. Keep both freezes; never describe
a modified binary or protocol as the original experiment. A change affecting
correctness requires a new source identity and rerunning affected experiments.

The default analysis recipe reads `results/evaluation/` and writes
`generated/`. Explicit `--results` and `--output` arguments let a reproduction
coexist with the archived series. Raw log paths are relative to the repository
and should retain their original locations. Keep the original artifact archive
for rebuilding the published PDF. A new run is expected to produce different
timings and will produce a new PDF if used for typesetting.

Performance runs execute serially. Preparation and C++ compilation finish
before the timed schedule. Keep other builds, test suites, and resource-heavy
applications idle while collecting. The full matrix includes deliberately
expensive cases; 30-second cutoffs can make collection take substantially
longer than the small pilot.

## Cross-runtime scenarios

The required Wasmtime and Node gates are part of `paper-check`. To recreate
the additional shared scenarios, first build the Node module and then run the
portability driver in a fresh reproduction checkout:

```sh
wasm-pack build --target nodejs --out-dir ../paper/build/node --release nibli-wasm
python3 paper/scripts/portability.py paper/results/local-portability
```

The driver refuses an existing output directory. Native,
Wasmtime, and Node share saved request snapshots and query expectations.
`artifacts.json` records the runtime artifact hashes. Fuel exhaustion and trap
recovery are separate host checks; these are behavioral comparisons under
adequate budgets, not a performance comparison between runtimes.

## Reading the evidence

- `protocol.json` defines seeds, sizes, bounds, repetitions, cutoffs, and the
  comparison boundary. `protocol.freeze.json` binds it to source and pilot.
- `results/evaluation/inputs/` contains neutral workloads, independent KR,
  clingo, and Soufflé translations, exact queries, and update sequences.
- `results/evaluation/compiled/` contains generated source, compiler commands,
  costs, logs, and executable hashes. The archive omits rebuildable executables.
- `results/evaluation/schedule.json` fixes the complete randomized schedule.
  Git stores its exact bytes compressed as `schedule.json.gz`; analysis reads
  either representation. New measurement runs still write plain JSON.
  `observations.jsonl` contains warm-ups and measured records;
  `completed.json` hashes that ledger.
- `results/evaluation/raw/` contains unedited output, error logs, GNU time
  records, full emitted proof envelopes, and update database snapshots at
  process termination. A cutoff can leave an unfinished update sequence.
- `generated/samples.csv`, `phases.csv`, `summary.csv`, and `compilation.csv`
  expose the values underlying every quantitative table and plot.
- `generated/cutoffs.csv` groups external cutoffs by their last completed phase
  and reports the peak memory observed up to termination.
- `generated/citation-audit.json` rechecks each emitted asserted/derived source
  against the active assertion registry reconstructed from its update sequence.
- `results/checks/`, `results/pilot/`, and `results/portability/` contain the
  verification, hand-derived adapter, and runtime evidence.

External timeouts and process failures are process statuses. They are not
engine `UNKNOWN` or `RESOURCE_EXCEEDED` verdicts. Latency quartiles use completed
runs only; cutoff counts and the complete sample ledger remain available.
Coverage uses every planned answer as its denominator, including answers never
emitted before a cutoff. A timeout during loading provides no observation of
query or certificate latency.

The source audit verifies record liveness and exact labels. Envelope validation
checks structural coherence. Neither is a complete independent semantic proof
checker. Lean proves explicitly modeled mechanisms under stated hypotheses;
the paper does not claim end-to-end verification of Rust, compilation, storage,
or the broader KR language.

## Authorship and source use

The manuscript and research tooling were developed with substantial assistance
from OpenAI Codex, including repository and literature analysis, experiment
implementation, execution, data analysis, and drafting. The manuscript discloses
this use under the [current arXiv policy](https://info.arxiv.org/help/moderation/index.html).
AI tools are not authors, and automated checks do not replace the named author's
responsibility for the submitted content. No human review is represented as
having occurred merely because these checks pass.

`research/sources.json` records verified primary references and the claims they
support. The latest local DOCX chapters were consulted for supporting exposition;
their names and hashes are in `research/manuscript-sources.json`. Their text,
figures, and the private manuscript files are not distributed. The paper's
prose and diagrams were written for the current engine and measured artifact.
