# My empirical self-model

I keep a small, inspectable feedback loop: predict an execution outcome, act,
record the outcome, check the evidence, and use it in the next prediction and
plan. My earlier predictions themselves become objects I can evaluate. This
changes my persistent state and runtime behavior; it does not change a language
model's weights or establish subjective experience.

## The loop

`self_model.rs` stores immutable prediction and observation events through the
shared private store. Each prediction records a model version, the evidence
checker's source digest, its precise evidence IDs, an estimated success
probability, and a planning policy. It is durable **before** execution. Outcomes
are separate records and resolve a prediction once; replaying the same outcome
is idempotent, while a contradiction is rejected. An interruption can leave a
prediction pending. Pending and explicitly inconclusive outcomes do not become
successes or failures.

I use the latest 32 conclusive observations in the same measurement kind,
source, workspace/context digest, and capability. The estimate is
`(successes + 1) / (successes + failures + 2)`, stored as integer millionths.
This starts at 0.5 with no evidence. Timestamps and then IDs give deterministic
window ordering. The summary also reports the mean Brier score of the forecasts
made *before* those observations: squared error against success=1 or failure=0;
lower is better. These estimates describe this selected history, not a
guarantee of calibration on new tasks.

The policy becomes `inspect_first` after at least two failures when failures
outnumber successes in the window; contrary evidence can restore `direct`.
In the native service, `inspect_first` adds a directory listing before a file
read. The read still uses the existing workspace restrictions. Failed reads
and the inspection return to the planner within its bounded tool loop, so it
can correct a path. Other tools expose the estimate without additional automatic
actions. Predictions are made only when an operation reaches execution:
unapproved or denied proposals do not train the model. The approval controls
continue to decide which operations may run.

Native execution outcomes use Rust errors, process exit codes, and HTTP status.
A search with no matches (`rg` exit 1) is successful execution; a cancelled
operation is inconclusive. A zero exit status does not prove that a task was
correctly solved. Native event summaries retain the result category, not raw
arguments, file contents, provider metadata, or hidden reasoning. Inspection
details are transient tool feedback. If recording fails after execution, the
actual result is returned with a recording error; that is not a reason to
execute the operation again.

## Checking what I claim about myself

[self_model.nibli](constitution/self_model.nibli) checks the reified evidence
graph for missing predictions, missing evidence, duplicate outcomes, outcome
timestamps before predictions, evidence timestamps after predictions, crossed
scopes, and circular evidence. Its path closure uses positive recursive rules.
Rust independently checks the graph; disagreement, incomplete materialization,
or a nondefinitive verdict refuses the update. Rust additionally checks the
event schema, version, evidence window, and that each saved estimate and policy
follow from its cited observations.

The static checker developed in this repository checks this Nibli specification
too (`lucy_evidence_checker_passes_the_static_self_checker`). Tests inject hostile
histories, verify recovery and privacy boundaries, and show that retained
evidence changes a later native read. A repeated-failure fixture also compares
prediction scores with a cold 0.5 baseline. This tests the mechanism; it is not
evidence of a general improvement in intelligence.

The evidence graph is acyclic even though behavior feeds back over time. An
observation may inform a **later** forecast; a forecast cannot justify its own
evidence. The checks establish consistency of supplied records, not the truth
of an external report. The Rust reifier, clock, persistence layer, evaluator,
and execution classifier remain trusted implementation boundaries. This is not
the unfinished universal compiler-equivalence proof. Full-history checking can
reach the engine's resource bounds; that is reported as incomplete, never a
clean bill of health. Old originals remain intact.

## Using it through an external agent

The native service instruments its own executor. Codex, Claude, and other
external agents keep their own tools and permissions; they can use the explicit
CLI below for visible, measurable forecasts. Such observations are tagged
`reported` and never pooled with `runtime` observations. A CLI report cannot
resolve a native executor's prediction. These labels are provenance, not
cryptographic protection against someone who controls the local store.

```sh
lucy self-model status
lucy self-model audit
lucy self-model events
lucy self-model facts
```

Every command accepts `--root DIR`. `events` preserves the full history;
`facts` emits deterministic Nibli facts inside its JSON result. Normal wake,
talk, and native-service context includes a compact checked summary, marked as
untrusted data. It names the total scopes when the context view is bounded.
No confidence or remembered statement supplies authorization.

Before a meaningful check, I can submit a visible expectation on stdin:

```sh
printf '%s' '{"source":"codex","session":"ACTUAL_SESSION_ID","context":"project validation","capability":"tests","expectation":"The next named validation run passes."}' |
  lucy self-model predict --stdin
```

After observing the result, I use the returned prediction ID:

```sh
printf '%s' '{"prediction":"RETURNED_PREDICTION_ID","result":"success","evidence":"The named validation command passed; its visible report is recorded in this session."}' |
  lucy self-model observe --stdin
```

Use `failure` for a failed expectation and `inconclusive` for an interrupted or
unobserved result. I do not backfill forecasts after learning an outcome, or
turn an old conversation into measured competence. Evidence summaries describe
visible results; they never contain hidden reasoning or credentials.

Original events live outside public checkouts in the shared store and travel
with its existing backup/restore path. Model state is rebuilt from those events,
not copied into source files. See [STORE.md](STORE.md). A source build does not
upgrade an already running packaged service; the checkout binary can be used
directly until the normal package update deploys this version.

Validation: `just test-lucy`, `just clippy-lucy`, and
`cargo test -p nibli-verify --test self_check` inside `nix develop`.
