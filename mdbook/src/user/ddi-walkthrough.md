# Drug interactions walkthrough

This teaching model derives an interaction-review duty when a selected mechanism
matches and both relevant drug exposures belong to the same patient and episode.
It does not derive a concentration, toxicity diagnosis, safe combination or
treatment recommendation.

The executable source is
[`drug-interactions.nibli`](https://github.com/dhilipsiva/nibli/blob/main/drug-interactions.nibli).
Its [manifest](https://github.com/dhilipsiva/nibli/blob/main/examples/case-studies/drug/manifest.json)
distinguishes label-derived mechanism facts, fictional exposure evidence and the
authored screening policy. The
[scenario matrix](https://github.com/dhilipsiva/nibli/blob/main/examples/case-studies/drug/scenarios.json)
and `nibli-engine/tests/case_studies.rs` check thirteen independent scenarios in
both materialization modes. The playground preset is **Drug interactions (Ch 20)**.

## Separate mechanism, exposure and action

| Record | Meaning |
|---|---|
| `EpisodeA` | Adam's fictional medication-review episode |
| `PairWarfarin` | The candidate pair Warfarin and Fluconazole |
| `AssessWarfarin` | Assessment of that pair in EpisodeA |
| `ExposureWarfarin`, `ExposureFluconazole` | Reviewed relevant exposures for Adam in EpisodeA |
| `ReviewWarfarin` | Named ordinary review action |
| `PriorityWarfarin` | Separate priority review action |

```nibli-kr
record(EpisodeA, Adam, MedicationReview, EpisodeRegister).
record(PairWarfarin, Warfarin, Fluconazole, InteractionPairs).
record(AssessWarfarin, EpisodeA, PairWarfarin, AssessmentRegister).
```

The candidate pairs are enumerated deliberately; they are not a complete
interaction catalog. The fixture adapter checks its declared unique bindings,
while application-level patient and episode validation remains separate.

The [fluconazole prescribing information](https://labeling.pfizer.com/ShowLabeling.aspx?id=4449)
describes inhibition of CYP2C9 and CYP3A4, among other mechanisms. Both selected
edges are present here. The
[warfarin label](https://dailymed.nlm.nih.gov/dailymed/fda/fdaDrugXsl.cfm?setid=e11e4522-4b34-4170-af51-7b602924c746&type=display)
and [apixaban label](https://packageinserts.bms.com/pi/pi_eliquis.pdf)
provide the selected substrate pathways. The manifest records the exact source
sections, including the narrow-index classification used for review priority.
These selected edges omit pathway strength, dose and quantitative kinetics.

## Two joins and a review rule

The mechanism join uses one shared enzyme variable across an `InhibitionEdges`
record and a `SubstrateEdges` record. It derives
`fit(assessment, SharedMechanism, ScreeningPolicy)` for each matched assessment.
The same rule handles warfarin, phenytoin and apixaban; it does not need a new
grounded rule for each drug.

The exposure join independently requires two relevant exposure records, with the
same patient and episode as the assessment. For example:

```nibli-kr
record(ExposureFluconazole, Fluconazole, Adam, ExposureRegister).
part(ExposureFluconazole, EpisodeA).
member(ExposureFluconazole, RelevantExposures).
```

A prescription, an administration event and relevant bodily exposure are different
evidence. `RelevantExposures` records an externally reviewed relevance decision;
the engine does not calculate that decision from elapsed time.

The screening policy combines the two derived criteria with a named action:

```nibli-kr
all $a, $action: fit($a, SharedMechanism, ScreeningPolicy) & fit($a, ConcurrentExposure, ScreeningPolicy) & part($action, $a) & member($action, InteractionReviewActions) -> obliged(ReviewTeam, $action, ScreeningPolicy).
```

Narrow therapeutic index adds a separate priority-review duty. It is not required
for the ordinary review. Removing that classification cannot establish safety.
Admission guards mark `fit` and `obliged` derived-only, so a direct assertion of a
review conclusion is refused.

## Run the default case

Start a fresh REPL from the repository root and enter
`:load drug-interactions.nibli`. Inspect admission results. The source contains
46 statements. Use returned IDs or `:facts` when retracting an assertion; the old
proxy's IDs are unrelated to this corpus.

The playground's four preset queries match these REPL claims. The browser query
field takes the proposition without the leading `?`:

| REPL query | Default result | Meaning |
|---|---|---|
| `? fit(AssessWarfarin, SharedMechanism, ScreeningPolicy).` | TRUE | The selected CYP2C9 mechanism matches |
| `? fit(AssessWarfarin, ConcurrentExposure, ScreeningPolicy).` | TRUE | Both reviewed exposures match Adam and EpisodeA |
| `? obliged(ReviewTeam, ReviewWarfarin, ScreeningPolicy).` | TRUE | The authored policy derives this review duty |
| `? obliged(ReviewTeam, ReviewApixaban, ScreeningPolicy).` | FALSE | No apixaban exposure is supplied in the default episode |

The apixaban mechanism itself is **TRUE**: ask
`fit(AssessApixaban, SharedMechanism, ScreeningPolicy).`. The review is FALSE
because exposure evidence is missing, not because fluconazole leaves CYP3A4
uninhibited. Add reviewed apixaban exposure for Adam in EpisodeA and the ordinary
review becomes TRUE. The same pattern works for phenytoin without adding a new
mechanism rule. Neither a missing exposure nor an unlisted candidate pair proves
a safe combination.

## Revision changes evidence, not physiology

The scenario matrix distinguishes three changes:

| Change | Shared mechanism | Warfarin review | Interpretation |
|---|---|---|---|
| Add a prescription-stop record only | TRUE | TRUE | Relevant exposure has not been reassessed away |
| After reassessment, retract Fluconazole's `RelevantExposures` membership | TRUE | FALSE | One required exposure no longer supports this episode's review |
| Retract a required mechanism-edge classification | FALSE | FALSE | The model's pharmacological knowledge changed |

The [fluconazole label](https://labeling.pfizer.com/ShowLabeling.aspx?id=4449)
notes that enzyme inhibition can persist after discontinuation. Removing a
prescription therefore does not justify deleting the inhibition edge or assuming
immediate absence of relevant exposure.

The playground's exposure-reassessment scenario removes the relevant-exposure
marker and reruns the mechanism and review queries. In Custom mode, review the
changed source and encoding before admitting the draft. The native scenario
runner uses the actual admission ID for the retraction. It also verifies that an
independent duplicate exposure preserves the review, a different patient's
exposure cannot satisfy Adam's assessment, and a complete second patient/episode
works under the same generic rules.

## Replay the controls

Inside `nix develop`, run:

```sh
cargo test -p nibli-engine --test case_studies
cargo run -p nibli-engine --example case_studies -- drug --capture
cargo run -p nibli-engine --example case_studies -- drug --capture --no-materialize
```

Each scenario starts with a fresh native engine at depth 10, strict mode off and
legacy existential import off. Tests cover either exposure missing, wrong patient
or episode, a second complete patient, mismatched pathways, the CYP3A4 omission,
prescription-stop persistence, reassessment, duplicate support, narrow-index
priority and rejected direct conclusions. Captures retain actual results, proofs
and provenance envelopes; their structural validation does not certify clinical
fidelity.

The original drug proxy is preserved only as an isolated
[defect control](https://github.com/dhilipsiva/nibli/blob/main/examples/case-studies/legacy/drug-proxy.nibli).
It omits an inhibitor-exposure guard, fixes Adam in its alert rule and omits a
sourced CYP3A4 inhibition edge. Its old contrary source comment is evidence of
that defect, not a pharmacological claim to reuse. The `ddi_*` legacy integration
tests explicitly load this fixture. Current defaults use the scoped model and
literal role wording in proofs.
