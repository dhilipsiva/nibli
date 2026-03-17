# Transparency Triad Review Notes

Date: 2026-03-15

## Context

These notes capture my feedback after reviewing the current Transparency Triad implementation and then re-evaluating it under the explicit assumption that all 10 steps from [docs/transparency-triad-implementation-plan.md](/Users/c-dhilipc/projects/dhilipsiva/nibli/docs/transparency-triad-implementation-plan.md) are fully implemented.

Important framing:

- The current codebase appears to implement roughly Steps 1-6.
- The feedback below includes both:
  - concerns about the current partial implementation, and
  - my revised opinion assuming the full intended 10-step design exists.

## High-Level Assessment

If all 10 planned steps are implemented as designed, the Transparency Triad becomes a legitimate and compelling product surface rather than just a promising prototype.

What gets much stronger in the full 10-step version:

- Proof traces become first-class UI artifacts rather than hidden internals.
- Fact management completes the knowledge-base lifecycle.
- Error UX and polish make the tool usable for repeated daily work.
- The full English -> Lojban -> back-translation -> assert/query -> proof workflow becomes coherent and demoable.

## Revised Feedback Under the "All 10 Steps Implemented" Assumption

### 1. The mutex/server concern becomes secondary if the final architecture is desktop-native

My earlier concurrency finding about `std::sync::Mutex` in `nibli-server` matters for the current GraphQL-based implementation, but it stops being a major architectural objection if the final system really follows Step 3 of the plan:

- direct Wasmtime embedding in the desktop app,
- engine ownership on the main thread,
- no GraphQL server in the hot path.

In that final architecture, the mutex finding is mostly a temporary implementation concern, not a fundamental design flaw.

If the GraphQL server split is kept long-term, however, the locking model should still be fixed.

### 2. The overall product direction is strong

The 10-step plan is good product thinking.

The strongest parts of the intended design are:

- proof traces are central, not bolted on,
- retraction/reset/load support real knowledge-base work,
- the UI is organized around inspection and verification,
- the system exposes the full symbolic workflow rather than hiding it.

That is the right direction for a symbolic reasoning product.

## Main Remaining Reservations

### 1. Back-translation is still the weakest link

Even assuming all 10 steps are implemented exactly as planned, the largest remaining concern is Step 5.

The plan explicitly says:

- no grammar-aware parsing,
- no structure-aware back-translation,
- robotic glossing is acceptable.

That is useful as a developer aid, but it is not enough to support the strongest version of the Transparency Triad claim.

Why this matters:

- the human reviewer is supposed to verify the formal input,
- but a token-gloss rendering does not preserve enough semantics,
- especially for quantifier scope, gadri distinctions, place structure, negation, and structural operators.

So even in the full 10-step version, I would still be cautious about claiming that non-Lojban experts can reliably validate the formal encoding from the back-translation alone.

My honest view:

- as a debugging and inspection tool, the robotic back-translation is good,
- as a semantic verification layer, it is not yet strong enough.

### 2. Translation should be validated before it is presented as reviewable formal input

Even in the full plan, I would still want the translated Lojban to be validated through the parser and semantic compiler before the UI treats it as reviewable formal content.

Why:

- otherwise the user may inspect or edit text that the engine cannot actually parse,
- and the failure only appears later during assert/query,
- which is the wrong place in the workflow.

Recommended standard:

- LLM output should be parser-validated,
- ideally semantically compiled too,
- before it is surfaced as accepted middle-pane content in the triad.

### 3. Do not oversell the trust model yet

If all 10 steps are complete, I would describe the system as:

- a strong interactive reasoning workbench,
- a compelling symbolic inspection UI,
- a good prototype for human-in-the-loop formal verification.

I would not yet describe it as a fully reliable semantic-verification firewall for non-Lojban experts unless the back-translation becomes structure-aware and semantically faithful.

## What I Like Most

- The architecture becomes much more convincing once proof visualization, fact management, and error UX are included.
- The plan correctly prioritizes auditability over flashy UI.
- The workflow is aligned with how symbolic systems should be experienced: inspectable, editable, replayable, and provable.
- The later phases close real usability gaps instead of adding gimmicks.

## Recommended Next Improvements After the 10 Steps

If the current 10-step plan is completed, these would be my highest-priority next improvements:

1. Upgrade back-translation from token glossing to structure-aware semantic rendering.
2. Validate translated Lojban through gerna/smuni before presenting it as reviewable input.
3. If the server split remains, replace blocking mutex-based execution with a model that does not block async executor threads.
4. Add explicit UI cues separating:
   - raw LLM draft,
   - validated formal encoding,
   - human-edited final encoding.

## Bottom Line

Assuming all 10 planned steps are complete, my opinion becomes substantially more positive.

The Transparency Triad would then look like a serious, coherent symbolic reasoning interface rather than an early mockup.

But one core caution remains:

the semantic trustworthiness of the back-translation is still the part I would push on hardest.

That is the difference between:

- "this is a great symbolic reasoning UI", and
- "this is a trustworthy human verification layer for formal input."
