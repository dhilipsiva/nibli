# GDPR walkthrough

This teaching model derives scoped processing prerequisites, subject rights and
controller duties for seven GDPR article themes. A result describes the encoded
case; it is not a finding of complete legal compliance.

The executable source is
[`gdpr.nibli`](https://github.com/dhilipsiva/nibli/blob/main/gdpr.nibli).
Its [manifest](https://github.com/dhilipsiva/nibli/blob/main/examples/case-studies/gdpr/manifest.json)
maps every statement to reviewed source context, an authored teaching policy or
fictional evidence. The
[scenario matrix](https://github.com/dhilipsiva/nibli/blob/main/examples/case-studies/gdpr/scenarios.json)
and `nibli-engine/tests/case_studies.rs` check sixteen independent scenarios with
materialization both on and off. The playground preset is
**GDPR compliance (Ch 19)**.

## Bind the case before deriving a conclusion

| Identifier | Meaning in this fixture |
|---|---|
| `CaseA` | One processing case with one declared purpose |
| `RecordsA` | The records in that case, classified as health data |
| `Adam` | The data subject linked to those records |
| `ControllerA` | The controller responsible for this case |
| `ResearchPurpose` | The reviewed purpose of this case |
| `ProvideAccess`, `EraseRecords` | Named actions scoped to the case |

```nibli-kr
record(CaseA, RecordsA, Adam, CaseRegister).
governs(ControllerA, CaseA).
uses(CaseA, RecordsA, ResearchPurpose).
```

The case identifier carries the processing scope. A new purpose, subject or set
of records requires a separate case. The fixture adapter checks unique direct
bindings in the manifest; it does not provide a general runtime legal-record
schema validator.

`permits(controller, case, basis)` records a derived processing route.
`entitled(subject, action, article)` records a right, while
`obliged(controller, action, article)` records a duty. Neither relation asserts
that the action happened. Admission guards mark these conclusion predicates
`derived_only`; directly asserting a favorable conclusion is refused.

## Seven article themes

The source is the [GDPR text on EUR-Lex](https://eur-lex.europa.eu/eli/reg/2016/679/oj/eng).
The manifest identifies the relevant provisions and the narrower teaching
interpretation used by each rule.

| Theme | Executable meaning | Remaining review |
|---|---|---|
| Article 5 | Controller duties for named accuracy, security and minimization actions | Adequacy and performance of those actions |
| Article 6 | Separate consent, contract and statutory-basis routes for the case | Applicability and each route's legal prerequisites |
| Article 7 | A positive `ConsentReviewComplete` gate for the consent route | Whether the recorded consent meets the source requirements |
| Article 9 | Separate special-category review and accepted-condition markers | Applicable exception and complete processing legality |
| Article 15 | Subject access right and controller response duty | Applicability and actual response evidence |
| Article 17 | Withdrawal-only erasure ground with reviewed other-basis and exception inventories | Other erasure grounds and the correctness of those reviews |
| Article 33 | Controller notification duty from a reviewed breach-risk trigger | Recipient, timing and notification performance |

For example, the consent route requires applicability, completed review, valid
consent evidence and no recorded withdrawal:

```nibli-kr
all $c, $case: governs($c, $case) & member($case, ApplicableGDPRCases) & member($case, ConsentReviewComplete) & member($case, ValidConsentRecorded) & ~member($case, ConsentWithdrawalRecorded) -> permits($c, $case, Article6Consent).
```

Contract and statutory processing bases use separately accepted evidence. No
rule infers a processing basis from an arbitrary duty, so an erasure duty cannot
supply its own competing legal ground.

## Run the default case

Start a fresh REPL from the repository root and enter `:load gdpr.nibli`.
Inspect every admission result. The source has 56 statements; obtain runtime IDs
from admission or `:facts` instead of copying IDs from another corpus.

In the playground, select the preset and use its query dropdown. The four
queries are exactly these claims, entered without a leading `?` in the browser:

| REPL query | Default result | What the result establishes |
|---|---|---|
| `? permits(ControllerA, CaseA, Article6Consent).` | TRUE | The case's encoded consent prerequisites hold |
| `? obliged(ControllerA, EraseRecords, Article17Withdrawal).` | FALSE | The withdrawal-only duty is not derived; no withdrawal is recorded |
| `? entitled(Adam, ProvideAccess, Article15).` | TRUE | The subject has the modeled access right |
| `? permits(ControllerA, CaseA, Article9Condition).` | FALSE | The separate Article 9 condition has not been accepted |

The consent route being TRUE does not fill the missing Article 9 condition.
The FALSE erasure result does not rule out other Article 17 grounds. Review the
formal scope and missing evidence before treating either result as an application
decision. Proof rendering retains the encoded actors and roles.

## Withdrawal is evidence, not a missing record

Removing `member(CaseA, ValidConsentRecorded).` makes the consent route FALSE.
It does **not** establish a withdrawal or create an erasure duty. This is the
playground's consent-evidence removal scenario.

To model a recorded withdrawal, start again from the default case and add:

```nibli-kr
member(CaseA, ConsentWithdrawalRecorded).
```

The consent route becomes FALSE. The controller's `Article17Withdrawal` duty
and Adam's corresponding right become TRUE because this fixture already records
consent history and completed basis and exception reviews. The absence tests for
`OtherBasisAccepted` and `ErasureExceptionApplies` are used only with those
positive review prerequisites. A NAF-dependent proof identifies that dependence;
it does not independently establish that the real legal inventory was complete.

Test the boundary by adding one accepted contract basis:

```nibli-kr
member(CaseA, ContractBasisAccepted).
```

The contract route becomes TRUE, `OtherBasisAccepted` follows, and the
withdrawal-only erasure duty becomes FALSE. The scenario matrix also checks a
statutory basis, an erasure exception, missing review evidence, a second case with
a different subject and purpose, wrong actors, category propagation, separate
Article 9 conditions, access rights, breach risk and rejected direct conclusions.

## Replay the controls

Inside `nix develop`, run:

```sh
cargo test -p nibli-engine --test case_studies
cargo run -p nibli-engine --example case_studies -- gdpr --capture
cargo run -p nibli-engine --example case_studies -- gdpr --capture --no-materialize
```

Each scenario starts with a fresh native engine at depth 10, strict mode off and
legacy existential import off. Captures include actual runtime IDs, query
results, proof trees and provenance envelopes checked for structural coherence.
That check is distinct from independently validating the law or replaying a proof
against an external legal specification.

The original proxy is retained only as an isolated
[defect control](https://github.com/dhilipsiva/nibli/blob/main/examples/case-studies/legacy/gdpr-proxy.nibli).
It demonstrates why absent approval, subject-level basis labels and misplaced
duty actors are inadequate. The `gdpr_*` legacy integration tests explicitly load
that fixture. Its old assertion IDs and outputs do not describe the current root
corpus or default preset.
