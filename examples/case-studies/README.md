# Scoped case studies

The root `gdpr.nibli` and `drug-interactions.nibli` are bounded teaching models.
Their manifests distinguish reviewed source context, fictional evidence, and
educational policy decisions. Neither reports complete legal compliance, measured
drug exposure, clinical safety, or performed actions.

Run from the repository root inside `nix develop`:

```sh
cargo test -p nibli-engine --test case_studies
cargo run -p nibli-engine --example case_studies -- gdpr --capture
cargo run -p nibli-engine --example case_studies -- drug --capture --no-materialize
```

Each scenario starts from a fresh engine. Manifests map stable authored source IDs
to one admitted assertion each; captures retain actual runtime IDs, query results,
validated certificates, and proof trees. `scenarios.json` supplies independently
authored expectations. Both materialization modes use depth 10. A missing review
is incomplete domain evidence even when a query correctly reports formal FALSE.
The runner checks source references and unique direct bindings in the declared
fixture scopes; it is not a general legal or patient-record schema validator.

`legacy/` preserves the original bytes as isolated defect controls. The GDPR
proxy conflates absent approval and withdrawal and binds some duties to the wrong
actor. The drug proxy omits the inhibitor-exposure guard, fixes Adam in its alert
rule, and omits a sourced CYP3A4 inhibition edge. Its contrary source comment is
preserved as evidence of the defect, not endorsed. These inputs are never loaded
by the default examples. Existing `gdpr_*`/`ddi_*` integration tests explicitly
load these legacy paths, preserving support, join, and retraction regressions.

Source-linked model limitations are deliberate: applicability, consent validity,
other grounds and exceptions are reviewed input classifications; exposures are
reviewed patient-and-episode evidence. Removing a prescription does not remove
relevant bodily exposure. No inference equates missing evidence with safety.
