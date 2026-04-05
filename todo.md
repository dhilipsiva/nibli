# Nibli — Reasoning Engine Backlog

Ordered by impact on the book ("Ultimate Symbolic Reasoning for AI Engineers").

## Tier 1: Core Reasoning Gaps

1. **Defeasible / prioritized rules (exception hierarchies)**
   No mechanism for "rule A takes precedence over rule B." Legal reasoning frequently has exception hierarchies (lex specialis). Currently, conflicts are silent.

## Tier 2: Domain Modeling & Interop

2. **Sorted logic / type hierarchy (compile-time sort checking)**
   No way to declare `person ⊂ animal` as a sort hierarchy. Currently encoded as rules which works but doesn't catch ill-sorted queries at compile time.

3. **Knowledge base import/export in standard formats (OWL, RDF)**
   No support for standard KR formats. The engine only ingests Lojban text and LogicBuffer.

## Tier 3: Developer Experience

4. **Interactive debugging / step-through tracing**
   No way to set breakpoints on predicates, step through backward chaining, or inspect the search tree live. Proof traces are post-hoc.
