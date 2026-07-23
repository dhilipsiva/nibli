# Nibli Interactive Documentation Roadmap

This roadmap outlines the plan to build interactive documentation for the Nibli ecosystem, to be hosted on `dhilipsiva.dev`.

The documentation is split into two primary guides to serve distinct audiences: Knowledge Engineers (using the engine) and Core Contributors (hacking on the engine).

## 1. Engine-User Guide (For Knowledge Engineers)
*Target Audience: Policy writers, compliance officers, and developers integrating `.nibli` files.*

- [ ] **Introduction to Nibli:** What is the Hallucination Firewall? Why deterministic logic?
- [ ] **Quickstart:**
  - Installing the `nibli` CLI.
  - Running your first REPL session.
- [ ] **The Nibli KR Language:**
  - Syntax basics: predicates, arguments, and constants.
  - Neo-Davidsonian Events: Decomposing claims (`event { ... }`).
  - Writing Rules: Universals (`all $x: ... -> ...`).
  - Negation-as-Failure (`~`).
- [ ] **The Transparency Triad (Interactive):** 
  - *Goal:* Build a WASM-powered interactive widget on `dhilipsiva.dev` showing Nibli KR input, the English back-translation, and the resulting proof trace side-by-side.
- [ ] **Domain Engineering:** 
  - Case Study Walkthrough: The GDPR Compliance Engine (`gdpr.nibli`).
  - Case Study Walkthrough: Utopia Legal Domain (`utopia.nibli`).
  - Handling Belief Revision and incremental retractions.
- [ ] **Host Integration:** 
  - Instantiating the WASM engine in Python or JavaScript.
  - Structuring host-driven assertions.

## 2. Engine-Developer Guide (For Core Rust Contributors)
*Target Audience: Systems engineers contributing to the Nibli compiler, execution engine, or Wasmtime host.*

- [ ] **Architecture Overview (Interactive):** 
  - *Goal:* Clickable Mermaid diagrams mapping the crate dependency graph (`nibli-kr` -> `nibli-semantics` -> `nibli-reason` -> `nibli-store`).
- [ ] **Mechanical Sympathy & Memory Layout:**
  - The flat `u32` vector arrays vs pointer trees.
  - Cache locality and WASM boundary safety.
- [ ] **The WASM Component Model:**
  - Sandboxing boundaries.
  - Wasmtime fuel exhaustion, mutation journaling, and guest poisoning recovery.
- [ ] **Semantic Compilation Pipeline:**
  - Lowering Neo-Davidsonian event semantics into First-Order Logic.
  - Skolemization and witness tracking.
- [ ] **The Open Compute Protocol:**
  - How synchronous host calls (e.g., database queries) operate across the boundary.
- [ ] **Testing & CI Workflow:**
  - Running regression tests (`just run`, `just test`, `cargo bench`).
  - The Vampire/clingo adversarial test suite.
