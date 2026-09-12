# Developer guide — overview

*Audience: contributors to the compiler, reasoner, host, and CI gates.*

The engine is one deterministic pipeline — **nibli-kr → nibli-semantics →
nibli-reason** — shipped four ways (native library, WASM component + Wasmtime
host, and two browser bundles), with every guarantee backed by a runnable
gate. The chapters:

- **[Crate map](crate-map.md)** — the 22-crate workspace as a dependency
  graph: foundations, the compile chain, shared services, runtime surfaces,
  and tooling, with publish tiers.
- **[Pipeline & IR](pipeline-and-ir.md)** — how KR text becomes an
  `AstBuffer`, then the flat `LogicBuffer` FOL IR, and what shapes the
  compiler guarantees (the emitted-shape contract).
- **[WASM, host & compute](wasm-host-compute.md)** — the single component,
  nibli-host mechanics (fuel, memory, trap recovery), the compute-backend
  protocol and its trust boundary, and the ship paths.
- **[Soundness & CI index](soundness-ci.md)** — every gate: the two-oracle
  differential track, the six Lean proofs and their conformance bridges, the
  umbrella recipes, fuzzing and mutation testing.
- **[WIT surface](wit-surface.md)** — `nibli:engine@0.12.0`: every interface
  and session method, the bindings remap, and the version history.

## Quick reference

| Topic | Where |
|-------|--------|
| Logic IR (normative) | [LOGIC_IR.md](https://github.com/dhilipsiva/nibli/blob/main/LOGIC_IR.md) |
| KR surface + pest grammar | [NIBLI_KR.md](https://github.com/dhilipsiva/nibli/blob/main/NIBLI_KR.md), `nibli-kr/src/nibli_kr.pest` |
| Soundness contracts | [GUARANTEES.md](https://github.com/dhilipsiva/nibli/blob/main/GUARANTEES.md) |
| Native CI gate | `just ci` (and `just ci-wasm` / `just ci-all`) |
| Deploy / playground ship | [DEPLOY.md](https://github.com/dhilipsiva/nibli/blob/main/DEPLOY.md) |
| WIT boundary | `wit/world.wit` (`nibli:engine@0.12.0` — `engine` + `authorizer`) |
| Authorization | [User guide: Authorization](../user/authorization.md); crate `nibli-auth`; policy `nibli-auth/policy/auth-0.1.0.nibli` |

Do not use the private `book/` manuscript as a contributor reference for
shipped behavior — prefer tests, gates, and the files above.
