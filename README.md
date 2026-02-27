# Nibli

**A Zero-Hallucination Symbolic Reasoning Engine**

Nibli is a deterministic theorem prover compiled to WebAssembly (WASI P2). It compiles Lojban natural language syntax into First-Order Logic and performs inference via egglog e-graph equality saturation. Every conclusion is formally derived — no hallucination, no approximation.

> *nibli* (Lojban): x1 logically necessitates/entails x2 under rules x3.

## Pipeline

```
Lojban text ──→ Lexer ──→ Parser (AST) ──→ Semantics (FOL IR) ──→ Reasoning (egglog e-graph)
                 │            │                    │                        │
                logos     recursive            Skolemization         equality saturation
              tokenizer    descent           SkolemFn witnesses      native egglog rules
```

5 WASM components composed via WIT interfaces into a single fused binary:

| Component | Role |
|-----------|------|
| **parser** | Lojban text → AST → flat WIT buffer |
| **semantics** | AST buffer → FOL logic IR → flat WIT logic buffer |
| **reasoning** | FOL logic buffer → egglog e-graph assert/query, compute dispatch |
| **orchestrator** | Chains parser → semantics → reasoning, compute predicate registry |
| **runner** | Native Wasmtime host, REPL, external compute backend TCP client |

## Quick Start

### Prerequisites

- [Nix](https://nixos.org/download.html) (all tooling — rustc, cargo-component, wac, just, wasmtime — comes from `flake.nix`)

### Build & Run

```bash
# Enter the dev shell
nix --extra-experimental-features 'nix-command flakes' develop

# Build components, fuse into a single engine, and launch the REPL
just run

# Run all unit tests
just test
```

### REPL Usage

```
~/nibli〉lo gerku cu barda
[Assert] 1 fact(s) inserted.

~/nibli〉? lo gerku cu barda
[Query] TRUE

~/nibli〉:debug re lo gerku cu barda
[Logic] (Count "_v0" 2 (And (Pred "gerku" ...) (Pred "barda" ...)))

~/nibli〉:assert tenfa 8 2 3
[Assert] tenfa(8, 2, 3)

~/nibli〉:reset
[Reset] Knowledge base cleared.
```

## Tech Stack

- **Language:** Rust (stable)
- **WASM:** WASI Preview 2 Component Model (cargo-component + wac)
- **Runtime:** Wasmtime
- **Logic Engine:** egglog (equality saturation)
- **Lexer:** Logos
- **Dictionary:** Perfect Hash Function (PHF) baked into binary
- **Dev Environment:** Nix flake
- **Compute Backend:** TCP + JSON Lines (generic protocol, any language)
- **Task Runner:** Just

## Lojban Coverage

- Gadri descriptions (`lo`/`le`/`la`), universal (`ro lo`/`ro le`), numeric quantifiers (`PA lo`/`su'o lo`)
- Place tags (`fa`/`fe`/`fi`/`fo`/`fu`), BAI modal tags (`ri'a`, `ni'i`, `mu'i`, `ki'u`, `pi'o`, `ba'i`), `fi'o`...`fe'u`
- Selbri: root, tanru, conversion (`se`/`te`/`ve`/`xe`), negation (`na`), grouping (`ke`...`ke'e`), compounds (`zei`), `be`...`bei`...`be'o`, lujvo (compound brivla)
- Relative clauses (`poi`/`noi`/`voi`) with `ke'a`, implicit variable injection, clause stacking
- Sumti connectives (`.e`/`.a`/`.o`/`.u` + `nai`), selbri connectives (`je`/`ja`/`jo`/`ju`)
- Sentence connectives (forethought: `ge`...`gi`, `ga`...`gi`, `ganai`...`gi`; afterthought: `.i je`/`ja`/`jo`/`ju` with `na`/`nai`)
- Abstractions (`nu`, `du'u`, `ka` with `ce'u`, `ni`, `si'o`)
- Tense (`pu`/`ca`/`ba`), deontic attitudinals (`ei`/`e'e`)
- Observative sentences (implicit `go'i` pro-bridi), explicit `go'i` as selbri
- Question pro-sumti `ma` — compiles to existential variable for witness extraction
- Quoted literals (`lu`...`li'u`), number sumti (`li` + PA)

## Reasoning

- Skolemization (independent + dependent under `∀` via `SkolemFn` constructor)
- All universals compile to native egglog rules (O(K) hash-join matching, zero Herbrand overhead)
- egglog e-graph with structural rewrites (commutativity, associativity, De Morgan, double negation) + inference rules (conjunction elimination/introduction, disjunctive syllogism, modus ponens/tollens)
- Count quantifier (exactly N) for numeric descriptions
- Numerical comparison predicates: `zmadu` (>), `mleca` (<), `dunli` (==) on `Num` terms
- Computation dispatch: `compute-backend` WIT protocol for external evaluation, `ComputeNode` IR variant
- Built-in arithmetic: `pilji` (multiply), `sumji` (add), `dilcu` (divide) with host-provided compute backend
- External compute backend: generic TCP client with JSON Lines protocol, lazy connect, auto-reconnect
- Compute result auto-ingestion: successful compute results automatically cached in the KB as ground predicates (closes reason→compute→reason loop)
- Direct fact assertion: `assert-fact` WIT method + `:assert` REPL command for programmatic fact injection bypassing Lojban parsing
- Existential witness extraction: `query-find` returns all satisfying entity bindings for existential variables (`??` REPL prefix)
- Proof trace generation: `query-entailment-with-proof` returns proof tree showing which rule/axiom was applied at each step (13 proof rule variants: conjunction, disjunction, negation, modal, exists-witness, forall-verified, count, predicate-check, compute-check, etc.) — `?!` REPL prefix
- Parser error recovery: per-sentence recovery skips to next `.i` on parse failure, continues parsing remaining sentences; errors include exact line:column positions
- Guarded conjunction introduction: `And(A, B)` derived when both A, B are atomic predicates sharing an `InDomain` entity (prevents combinatorial explosion)
- Typed WIT error variants: shared `nibli-error` variant (`syntax`/`semantic`/`reasoning`/`backend`) across all interfaces; syntax errors carry line:column positions; structured REPL error output
- WASM fuel limits: per-command execution budget prevents unbounded computation; configurable via `NIBLI_FUEL` env var or `:fuel` REPL command

## Compute Backend

The runner connects to an external compute backend over TCP using a JSON Lines protocol. Any process (Python, Node.js, Rust, another WASM module) can serve as a backend.

```bash
# Terminal 1: Start the Python reference backend
just backend

# Terminal 2: Launch the engine with backend configured
just run-with-backend

# In the REPL:
:compute tenfa                      # register tenfa for compute dispatch
li bi tenfa li re li ci             # assert: 8 = 2^3
? li bi tenfa li re li ci           # query: TRUE (dispatched to Python)
```

Set `NIBLI_COMPUTE_ADDR=host:port` or use `:backend host:port` in the REPL. Without a backend, built-in arithmetic still works.

## Roadmap

See `todo.md` for the full phased roadmap (Phases 1-5), dependency graph, and technical debt tracker.

## License

See `LICENSE` for details.
