# Nibli

**A Zero-Hallucination Symbolic Reasoning Engine**

Nibli is a deterministic theorem prover compiled to WebAssembly (WASI P2). It compiles Lojban natural language syntax into First-Order Logic and performs inference via egglog e-graph equality saturation. Every conclusion is formally derived — no hallucination, no approximation.

> *nibli* (Lojban): x1 logically necessitates/entails x2 under rules x3.

## Pipeline

```
Lojban text ──→ Lexer ──→ Parser (AST) ──→ Semantics (FOL IR) ──→ Reasoning (egglog e-graph)
                 │            │                    │                        │
                logos     recursive            Skolemization         equality saturation
              tokenizer    descent          Herbrand instantiation    inference rules
```

5 WASM components composed via WIT interfaces into a single fused binary:

| Component | Role |
|-----------|------|
| **parser** | Lojban text → AST → flat WIT buffer |
| **semantics** | AST buffer → FOL logic IR → flat WIT logic buffer |
| **reasoning** | FOL logic buffer → egglog e-graph assert/query |
| **orchestrator** | Chains parser → semantics → reasoning |
| **runner** | Native Wasmtime host, REPL, loads fused WASM |

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
- **Task Runner:** Just

## Lojban Coverage

- Gadri descriptions (`lo`/`le`/`la`), universal (`ro lo`/`ro le`), numeric quantifiers (`PA lo`/`su'o lo`)
- Place tags (`fa`/`fe`/`fi`/`fo`/`fu`), BAI modal tags (`ri'a`, `ni'i`, `mu'i`, `ki'u`, `pi'o`, `ba'i`), `fi'o`...`fe'u`
- Selbri: root, tanru, conversion (`se`/`te`/`ve`/`xe`), negation (`na`), grouping (`ke`...`ke'e`), compounds (`zei`), `be`...`bei`...`be'o`
- Relative clauses (`poi`/`noi`/`voi`) with `ke'a`, implicit variable injection, clause stacking
- Sumti connectives (`.e`/`.a`/`.o`/`.u` + `nai`), selbri connectives (`je`/`ja`/`jo`/`ju`)
- Sentence connectives (forethought: `ge`...`gi`, `ga`...`gi`, `ganai`...`gi`; afterthought: `.i je`/`ja`/`jo`/`ju` with `na`/`nai`)
- Abstractions (`nu`, `du'u`, `ka` with `ce'u`, `ni`, `si'o`)
- Tense (`pu`/`ca`/`ba`)
- Quoted literals (`lu`...`li'u`), number sumti (`li` + PA)

## Reasoning

- Skolemization (independent + dependent under `∀`)
- Native egglog rules for universal formulas (O(K) hash-join matching, no Herbrand cross-product)
- egglog e-graph with structural rewrites (commutativity, associativity, De Morgan, double negation) + inference rules (conjunction elimination, disjunctive syllogism, modus ponens/tollens)
- Count quantifier (exactly N) for numeric descriptions

## Roadmap

See `todo.md` for the full phased roadmap (Phases 1-5), dependency graph, and technical debt tracker.

## License

See `LICENSE` for details.
