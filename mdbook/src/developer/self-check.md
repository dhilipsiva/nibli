# Self-hosted static checker

`nibli-verify/spec/nibli_checker.nibli` analyzes a parsed KR program represented
as ordinary base facts. The subject's rules are data: loading its AST never
executes those rules. `just verify-self-check` runs the exporter tests, the
checker on itself, native compiler differentials, and content pins over the
live checker.

The pin runner loads fixtures through the ordered batch constructor, so the
large AST fact set does not copy a growing session on every line. Failed
batches use the ordinary assertion path to retain file and line diagnostics;
no pins run against a partially loaded fixture.

Run commands inside the repository's Nix development shell:

```sh
cargo build -p nibli --bin nibli-ast --bin nibli-pin
nibli_ast=target/debug/nibli-ast
"$nibli_ast" --emit-ast-facts nibli-verify/spec/nibli_checker.nibli > /tmp/nibli-self.ast.nibli
target/debug/nibli-pin \
  --kb nibli-verify/spec/nibli_checker.nibli \
  --kb /tmp/nibli-self.ast.nibli \
  nibli-verify/spec/self_check.pins.nibli
```

For another subject, replace the exporter input. `--query` requests query
compilation checks; without it, the subject is an ordered sequence of
assertions into a fresh session. `-` reads stdin. A parse error fails the
export without emitting partial facts. Unknown predicates and other parsed
static errors are exported so the checker can diagnose them.

## Schema and trust boundary

The public Rust entry point is
`nibli_kr::reify::ast_to_nibli(&[Statement], InputIntent)`. The lower-level
`reify` result contains the same facts as typed rows for embedding consumers.
It walks the raw `parser::parse_statements` tree, before the validating emitter.
It does not invoke the semantic compiler or reasoner, or export their verdicts,
rule classifications, variable bindings, or dependency graphs.

| Facts | Meaning |
| --- | --- |
| `ast_program(program, version)` | Schema version `nibli-ast-v1` |
| `ast_statement(statement, root, intent)`, `ast_next_statement(before, after)` | Ordered assertion or query roots |
| `ast_node(node, kind)` | Every claim, term, argument, sequence, word, binder, and clause |
| `ast_child(parent, field, index, child)`, `ast_length(parent, field, length)` | Ordered structural fields, including empty lists |
| `ast_value(node, field, type, value)` | Names, literal values, determiner/prefix tags, and counts |
| `ast_span(node, start, end)` | Parser byte spans where the AST carries them |
| `ast_text_byte(text, index, byte)`, `ast_text_end(text, length)` | UTF-8 payload bytes |
| `ast_index_next(index, successor)` | Finite ordinal successor relation |
| `lex_pred(spelling, canonical, arity)`, `lex_place(spelling, label, surface, canonical)` | Committed lexicon projection, including converted aliases |
| `lex_role(predicate, place, role)`, `lex_domain(predicate, domain)` | Fixed lexical spellings of event roles and definite domains |
| `lex_builtin(predicate, kind)`, `lex_pronoun(spelling, constant)`, `lex_name_byte(byte, folded)` | Builtin classification, pronouns, and ASCII name-folding alphabet |

Every argument is a quoted Nibli string constant. Source text uses injective
`text:` plus hexadecimal UTF-8 encoding; numbers retain their IEEE-754 bits.
Nodes have source-order traversal IDs, and text tables are sorted. Variables,
predicate names, punctuation, and malicious strings cannot escape into subject
code. The committed snapshot pins byte-for-byte output.

The parser, serializer, committed lexicon, and Nibli evaluator remain trusted.
Stage 1 demonstrates that this checker satisfies its own checks. Stage 2 is a
regression oracle over concrete programs; it is not a universal proof that
the Rust compiler and checker are equivalent for every program.

## Native behavior and advisories

The compatibility profile is a fresh `CoreSession` with default compute names,
existential import off, and strict mode off. Query intent runs compilation
checks without asserting the subject. Parser rejection, manually corrupted
AST/IR, runtime compute dispatch, retraction, and alternate session profiles
are outside this comparison. Aggregation has an embedding API but no separate
KR AST constructor; source exact-count expressions are covered.

`checker_complete("program:0")` must be true before interpreting acceptance
as a verdict. `checker_accepts("program:0")` is the ground acceptance proposition.
`native_violation(program, node, category)` retains diagnostic locations;
`violation_kind(program, category)` provides ground category queries. Categories
cover vocabulary, derived-only facts, declaration order, arity, places,
special-term positions, textual scope, query-only constructs, assertion forms,
and stratification.

The current implementation is experimental and does not establish equivalence
for all parsed programs. In particular, literal declarations targeting
compiler-generated `__abs_` quotation identities produce
`checker_incomplete(program, "quotation_identity_declaration")` when ground
quotations are present. Their canonical IR identity is not part of the raw AST
export, and its independent Nibli encoding remains unimplemented. These inputs
cannot receive `checker_complete` or `checker_accepts`; they must not be
reported as native compiler rejections either. The native compiler remains
authoritative for this boundary.

The checker preserves current native behavior:

- Predicate spellings resolve against the committed lexicon. `admits` does
  not add vocabulary. Its closed-vocabulary gate concerns asserted facts;
  rule heads and bodies still resolve through the lexicon.
- Declarations take effect in statement order. The gates for a conjunction
  see the declarations that preceded that statement.
- Fewer arguments are permitted; excess arguments, unknown labels, repeated
  places, and invalid restrictor bound places are refused.
- Unsafe rule variables and overlapping `admits`/`derived_only` declarations
  are accepted by native assertion ingress. They produce
  `advisory_kind(program, "range_restriction")` and
  `advisory_kind(program, "schema_conflict")`, respectively, without changing
  the native acceptance proposition.
- Dependencies are derived in Nibli from structural facts. Positive recursive
  rules compute ordinary reachability and paths containing at least one
  negative edge. A negative path back to its start identifies an
  unstratifiable cycle; two negative edges do not cancel.

The integration tests require definitive results and completed materialization
for each verdict relation. `UNKNOWN`, resource exhaustion, or an incomplete
analysis cannot count as a successful check. Ground verdict queries also avoid
the cost of enumerating anonymous witnesses in recursive diagnostic relations.

## Regression coverage

`nibli-verify/tests/self_check.rs` checks the live specification's own AST,
Utopia, GDPR, drug interactions, Lucy's constitution, and the adjudication
policy. It also exercises the KR construct inventory in assertion and query
modes, hostile mutations, declaration and scope edge cases, seeded dependency
graphs, and the native 32-clause DNF boundary. The self-check content pins
require acceptance and absence of every rejection category and both advisories.

Changes to AST constructors must update the exhaustive exporter walk and the
checker together. Changes to lexical metadata or native static policy must
update the relevant differential cases. Existing domain specifications are
inputs to these tests and retain their original semantics.

## Production proof checkpoint

`proofs/self-check/` contains a separate, pinned Charon → Aeneas → Lean
environment for extracting the production Rust functions. Its Nix lock pins
Aeneas and its compatible Charon toolchain; the Lake manifest pins the Lean
libraries. The shipping Rust toolchain is unchanged. This checkpoint targets
`x86_64-unknown-linux-gnu` under the extraction toolchain, with default crate
features and debug checks enabled.

The component gate regenerates the verdict combiners and their Nibli
dependencies, checks `Verdicts.lean` against those generated definitions, and
audits every theorem's axioms. It proves totality, the exact conditions for
definitive conjunction/disjunction/NAF verdicts, indeterminate propagation, and
resource/reason precedence. It does not verify the callers or general evaluator.
The trusted boundary includes Rust/MIR compilation, Charon and Aeneas translation,
Lean's kernel, and the imported primitive library specifications; this is not a
proof of those tools or of the shipping compiler binary.

Bootstrap the pinned Lean dependencies once, then run the gates:

```sh
nix develop ./proofs/self-check --command elan toolchain install leanprover/lean4:v4.35.0
nix develop ./proofs/self-check
cd proofs/self-check
lake exe cache get
cd ../..
just verify-self-check-verdicts
just verify-self-check-scc-stack
just verify-self-check-extraction
```

The extraction gate probes the exporter, validating emitter, semantic compiler,
quotation codec, stratifier, indexed SCC kernel, assertion ingress, evaluator,
and arithmetic. Its current result is a failure: the pinned Aeneas cannot translate all these paths.
Observed blockers include nested borrows in the exporter, loop exits in compiler
and reasoner code, and floating-point operations in native arithmetic. A larger
timeout does not resolve an unsupported operation. The verdict component gate
can pass independently; its report always leaves full self-check equivalence
unverified.

The production SCC traversal now lives in `nibli-reason/src/dependency_graph.rs`.
Both stratification and materialization call this indexed, iterative Tarjan
kernel through the existing predicate-name adapter. Fixed stack buffers keep
the traversal within the extractor's supported operations. The kernel and named
stratifier now translate without opaque Nibli definitions. The named path uses
the explicit standard-library boundary described below.

The name adapter and negative-edge scan use owned temporary names and explicit
loops. The scan retains the first diagnostic in the existing traversal order
and returns it after the loops. The named path passes fresh Charon/Aeneas
extraction, Lean compilation, and binding assumption audits using the reviewed
`stratifier-std-v1` profile. This is extraction under library specifications;
the predicate-name adapter and negative-edge decision still need correctness
proofs.

The diagnostic uses explicit string appends with the same text and predicate
names. The pinned Aeneas formatting model represents arguments as `Unit`, erasing
their contents before the external formatting call. Avoiding that call keeps the
diagnostic values available to a future proof; it does not itself verify string
operations or their allocation behavior.

`just verify-self-check-library-models` checks the library model contracts.
`StdStrings.lean` preserves exact UTF-8 bytes, including Unicode
and embedded NULs, through borrowing, conversion, cloning, and appending.
Comparison uses unsigned UTF-8 bytes, and equality of the byte representations
implies equality of the strings. Invalid UTF-8 is refused, and modeled byte-vector
allocations are bounded by the target's `isize` maximum. This is a conditional
allocation model, not a guarantee that the host can satisfy an allocation.
The command checks the complete public theorem inventory, re-elaborates with
warnings fatal, binds the report to source hashes, and audits transitive proof
assumptions. Its report verifies model contracts only: it leaves native std
implementation, extraction binding verification, and full self-check equivalence
false. The extraction report separately records installed models, successful
binding typechecking, and completed binding assumption audits.

`StdMaps.lean` models finite-map entries in arbitrary enumeration order. Its
contracts prove exact lookup, replacement of only the selected binding, return
of the former value, preservation of unique keys, and growth only for a new key.
Lookup is invariant under permutation of a valid entry list. The iterator
contract returns exactly the next entry and reduces the remaining enumeration.
`StdSetsSort.lean` proves membership, uniqueness, and exact cardinality changes
for set insertion; ordered insertion preserves order. Sorting produces a
permutation in comparator order with unchanged length. Comparisons remain
monadic, and the proofs require explicit success, totality, and transitivity
contracts rather than assuming arbitrary comparisons behave correctly.
These collection models operate on mathematical lists. Proving the named
stratifier establishes their representation invariants remains open.
The model runner audits each selected module separately and clears all selected
reports before starting, so an early failure cannot leave a later stale success.

`StdHash.lean` records a hashing byte stream and takes its digest function as a
parameter. Its string contract appends the exact UTF-8 bytes and the `0xff`
delimiter. This specifies the collection-hashing interface; it does not prove
SipHash, randomness, collision resistance, or quotation identity. The finite-map
and set models expose equality and membership without physical hash buckets.
`StdBounded.lean` checks that element counts and slice lengths fit the extracted
machine word, failing explicitly on overflow. Concrete allocator capacity,
layout, and host resource behavior remain outside these models.

`std_boundary.py` supplies only the reviewed standard-library bindings.
`std_boundary_signatures.json` pins every Lean signature and corresponding Rust
identity, together with the template preambles. The profile is restricted to the
named-stratifier and combined SCC extraction roots. Missing or additional
declarations, changed Rust identities or types, extra header/inter-declaration
code, unexpected template files, and use from another probe all fail. Both
template inventories are checked before either replacement is written. Each
profiled extraction audits every model, compiles the bound generated modules,
and checks the transitive assumptions of every external type and function.
The extraction report records this boundary and leaves native standard-library
implementation verification false. Nibli compiler functions cannot be replaced
through this profile. The combined SCC extraction includes the named path so
later proofs can use one set of generated kernel and adapter definitions.

`just verify-self-check-scc-stack` regenerates the kernel and checks
`SccGraph.lean`, `SccKernelProofs.lean`, `SccInvariant.lean`, `SccTermination.lean`,
`SccTraversal.lean`, and `SccCriterion.lean`.
The proofs establish component-removal termination, the
topmost-root stopping position, the exact reversed active suffix returned, and
preservation of the state-buffer length. The complete removal preserves every
state entry except the emitted nodes' stack flags, which it clears. These
preconditions require a root in the active stack prefix and valid state indices.

The `pop_component_scc` theorem connects that extracted operation to graph
reachability. It proves that the emitted list is exactly a maximal mutual-
reachability class, without duplicates, under explicit `RootFrontier` and ordered-
stack preconditions. `SccGraph.lean` defines these conditions over the extracted
graph and Rust discovery indices and lowlinks: live DFS ancestors reach later
active nodes, active nodes return to an ancestor, processed edges respect the
lowlink bound, and completed vertices form a disjoint forward-closed set. Removal
preserves discovery metadata, the remaining stack's order and membership flags,
and forward closure after adding the emitted component to the completed set.

The DFS branch contracts also refer directly to the extracted loop body. They
prove exact updates for discovering a vertex, inspecting a visited target,
finishing a nonroot frame, completing a root, and exiting with an empty DFS
stack. These contracts cover arithmetic and buffer bounds, parent edge-cursor
advancement, both stack pushes, and parent-lowlink propagation. Edges to completed
components leave the current lowlink unchanged. The root-completion contract
applies `pop_component_scc`, appends its output, and preserves its graph result
through the caller's parent update. `DfsState` only names the native tuple's
fields; it defines no replacement traversal. `EmissionReady` binds the root
preconditions to the actual active stack, DFS frames, and completed-component
buffer.

`SccInvariant.lean` records discovery indices, active-stack order, live frames,
completed components, reachability witnesses, and processed-edge bounds for each
frame's active interval. The production allocation prefix establishes this
invariant. From it, the proofs derive every local branch's bounds and the root
emission preconditions, so one iteration of the extracted DFS body cannot fail.
An empty DFS stack also implies no active vertices remain. Inspecting an already
visited target preserves the complete invariant, both for active targets and
targets in completed components. Discovery also preserves it: the fresh index,
both stack pushes, and the parent's advanced cursor maintain discovery order,
reachability witnesses, and the processed-edge bounds.

Both frame-completion branches preserve the invariant. For a nonroot, the
lowlink witness gives a return path to an earlier live frame, and the parent's
new lowlink bounds the merged active interval. Root completion emits the maximal
SCC, moves its vertices to the completed set, and preserves witnesses for retained
vertices. The parent-lowlink write after root emission leaves its state unchanged.
The combined `invariant_step_preserved` theorem covers every inner-loop branch.

`SccTermination.lean` proves termination of the actual inner DFS loop from any
state satisfying the invariant. Its lexicographic measure tracks undiscovered
vertices, the remaining cursor increments allowed by the work buffer's machine
word bounds, and live DFS depth. Discovery decreases the first part, inspecting a
visited target decreases the second, and completion decreases the third. The
`dfs_total` theorem combines these decreases with invariant preservation through
the extracted loop's well-founded recursion and returns with both logical stacks
empty. It also preserves every previously discovered vertex.

`SccTraversal.lean` closes the indexed kernel's outer-loop obligations. Starting
a fresh root establishes the DFS invariant from empty stacks. Each scan iteration
advances the cursor and preserves discovery of the scanned prefix, including the
new root after DFS. The scan terminates at the graph length. Composing this with
the production allocation prefix gives `compute_sccs_correct`: for every graph
whose edge targets are in bounds, the actual indexed kernel terminates and returns
a partition into nonempty, valid maximal SCCs. Every graph vertex appears exactly
once across the components.

`SccCriterion.lean` specifies `dep_path` and `neg_dep_path` by the same positive
Horn clause shapes used in the checker. A negative path is exactly an arbitrary
prefix, a marked negative edge, and an arbitrary suffix. Thus a negative self-path
exists exactly when a negative edge has a return path. For the partition returned
by the actual indexed kernel, this is equivalent to both endpoints of a negative
edge belonging to one component. The proof requires negative edges to be graph
edges, and handles any number of negative edges without a parity assumption.
The gate conservatively checks every source line mentioning the modeled checker
predicates, including their declarations and violation consumer. This catches
source drift; it is not a parser or evaluator refinement proof.

The predicate-name adapter, native negative-edge scan, dependency extraction,
and production evaluation of the Horn clauses remain separate obligations. The
component report certifies the indexed SCC kernel and its mathematical criterion
bridge under the stated graph precondition and trusted extraction/library
boundary; it does not certify the whole stratifier or checker.

The shared component runner regenerates each component in its own Lean module,
checks every local proof file's public theorem inventory, rechecks helpers with warnings fatal,
and applies the same source/artifact drift and transitive axiom audits to both
gates. The ordinary Rust suite also checks the indexed
kernel against independent reachability on exhaustive small graphs, long chains
and cycles, and the existing compiler/checker differential corpus.

Commands, source hashes, diagnostics, and generated artifacts are written below
`target/self-check-proof/`. The runners reject missing production roots, opaque
Nibli dependencies, unreviewed external-definition templates, stale artifacts, concurrent
runs, and source changes during a run. Missing tools, an admitted theorem, or an
unexpected axiom cannot become a passing proof result. The axiom audit permits
only Lean's `propext`, `Classical.choice`, and `Quot.sound` foundations.

`coverage.toml` maps the remaining obligations to implementation and regression
sources. It is an obligation inventory, not an exhaustive call-graph certificate.
Full compiler/checker equivalence, independent quotation identity, a verified
general evaluator, and a composed Stage 1 theorem remain unproved. The initial
extraction feasibility milestone is therefore blocked; the full-equivalence
proof gate and certified CLI are not implemented. The existing Stage 1/Stage 2
regression gate remains `just verify-self-check`.
