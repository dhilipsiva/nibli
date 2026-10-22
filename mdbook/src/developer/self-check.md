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
