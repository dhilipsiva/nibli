# nibli KR cookbook

Short surface cheat sheet. **Normative reference:** [NIBLI_KR.md](https://github.com/dhilipsiva/nibli/blob/main/NIBLI_KR.md) (v0.1). Executable grammar: `nibli-kr/src/nibli_kr.pest`. Examples match the product [README](https://github.com/dhilipsiva/nibli/blob/main/README.md) language table.

nibli KR is a strict predicate-call surface: one statement per line, ending with a period. Unknown predicate words are a **compile error**, never a guess — names resolve through the committed English corpus, fail-closed.

## Common patterns

| nibli KR | Reads as |
|----------|----------|
| `dog(Adam).` | Adam is a dog |
| `animal(every dog).` | every dog is an animal (a rule) |
| `~eats(Adam).` | Adam does not eat |
| `past eats(me, some food).` | I ate some food |
| `dog(Adam) & cat(Betis).` | conjunction (`\|` or, `->` if-then) |
| `goes(Adam, destination: some market).` | named argument places |
| `beautiful(every person where ~cat).` | rule with a negated restrictor (NAF) |
| `Kim = Adam.` | identity |
| `red(exactly 2 red).` | exact-count claim |
| `all $x: dangerous($x) & uses(Adam, $x) -> warns($x).` | prenex rule with variables |

## Predicates and places

```nibli-kr
dog(Adam).
goes(Adam, destination: some market).
```

- Positional args fill places in order; named args use corpus place labels (`destination:`, …).
- Converted aliases and compounds are dictionary-driven; uncurated `a+b` compounds fail closed.

## Rules

```nibli-kr
animal(every dog).
eats(every animal).
dog(Adam).
```

Description-style universals (`every dog`) compile to rules. Explicit prenex:

```nibli-kr
all $x: dog($x) -> animal($x).
```

## Negation-as-failure

```nibli-kr
~eats(Adam).
```

Stratified NAF under closed-world assumptions — see GUARANTEES for oracle coverage. Unstratifiable programs are rejected at assert time.

## Where to go next

- Full construct inventory and profiles: [NIBLI_KR.md](https://github.com/dhilipsiva/nibli/blob/main/NIBLI_KR.md)
- IR after compile: [LOGIC_IR.md](https://github.com/dhilipsiva/nibli/blob/main/LOGIC_IR.md)
- Try it without installing: [Playground](playground.md)
