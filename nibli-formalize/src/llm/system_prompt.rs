//! The English→KB system prompt, GROUNDED in the actual nibli KR grammar and
//! dictionary. The prompt embeds:
//!   - the pest PEG grammar (`nibli_kr::GRAMMAR`, in-sync with the parser by
//!     construction),
//!   - a distilled §4/§6/§7 semantics block (determiners, operators/prefixes,
//!     relative clauses — the parts the grammar can't convey),
//!   - the FULL committed corpus (`nibli_lexicon::corpus::corpus_entries()`,
//!     plus `corpus_compounds()`) as `name(places…) — gloss` lines, so the model
//!     uses valid predicate names, and
//!   - the proven few-shot examples + the iterative-correction clause the
//!     validate→feedback loop relies on.
//!
//! Because the corpus is a compile-time input, the whole prompt is
//! source-independent: it is assembled ONCE via `LazyLock` and reused across every
//! self-correction turn, so `system_prompt()` keeps its `&'static str` signature.
//! ONE build mode since the committed-corpus milestone — local, CI and deployed
//! builds all embed the identical table, with no network and no FULL/FALLBACK
//! split.
//! (KR-only since THE DROP; the legacy Lojban prompt retired with the front end.)

use std::sync::LazyLock;

const ROLE: &str = "You are a formalizer. Rewrite the user's English text as nibli KR — a strict predicate-call knowledge-base language.";

const RULES: &str = "Rules:
- Output ONLY the nibli KR statements, nothing else. No explanations, no notes.
- One claim per line; every statement ends with a period: \"dog(Adam).\"
- A statement is predicate(arguments): the predicate is a lowercase English word (a third-person verb, or a noun/adjective), e.g. \"eats\", \"dog\", \"beautiful\".
- Names are capitalized words: \"Adam\". The speaker is \"me\", the listener \"you\".
- Positional arguments come first; extra places are named like keyword arguments after them: \"goes(Adam, destination: some market).\"
- Use a predicate word from the Predicates list below and fill its argument places in the order shown. The compiler FAILS CLOSED on words it does not know — if one is rejected, retry with a listed synonym.";

const SEMANTICS: &str = "Semantics (these details change the logic — get them right):

Determiners build a term from a predicate word and are NOT interchangeable:
- \"some dog\" — there exists a dog (use for English \"a/an/some\").
- \"the dog\" — one definite dog, a constant with no quantifier (only for a genuinely definite referent).
- \"every dog\" — universal; \"animal(every dog).\" is the rule \"every dog is an animal\".
- \"exactly 2 dog\" is an entity-count QUERY; \"no dog\" means \"exactly 0 dog\". Both are \
query-only and cannot appear in successful KB-assertion output. Nibli has no persistent \
cardinality-constraint assertion. If the source explicitly enumerates named members, assert \
only those source-supported ordinary facts. Otherwise preserve the exact/no formula so the \
deterministic gate reports it as unsupported: NEVER omit, weaken, or fabricate around the claim. \
An exact count inside opaque \"fact { ... }\" or \"event { ... }\" content is quoted, not an outer-KB assertion.
The arithmetic predicates \"product\", \"sum\", and \"quotient\" are also query-only compute \
formulas. Do not emit them as KB facts, rule guards, or rule conclusions; executable compute \
in asserted output is rejected before it can become a premise. The external compute names \
\"exponential\" and \"logarithm\" are query-only on the same terms — even before any backend \
registration; never emit them as KB facts or rule atoms either. Compute text inside an opaque \
fact/event abstraction remains quoted content.
The comparisons \"greater\", \"less\", and \"num_equal\" are query-only WHENEVER an operand is a \
number or a variable: a query computes them arithmetically, so an asserted one would never be \
consulted. There is no numeric threshold rule — do not write \"& greater($n, 15) ->\". Assert the \
classification the source states (a predicate like \"thin(Varfarin).\") instead of inventing a \
numeric condition around it. A comparison between two named things (\"greater(Alis, Bob).\" for \
\"Alis is taller than Bob\") is an ordinary relational fact and is fine.
When the body is compound or a variable must be shared across conjuncts, use a binder block:
  every dog $d: animal($d) & runs($d).
  some dog $d: big($d) & goes($d).
A restrictor may add a modifier (last word is the head: \"every data controller\"), a linked argument (\"every carer(of: some data)\"), or a relative clause (below).

Operators, precedence tightest-first: \"~\" (not) · the \"past\"/\"now\"/\"future\" and \"must\"/\"may\" prefixes · \"&\" (and) · \"|\" (or) · \"^\" (xor) · \"<->\" (iff) · \"->\" (if-then, right-associative). Parentheses group. \"A -> B\" is a rule.

Prefixes — choose at most ONE prefix family per atom: either one deontic (\"must\"/\"may\") OR one tense (\"past\"/\"now\"/\"future\"), optionally followed by one \"~\" (negation innermost):
- \"must ~eats(Adam).\" and \"past ~eats(Adam).\" are legal single-prefix examples.
- Never combine a tense and a deontic: both must-past and past-must orderings are rejected because the runtime has one flavor slot.
- \"past ~P\" is fine; \"~past P\" is NOT expressible — reword.
- Prefixes and \"~\" attach to a single predicate atom only: \"past (A & B)\" and \"~(A & B)\" are REJECTED — distribute by hand (write \"~A | ~B\").

Two universal forms (different shapes, both valid):
- \"animal(every dog).\" — universal in argument position (the rule \"all dogs are animals\").
- \"all $x: dog($x) -> animal($x).\" — an explicit prenex rule over $x.
$x names co-refer across ordinary connected clauses; an unbound $x in a body is existential. Do not reuse one free name across negative, modal, quantified, anonymous-witness, or abstraction scope boundaries; that ambiguous claim is rejected for both assertion and query. Variable names are preserved verbatim, with no fixed three-variable cap.

Relative clauses restrict or annotate the bound entity:
- \"where <body>\" restricts (domain side); \"also <body>\" adds incidental info.
- Bare-predicate sugar: \"every person where consents\" means \"where consents(it)\".
- Mandatory \"it\": inside a PARENTHESIZED clause body, write \"it\" explicitly for the bound entity: \"every dog where owns(it, some home)\". A full clause body with zero \"it\" is a syntax error.
- Stack freely (\"where A where B\") or conjoin (\"where A & B\").";

const ITERATIVE: &str = "This is an iterative process. You may receive a follow-up message reporting a grammar or semantic error from the nibli KR compiler about your previous output. When you do, correct that output and reply with ONLY the corrected nibli KR — no explanation, no apology. Prefer the simplest wording the strict compiler accepts.";

/// The few-shot examples. Kept in plain, high-frequency corpus vocabulary — the
/// gate-validity guard below compiles every one of them, so an exotic entry
/// would put the prompt at the mercy of a corpus refinement.
const EXAMPLES: &str = "Examples:
- \"The dog goes to the market\" → \"goes(some dog, destination: some market).\"
- \"I love you\" → \"loves(me, you).\"
- \"Adam sees the cat\" → \"sees(Adam, some cat).\"
- \"The big dog runs\" → \"runs(some [big dog]).\"
- \"I ate the food\" → \"past eats(me, some food).\"
- \"Every dog is an animal\" → \"animal(every dog).\"
- \"Adam does not eat\" → \"~eats(Adam).\"
- \"Adam and the cat eat\" → \"eats(Adam) & eats(some cat).\"
- \"The home is owned by Adam\" → \"owned(some home, Adam).\"";

/// One line per corpus predicate, sorted: `- name(place1, place2, …) — gloss`.
/// Every place is NAMED (the committed corpus has zero positional places), so
/// the model sees the arity and the named-argument vocabulary. Generated from
/// the shipped `nibli_lexicon` corpus (the committed four-figure table — one
/// build mode, always the whole of it), so it can never drift from what the
/// resolver actually accepts. The source gismu is deliberately ABSENT: gismu
/// spellings no longer resolve, and showing them would invite the model to
/// emit words that fail closed. Compounds get their own short section.
fn dictionary_block() -> String {
    let mut out = String::from(
        "Predicates — the valid predicate words and their argument places, `name(places…) — gloss`. Use these names:\n",
    );
    for entry in nibli_lexicon::corpus::corpus_entries() {
        out.push_str(&format!(
            "- {}({}) — {}\n",
            entry.name,
            entry.places.join(", "),
            entry.gloss
        ));
    }
    out.push_str(
        "\nCompound predicates — spelled with `+`, resolve only via these entries (an undefined compound is a compile error):\n",
    );
    for c in nibli_lexicon::corpus::corpus_compounds() {
        out.push_str(&format!(
            "- {}({}) — {}\n",
            c.name,
            c.places.join(", "),
            c.gloss
        ));
    }
    out
}

/// The assembled system prompt — built ONCE (the alias map is compile-time), then
/// reused verbatim across every self-correction turn.
static PROMPT: LazyLock<String> = LazyLock::new(|| {
    format!(
        "{ROLE}\n\n{RULES}\n\n{SEMANTICS}\n\nGrammar (pest PEG — the exact syntax the compiler accepts):\n```\n{grammar}\n```\n\n{dictionary}\n{ITERATIVE}\n\n{EXAMPLES}",
        grammar = nibli_kr::GRAMMAR.trim_end(),
        dictionary = dictionary_block(),
    )
});

/// The system prompt the agent loop passes to `chat()`.
pub fn system_prompt() -> &'static str {
    &PROMPT
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::{EXAMPLES, system_prompt};

    /// Every few-shot example shipped in the prompt must pass our own gates —
    /// otherwise the prompt would be teaching the model KB text that our own
    /// firewall rejects. `validate()` runs the render round-trip gate too, so every
    /// shipped example is additionally pinned canonical-compatible.
    ///
    /// This covers `EXAMPLES` only; `prose_kr_statements_are_gate_valid` below
    /// covers the KR written into the instruction prose.
    #[test]
    fn shipped_nibli_kr_examples_are_gate_valid() {
        let mut checked = 0;
        for line in EXAMPLES.lines() {
            let Some((_, rhs)) = line.split_once('→') else {
                continue;
            };
            let text = rhs.trim().trim_matches('"');
            if text.is_empty() {
                continue;
            }
            assert!(
                crate::gates::validate(text).is_ok(),
                "shipped few-shot example is not gate-valid: {text:?} — {:?}",
                crate::gates::validate(text).err()
            );
            checked += 1;
        }
        assert!(
            checked >= 5,
            "expected to check the few-shot examples, got {checked}"
        );
    }

    /// The few-shot guard above covered `EXAMPLES` and nothing else, so the KR
    /// written into the INSTRUCTION PROSE was ungated — which is how
    /// `every dog $d: animal($d) & barks($d).` shipped in `SEMANTICS` with
    /// `barks` not a corpus name at all, in a prompt whose own text warns that
    /// the compiler fails closed on unknown words. Every complete statement
    /// anywhere in the prompt must compile.
    ///
    /// Two shapes carry a complete statement, and both END IN `).` — that
    /// terminator is the whole discriminator, which is why the clause fragment
    /// `"every dog where owns(it, some home)"` and the notation `"~(A & B)"`
    /// are correctly skipped rather than reported as failures:
    ///   1. inside double quotes (`"animal(every dog)."`), and
    ///   2. alone on an indented line (the binder-block demo).
    ///
    /// A prose sentence that merely ends in `).` — "…or a relative clause
    /// (below)." — carries quotes elsewhere on the line, so rule 1 applies to
    /// it and only its QUOTED spans are considered; none of those terminate.
    #[test]
    fn prose_kr_statements_are_gate_valid() {
        let mut checked = 0;
        for block in [super::RULES, super::SEMANTICS] {
            for line in block.lines() {
                let quoted: Vec<&str> = line.split('"').collect();
                let candidates: Vec<&str> = if quoted.len() > 1 {
                    // Odd indices are the spans inside quotes.
                    quoted.iter().skip(1).step_by(2).copied().collect()
                } else {
                    vec![line.trim()]
                };
                for cand in candidates {
                    let text = cand.trim();
                    if !text.ends_with(").") || !text.contains('(') {
                        continue;
                    }
                    assert!(
                        crate::gates::validate(text).is_ok(),
                        "the shipped prompt teaches KR that our own gates reject: \
                         {text:?} — {:?}",
                        crate::gates::validate(text).err()
                    );
                    checked += 1;
                }
            }
        }
        assert!(
            checked >= 6,
            "prose KR extraction found only {checked} statement(s) — the shapes \
             moved and this guard is checking (almost) nothing"
        );
    }

    /// The grounding actually shipped: the assembled prompt embeds the exact pest
    /// grammar and a dictionary block generated from the committed corpus (one
    /// build mode — always the whole four-figure table).
    #[test]
    fn assembled_prompt_is_grounded() {
        let prompt = system_prompt();
        assert!(
            prompt.contains(nibli_kr::GRAMMAR.trim_end()),
            "system prompt does not embed the pest grammar"
        );
        assert!(
            prompt.contains("Never combine a tense and a deontic"),
            "system prompt does not teach the fail-closed prefix contract"
        );
        assert!(
            prompt.contains("\"exponential\" and \"logarithm\" are query-only"),
            "system prompt does not teach the reserved external compute names"
        );
        // Known corpus lines are present, gismu-free.
        assert!(
            prompt.contains("- goes(goer, destination"),
            "system prompt missing the dictionary block (or the goes entry)"
        );
        assert!(
            prompt.contains("- computer+user("),
            "system prompt missing the compound section"
        );
        assert!(
            !prompt.contains("— klama"),
            "gismu leaked into the dictionary block (they no longer resolve as input)"
        );
        // Entry lines have the `) — ` signature (close-paren, em-dash, gloss).
        let entry_lines = prompt.lines().filter(|l| l.contains(") — ")).count();
        assert!(
            entry_lines >= 1300,
            "dictionary block too small: {entry_lines} entry lines (the committed corpus is four-figure)"
        );
    }
}
