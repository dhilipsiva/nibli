//! The English→KB system prompt, GROUNDED in the actual nibli KR grammar and
//! dictionary. The prompt embeds:
//!   - the pest PEG grammar (`nibli_kr::GRAMMAR`, in-sync with the parser by
//!     construction),
//!   - a distilled §4/§6/§7 semantics block (determiners, operators/prefixes,
//!     relative clauses — the parts the grammar can't convey),
//!   - the FULL shipped alias map (`nibli_lexicon::ALIASES`) as `alias(places…) —
//!     predicate` lines, so the model uses valid predicate names, and
//!   - the proven few-shot examples + the iterative-correction clause the
//!     validate→feedback loop relies on.
//!
//! Because the alias map is a compile-time input, the whole prompt is
//! source-independent: it is assembled ONCE via `LazyLock` and reused across every
//! self-correction turn, so `system_prompt()` keeps its `&'static str` signature.
//! Dual-mode automatically: the full ~1,341-alias map in a local build, the
//! curated core (~116) in the CI fallback build (whatever `ALIASES` holds).
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
- \"exactly 2 dog\" — entity counting; \"no dog\" means \"exactly 0 dog\".
When the body is compound or a variable must be shared across conjuncts, use a binder block:
  every dog $d: animal($d) & barks($d).      some dog $d: big($d) & goes($d).
A restrictor may add a modifier (last word is the head: \"every data controller\"), a linked argument (\"every carer(of: some data)\"), or a relative clause (below).

Operators, precedence tightest-first: \"~\" (not) · the \"past\"/\"now\"/\"future\" and \"must\"/\"may\" prefixes · \"&\" (and) · \"|\" (or) · \"^\" (xor) · \"<->\" (iff) · \"->\" (if-then, right-associative). Parentheses group. \"A -> B\" is a rule.

Prefixes — at most one deontic (\"must\"/\"may\"), one tense (\"past\"/\"now\"/\"future\"), and one \"~\", written in THAT fixed order (deontic outermost, then tense, then negation innermost):
- \"must past ~eats(Adam).\" is legal; keep that order.
- \"past ~P\" is fine; \"~past P\" is NOT expressible — reword.
- Prefixes and \"~\" attach to a single predicate atom only: \"past (A & B)\" and \"~(A & B)\" are REJECTED — distribute by hand (write \"~A | ~B\").

Two universal forms (different shapes, both valid):
- \"animal(every dog).\" — universal in argument position (the rule \"all dogs are animals\").
- \"all $x: dog($x) -> animal($x).\" — an explicit prenex rule over $x.
$x names co-refer within one statement; an unbound $x in a body is existential. At most 3 distinct bare variables per statement ($x $y $z); a 4th is a hard error.

Relative clauses restrict or annotate the bound entity:
- \"where <body>\" restricts (domain side); \"also <body>\" adds incidental info.
- Bare-predicate sugar: \"every person where consents\" means \"where consents(it)\".
- Mandatory \"it\": inside a PARENTHESIZED clause body, write \"it\" explicitly for the bound entity: \"every dog where owns(it, some home)\". A full clause body with zero \"it\" is a syntax error.
- Stack freely (\"where A where B\") or conjoin (\"where A & B\").";

const ITERATIVE: &str = "This is an iterative process. You may receive a follow-up message reporting a grammar or semantic error from the nibli KR compiler about your previous output. When you do, correct that output and reply with ONLY the corrected nibli KR — no explanation, no apology. Prefer the simplest wording the strict compiler accepts.";

/// The few-shot examples. Kept in curated-core vocabulary so the gate-validity
/// guard below holds in the CI fallback dictionary build too.
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
/// the shipped `nibli_lexicon` corpus (the committed ~1,342-entry table — one
/// build mode, always the full map), so it can never drift from what the
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
    /// shipped example is additionally pinned canonical-compatible. Curated-core
    /// vocabulary only, so it holds in the CI fallback dictionary build.
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

    /// The grounding actually shipped: the assembled prompt embeds the exact pest
    /// grammar and a dictionary block generated from the committed corpus (one
    /// build mode — always the full ~1,342-entry table).
    #[test]
    fn assembled_prompt_is_grounded() {
        let prompt = system_prompt();
        assert!(
            prompt.contains(nibli_kr::GRAMMAR.trim_end()),
            "system prompt does not embed the pest grammar"
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
            "dictionary block too small: {entry_lines} entry lines (the committed corpus is ~1,342)"
        );
    }
}
