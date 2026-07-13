//! The English→KB system prompt. Extends the proven `nibli-ui` prompt shape
//! with an iterative-correction clause so the model expects, and acts on, the
//! compiler errors the validate→feedback loop appends to the conversation.
//! (KR-only since THE DROP; the legacy Lojban prompt retired with the front
//! end. The grammar+dictionary-grounded prompt builder is a tracked TODO.md
//! bullet.)

/// English→Klaro. Klaro (nibli KR) is the KB language: a predicate-call
/// surface (`dog(Adam).`). The few-shots use only curated-core vocabulary
/// (they must stay gate-valid in the CI fallback dictionary build — the guard
/// test below runs in both modes).
pub const KLARO_SYSTEM_PROMPT: &str = r#"You are a formalizer. Rewrite the user's English text as Klaro — a strict predicate-call knowledge-base language.

Rules:
- Output ONLY the Klaro statements, nothing else. No explanations, no notes.
- One claim per line; every statement ends with a period: "dog(Adam)."
- A statement is predicate(arguments): the predicate is a lowercase English word (third-person verb or noun/adjective), e.g. "eats", "dog", "beautiful".
- Names are capitalized words: "Adam". The speaker is "me", the listener "you".
- Determiners build terms from predicates: "some dog" (a/some), "every dog" (all), "no dog", "exactly 2 dog".
- "~" before the predicate negates the claim: "~eats(Adam)." (Adam does not eat).
- "past" / "future" before the predicate mark tense: "past eats(Adam)."
- Join claims with operators: "&" (and), "|" (or), "->" (if-then): "dog(Adam) & cat(Betis)."
- "X = Y." states that X and Y are the same individual.
- Extra argument places can be named like Python keyword arguments, after the positional ones: "goes(Adam, destination: some market)."
- Use common, simple English predicate words. The compiler fails closed on words it does not know — if a word is rejected, retry with a plainer synonym.

This is an iterative process. You may receive a follow-up message reporting a grammar or semantic error from the Klaro compiler about your previous output. When you do, correct that output and reply with ONLY the corrected Klaro — no explanation, no apology. Prefer the simplest wording the strict compiler accepts.

Examples:
- "The dog goes to the market" → "goes(some dog, destination: some market)."
- "I love you" → "loves(me, you)."
- "Adam sees the cat" → "sees(Adam, some cat)."
- "The big dog runs" → "runs(some [big dog])."
- "I ate the food" → "past eats(me, some food)."
- "Every dog is an animal" → "animal(every dog)."
- "Adam does not eat" → "~eats(Adam)."
- "Adam and the cat eat" → "eats(Adam) & eats(some cat)."
- "The home is owned by Adam" → "owned(some home, Adam).""#;

/// The system prompt the agent loop passes to `chat()`.
pub fn system_prompt() -> &'static str {
    KLARO_SYSTEM_PROMPT
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::KLARO_SYSTEM_PROMPT;

    /// Every few-shot example shipped in the prompt must pass our own gates —
    /// otherwise the prompt would be teaching the model KB text that our own
    /// firewall rejects. This also guards new examples. validate() runs the
    /// render round-trip gate too, so every shipped example is additionally
    /// pinned canonical-compatible. Uses curated-core vocabulary only, so it
    /// holds in the CI fallback dictionary build too.
    #[test]
    fn shipped_klaro_examples_are_gate_valid() {
        let examples = KLARO_SYSTEM_PROMPT
            .split("Examples:")
            .nth(1)
            .expect("the prompt has an Examples section");
        let mut checked = 0;
        for line in examples.lines() {
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
}
