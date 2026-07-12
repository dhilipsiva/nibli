//! The English→KB system prompts, one per front-end language. Each extends the
//! proven `nibli-ui` prompt shape with an iterative-correction clause so the
//! model expects, and acts on, the compiler errors the validate→feedback loop
//! appends to the conversation. [`system_prompt`] selects by [`Language`].

use nibli_types::lang::Language;

/// English→Klaro. Klaro is the primary KB language since THE FLIP: a
/// predicate-call surface (`dog(Adam).`) that is far closer to the English
/// source than Lojban, so the prompt is correspondingly simpler. The few-shots
/// use only curated-core vocabulary (they must stay gate-valid in the CI
/// fallback dictionary build — the guard test below runs in both modes).
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

/// English→Lojban (the legacy front-end).
pub const LOJBAN_SYSTEM_PROMPT: &str = r#"You are a Lojban translator. Translate the user's English text into grammatically correct Lojban.

Rules:
- Output ONLY the Lojban translation, nothing else. No explanations, no notes.
- Use standard Lojban grammar: [sumti] [selbri] [sumti] structure
- Use gadri: "lo" for veridical descriptions, "le" for non-veridical
- Wrap names in dots as cmevla: "Adam" → ".adam."
- Use "cu" to separate sumti from selbri when needed
- Use tense markers: "pu" (past), "ca" (present), "ba" (future)

Grammar fragments (a strict parser is picky about these):
- "cu" separates a leading sumti from the selbri: "la .adam. cu gerku".
- "na" just before the selbri negates the whole claim: "la .adam. na citka" (Adam does not eat).
- "ro lo X" means "every X" (a universal); plain "lo X" is "a/some X".
- "se" swaps the first two places of a selbri: "se viska" = "is seen by".
- ".i" starts a new sentence; ".e" joins two sumti ("and").
- Names are cmevla wrapped in dots, introduced by "la": "Adam" → "la .adam.".

This is an iterative process. You may receive a follow-up message reporting a grammar or semantic error from a Lojban compiler about your previous output. When you do, correct that output and reply with ONLY the corrected Lojban — no explanation, no apology. Prefer the simplest wording that a strict parser accepts.

Examples:
- "The dog goes to the market" → "lo gerku cu klama lo zarci"
- "I love you" → "mi prami do"
- "Adam sees the cat" → "la .adam. viska lo mlatu"
- "The big dog runs" → "lo barda gerku cu bajra"
- "I ate the food" → "mi pu citka lo cidja"
- "Every dog is an animal" → "ro lo gerku cu danlu"
- "Adam does not eat" → "la .adam. na citka"
- "Adam and the cat eat" → "la .adam. .e lo mlatu cu citka"
- "The cat is seen by Adam" → "lo mlatu cu se viska la .adam.""#;

/// The system prompt the agent loop passes to `chat()`, selected by the KB
/// language.
pub fn system_prompt(lang: Language) -> &'static str {
    match lang {
        Language::Klaro => KLARO_SYSTEM_PROMPT,
        Language::Lojban => LOJBAN_SYSTEM_PROMPT,
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::{KLARO_SYSTEM_PROMPT, LOJBAN_SYSTEM_PROMPT};
    use nibli_types::lang::Language;

    /// Every few-shot example shipped in a prompt must pass our own gates for
    /// its language — otherwise the prompt would be teaching the model KB text
    /// that our own firewall rejects. This also guards new examples.
    fn assert_examples_gate_valid(prompt: &str, lang: Language) {
        let examples = prompt
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
                crate::gates::validate(lang, text).is_ok(),
                "shipped few-shot example is not gate-valid for {lang:?}: {text:?} — {:?}",
                crate::gates::validate(lang, text).err()
            );
            checked += 1;
        }
        assert!(
            checked >= 5,
            "expected to check the few-shot examples, got {checked}"
        );
    }

    #[test]
    fn shipped_examples_are_gate_valid() {
        assert_examples_gate_valid(LOJBAN_SYSTEM_PROMPT, Language::Lojban);
    }

    /// The Klaro twin of the guard: validate() in Klaro mode also runs the
    /// render round-trip gate, so every shipped example is additionally pinned
    /// canonical-compatible. Uses curated-core vocabulary only, so it holds in
    /// the CI fallback dictionary build too.
    #[test]
    fn shipped_klaro_examples_are_gate_valid() {
        assert_examples_gate_valid(KLARO_SYSTEM_PROMPT, Language::Klaro);
    }
}
