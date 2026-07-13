//! The agentic formalization loop — the self-correcting core.
//!
//! [`translate_agentic`] asks the LLM for a candidate, runs it through the
//! validation gate, and on failure appends the compiler's own message to the
//! conversation and asks again, up to `max_attempts`. A provider/transport
//! error aborts as [`Outcome::ChatFailed`] (not a gate failure); an exact
//! repeat of the previous candidate stops early as [`Outcome::Exhausted`].
//!
//! A gate-clean candidate then faces the SEMANTIC VERIFICATION TURN
//! ([`crate::verify`]): a fresh-context judge reads the engine's own
//! back-translation of each KB line and a MISMATCH verdict retries through the
//! same feedback loop as a gate failure (`GateError::Verification`) — the
//! syntax gates prove well-formedness, this turn checks MEANING (best-effort).
//! The whole thing is native-testable via a mock [`crate::llm::ToolChat`].
//! (The jbotci MCP tool loop retired with the Lojban front-end at THE DROP.)

use crate::gates::{self, GateError};
use crate::llm::{LlmConfig, ToolChat, Turn, clean_output, system_prompt};
use crate::verify;

/// One outer-loop iteration: the candidate the LLM produced and the gate error it
/// hit (`None` = it passed every gate).
#[derive(Clone, Debug)]
pub struct Attempt {
    pub n: u32,
    pub candidate: String,
    pub error: Option<GateError>,
}

/// The result of a formalization run, always carrying the full attempt trace
/// for the UI.
#[derive(Debug)]
pub enum Outcome {
    /// Converged — the formalized `kr` text passed every gate.
    Success { kr: String, attempts: Vec<Attempt> },
    /// Hit the attempt cap or an oscillation without converging; `best` is the last
    /// candidate and `last_error` the gate it failed.
    Exhausted {
        best: String,
        last_error: GateError,
        attempts: Vec<Attempt>,
    },
    /// The provider call itself failed (network/auth/parse) — distinct from a gate
    /// failure, so the caller can show a transport error rather than "invalid KR".
    ChatFailed {
        error: String,
        attempts: Vec<Attempt>,
    },
}

/// Cap on how many prior failed-attempt `[assistant, user-feedback]` pairs the
/// conversation carries into the next attempt. The original request (`convo[0]`) is
/// always kept; older middle pairs are dropped so the context can't grow without
/// bound under a large `max_attempts`. The most recent failures are what the model
/// actually corrects from, so keeping the tail preserves convergence.
const MAX_HISTORY_PAIRS: usize = 3;

/// Trim `convo` in place to the original request plus the last `keep_pairs`
/// `[assistant, user]` feedback pairs. Safe because `convo` only ever holds User/
/// Assistant text turns (the tool loop's `AssistantTools`/`ToolResults` turns are
/// ephemeral — see `tools.rs`), and pairs are appended atomically, so `len - 1` is
/// always even and a pair-aligned drop can't split a pair.
fn trim_history(convo: &mut Vec<Turn>, keep_pairs: usize) {
    let max_len = 1 + keep_pairs * 2;
    if convo.len() <= max_len {
        return;
    }
    let first_kept = convo.len() - keep_pairs * 2;
    convo.drain(1..first_kept);
}

/// Formalize `source` into a valid KR KB, self-correcting against the
/// validation gate. See the module docs for the termination rules.
///
/// `validator` is the FRESH-CONTEXT semantic judge (int19h's suggestion): after
/// the gates pass, the engine's own back-translation of the candidate is sent
/// to `validator` in a brand-new single-turn conversation — the Chat seam is
/// stateless, so the judge never sees the translation history and cannot
/// green-light its own past output. A MISMATCH verdict retries through the
/// same bounded feedback loop as a hard gate failure
/// (`GateError::Verification`). The check is best-effort advisory: a validator
/// transport error or malformed verdict never blocks a gate-clean translation
/// (the deterministic gates remain the hard guarantee). Callers typically pass
/// the same zero-sized `HttpChat` for `chat` and `validator`.
pub async fn translate_agentic<C: ToolChat, V: ToolChat>(
    chat: &C,
    validator: &V,
    cfg: &LlmConfig,
    source: &str,
    max_attempts: u32,
) -> Outcome {
    let max_attempts = max_attempts.max(1);

    // "Formalize", not "translate": the LLM step is interpretive
    // formalization behind gates — "compile" stays reserved for the
    // deterministic KB→logic step (user decision 2026-07-12).
    let request = format!("Formalize into nibli KR: {}", source.trim());
    let mut convo = vec![Turn::user(request)];
    let mut attempts: Vec<Attempt> = Vec::new();
    let mut prev: Option<String> = None;

    for n in 1..=max_attempts {
        // Bound the context: keep the request + the most recent failed attempts.
        trim_history(&mut convo, MAX_HISTORY_PAIRS);
        let raw = match chat.chat_tools(cfg, system_prompt(), &convo, &[]).await {
            Ok(reply) => reply.text.unwrap_or_default(),
            Err(e) => {
                return Outcome::ChatFailed {
                    error: e.to_string(),
                    attempts,
                };
            }
        };
        let candidate = clean_output(&raw);

        // Gate check first; a gate-clean candidate then faces the fresh-context
        // semantic verifier. Folding the verifier's MISMATCH into the same
        // `Err` arm reuses the whole retry machinery (trace, oscillation
        // guard, feedback turns, exhaustion).
        let gate_result = match gates::validate_kb(&candidate) {
            Ok(()) => verify_semantics(validator, cfg, source, &candidate).await,
            Err(e) => Err(e),
        };
        match gate_result {
            Ok(()) => {
                attempts.push(Attempt {
                    n,
                    candidate: candidate.clone(),
                    error: None,
                });
                return Outcome::Success {
                    kr: candidate,
                    attempts,
                };
            }
            Err(err) => {
                let oscillated = prev.as_deref() == Some(candidate.as_str());
                attempts.push(Attempt {
                    n,
                    candidate: candidate.clone(),
                    error: Some(err.clone()),
                });
                if oscillated {
                    return Outcome::Exhausted {
                        best: candidate,
                        last_error: err,
                        attempts,
                    };
                }
                prev = Some(candidate.clone());
                convo.push(Turn::assistant(candidate));
                convo.push(Turn::user(gates::feedback_for(&err)));
            }
        }
    }

    // Cap reached without success. The last attempt necessarily failed a gate.
    let (best, last_error) = {
        let last = attempts
            .last()
            .expect("max_attempts >= 1 ⇒ at least one attempt was recorded");
        (
            last.candidate.clone(),
            last.error
                .clone()
                .expect("a non-success attempt carries its gate error"),
        )
    };
    Outcome::Exhausted {
        best,
        last_error,
        attempts,
    }
}

/// The fresh-context semantic verification turn. `Ok(())` = verified or
/// best-effort skipped; `Err(GateError::Verification)` = the judge reported a
/// concrete meaning mismatch. Fail-open by design at every non-verdict edge:
/// back-translation failure (cannot normally happen — the gates just passed),
/// validator transport error, tool-call-only reply, or a malformed verdict all
/// let the gate-clean candidate through — the deterministic gates are the hard
/// guarantee, this turn is the advisory meaning check.
async fn verify_semantics<V: ToolChat>(
    validator: &V,
    cfg: &LlmConfig,
    source: &str,
    candidate: &str,
) -> Result<(), gates::GateError> {
    let Ok(back) = verify::back_translation(candidate) else {
        return Ok(());
    };
    if back.is_empty() {
        return Ok(());
    }
    let prompt = verify::judge_prompt(source, &back);
    // A brand-new single-turn conversation: the judge sees only the source,
    // the candidate lines, and the engine's reading of them.
    let reply = match validator
        .chat_tools(
            cfg,
            verify::VALIDATOR_SYSTEM_PROMPT,
            &[Turn::user(prompt)],
            &[],
        )
        .await
    {
        Ok(r) => r,
        Err(_) => return Ok(()),
    };
    match reply.text.as_deref().and_then(verify::parse_verdict) {
        Some(issues) => Err(gates::GateError::Verification(issues)),
        None => Ok(()),
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;
    use crate::llm::{ChatError, ChatResponse, Provider, ToolDecl};
    use std::cell::RefCell;

    /// A `ToolChat` that hands back pre-scripted responses in order (text-only —
    /// these tests exercise the outer validate/feedback loop, not tool-use) and
    /// records every conversation it is handed, so tests can inspect both the
    /// translation feedback turns and the validator's fresh context.
    struct Scripted {
        replies: RefCell<Vec<Result<ChatResponse, ChatError>>>,
        seen: RefCell<Vec<(String, Vec<Turn>)>>,
    }
    impl Scripted {
        fn new(replies: Vec<Result<ChatResponse, ChatError>>) -> Self {
            Self {
                replies: RefCell::new(replies),
                seen: RefCell::new(Vec::new()),
            }
        }
    }
    impl ToolChat for Scripted {
        async fn chat_tools(
            &self,
            _cfg: &LlmConfig,
            system: &str,
            turns: &[Turn],
            _tools: &[ToolDecl],
        ) -> Result<ChatResponse, ChatError> {
            self.seen
                .borrow_mut()
                .push((system.to_string(), turns.to_vec()));
            self.replies.borrow_mut().remove(0)
        }
    }

    /// A semantic validator that verifies everything — the neutral default for
    /// tests that exercise the gate loop, keeping their behavior unchanged.
    struct AlwaysMatch;
    impl ToolChat for AlwaysMatch {
        async fn chat_tools(
            &self,
            _cfg: &LlmConfig,
            _system: &str,
            _turns: &[Turn],
            _tools: &[ToolDecl],
        ) -> Result<ChatResponse, ChatError> {
            Ok(ChatResponse {
                text: Some("MATCH".to_string()),
                tool_calls: vec![],
            })
        }
    }

    fn text(s: &str) -> Result<ChatResponse, ChatError> {
        Ok(ChatResponse {
            text: Some(s.to_string()),
            tool_calls: vec![],
        })
    }

    /// A candidate the nibli-kr resolve rejects (unknown alias), distinct per tag.
    fn bad(tag: &str) -> String {
        format!("zzyzxq{tag}(Adam).")
    }
    const GOOD: &str = "dog(Adam).";

    fn run(replies: Vec<Result<ChatResponse, ChatError>>, max: u32) -> Outcome {
        run_seen(replies, max).0
    }

    /// Like `run`, returning the chat mock too, for prompt checks.
    fn run_seen(replies: Vec<Result<ChatResponse, ChatError>>, max: u32) -> (Outcome, Scripted) {
        let chat = Scripted::new(replies);
        let cfg = LlmConfig::new(Provider::Anthropic);
        let out = futures::executor::block_on(translate_agentic(
            &chat,
            &AlwaysMatch,
            &cfg,
            "Adam is a dog",
            max,
        ));
        (out, chat)
    }

    /// Like `run`, but with a scripted semantic validator; returns the outcome
    /// plus both mocks for conversation inspection.
    fn run_with_validator(
        replies: Vec<Result<ChatResponse, ChatError>>,
        validator_replies: Vec<Result<ChatResponse, ChatError>>,
        source: &str,
        max: u32,
    ) -> (Outcome, Scripted, Scripted) {
        let chat = Scripted::new(replies);
        let validator = Scripted::new(validator_replies);
        let cfg = LlmConfig::new(Provider::Anthropic);
        let out =
            futures::executor::block_on(translate_agentic(&chat, &validator, &cfg, source, max));
        (out, chat, validator)
    }

    #[test]
    fn fails_once_then_converges() {
        let out = run(vec![text(&bad("x")), text(GOOD)], 5);
        match out {
            Outcome::Success { kr, attempts, .. } => {
                assert_eq!(kr, GOOD);
                assert_eq!(attempts.len(), 2);
                assert!(attempts[0].error.is_some());
                assert!(attempts[1].error.is_none());
            }
            other => panic!("expected Success, got {other:?}"),
        }
    }

    #[test]
    fn exhausts_the_cap_when_never_valid() {
        let out = run(vec![text(&bad("1")), text(&bad("2")), text(&bad("3"))], 3);
        match out {
            Outcome::Exhausted { attempts, .. } => assert_eq!(attempts.len(), 3),
            other => panic!("expected Exhausted, got {other:?}"),
        }
    }

    #[test]
    fn stops_early_on_oscillation() {
        let out = run(vec![text(&bad("same")), text(&bad("same")), text(GOOD)], 5);
        match out {
            Outcome::Exhausted { attempts, .. } => assert_eq!(attempts.len(), 2),
            other => panic!("expected Exhausted (oscillation), got {other:?}"),
        }
    }

    #[test]
    fn provider_error_aborts_as_chat_failed() {
        let out = run(vec![Err(ChatError("boom".into()))], 5);
        assert!(matches!(out, Outcome::ChatFailed { .. }));
    }

    #[test]
    fn nibli_kr_mode_converges_and_uses_the_nibli_kr_prompt() {
        let (out, chat) = run_seen(vec![text("dog(Adam).")], 5);
        match out {
            Outcome::Success { kr, .. } => assert_eq!(kr, "dog(Adam)."),
            other => panic!("expected Success, got {other:?}"),
        }
        let seen = chat.seen.borrow();
        let (system, turns) = &seen[0];
        assert!(
            system.contains("nibli KR"),
            "nibli KR mode must select the nibli KR system prompt"
        );
        assert!(
            matches!(&turns[0], Turn::User(s) if s.starts_with("Formalize into nibli KR:")),
            "the nibli KR request turn says formalize, not translate: {turns:?}"
        );
    }

    #[test]
    fn nibli_kr_mode_feeds_the_gate_error_back_then_converges() {
        // Attempt 1 fails closed at the nibli-kr grammar gate (unknown alias);
        // the feedback turn must carry the nibli KR correction prose.
        let (out, chat) = run_seen(vec![text("zzyzxq(Adam)."), text("dog(Adam).")], 5);
        match out {
            Outcome::Success { kr, attempts, .. } => {
                assert_eq!(kr, "dog(Adam).");
                assert_eq!(attempts.len(), 2);
                assert!(matches!(attempts[0].error, Some(GateError::Syntax(_))));
            }
            other => panic!("expected Success, got {other:?}"),
        }
        let seen = chat.seen.borrow();
        let fed = seen[1].1.iter().any(
            |t| matches!(t, Turn::User(s) if s.contains("nibli-kr compiler") && s.contains("corrected nibli KR")),
        );
        assert!(
            fed,
            "nibli KR feedback turn missing from the retry conversation"
        );
    }

    // ── The semantic verification turn (int19h feedback, 2026-07-10) ──
    // Fixture: the Genesis 1:1–8 pair. Gemini's attempt PARSES — these 8 lines
    // pass every local gate verbatim (probe-verified) — while claiming nonsense
    // ("John is a name-word meaning a sun" for "God called the light Day").
    // Exactly the silent-mistranslation phenomenon the fresh-context verifier
    // exists to catch: grammar gates cannot see it, the back-translation can.

    const GENESIS_SOURCE: &str = "In the beginning God created the heaven and the earth. \
And God saw the light, that it was good: and God divided the light from the darkness. \
And God called the light Day, and the darkness he called Night.";

    /// Gate-valid nonsense — the KR re-creation of the original Lojban fixture
    /// (Gemini's Genesis lines, which passed every gate while claiming things
    /// like "John is a name-word meaning a sun"). Curated-core vocabulary so
    /// the fixture stays gate-valid in the CI fallback dictionary build.
    const GENESIS_GEMINI_PARSING: &str = "\
past goes(John, some market).
sees(John, some dog).
eats(some person, some food).";

    /// A simplified corrected retry (must genuinely pass the gates).
    const GENESIS_CORRECTED: &str =
        "past sees(some person, some animal).\nloves(some person, some animal).";

    const GENESIS_MISMATCH_VERDICT: &str = "MISMATCH\n\
1. Line 6 claims John is a name-word meaning a sun; the source says God called the light Day.\n\
2. Line 1 claims the creation was done by someone named John before some past thing; the source names God.";

    /// The phenomenon pin: every fixture line must keep passing the gates —
    /// if a grammar change eats the fixture, this fails loudly instead of the
    /// verification tests silently testing nothing.
    #[test]
    fn genesis_gemini_lines_pass_gates() {
        for line in GENESIS_GEMINI_PARSING.lines() {
            assert!(
                gates::validate(line.trim()).is_ok(),
                "fixture line no longer passes the gates (fixture rot): {line}"
            );
        }
        assert!(
            gates::validate_kb(GENESIS_CORRECTED).is_ok(),
            "the corrected retry KB must pass the gates"
        );
    }

    #[test]
    fn genesis_garbage_parses_but_mismatch_feeds_back() {
        let (out, chat, validator) = run_with_validator(
            vec![text(GENESIS_GEMINI_PARSING), text(GENESIS_CORRECTED)],
            vec![text(GENESIS_MISMATCH_VERDICT), text("MATCH")],
            GENESIS_SOURCE,
            5,
        );
        match out {
            Outcome::Success { kr, attempts, .. } => {
                assert_eq!(kr, GENESIS_CORRECTED);
                assert_eq!(attempts.len(), 2);
                match &attempts[0].error {
                    Some(GateError::Verification(issues)) => {
                        assert!(issues.contains("name-word"), "issues carried: {issues}")
                    }
                    other => panic!("attempt 1 must fail the semantic verifier, got {other:?}"),
                }
                assert!(attempts[1].error.is_none());
            }
            other => panic!("expected Success on the corrected retry, got {other:?}"),
        }
        // The translator's second call must carry the verifier's issues as the
        // feedback turn, in the house style.
        let seen = chat.seen.borrow();
        assert_eq!(seen.len(), 2);
        let fed = seen[1].1.iter().any(|t| {
            matches!(t, Turn::User(s) if s.contains("does not MEAN") && s.contains("name-word"))
        });
        assert!(
            fed,
            "semantic feedback turn missing from the retry conversation"
        );
        // The validator ran once per gate-clean candidate.
        assert_eq!(validator.seen.borrow().len(), 2);
    }

    #[test]
    fn validator_sees_fresh_context_only() {
        let (out, _chat, validator) =
            run_with_validator(vec![text(GOOD)], vec![text("MATCH")], "Adam is a dog", 3);
        assert!(matches!(out, Outcome::Success { .. }));
        let vseen = validator.seen.borrow();
        assert_eq!(vseen.len(), 1);
        let (system, turns) = &vseen[0];
        assert!(
            system.contains("independent semantic auditor"),
            "validator must get its own system prompt"
        );
        assert_eq!(turns.len(), 1, "fresh context = exactly one user turn");
        assert!(
            matches!(&turns[0], Turn::User(s) if s.contains("SOURCE TEXT") && s.contains(GOOD)),
            "the single turn carries source + candidate + claims"
        );
        assert!(
            !format!("{turns:?}").contains("Formalize into nibli KR:"),
            "the validator must never see the formalization conversation"
        );
    }

    #[test]
    fn validator_transport_error_is_best_effort() {
        // The deterministic gates are the hard guarantee; a judge outage never
        // blocks a gate-clean translation.
        let (out, _chat, _validator) = run_with_validator(
            vec![text(GOOD)],
            vec![Err(ChatError("net down".into()))],
            "Adam is a dog",
            3,
        );
        match out {
            Outcome::Success { attempts, .. } => assert!(attempts[0].error.is_none()),
            other => panic!("expected best-effort Success, got {other:?}"),
        }
    }

    #[test]
    fn unparseable_verdict_fails_open() {
        let (out, _chat, _validator) = run_with_validator(
            vec![text(GOOD)],
            vec![text("Looks mostly fine to me!")],
            "Adam is a dog",
            3,
        );
        assert!(matches!(out, Outcome::Success { .. }));
    }

    #[test]
    fn semantic_mismatch_oscillation_stops_early() {
        // The verifier keeps rejecting and the model repeats itself — the
        // shared oscillation guard ends the loop instead of burning attempts.
        let (out, _chat, _validator) = run_with_validator(
            vec![text(GOOD), text(GOOD)],
            vec![
                text("MISMATCH\n1. wrong participant"),
                text("MISMATCH\n1. wrong participant"),
            ],
            "Adam is a dog",
            5,
        );
        match out {
            Outcome::Exhausted {
                attempts,
                last_error,
                ..
            } => {
                assert_eq!(attempts.len(), 2);
                assert!(matches!(last_error, GateError::Verification(_)));
            }
            other => panic!("expected Exhausted (oscillation), got {other:?}"),
        }
    }

    /// A `ToolChat` that records the turns it is handed each call and always returns
    /// a distinct invalid candidate, so the loop runs to the cap and we can inspect
    /// how the conversation grows.
    struct Capturing {
        seen: RefCell<Vec<Vec<Turn>>>,
        n: std::cell::Cell<u32>,
    }
    impl Capturing {
        fn new() -> Self {
            Self {
                seen: RefCell::new(Vec::new()),
                n: std::cell::Cell::new(0),
            }
        }
    }
    impl ToolChat for Capturing {
        async fn chat_tools(
            &self,
            _cfg: &LlmConfig,
            _system: &str,
            turns: &[Turn],
            _tools: &[ToolDecl],
        ) -> Result<ChatResponse, ChatError> {
            self.seen.borrow_mut().push(turns.to_vec());
            let i = self.n.get();
            self.n.set(i + 1);
            Ok(ChatResponse {
                text: Some(bad(&i.to_string())),
                tool_calls: vec![],
            })
        }
    }

    #[test]
    fn history_is_trimmed_to_request_plus_recent_pairs() {
        // Six never-valid attempts: the conversation would otherwise grow to 11 turns
        // (1 + 2*5); trimming must bound it to 1 + 2*MAX_HISTORY_PAIRS, keeping the
        // original request as convo[0].
        let chat = Capturing::new();
        let cfg = LlmConfig::new(Provider::Anthropic);
        let out = futures::executor::block_on(translate_agentic(
            &chat,
            &AlwaysMatch,
            &cfg,
            "Adam is a dog",
            6,
        ));
        assert!(matches!(out, Outcome::Exhausted { .. }));
        let seen = chat.seen.borrow();
        assert_eq!(seen.len(), 6, "one chat call per attempt");
        let cap = 1 + MAX_HISTORY_PAIRS * 2;
        let request = Turn::user("Formalize into nibli KR: Adam is a dog");
        for turns in seen.iter() {
            assert!(
                turns.len() <= cap,
                "history exceeded the cap: {}",
                turns.len()
            );
            assert_eq!(
                turns[0], request,
                "the original request must stay as convo[0]"
            );
        }
        assert_eq!(
            seen.last().unwrap().len(),
            cap,
            "the last attempt should be trimmed to exactly the cap",
        );
    }
}
