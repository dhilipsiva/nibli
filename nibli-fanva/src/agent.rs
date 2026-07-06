//! The agentic translation loop — the self-correcting core.
//!
//! [`translate_agentic`] asks the LLM for a candidate, runs it through the
//! validation gate, and on failure appends the compiler's own message to the
//! conversation and asks again — up to `max_attempts`. A provider/transport error
//! aborts as [`Outcome::ChatFailed`] (not a gate failure); an exact repeat of the
//! previous candidate stops early as [`Outcome::Exhausted`] (the model is stuck).
//!
//! jbotci tool-use is not wired here yet (Phase 3); this is the outer
//! validate→feedback loop over the local gates, and it is fully native-testable
//! via a mock [`Chat`].

use crate::gates::{self, GateError};
use crate::llm::{Chat, LlmConfig, Turn, clean_lojban_output, system_prompt};

/// One outer-loop iteration: the candidate the LLM produced and the gate error it
/// hit (`None` = it passed every gate).
#[derive(Clone, Debug)]
pub struct Attempt {
    pub n: u32,
    pub candidate: String,
    pub error: Option<GateError>,
}

/// The result of a translation run, always carrying the full attempt trace for
/// the UI.
#[derive(Debug)]
pub enum Outcome {
    /// Converged — `lojban` passed every gate.
    Success {
        lojban: String,
        attempts: Vec<Attempt>,
    },
    /// Hit the attempt cap or an oscillation without converging; `best` is the
    /// last candidate and `last_error` the gate it failed.
    Exhausted {
        best: String,
        last_error: GateError,
        attempts: Vec<Attempt>,
    },
    /// The provider call itself failed (network/auth/parse) — distinct from a
    /// gate failure, so the caller can show a transport error rather than "invalid
    /// Lojban".
    ChatFailed {
        error: String,
        attempts: Vec<Attempt>,
    },
}

/// Translate `source` into valid Lojban, self-correcting against the validation
/// gate. See the module docs for the loop's termination rules.
pub async fn translate_agentic<C: Chat>(
    chat: &C,
    cfg: &LlmConfig,
    source: &str,
    max_attempts: u32,
) -> Outcome {
    let max_attempts = max_attempts.max(1);
    let mut convo = vec![Turn::user(format!(
        "Translate to Lojban: {}",
        source.trim()
    ))];
    let mut attempts: Vec<Attempt> = Vec::new();
    let mut prev: Option<String> = None;

    for n in 1..=max_attempts {
        let raw = match chat.chat(cfg, system_prompt(), &convo).await {
            Ok(t) => t,
            Err(e) => {
                return Outcome::ChatFailed {
                    error: e.to_string(),
                    attempts,
                };
            }
        };
        let candidate = clean_lojban_output(&raw);

        match gates::validate(&candidate) {
            Ok(_logic) => {
                attempts.push(Attempt {
                    n,
                    candidate: candidate.clone(),
                    error: None,
                });
                return Outcome::Success {
                    lojban: candidate,
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

    // Cap reached without success. The last attempt necessarily failed a gate
    // (a success would have returned above).
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::llm::{ChatError, Provider};
    use std::cell::RefCell;

    /// A `Chat` that hands back pre-scripted replies in order.
    struct Scripted {
        replies: RefCell<Vec<Result<String, ChatError>>>,
    }
    impl Scripted {
        fn new(replies: Vec<Result<String, ChatError>>) -> Self {
            Self {
                replies: RefCell::new(replies),
            }
        }
    }
    impl Chat for Scripted {
        async fn chat(
            &self,
            _cfg: &LlmConfig,
            _system: &str,
            _turns: &[Turn],
        ) -> Result<String, ChatError> {
            self.replies.borrow_mut().remove(0)
        }
    }

    /// A candidate gerna rejects (contains an invalid character), distinct per tag.
    fn bad(tag: &str) -> String {
        format!("la .adam. cu gerku .i \u{ff}{tag}")
    }
    const GOOD: &str = "la .adam. cu gerku";

    fn run(replies: Vec<Result<String, ChatError>>, max: u32) -> Outcome {
        let chat = Scripted::new(replies);
        let cfg = LlmConfig::new(Provider::Anthropic);
        futures::executor::block_on(translate_agentic(&chat, &cfg, "Adam is a dog", max))
    }

    #[test]
    fn fails_once_then_converges() {
        let out = run(vec![Ok(bad("x")), Ok(GOOD.into())], 5);
        match out {
            Outcome::Success { lojban, attempts } => {
                assert_eq!(lojban, GOOD);
                assert_eq!(attempts.len(), 2);
                assert!(attempts[0].error.is_some());
                assert!(attempts[1].error.is_none());
            }
            other => panic!("expected Success, got {other:?}"),
        }
    }

    #[test]
    fn exhausts_the_cap_when_never_valid() {
        // Three DISTINCT invalid candidates so the oscillation guard doesn't fire.
        let out = run(vec![Ok(bad("1")), Ok(bad("2")), Ok(bad("3"))], 3);
        match out {
            Outcome::Exhausted { attempts, .. } => assert_eq!(attempts.len(), 3),
            other => panic!("expected Exhausted, got {other:?}"),
        }
    }

    #[test]
    fn stops_early_on_oscillation() {
        // Same invalid candidate twice ⇒ stop before the cap (GOOD never consumed).
        let out = run(vec![Ok(bad("same")), Ok(bad("same")), Ok(GOOD.into())], 5);
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
}
