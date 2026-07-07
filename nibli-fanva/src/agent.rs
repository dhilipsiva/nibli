//! The agentic translation loop — the self-correcting core.
//!
//! [`translate_agentic`] asks the LLM for a candidate — letting it call the jbotci
//! tools via [`crate::tools::run_llm_tool_loop`] when a proxy is configured — runs
//! the candidate through the validation gate, and on failure appends the compiler's
//! own message to the conversation and asks again, up to `max_attempts`. A
//! provider/transport error aborts as [`Outcome::ChatFailed`] (not a gate failure);
//! an exact repeat of the previous candidate stops early as [`Outcome::Exhausted`].
//!
//! When the MCP client has no proxy (or it is unreachable) the loop runs with NO
//! tools — the local gerna+smuni+camxes gates only — and flags the `Outcome` as
//! `degraded`; it never hard-fails on jbotci being unavailable. The whole thing is
//! native-testable via a mock [`crate::llm::ToolChat`] + an empty [`McpClient`].

use crate::gates::{self, GateError};
use crate::llm::{LlmConfig, ToolChat, Turn, clean_lojban_output, system_prompt};
use crate::mcp::McpClient;
use crate::tools;

/// One outer-loop iteration: the candidate the LLM produced and the gate error it
/// hit (`None` = it passed every gate).
#[derive(Clone, Debug)]
pub struct Attempt {
    pub n: u32,
    pub candidate: String,
    pub error: Option<GateError>,
    /// The jbotci tools the model called while producing this candidate (empty
    /// when jbotci is off / no proxy configured).
    pub tool_calls: Vec<crate::tools::ToolCallTrace>,
}

/// The result of a translation run, always carrying the full attempt trace for the
/// UI. `degraded` is true when jbotci was unavailable (no proxy / unreachable), so
/// the run used only the local gates with no tool-use.
#[derive(Debug)]
pub enum Outcome {
    /// Converged — `lojban` passed every gate.
    Success {
        lojban: String,
        attempts: Vec<Attempt>,
        degraded: bool,
    },
    /// Hit the attempt cap or an oscillation without converging; `best` is the last
    /// candidate and `last_error` the gate it failed.
    Exhausted {
        best: String,
        last_error: GateError,
        attempts: Vec<Attempt>,
        degraded: bool,
    },
    /// The provider call itself failed (network/auth/parse) — distinct from a gate
    /// failure, so the caller can show a transport error rather than "invalid Lojban".
    ChatFailed {
        error: String,
        attempts: Vec<Attempt>,
        degraded: bool,
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

/// Translate `source` into valid Lojban, self-correcting against the validation
/// gate, with optional jbotci tool-use. See the module docs for the termination
/// rules and the degrade behavior.
pub async fn translate_agentic<C: ToolChat>(
    chat: &C,
    mcp: &McpClient,
    cfg: &LlmConfig,
    source: &str,
    max_attempts: u32,
    max_tool_steps: u32,
) -> Outcome {
    let max_attempts = max_attempts.max(1);

    // Discover the jbotci tools once. No proxy / unreachable ⇒ run tool-free on the
    // local gates and flag the run as degraded (never hard-fail).
    let (tool_decls, degraded) = if mcp.is_available() {
        match mcp.list_tools().await {
            Ok(t) => (tools::to_tool_decls(&t), false),
            Err(_) => (Vec::new(), true),
        }
    } else {
        (Vec::new(), true)
    };

    let mut convo = vec![Turn::user(format!(
        "Translate to Lojban: {}",
        source.trim()
    ))];
    let mut attempts: Vec<Attempt> = Vec::new();
    let mut prev: Option<String> = None;

    for n in 1..=max_attempts {
        // Bound the context: keep the request + the most recent failed attempts.
        trim_history(&mut convo, MAX_HISTORY_PAIRS);
        // Inner jbotci tool loop: the model may call tools while producing a
        // candidate. With `tool_decls` empty (degraded) this is a single text call.
        let (raw, tool_calls) = match tools::run_llm_tool_loop(
            chat,
            mcp,
            cfg,
            system_prompt(),
            convo.clone(),
            &tool_decls,
            max_tool_steps,
        )
        .await
        {
            Ok(pair) => pair,
            Err(e) => {
                return Outcome::ChatFailed {
                    error: e.to_string(),
                    attempts,
                    degraded,
                };
            }
        };
        let candidate = clean_lojban_output(&raw);

        match gates::validate_kb(&candidate) {
            Ok(()) => {
                attempts.push(Attempt {
                    n,
                    candidate: candidate.clone(),
                    error: None,
                    tool_calls,
                });
                return Outcome::Success {
                    lojban: candidate,
                    attempts,
                    degraded,
                };
            }
            Err(err) => {
                let oscillated = prev.as_deref() == Some(candidate.as_str());
                attempts.push(Attempt {
                    n,
                    candidate: candidate.clone(),
                    error: Some(err.clone()),
                    tool_calls,
                });
                if oscillated {
                    return Outcome::Exhausted {
                        best: candidate,
                        last_error: err,
                        attempts,
                        degraded,
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
        degraded,
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;
    use crate::llm::{ChatError, ChatResponse, Provider, ToolDecl};
    use std::cell::RefCell;

    /// A `ToolChat` that hands back pre-scripted responses in order (text-only —
    /// these tests exercise the outer validate/feedback loop, not tool-use).
    struct Scripted {
        replies: RefCell<Vec<Result<ChatResponse, ChatError>>>,
    }
    impl Scripted {
        fn new(replies: Vec<Result<ChatResponse, ChatError>>) -> Self {
            Self {
                replies: RefCell::new(replies),
            }
        }
    }
    impl ToolChat for Scripted {
        async fn chat_tools(
            &self,
            _cfg: &LlmConfig,
            _system: &str,
            _turns: &[Turn],
            _tools: &[ToolDecl],
        ) -> Result<ChatResponse, ChatError> {
            self.replies.borrow_mut().remove(0)
        }
    }

    fn text(s: &str) -> Result<ChatResponse, ChatError> {
        Ok(ChatResponse {
            text: Some(s.to_string()),
            tool_calls: vec![],
        })
    }

    /// A candidate gerna rejects (contains an invalid character), distinct per tag.
    fn bad(tag: &str) -> String {
        format!("la .adam. cu gerku .i \u{ff}{tag}")
    }
    const GOOD: &str = "la .adam. cu gerku";

    fn run(replies: Vec<Result<ChatResponse, ChatError>>, max: u32) -> Outcome {
        let chat = Scripted::new(replies);
        let mcp = McpClient::new(""); // empty proxy ⇒ degrade to the local gates
        let cfg = LlmConfig::new(Provider::Anthropic);
        futures::executor::block_on(translate_agentic(
            &chat,
            &mcp,
            &cfg,
            "Adam is a dog",
            max,
            4,
        ))
    }

    #[test]
    fn fails_once_then_converges() {
        let out = run(vec![text(&bad("x")), text(GOOD)], 5);
        match out {
            Outcome::Success {
                lojban, attempts, ..
            } => {
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
    fn mcp_unavailable_marks_degraded_and_uses_local_gates() {
        // Empty proxy ⇒ no tools ⇒ local gates only, and the run is flagged degraded.
        let out = run(vec![text(GOOD)], 5);
        match out {
            Outcome::Success {
                lojban, degraded, ..
            } => {
                assert_eq!(lojban, GOOD);
                assert!(degraded, "empty-proxy run must be marked degraded");
            }
            other => panic!("expected Success, got {other:?}"),
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
        let mcp = McpClient::new("");
        let cfg = LlmConfig::new(Provider::Anthropic);
        let out = futures::executor::block_on(translate_agentic(
            &chat,
            &mcp,
            &cfg,
            "Adam is a dog",
            6,
            4,
        ));
        assert!(matches!(out, Outcome::Exhausted { .. }));
        let seen = chat.seen.borrow();
        assert_eq!(seen.len(), 6, "one chat call per attempt");
        let cap = 1 + MAX_HISTORY_PAIRS * 2;
        let request = Turn::user("Translate to Lojban: Adam is a dog");
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
