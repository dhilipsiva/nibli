//! The jbotci tool loop: give the LLM the jbotci tools, execute any it calls (via
//! an MCP client), feed the results back, and return the model's final text. The
//! provider-specific tool wiring lives in [`crate::llm`]; this is the integration
//! that binds it to [`crate::mcp`]. Phase 5 threads [`run_llm_tool_loop`] into
//! `agent::translate_agentic`.

use serde_json::Value;

use crate::llm::{ChatError, ChatResponse, LlmConfig, ToolChat, ToolDecl, ToolResult, Turn};
use crate::mcp::{McpClient, ToolInfo};

/// A record of one jbotci tool call the model made during the loop — surfaced in
/// the UI trace (the Phase-6 tool-call rows). Empty when jbotci is off.
#[derive(Clone, Debug, PartialEq)]
pub struct ToolCallTrace {
    pub name: String,
    pub args: Value,
    pub result: String,
    pub is_error: bool,
}

/// Executes a single tool call, returning `(content, is_error)`. Abstracted so the
/// loop is testable with a mock; the real impl is [`McpClient`].
#[allow(async_fn_in_trait)]
pub trait ToolRunner {
    async fn run_tool(&self, name: &str, args: &Value) -> (String, bool);
}

impl ToolRunner for McpClient {
    async fn run_tool(&self, name: &str, args: &Value) -> (String, bool) {
        match self.call_tool(name, args.clone()).await {
            Ok(r) => (r.text, r.is_error),
            // A transport/protocol failure is surfaced to the model as an error
            // tool result so it can adapt, rather than aborting the whole turn.
            Err(e) => (format!("tool error: {e}"), true),
        }
    }
}

/// Convert discovered MCP tools into provider-agnostic declarations.
pub fn to_tool_decls(tools: &[ToolInfo]) -> Vec<ToolDecl> {
    tools
        .iter()
        .map(|t| ToolDecl {
            name: t.name.clone(),
            description: t.description.clone(),
            input_schema: t.input_schema.clone(),
        })
        .collect()
}

/// Run the LLM with `tools` available; execute any tool calls via `runner`, feed
/// the results back, and repeat up to `max_tool_steps`. Returns the final text
/// plus a trace of every tool call made (for the UI). When the step cap is hit,
/// one last call is made with NO tools to force a text answer.
pub async fn run_llm_tool_loop<C: ToolChat, R: ToolRunner>(
    chat: &C,
    runner: &R,
    cfg: &LlmConfig,
    system: &str,
    initial: Vec<Turn>,
    tools: &[ToolDecl],
    max_tool_steps: u32,
) -> Result<(String, Vec<ToolCallTrace>), ChatError> {
    let mut turns = initial;
    let mut traces: Vec<ToolCallTrace> = Vec::new();
    for _ in 0..max_tool_steps.max(1) {
        let resp: ChatResponse = chat.chat_tools(cfg, system, &turns, tools).await?;
        if resp.tool_calls.is_empty() {
            return Ok((resp.text.unwrap_or_default(), traces));
        }
        turns.push(Turn::AssistantTools {
            text: resp.text.clone(),
            calls: resp.tool_calls.clone(),
        });
        let mut results = Vec::with_capacity(resp.tool_calls.len());
        for call in &resp.tool_calls {
            let (content, is_error) = runner.run_tool(&call.name, &call.args).await;
            traces.push(ToolCallTrace {
                name: call.name.clone(),
                args: call.args.clone(),
                result: content.clone(),
                is_error,
            });
            results.push(ToolResult {
                id: call.id.clone(),
                name: call.name.clone(),
                content,
                is_error,
            });
        }
        turns.push(Turn::ToolResults(results));
    }
    // Step cap reached — one final call with no tools to force a text answer.
    let resp = chat.chat_tools(cfg, system, &turns, &[]).await?;
    Ok((resp.text.unwrap_or_default(), traces))
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;
    use crate::llm::{Provider, ToolCall};
    use std::cell::RefCell;

    /// A `ToolChat` that returns a scripted sequence of responses.
    struct ScriptedChat {
        responses: RefCell<Vec<ChatResponse>>,
    }
    impl ToolChat for ScriptedChat {
        async fn chat_tools(
            &self,
            _cfg: &LlmConfig,
            _system: &str,
            _turns: &[Turn],
            _tools: &[ToolDecl],
        ) -> Result<ChatResponse, ChatError> {
            Ok(self.responses.borrow_mut().remove(0))
        }
    }

    /// A `ToolRunner` that records the calls it received and returns a canned card.
    struct MockRunner {
        calls: RefCell<Vec<(String, Value)>>,
    }
    impl ToolRunner for MockRunner {
        async fn run_tool(&self, name: &str, args: &Value) -> (String, bool) {
            self.calls
                .borrow_mut()
                .push((name.to_string(), args.clone()));
            (
                "tavla: x1 talks to x2 about x3 in language x4".to_string(),
                false,
            )
        }
    }

    fn call() -> ToolCall {
        ToolCall {
            id: "c1".into(),
            name: "vlacku".into(),
            args: serde_json::json!({ "query": "tavla" }),
            thought_signature: None,
        }
    }

    #[test]
    fn drives_one_tool_call_then_returns_text() {
        let chat = ScriptedChat {
            responses: RefCell::new(vec![
                // First turn: the model requests a tool call.
                ChatResponse {
                    text: None,
                    tool_calls: vec![call()],
                },
                // Second turn: with the result in hand, it answers.
                ChatResponse {
                    text: Some("lo tavla".into()),
                    tool_calls: vec![],
                },
            ]),
        };
        let runner = MockRunner {
            calls: RefCell::new(Vec::new()),
        };
        let cfg = LlmConfig::new(Provider::Anthropic);
        let (out, traces) = futures::executor::block_on(run_llm_tool_loop(
            &chat,
            &runner,
            &cfg,
            "SYS",
            vec![Turn::user("translate: talkers")],
            &[],
            5,
        ))
        .unwrap();
        assert_eq!(out, "lo tavla");
        assert_eq!(runner.calls.borrow().len(), 1);
        assert_eq!(runner.calls.borrow()[0].0, "vlacku");
        assert_eq!(
            runner.calls.borrow()[0].1["query"],
            serde_json::json!("tavla")
        );
        // The tool call is recorded in the trace.
        assert_eq!(traces.len(), 1);
        assert_eq!(traces[0].name, "vlacku");
        assert!(!traces[0].is_error);
    }

    #[test]
    fn returns_text_immediately_when_no_tool_calls() {
        let chat = ScriptedChat {
            responses: RefCell::new(vec![ChatResponse {
                text: Some("mi prami do".into()),
                tool_calls: vec![],
            }]),
        };
        let runner = MockRunner {
            calls: RefCell::new(Vec::new()),
        };
        let cfg = LlmConfig::new(Provider::OpenAi);
        let (out, traces) = futures::executor::block_on(run_llm_tool_loop(
            &chat,
            &runner,
            &cfg,
            "SYS",
            vec![Turn::user("x")],
            &[],
            5,
        ))
        .unwrap();
        assert_eq!(out, "mi prami do");
        assert!(runner.calls.borrow().is_empty());
        assert!(traces.is_empty());
    }
}
