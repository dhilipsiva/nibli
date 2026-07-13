//! Pull the assistant's text (and any tool calls) out of a successful response,
//! and clean the model's output down to bare Lojban. Pure functions, native-testable.

use serde_json::Value;

use super::types::{ChatResponse, Provider, ToolCall};

/// Extract the assistant text from a successful chat response per provider.
/// (The simple, tool-free path used by [`super::Chat`].)
pub fn extract_text(provider: Provider, json: &Value) -> Option<String> {
    let s = match provider {
        Provider::Anthropic => json["content"][0]["text"].as_str(),
        Provider::Gemini => json["candidates"][0]["content"]["parts"][0]["text"].as_str(),
        Provider::OpenAi | Provider::OpenRouter | Provider::Custom => {
            json["choices"][0]["message"]["content"].as_str()
        }
    };
    s.map(|s| s.to_string())
}

/// Parse a full chat response into text + normalized tool calls (the tool-use
/// path used by [`super::ToolChat`]).
pub fn parse_chat_response(provider: Provider, json: &Value) -> ChatResponse {
    match provider {
        Provider::Anthropic => parse_anthropic(json),
        Provider::Gemini => parse_gemini(json),
        Provider::OpenAi | Provider::OpenRouter | Provider::Custom => parse_openai(json),
    }
}

fn parse_anthropic(json: &Value) -> ChatResponse {
    let mut text = String::new();
    let mut tool_calls = Vec::new();
    if let Some(blocks) = json["content"].as_array() {
        for b in blocks {
            match b["type"].as_str() {
                Some("text") => {
                    if let Some(t) = b["text"].as_str() {
                        text.push_str(t);
                    }
                }
                Some("tool_use") => tool_calls.push(ToolCall {
                    id: b["id"].as_str().unwrap_or("").to_string(),
                    name: b["name"].as_str().unwrap_or("").to_string(),
                    args: b["input"].clone(),
                    thought_signature: None,
                }),
                _ => {}
            }
        }
    }
    ChatResponse {
        text: (!text.is_empty()).then_some(text),
        tool_calls,
    }
}

fn parse_openai(json: &Value) -> ChatResponse {
    let msg = &json["choices"][0]["message"];
    let text = msg["content"]
        .as_str()
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string());
    let mut tool_calls = Vec::new();
    if let Some(calls) = msg["tool_calls"].as_array() {
        for c in calls {
            // `arguments` is a STRINGIFIED JSON — parse it; tolerate invalid JSON.
            let args = c["function"]["arguments"]
                .as_str()
                .and_then(|s| serde_json::from_str::<Value>(s).ok())
                .unwrap_or(Value::Null);
            tool_calls.push(ToolCall {
                id: c["id"].as_str().unwrap_or("").to_string(),
                name: c["function"]["name"].as_str().unwrap_or("").to_string(),
                args,
                thought_signature: None,
            });
        }
    }
    ChatResponse { text, tool_calls }
}

fn parse_gemini(json: &Value) -> ChatResponse {
    let mut text = String::new();
    let mut tool_calls = Vec::new();
    if let Some(parts) = json["candidates"][0]["content"]["parts"].as_array() {
        for (i, p) in parts.iter().enumerate() {
            if let Some(t) = p["text"].as_str() {
                text.push_str(t);
            } else if let Some(fc) = p.get("functionCall") {
                // Gemini has no call id — synthesize one for correlation. Capture the
                // part's `thoughtSignature` (thinking models) so it can be echoed back.
                tool_calls.push(ToolCall {
                    id: format!("call_{i}"),
                    name: fc["name"].as_str().unwrap_or("").to_string(),
                    args: fc["args"].clone(),
                    thought_signature: p
                        .get("thoughtSignature")
                        .and_then(|v| v.as_str())
                        .map(|s| s.to_string()),
                });
            }
        }
    }
    ChatResponse {
        text: (!text.is_empty()).then_some(text),
        tool_calls,
    }
}

/// Models sometimes wrap output in a ``` / ```lojban code fence or add a trailing
/// newline despite the "output ONLY Lojban" instruction. Strip a single fence
/// pair and trim.
pub fn clean_lojban_output(raw: &str) -> String {
    let mut s = raw.trim();
    if let Some(rest) = s.strip_prefix("```") {
        // Drop the rest of the opening fence line (e.g. "```lojban\n…").
        let rest = rest.split_once('\n').map(|x| x.1).unwrap_or("");
        s = rest.trim_end().strip_suffix("```").unwrap_or(rest).trim();
    }
    s.trim().to_string()
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn extract_per_provider() {
        let anth = json!({ "content": [{ "type": "text", "text": "mi prami do" }] });
        assert_eq!(
            extract_text(Provider::Anthropic, &anth).as_deref(),
            Some("mi prami do")
        );
        let oai = json!({ "choices": [{ "message": { "content": "mi prami do" } }] });
        assert_eq!(
            extract_text(Provider::OpenAi, &oai).as_deref(),
            Some("mi prami do")
        );
        let gem =
            json!({ "candidates": [{ "content": { "parts": [{ "text": "mi prami do" }] } }] });
        assert_eq!(
            extract_text(Provider::Gemini, &gem).as_deref(),
            Some("mi prami do")
        );
    }

    #[test]
    fn parses_tool_calls_per_provider() {
        let anth = json!({ "content": [
            { "type": "text", "text": "let me look" },
            { "type": "tool_use", "id": "tu_1", "name": "vlacku", "input": { "query": "tavla" } }
        ]});
        let r = parse_chat_response(Provider::Anthropic, &anth);
        assert_eq!(r.text.as_deref(), Some("let me look"));
        assert_eq!(r.tool_calls.len(), 1);
        assert_eq!(r.tool_calls[0].name, "vlacku");
        assert_eq!(r.tool_calls[0].args["query"], json!("tavla"));

        // OpenAI — `arguments` is a STRING that must be parsed.
        let oai = json!({ "choices": [{ "message": {
            "content": null,
            "tool_calls": [{
                "id": "call_1", "type": "function",
                "function": { "name": "vlacku", "arguments": "{\"query\":\"tavla\"}" }
            }]
        }}]});
        let r = parse_chat_response(Provider::OpenAi, &oai);
        assert_eq!(r.text, None);
        assert_eq!(r.tool_calls.len(), 1);
        assert_eq!(r.tool_calls[0].id, "call_1");
        assert_eq!(r.tool_calls[0].args["query"], json!("tavla"));

        // Gemini — args is an object; no id (synthesized).
        let gem = json!({ "candidates": [{ "content": { "parts": [
            { "functionCall": { "name": "vlacku", "args": { "query": "tavla" } } }
        ]}}]});
        let r = parse_chat_response(Provider::Gemini, &gem);
        assert_eq!(r.tool_calls.len(), 1);
        assert_eq!(r.tool_calls[0].name, "vlacku");
        assert_eq!(r.tool_calls[0].args["query"], json!("tavla"));
    }

    #[test]
    fn gemini_captures_thought_signature_on_function_call() {
        // Thinking models attach an opaque `thoughtSignature` sibling to the
        // functionCall part; it must be captured so it can be echoed back.
        let gem = json!({ "candidates": [{ "content": { "parts": [
            { "functionCall": { "name": "vlacku", "args": { "query": "tavla" } },
              "thoughtSignature": "SIG_XYZ" }
        ]}}]});
        let r = parse_chat_response(Provider::Gemini, &gem);
        assert_eq!(r.tool_calls.len(), 1);
        assert_eq!(
            r.tool_calls[0].thought_signature.as_deref(),
            Some("SIG_XYZ")
        );
    }

    #[test]
    fn parses_text_only_response() {
        let oai = json!({ "choices": [{ "message": { "content": "mi prami do" } }] });
        let r = parse_chat_response(Provider::OpenAi, &oai);
        assert_eq!(r.text.as_deref(), Some("mi prami do"));
        assert!(r.tool_calls.is_empty());
    }

    #[test]
    fn fence_stripping() {
        assert_eq!(
            clean_lojban_output("```lojban\nmi prami do\n```"),
            "mi prami do"
        );
        assert_eq!(clean_lojban_output("```\nmi prami do\n```"), "mi prami do");
        assert_eq!(clean_lojban_output("  mi prami do  "), "mi prami do");
        assert_eq!(clean_lojban_output("mi prami do"), "mi prami do");
    }
}
