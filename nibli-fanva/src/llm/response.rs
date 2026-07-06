//! Pull the assistant's text out of a successful response, and clean the model's
//! output down to bare Lojban. Pure functions, native-testable. (Tool-call
//! parsing per provider arrives with the Phase-3 jbotci tool loop.)

use serde_json::Value;

use super::types::Provider;

/// Extract the assistant text from a successful chat response per provider.
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

/// Models sometimes wrap output in a ``` / ```lojban code fence or add a trailing
/// newline despite the "output ONLY Lojban" instruction. Strip a single fence
/// pair and trim.
pub fn clean_lojban_output(raw: &str) -> String {
    let mut s = raw.trim();
    if let Some(rest) = s.strip_prefix("```") {
        // Drop the rest of the opening fence line (e.g. "```lojban\n…").
        let rest = rest.splitn(2, '\n').nth(1).unwrap_or("");
        s = rest.trim_end().strip_suffix("```").unwrap_or(rest).trim();
    }
    s.trim().to_string()
}

#[cfg(test)]
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
