//! Emit safe nibli KR fragments for auth queries and facts.

/// Escape a string for use inside a KR double-quoted constant.
pub fn escape_quoted(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Emit an agent/resource term: Capitalized Name if legal, else quoted constant.
pub fn emit_entity(s: &str) -> String {
    if is_name_constant(s) {
        s.to_string()
    } else {
        escape_quoted(s)
    }
}

/// Action / role / attr tokens are always quoted string constants.
pub fn emit_token(s: &str) -> String {
    escape_quoted(s)
}

fn is_name_constant(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_uppercase() => {
            chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        }
        _ => false,
    }
}

/// `authorized(Agent, "action", Resource).`
pub fn authorized_query(agent: &str, action: &str, resource: &str) -> String {
    format!(
        "authorized({}, {}, {}).",
        emit_entity(agent),
        emit_token(action),
        emit_entity(resource)
    )
}

/// `visible_attr(Agent, Resource, "attr").` (for future fine-grained field rules)
#[allow(dead_code)]
pub fn visible_attr_query(agent: &str, resource: &str, attr: &str) -> String {
    format!(
        "visible_attr({}, {}, {}).",
        emit_entity(agent),
        emit_entity(resource),
        emit_token(attr)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn name_vs_quoted() {
        assert_eq!(emit_entity("Alice"), "Alice");
        assert_eq!(emit_entity("alice"), "\"alice\"");
        assert_eq!(emit_token("update"), "\"update\"");
    }
}
