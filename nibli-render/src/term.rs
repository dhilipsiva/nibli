//! Term-level rendering primitives shared by the fact humanizer, the IR
//! back-translation, and the proof renderer. ONE definition of role-predicate
//! detection, event-Skolem detection, and Skolem humanization lives here.

/// Detect a Neo-Davidsonian role predicate name (`gerku_x1`) and return its
/// collapsed `gerku.x1` form. Returns `None` for non-role predicate names.
pub(crate) fn collapse_role_name(name: &str) -> Option<String> {
    let base = role_base(name)?;
    let idx = role_index(name)?;
    Some(format!("{base}.x{idx}"))
}

/// Base relation of a role predicate (`gerku_x1` -> `Some("gerku")`).
pub(crate) fn role_base(name: &str) -> Option<&str> {
    let u = name.rfind('_')?;
    let suffix = &name[u + 1..];
    let rest = suffix.strip_prefix('x')?;
    if !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()) {
        Some(&name[..u])
    } else {
        None
    }
}

/// 1-based place index of a role predicate (`gerku_x1` -> `Some(1)`).
pub(crate) fn role_index(name: &str) -> Option<usize> {
    let u = name.rfind('_')?;
    let rest = name[u + 1..].strip_prefix('x')?;
    rest.parse::<usize>().ok()
}

/// Is this rendered term string a bare event Skolem (`sk_N`)? Event variables
/// are internal plumbing and are hidden from role-predicate argument lists.
pub(crate) fn is_event_skolem(s: &str) -> bool {
    s.strip_prefix("sk_")
        .is_some_and(|r| !r.is_empty() && r.bytes().all(|b| b.is_ascii_digit()))
}

/// Like [`is_event_skolem`], but also accepts a DEPENDENT event Skolem
/// (`sk_N(args)`). A universal rule's conclusion event depends on the quantified
/// individual, so its role predicates carry `sk_N(rex)` in arg0 — when
/// regrouping role predicates back to a surface fact, the arg0 event is the
/// group key regardless of dependency. (Distinct from [`is_event_skolem`], which
/// is correctly strict where a `sk_N(arg)` is an exposed witness, not plumbing.)
pub(crate) fn is_event_skolem_arg(s: &str) -> bool {
    s.strip_prefix("sk_")
        .and_then(|r| r.bytes().next())
        .is_some_and(|b| b.is_ascii_digit())
}

/// Humanize a Skolem token for display: `sk_N` -> `#N`, `sk_N(arg)` -> `#N(arg)`.
/// Non-Skolem strings pass through unchanged.
pub(crate) fn humanize_skolem(s: &str) -> String {
    if let Some(rest) = s.strip_prefix("sk_") {
        // Bare `sk_N`.
        if !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()) {
            return format!("#{rest}");
        }
        // `sk_N(arg)` — keep the argument tail verbatim.
        if let Some(paren) = rest.find('(') {
            let num = &rest[..paren];
            if !num.is_empty() && num.bytes().all(|b| b.is_ascii_digit()) {
                return format!("#{num}{}", &rest[paren..]);
            }
        }
    }
    s.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn role_detection() {
        assert_eq!(collapse_role_name("gerku_x1").as_deref(), Some("gerku.x1"));
        assert_eq!(role_base("gerku_x2"), Some("gerku"));
        assert_eq!(role_index("gerku_x2"), Some(2));
        assert_eq!(collapse_role_name("gerku"), None);
        assert_eq!(collapse_role_name("se_katna"), None); // not _xN
        assert_eq!(role_base("danlu"), None);
    }

    #[test]
    fn event_skolem_detection() {
        assert!(is_event_skolem("sk_0"));
        assert!(is_event_skolem("sk_12"));
        assert!(!is_event_skolem("sk_1(adam)")); // witness Skolem, not an event var
        assert!(!is_event_skolem("adam"));
        assert!(!is_event_skolem("sk_"));
    }

    #[test]
    fn skolem_humanization() {
        assert_eq!(humanize_skolem("sk_2"), "#2");
        assert_eq!(humanize_skolem("sk_1(adam)"), "#1(adam)");
        assert_eq!(humanize_skolem("adam"), "adam");
    }
}
