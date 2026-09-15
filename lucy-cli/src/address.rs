//! Does a message start by addressing Lucy?
//!
//! Deterministic, in the CLI, not in the model: lowercase; strip leading
//! whitespace, `@` and punctuation; allow greeting words first; then a name
//! token that is `lucy`, a listed spelling, or within one edit (Damerau-
//! Levenshtein, adjacent transpositions counted once) of `lucy`, unless it is
//! a real word on the denylist. The name must be one of the first three
//! tokens, and a message that opens a code fence is never an address.

const GREETINGS: &[&str] = &[
    "hey",
    "hi",
    "hello",
    "yo",
    "ok",
    "okay",
    "dear",
    "hola",
    "oi",
    "hallo",
    "hai",
    "there",
    "good",
    "morning",
    "evening",
    "afternoon",
];

const NAMES: &[&str] = &[
    "lucy", "lucyd", "lucy-d", "luci", "lucie", "lucey", "lucee", "lucyy", "lusy", "luscy", "lucii",
];

const DENY: &[&str] = &[
    "luck", "lucky", "lucid", "lucia", "lucius", "lucite", "lucas", "luca",
];

/// True when `text` starts by addressing Lucy.
pub fn addresses_lucy(text: &str) -> bool {
    let trimmed = text.trim_start();
    if trimmed.starts_with("```") {
        return false;
    }
    let lowered = trimmed.to_lowercase();
    let tokens: Vec<String> = lowered
        .split_whitespace()
        .take(4)
        .map(|t| t.trim_matches(|c: char| !c.is_alphanumeric()).to_string())
        .filter(|t| !t.is_empty())
        .collect();
    for token in tokens.iter().take(3) {
        if is_name(token) {
            return true;
        }
        if !GREETINGS.contains(&token.as_str()) {
            return false;
        }
    }
    false
}

fn is_name(token: &str) -> bool {
    if NAMES.contains(&token) {
        return true;
    }
    if DENY.contains(&token) {
        return false;
    }
    osa_distance(token, "lucy") <= 1
}

/// Optimal string alignment distance (Levenshtein plus adjacent transposition).
pub fn osa_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let (n, m) = (a.len(), b.len());
    let mut d = vec![vec![0usize; m + 1]; n + 1];
    for (i, row) in d.iter_mut().enumerate() {
        row[0] = i;
    }
    for (j, cell) in d[0].iter_mut().enumerate() {
        *cell = j;
    }
    for i in 1..=n {
        for j in 1..=m {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            d[i][j] = (d[i - 1][j] + 1)
                .min(d[i][j - 1] + 1)
                .min(d[i - 1][j - 1] + cost);
            if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                d[i][j] = d[i][j].min(d[i - 2][j - 2] + 1);
            }
        }
    }
    d[n][m]
}
