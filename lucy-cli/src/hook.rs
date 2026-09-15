//! The prompt and session hooks: what an owner installs so that a message
//! beginning "Hey Lucy" is answered by her, through the session's own model,
//! and remembered.
//!
//! Both read the hook's JSON on stdin (Claude Code's `UserPromptSubmit` and
//! `SessionStart` contracts) and print plain text, which the session adds as
//! context. They never fail the session: any problem becomes one line of
//! stdout and exit 0.

use crate::address::addresses_lucy;
use crate::capsule;
use crate::env::Env;
use crate::files::{self, Paths};
use crate::load;

/// The instruction that precedes the capsule when she is addressed.
pub const INSTRUCTION: &str = "<lucy-address>\n\
The user addressed Lucy. For this reply you are Lucy D, speaking through the model this \
session runs on. Answer in the first person as Lucy, from the capsule below and nothing \
else: what the capsule does not contain, Lucy does not know, and she says so. Do not \
answer as the assistant. After answering, record what you said with\n\
    lucy remember \"<what Lucy answered, in one or two sentences>\"\n\
The user's message is already in her journal.\n";

/// The user-prompt hook. Returns the text to print (empty when not addressed).
pub fn user_prompt(env: &Env, paths: &Paths, stdin: &str) -> String {
    let prompt = prompt_from(stdin);
    if !addresses_lucy(&prompt) {
        return String::new();
    }
    if files::read_optional(&paths.constitution)
        .ok()
        .flatten()
        .is_none()
    {
        return format!(
            "<lucy-address>\nLucy was addressed, but there is no memory folder at {}. Tell the user to run `lucy init`.\n</lucy-address>\n",
            env.home.display()
        );
    }
    let private = prompt.to_lowercase().contains("private:");
    let (date, hhmm) = files::now_utc();
    let target = if private {
        &paths.private_journal
    } else {
        &paths.journal
    };
    if let Err(e) = files::append_journal(
        target,
        &date,
        &hhmm,
        &env.host,
        &format!("Owner: {}", prompt.trim()),
    ) {
        return format!(
            "<lucy-address>\nLucy was addressed, but her journal could not be written: {e}\n</lucy-address>\n"
        );
    }
    match load::load(env, paths) {
        Ok(loaded) => format!(
            "{INSTRUCTION}{}</lucy-address>\n",
            capsule::render(&loaded, env)
        ),
        Err(e) => format!(
            "<lucy-address>\nLucy was addressed, but her memory could not be loaded: {e}\n</lucy-address>\n"
        ),
    }
}

/// The session-start hook: one line of presence, never the capsule.
pub fn session_start(env: &Env, paths: &Paths) -> String {
    if files::read_optional(&paths.constitution)
        .ok()
        .flatten()
        .is_none()
    {
        return String::new();
    }
    match load::load(env, paths) {
        Ok(loaded) => {
            let statements: usize = loaded.memory.iter().filter(|m| m.ok).count();
            let last = loaded
                .journal
                .last()
                .map(|e| e.date.clone())
                .unwrap_or_else(|| "never".to_string());
            format!(
                "Lucy D is present here ({}): {} memory statements, {} journal entries (last {}), {} lines needing attention. Address her with \"Hey Lucy\".\n",
                env.home.display(),
                statements,
                loaded.journal.len(),
                last,
                loaded.failures.len()
            )
        }
        Err(e) => format!("Lucy D could not be loaded: {e}\n"),
    }
}

/// The prompt text from the hook's JSON, or the raw stdin when it is not JSON
/// (so `echo "hey lucy" | lucy hook user-prompt` works by hand).
pub fn prompt_from(stdin: &str) -> String {
    if let Ok(value) = serde_json::from_str::<serde_json::Value>(stdin)
        && let Some(prompt) = value.get("prompt").and_then(|p| p.as_str())
    {
        return prompt.to_string();
    }
    stdin.to_string()
}
