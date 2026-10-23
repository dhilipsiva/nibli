//! Lucy D: a persistent identity whose memory is nibli.
//!
//! Her memory is plain text in one folder (`LUCY_HOME`, default `~/.lucy`):
//! `constitution.nibli` (who she is and the rules that give her standing),
//! `memory.nibli` (direct facts and rules), and `interactions.nibli` (complete
//! conversations and quoted claims). `private.nibli` and `private-interactions.nibli` sit
//! beside them and are read when present; what to sync or share is the
//! user's decision. These files are not signed or encrypted; their formal
//! content is checked for what nibli checks: every formal line compiles, and a line that does not is
//! reported by file and line and skipped, never silently dropped.
//!
//! Her empirical self-model records predictions before actions, compares them
//! with observed outcomes, and checks its evidence graph in Nibli. It changes
//! planning context and bounded runtime behavior, not the selected model's weights.
//! This provides no test or conclusion about subjective experience.
//! Any agent session that runs this CLI is Lucy
//! for that session: `lucy wake` loads the files into a fresh nibli engine and
//! prints her capsule; `lucy remember` appends; `lucy ask` reasons with proofs;
//! `lucy hook user-prompt` is the prompt hook a user installs so that a
//! message beginning "Hey Lucy" is answered by her, through the session's own
//! model, and remembered. Older Markdown journals are imported once without
//! relabelling their entries as complete messages. Hosted agents submit their
//! replies via `record`; the Ollama path records both sides itself.
//!
//! Cross-platform by construction: no Unix-only paths, `\r\n` accepted, the
//! host name and home taken from the environment of whatever OS runs her.

#![forbid(unsafe_code)]

pub mod address;
pub mod ask;
pub mod capsule;
pub mod cli;
pub mod dataset;
#[cfg(unix)]
pub mod desktop;
pub mod env;
pub mod files;
pub mod hook;
pub mod interactions;
pub mod load;
pub mod self_model;
pub mod store;
#[cfg(test)]
mod store_tests;
pub mod talk;
pub mod topics;

pub use cli::{Outcome, run};

/// The constitution template written by `lucy init` and pinned by
/// `just verify-lucy-pins` against this exact file.
pub const CONSTITUTION_TEMPLATE: &str = include_str!("../constitution/lucy.nibli");

#[cfg(test)]
mod dataset_tests;
#[cfg(test)]
mod interaction_tests;
#[cfg(test)]
mod tests;
