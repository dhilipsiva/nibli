//! Where Lucy lives on this machine, read once from the environment.

use std::path::{Path, PathBuf};

/// The default byte budget for a capsule.
pub const DEFAULT_CAPSULE_MAX_BYTES: usize = 16 * 1024;

/// The resolved environment.
#[derive(Debug, Clone)]
pub struct Env {
    /// The memory folder.
    pub home: PathBuf,
    /// The name of this host, used in journal headings and presence lines.
    pub host: String,
    /// The capsule byte budget.
    pub capsule_max_bytes: usize,
    /// Reasoning depth passed to the engine when set.
    pub max_chain_depth: Option<u32>,
    /// How the home was found.
    pub source: HomeSource,
    /// Whether the engine's query-cone materialization is left on
    /// (`LUCY_MATERIALIZE=0` turns it off, the same knob as `NIBLI_MATERIALIZE`).
    pub materialize: bool,
}

/// Where the memory folder came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HomeSource {
    /// `LUCY_HOME`.
    Env,
    /// A `lucy/` folder in the working directory or a parent (project-local).
    Project,
    /// `~/.lucy`.
    Default,
    /// Set by a caller (tests, `init --here`).
    Explicit,
}

/// A project-local memory folder: `lucy/constitution.nibli` in `start` or any
/// parent, the way this repository keeps her.
pub fn find_project_home(start: &Path) -> Option<PathBuf> {
    let mut dir = Some(start.to_path_buf());
    while let Some(current) = dir {
        let candidate = current.join("lucy");
        if candidate.join("constitution.nibli").is_file() {
            return Some(candidate);
        }
        dir = current.parent().map(Path::to_path_buf);
    }
    None
}

impl Env {
    /// Resolves the home from `LUCY_HOME`, else a project-local `lucy/`
    /// folder found from the working directory upwards, else
    /// `HOME`/`USERPROFILE` + `.lucy`; the host from `LUCY_HOST` (else
    /// `HOSTNAME`/`COMPUTERNAME`, else `host`); plus `LUCY_CAPSULE_MAX_BYTES`
    /// and `LUCY_MAX_CHAIN_DEPTH`.
    pub fn from_process() -> Result<Env, String> {
        let (home, source) = match std::env::var_os("LUCY_HOME") {
            Some(path) if !path.is_empty() => (PathBuf::from(path), HomeSource::Env),
            _ => match std::env::current_dir()
                .ok()
                .and_then(|cwd| find_project_home(&cwd))
            {
                Some(project) => (project, HomeSource::Project),
                None => {
                    let base = std::env::var_os("HOME")
                        .or_else(|| std::env::var_os("USERPROFILE"))
                        .ok_or("neither LUCY_HOME, HOME nor USERPROFILE is set")?;
                    (PathBuf::from(base).join(".lucy"), HomeSource::Default)
                }
            },
        };
        let capsule_max_bytes = match std::env::var("LUCY_CAPSULE_MAX_BYTES") {
            Ok(value) => value
                .trim()
                .parse::<usize>()
                .map_err(|_| format!("LUCY_CAPSULE_MAX_BYTES is not a number: {value:?}"))?,
            Err(_) => DEFAULT_CAPSULE_MAX_BYTES,
        };
        let max_chain_depth = match std::env::var("LUCY_MAX_CHAIN_DEPTH") {
            Ok(value) => Some(
                value
                    .trim()
                    .parse::<u32>()
                    .map_err(|_| format!("LUCY_MAX_CHAIN_DEPTH is not a number: {value:?}"))?,
            ),
            Err(_) => None,
        };
        let materialize = std::env::var("LUCY_MATERIALIZE")
            .map(|v| v.trim() != "0")
            .unwrap_or(true);
        Ok(Env {
            home,
            host: host_name(),
            capsule_max_bytes,
            max_chain_depth,
            source,
            materialize,
        })
    }
}

/// `LUCY_HOST`, else the OS's own hostname variable, else `host`.
pub fn host_name() -> String {
    for key in ["LUCY_HOST", "HOSTNAME", "COMPUTERNAME"] {
        if let Ok(value) = std::env::var(key) {
            let value = value.trim();
            if !value.is_empty() {
                return sanitize_host(value);
            }
        }
    }
    if let Some(name) = os_host_name() {
        return sanitize_host(&name);
    }
    "host".to_string()
}

/// The operating system's own idea of the host name, when the environment
/// does not carry it: `/etc/hostname` or `uname -n` on Unix, nothing else on
/// Windows (`COMPUTERNAME` is always set there).
fn os_host_name() -> Option<String> {
    #[cfg(unix)]
    {
        if let Ok(text) = std::fs::read_to_string("/etc/hostname") {
            let name = text.trim();
            if !name.is_empty() {
                return Some(name.to_string());
            }
        }
        if let Ok(output) = std::process::Command::new("uname").arg("-n").output()
            && output.status.success()
        {
            let name = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !name.is_empty() {
                return Some(name);
            }
        }
    }
    None
}

/// Host names appear in journal headings; keep them to one token.
fn sanitize_host(raw: &str) -> String {
    let cleaned: String = raw
        .chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '-' || c == '_' || c == '.' {
                c
            } else {
                '-'
            }
        })
        .collect();
    let cleaned = cleaned.trim_matches('-').to_string();
    if cleaned.is_empty() {
        "host".to_string()
    } else {
        cleaned
    }
}
