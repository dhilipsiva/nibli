//! The same tools serve terminal and GTK clients. Mutating and network actions
//! are proposals; the model has no approval tool or UI control token.
use super::{Result, err, net, string};
use serde_json::{Value, json};
use std::fs;
use std::io::{Read, Seek, SeekFrom, Write};
use std::os::unix::process::CommandExt;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

// Names no tool reads, lists, searches or lets a command see, at any depth: credentials, agent
// state, and configuration other programs execute.
const DENIED: &[&str] = &[
    ".git",
    ".ssh",
    ".gnupg",
    ".aws",
    ".azure",
    ".codex",
    ".claude",
    ".agents",
    ".config",
    ".local",
    ".env",
    ".envrc",
    ".direnv",
    ".netrc",
    ".git-credentials",
    ".gitconfig",
    ".docker",
    ".kube",
    ".npmrc",
    ".pypirc",
    ".mozilla",
    ".var",
    ".password-store",
    ".pki",
    ".terraform.d",
    ".vault-token",
    "credentials.toml",
];
// A bounded walk finds denied names for the sandbox; a larger workspace is refused, not
// half-masked.
const MAX_SANDBOX_DIRECTORIES: usize = 100_000;
pub fn schemas() -> Value {
    let definitions = [
        (
            "list",
            "List files and directories in the workspace.",
            json!({"path":{"type":"string"}}),
            vec![],
        ),
        (
            "read",
            "Read a UTF-8 file inside the workspace.",
            json!({"path":{"type":"string"}}),
            vec!["path"],
        ),
        (
            "search",
            "Search workspace text literally.",
            json!({"query":{"type":"string"}}),
            vec!["query"],
        ),
        (
            "git",
            "Inspect repository status, diff or recent log.",
            json!({"operation":{"type":"string","enum":["status","diff","log"]}}),
            vec!["operation"],
        ),
        (
            "diagnostics",
            "Inspect system, GPU, model and user-service health.",
            json!({}),
            vec![],
        ),
        (
            "write",
            "Propose an atomic complete file replacement; user approves before/after.",
            json!({"path":{"type":"string"},"text":{"type":"string"}}),
            vec!["path", "text"],
        ),
        (
            "command",
            "Propose argv in an offline workspace sandbox; requires user approval.",
            json!({"argv":{"type":"array","items":{"type":"string"}}}),
            vec!["argv"],
        ),
        (
            "http",
            "Propose an HTTP(S) request including its URL, method and JSON body; requires approval.",
            json!({"url":{"type":"string"},"method":{"type":"string","enum":["GET","POST","PUT","PATCH","DELETE","HEAD"]},"body":{}}),
            vec!["url", "method"],
        ),
        (
            "service",
            "Read status or propose start/stop/restart of one named service.",
            json!({"name":{"type":"string"},"operation":{"type":"string","enum":["status","start","stop","restart"]},"system":{"type":"boolean"}}),
            vec!["name", "operation"],
        ),
        (
            "launch",
            "Propose launching an installed application by desktop ID.",
            json!({"desktop_id":{"type":"string"}}),
            vec!["desktop_id"],
        ),
        (
            "window",
            "List desktop windows or propose focusing/closing one.",
            json!({"action":{"type":"string","enum":["list","focus","close"]},"address":{"type":"string"}}),
            vec!["action"],
        ),
        (
            "screenshot",
            "Propose an explicit screenshot of the unlocked desktop.",
            json!({}),
            vec![],
        ),
        (
            "gui",
            "Propose one literal ydotool keyboard or mouse action.",
            json!({"argv":{"type":"array","items":{"type":"string"}}}),
            vec!["argv"],
        ),
        (
            "privileged",
            "Propose an authenticated hardware diagnostic.",
            json!({"operation":{"type":"string","enum":["hardware-info"]}}),
            vec!["operation"],
        ),
    ];
    json!(definitions.into_iter().map(|(name,description,properties,required)|json!({
        "type":"function","function":{"name":name,"description":description,
        "parameters":{"type":"object","properties":properties,"required":required,"additionalProperties":false}}
    })).collect::<Vec<_>>())
}
pub fn needs_approval(name: &str, args: &Value) -> Result<bool> {
    if !schemas()
        .as_array()
        .unwrap()
        .iter()
        .any(|s| s["function"]["name"] == name)
    {
        return Err("unknown tool".into());
    }
    if !args.is_object() {
        return Err("tool arguments must be an object".into());
    }
    Ok(match name {
        "list" | "read" | "search" | "git" | "diagnostics" => false,
        "window" => args["action"] != "list",
        "service" => args["operation"] != "status",
        _ => true,
    })
}
fn denied(name: &str) -> bool {
    DENIED.contains(&name)
        || name.starts_with(".env.")
        || (name.starts_with('.') && name.ends_with("history"))
}
/// The canonical workspace. Refused: the home directory and its ancestors (they hold the
/// credentials and shell startup files the deny list can only partly name), anything inside a
/// denied name (`~/.ssh`, a repository's `.git`), and the runtime and kernel trees, which hold
/// sockets to the session bus and to Lucy's own service.
fn workspace(root: &Path) -> Result<PathBuf> {
    let root = root.canonicalize().map_err(err)?;
    let refused = |what: &str| {
        Err(format!(
            "tools need a project directory as the workspace, not {what}"
        ))
    };
    if let Some(home) = std::env::var_os("HOME").and_then(|h| Path::new(&h).canonicalize().ok())
        && home.starts_with(&root)
    {
        return refused("the home directory or above it");
    }
    if root
        .components()
        .any(|c| denied(&c.as_os_str().to_string_lossy()))
    {
        return refused("a credential or configuration directory");
    }
    let runtime = std::env::var_os("XDG_RUNTIME_DIR").map(PathBuf::from);
    for system in ["/run", "/proc", "/sys", "/dev"]
        .into_iter()
        .map(PathBuf::from)
        .chain(runtime)
    {
        let system = system.canonicalize().unwrap_or(system);
        if root.starts_with(&system) || system.starts_with(&root) {
            return refused("a runtime or system directory");
        }
    }
    Ok(root)
}
/// What the sandbox hides, found by a bounded walk that never follows symlinks: every denied
/// name; every socket and FIFO, each a door to another process (the session bus, Lucy's own
/// service); and, for a writable sandbox, every directory this user cannot read, which an
/// approved command could otherwise chmod open. Each entry says whether it is a directory.
fn masks(root: &Path, writable: bool) -> Result<Vec<(PathBuf, bool)>> {
    use std::os::unix::fs::FileTypeExt;
    let mut found = Vec::new();
    let mut directories = vec![root.to_path_buf()];
    let mut walked = 0;
    while let Some(directory) = directories.pop() {
        let entries = match fs::read_dir(&directory) {
            Ok(entries) => entries,
            // Read-only, an unreadable directory stays unreadable (a mask over it would show git
            // its tracked files as deleted); writable, an approved command could chmod it open.
            Err(_) if directory != root => {
                if writable {
                    found.push((directory, true));
                }
                continue;
            }
            Err(error) => return Err(err(error)),
        };
        for entry in entries {
            let entry = entry.map_err(err)?;
            let kind = entry.file_type().map_err(err)?;
            let path = entry.path();
            if kind.is_socket() || kind.is_fifo() {
                found.push((path, false));
            } else if denied(&entry.file_name().to_string_lossy()) {
                if kind.is_dir() || kind.is_file() {
                    found.push((path, kind.is_dir()));
                }
            } else if kind.is_dir() {
                walked += 1;
                if walked > MAX_SANDBOX_DIRECTORIES {
                    return Err(
                        "the workspace is too large to sandbox; choose a smaller one".into(),
                    );
                }
                directories.push(path);
            }
        }
    }
    Ok(found)
}
/// bwrap arguments that run a program in the workspace with no network, no environment and none
/// of the host but the Nix store, the system profile and `git_dirs`, with `masks` hidden.
/// `writable` is for approved commands; the unapproved git inspection gets a read-only workspace
/// and keeps the repository's own `.git`, so repository configuration (filters, drivers) can run
/// nothing that changes or reaches anything.
fn sandbox(root: &Path, writable: bool, git_dirs: &[PathBuf]) -> Result<Vec<String>> {
    let utf8 = |path: &Path| {
        path.to_str()
            .map(str::to_owned)
            .ok_or_else(|| "workspace path is not UTF-8".to_owned())
    };
    let workspace = utf8(root)?;
    let mut command = strings(&[
        "bwrap",
        "--unshare-all",
        "--die-with-parent",
        "--new-session",
        "--ro-bind",
        "/nix/store",
        "/nix/store",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
        "--tmpfs",
        "/tmp",
        "--dir",
        "/etc",
        "--dir",
        "/run",
        "--dir",
        "/home",
        "--ro-bind",
        "/run/current-system/sw",
        "/run/current-system/sw",
    ]);
    for directory in git_dirs {
        let directory = utf8(directory)?;
        command.extend(["--ro-bind".into(), directory.clone(), directory]);
    }
    command.extend([
        if writable { "--bind" } else { "--ro-bind" }.into(),
        workspace.clone(),
        workspace.clone(),
        "--chdir".into(),
        workspace,
        "--clearenv".into(),
        "--setenv".into(),
        "PATH".into(),
        std::env::var("LUCY_COMMAND_PATH").unwrap_or_else(|_| "/run/current-system/sw/bin".into()),
    ]);
    for (path, directory) in masks(root, writable)? {
        if !writable && path == root.join(".git") {
            continue;
        }
        let path = utf8(&path)?;
        if directory {
            command.extend(["--tmpfs".into(), path]);
        } else {
            command.extend(["--ro-bind".into(), "/dev/null".into(), path]);
        }
    }
    command.push("--".into());
    Ok(command)
}
/// The git directories a read-only inspection needs bound besides the workspace, which must be
/// the repository's root (from a subdirectory git would need the whole work tree). A linked
/// worktree's `.git` is a file naming its git directory elsewhere; it is bound, with the
/// repository's common directory, only when it has a real worktree's layout and git's own
/// back-pointer names this workspace's `.git`, so a planted `.git` file cannot name some other
/// directory, or another repository's worktree, into the sandbox.
fn git_dirs(root: &Path) -> Result<Vec<PathBuf>> {
    let dot = root.join(".git");
    match fs::symlink_metadata(&dot) {
        Ok(meta) if meta.is_dir() => Ok(Vec::new()),
        Ok(meta) if meta.is_file() => {
            let named = fs::read_to_string(&dot).map_err(err)?;
            let named = named
                .strip_prefix("gitdir:")
                .map(str::trim)
                .ok_or("the workspace's .git file names no git directory")?;
            let gitdir = root.join(named).canonicalize().map_err(err)?;
            let common = fs::read_to_string(gitdir.join("commondir"))
                .map_err(|_| "the workspace's .git file does not name a linked worktree")?;
            let common = gitdir.join(common.trim()).canonicalize().map_err(err)?;
            let back = fs::read_to_string(gitdir.join("gitdir"))
                .ok()
                .and_then(|back| Path::new(back.trim()).canonicalize().ok());
            if gitdir.parent() != Some(common.join("worktrees").as_path())
                || !common.join("HEAD").is_file()
                || !common.join("objects").is_dir()
                || back != dot.canonicalize().ok()
            {
                return Err("the workspace's .git file does not name a linked worktree".into());
            }
            Ok(vec![common, gitdir])
        }
        _ => match root.ancestors().skip(1).find(|a| a.join(".git").exists()) {
            Some(top) => Err(format!(
                "git inspection needs the repository root as the workspace ({})",
                top.display()
            )),
            None => Ok(Vec::new()),
        },
    }
}
/// Pathspecs that keep every denied name out of git's output: the sandbox masks those paths, so
/// git would otherwise report them as deleted and print their committed content.
fn git_pathspecs() -> Vec<String> {
    let mut specs = vec![".".to_owned()];
    for name in DENIED
        .iter()
        .copied()
        .filter(|name| *name != ".git")
        .chain([".env.*", ".*history"])
    {
        specs.push(format!(":(exclude,glob)**/{name}"));
        specs.push(format!(":(exclude,glob)**/{name}/**"));
    }
    specs
}
pub fn path(root: &Path, relative: &str, allow_root: bool) -> Result<PathBuf> {
    let root = workspace(root)?;
    let mut target = if Path::new(relative).is_absolute() {
        PathBuf::new()
    } else {
        root.clone()
    };
    for component in Path::new(relative).components() {
        match component {
            Component::ParentDir => {
                target.pop();
            }
            Component::CurDir => {}
            other => target.push(other.as_os_str()),
        }
    }
    let mut missing = Vec::new();
    let mut existing = target.as_path();
    while !existing.exists() {
        missing.push(
            existing
                .file_name()
                .ok_or("invalid workspace path")?
                .to_owned(),
        );
        existing = existing.parent().ok_or("invalid workspace path")?;
    }
    let mut resolved = existing.canonicalize().map_err(err)?;
    for component in missing.iter().rev() {
        resolved.push(component);
    }
    let relative = resolved
        .strip_prefix(&root)
        .map_err(|_| "path escapes the workspace")?;
    if !allow_root && relative.as_os_str().is_empty() {
        return Err("path must name a file inside the workspace".into());
    }
    if relative
        .components()
        .any(|p| denied(&p.as_os_str().to_string_lossy()))
    {
        return Err(
            "credential and configuration paths require an explicit external workflow".into(),
        );
    }
    Ok(resolved)
}
/// Linux input event names for the keys a `gui` proposal presses, so its approval reads
/// "Y down", not "21:1".
fn key_name(code: u16) -> String {
    const NAMES: &[(u16, &str)] = &[
        (1, "ESC"),
        (2, "1"),
        (3, "2"),
        (4, "3"),
        (5, "4"),
        (6, "5"),
        (7, "6"),
        (8, "7"),
        (9, "8"),
        (10, "9"),
        (11, "0"),
        (12, "MINUS"),
        (13, "EQUAL"),
        (14, "BACKSPACE"),
        (15, "TAB"),
        (16, "Q"),
        (17, "W"),
        (18, "E"),
        (19, "R"),
        (20, "T"),
        (21, "Y"),
        (22, "U"),
        (23, "I"),
        (24, "O"),
        (25, "P"),
        (26, "LEFTBRACE"),
        (27, "RIGHTBRACE"),
        (28, "ENTER"),
        (29, "LEFTCTRL"),
        (30, "A"),
        (31, "S"),
        (32, "D"),
        (33, "F"),
        (34, "G"),
        (35, "H"),
        (36, "J"),
        (37, "K"),
        (38, "L"),
        (39, "SEMICOLON"),
        (40, "APOSTROPHE"),
        (41, "GRAVE"),
        (42, "LEFTSHIFT"),
        (43, "BACKSLASH"),
        (44, "Z"),
        (45, "X"),
        (46, "C"),
        (47, "V"),
        (48, "B"),
        (49, "N"),
        (50, "M"),
        (51, "COMMA"),
        (52, "DOT"),
        (53, "SLASH"),
        (54, "RIGHTSHIFT"),
        (56, "LEFTALT"),
        (57, "SPACE"),
        (58, "CAPSLOCK"),
        (59, "F1"),
        (60, "F2"),
        (61, "F3"),
        (62, "F4"),
        (63, "F5"),
        (64, "F6"),
        (65, "F7"),
        (66, "F8"),
        (67, "F9"),
        (68, "F10"),
        (87, "F11"),
        (88, "F12"),
        (96, "KPENTER"),
        (97, "RIGHTCTRL"),
        (100, "RIGHTALT"),
        (102, "HOME"),
        (103, "UP"),
        (104, "PAGEUP"),
        (105, "LEFT"),
        (106, "RIGHT"),
        (107, "END"),
        (108, "DOWN"),
        (109, "PAGEDOWN"),
        (110, "INSERT"),
        (111, "DELETE"),
        (125, "LEFTMETA"),
        (126, "RIGHTMETA"),
    ];
    NAMES
        .iter()
        .find(|(known, _)| *known == code)
        .map_or_else(|| format!("KEY_{code}"), |(_, name)| (*name).to_owned())
}
/// Checks a `gui` argv and returns the key events it presses, by name. Synthetic input must not
/// be able to answer an approval prompt, so it may not press Enter, keypad Enter or Linefeed, may
/// hold no modifier but Shift (Ctrl, Alt, Meta and CapsLock, often remapped to Ctrl, turn
/// ordinary keys into control characters on any layout), must release every key it presses, and
/// may not type control characters or backslashes (ydotool expands backslash escapes). Keys come
/// from a short list and a click is a whole left or right click. This is best effort: the
/// terminal's flushed, terminal-only read is what protects its prompt.
fn gui_events(args: &[String]) -> Result<Option<Vec<String>>> {
    let unsupported = || Err::<_, String>("unsupported literal mouse/keyboard action".into());
    match args[0].as_str() {
        "type" if args.len() == 3 && args[1] == "--" && args[2].len() <= 4096 => {
            if args[2]
                .chars()
                .any(|c| (c.is_control() && c != '\t') || c == '\\')
            {
                return Err(
                    "synthetic input may not type line breaks, control characters or \
                     backslashes"
                        .into(),
                );
            }
            Ok(None)
        }
        "key" if args.len() > 1 && args.len() <= 65 => {
            let mut held = std::collections::BTreeSet::new();
            let mut names = Vec::new();
            for event in &args[1..] {
                let Some((code, state)) = event.split_once(':') else {
                    return unsupported();
                };
                let Some(code) = code.parse::<u16>().ok().filter(|n| *n <= 999) else {
                    return unsupported();
                };
                let down = match state {
                    "1" => true,
                    "0" => false,
                    _ => return unsupported(),
                };
                if matches!(code, 28 | 96 | 101) {
                    return Err("synthetic input may not press Enter or submit a line".into());
                }
                if matches!(code, 29 | 97 | 56 | 100 | 125 | 126 | 58 | 127) {
                    return Err("synthetic input may hold Shift but no other modifier".into());
                }
                // Letters, digits, punctuation, Shift, Space, Tab, Backspace, Escape, F1-F12,
                // the arrows, Home, End, Page Up/Down and Delete: nothing that pastes (Insert),
                // powers off, sleeps or presses a mouse button.
                if !matches!(code, 1..=27 | 30..=54 | 57 | 59..=68 | 87 | 88 | 102..=109 | 111) {
                    return Err(format!("synthetic input may not press key {code}"));
                }
                if down {
                    held.insert(code);
                } else {
                    held.remove(&code);
                }
                names.push(format!(
                    "{} {}",
                    key_name(code),
                    if down { "down" } else { "up" }
                ));
            }
            if !held.is_empty() {
                return Err("synthetic input must release every key it presses".into());
            }
            Ok(Some(names))
        }
        // 0xC0 and 0xC1: the left or right button pressed and released. Not a button left
        // down, nor the middle button, which pastes.
        "click"
            if args.len() == 2
                && args[1]
                    .strip_prefix("0x")
                    .and_then(|hex| u8::from_str_radix(hex, 16).ok())
                    .is_some_and(|code| matches!(code, 0xC0 | 0xC1)) =>
        {
            Ok(None)
        }
        "mousemove" => {
            let positions = if args.get(1).is_some_and(|s| s == "--absolute") {
                &args[2..]
            } else {
                &args[1..]
            };
            if positions.len() == 2
                && positions
                    .iter()
                    .all(|s| s.parse::<i32>().is_ok_and(|n| n.unsigned_abs() <= 99999))
            {
                Ok(None)
            } else {
                unsupported()
            }
        }
        _ => unsupported(),
    }
}
fn argv(args: &Value) -> Result<Vec<String>> {
    let values = args["argv"]
        .as_array()
        .filter(|a| !a.is_empty())
        .ok_or("argv must be a nonempty string array")?;
    values
        .iter()
        .map(|v| {
            v.as_str()
                .filter(|s| !s.contains('\0'))
                .map(str::to_owned)
                .ok_or("invalid argv".into())
        })
        .collect()
}
pub fn preview(root: &Path, name: &str, args: Value) -> Result<Value> {
    let mut value = json!({"tool":name,"arguments":args});
    if name == "write" {
        let target = path(root, string(&value["arguments"], "path")?, false)?;
        if fs::metadata(&target).is_ok_and(|m| m.len() > 1_000_000) {
            return Err("file preview exceeds 1 MB".into());
        }
        let before = if target.exists() {
            fs::read_to_string(&target).map_err(err)?
        } else {
            String::new()
        };
        if before.len() > 1_000_000 || string(&value["arguments"], "text")?.len() > 1_000_000 {
            return Err("file preview exceeds 1 MB".into());
        }
        value["diff"] = json!({"path":value["arguments"]["path"],"before":before,"after":value["arguments"]["text"]});
        value["before"] = json!({"path":target,"exists":target.exists(),"text":before});
    }
    if name == "command" {
        argv(&value["arguments"])?;
    }
    if name == "gui"
        && let Some(keys) = gui_events(&argv(&value["arguments"])?)?
    {
        value["keys"] = json!(keys);
    }
    if name == "http" {
        let url =
            reqwest::Url::parse(string(&value["arguments"], "url")?).map_err(|_| "invalid URL")?;
        if !matches!(url.scheme(), "http" | "https")
            || !url.username().is_empty()
            || url.password().is_some()
        {
            return Err("use an HTTP(S) URL without credentials in its authority".into());
        }
    }
    Ok(value)
}
fn unlocked() -> bool {
    let uid = nix::unistd::getuid().as_raw().to_string();
    let Ok(output) = Command::new("loginctl")
        .args(["list-sessions", "--no-legend"])
        .output()
    else {
        return false;
    };
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        let parts: Vec<_> = line.split_whitespace().collect();
        if parts.get(1) == Some(&uid.as_str())
            && let Some(id) = parts.first()
            && let Ok(output) = Command::new("loginctl")
                .args([
                    "show-session",
                    id,
                    "-p",
                    "Active",
                    "-p",
                    "LockedHint",
                    "-p",
                    "Type",
                ])
                .output()
        {
            let text = String::from_utf8_lossy(&output.stdout);
            if text.lines().any(|l| l == "Active=yes")
                && text.lines().any(|l| l == "LockedHint=no")
                && text.lines().any(|l| l == "Type=wayland")
            {
                return true;
            }
        }
    }
    false
}
pub fn run(
    root: &Path,
    cancel: &AtomicBool,
    args: &[String],
    gui: bool,
    timeout: u64,
) -> Result<Value> {
    if args.is_empty() || cancel.load(Ordering::SeqCst) || (gui && !unlocked()) {
        return Err("cancelled, invalid command or desktop locked".into());
    }
    let mut output = tempfile::tempfile().map_err(err)?;
    let mut command = Command::new(&args[0]);
    command
        .args(&args[1..])
        .current_dir(root)
        .stdin(Stdio::null())
        .stdout(output.try_clone().map_err(err)?)
        .stderr(output.try_clone().map_err(err)?)
        .process_group(0);
    if args[0] == "pkexec" {
        command.env_remove("SHELL");
    }
    let mut child = command.spawn().map_err(err)?;
    let start = Instant::now();
    let result: Result<i32> = loop {
        match child.try_wait().map_err(err)? {
            Some(status) => break Ok(status.code().unwrap_or(-1)),
            None if cancel.load(Ordering::SeqCst)
                || start.elapsed() > Duration::from_secs(timeout)
                || output.metadata().is_ok_and(|m| m.len() > 1_000_000)
                || (gui && !unlocked()) =>
            {
                let _ = nix::sys::signal::killpg(
                    nix::unistd::Pid::from_raw(child.id() as i32),
                    nix::sys::signal::Signal::SIGKILL,
                );
                let _ = child.wait();
                break Err("action stopped: cancelled, locked or timed out".into());
            }
            _ => std::thread::sleep(Duration::from_millis(50)),
        }
    };
    let code = result?;
    output.seek(SeekFrom::Start(0)).map_err(err)?;
    let mut bytes = Vec::new();
    output.take(64000).read_to_end(&mut bytes).map_err(err)?;
    Ok(json!({"exit_code":code,"output":String::from_utf8_lossy(&bytes)}))
}
fn strings(args: &[&str]) -> Vec<String> {
    args.iter().map(|s| (*s).into()).collect()
}

/// Whether the workspace sandbox can run on this host (bwrap, user namespaces, the system
/// profile).
pub fn sandbox_works(root: &Path) -> bool {
    execute(
        root,
        &AtomicBool::new(false),
        "command",
        &json!({"argv":["true"]}),
        None,
    )
    .is_ok_and(|result| result["exit_code"] == 0)
}

pub fn execute(
    root: &Path,
    cancel: &AtomicBool,
    name: &str,
    args: &Value,
    before: Option<&Value>,
) -> Result<Value> {
    if cancel.load(Ordering::SeqCst) {
        return Err("request cancelled".into());
    }
    match name {
        "list" => {
            let directory = path(root, args["path"].as_str().unwrap_or("."), true)?;
            let mut entries = Vec::new();
            for entry in fs::read_dir(directory).map_err(err)?.take(1000) {
                let entry = entry.map_err(err)?;
                let name = entry.file_name().to_string_lossy().to_string();
                if denied(&name) {
                    continue;
                }
                let kind = entry.file_type().map_err(err)?;
                entries.push(
                    json!({"name":name,"directory":kind.is_dir(),"symlink":kind.is_symlink()}),
                );
            }
            Ok(json!({"entries":entries}))
        }
        "read" => {
            let file = fs::File::open(path(root, string(args, "path")?, false)?).map_err(err)?;
            let mut bytes = Vec::new();
            file.take(64000).read_to_end(&mut bytes).map_err(err)?;
            Ok(json!({"text":String::from_utf8_lossy(&bytes)}))
        }
        "search" => {
            let mut command = strings(&[
                "rg",
                "--fixed-strings",
                "--line-number",
                "--max-count",
                "10",
                "--max-filesize",
                "1M",
            ]);
            for part in DENIED {
                command.extend([
                    "--glob".into(),
                    format!("!{part}"),
                    "--glob".into(),
                    format!("!**/{part}/**"),
                ]);
            }
            command.extend(strings(&[
                "--glob",
                "!.env.*",
                "--glob",
                "!.*history",
                "--",
                string(args, "query")?,
                ".",
            ]));
            run(&workspace(root)?, cancel, &command, false, 30)
        }
        "git" => {
            let root = workspace(root)?;
            let mut command = sandbox(&root, false, &git_dirs(&root)?)?;
            command.extend(strings(&[
                "git",
                "--no-pager",
                "--no-optional-locks",
                "-c",
                "core.fsmonitor=false",
                "-c",
                "core.hooksPath=/dev/null",
            ]));
            let operation = string(args, "operation")?;
            command.extend(match operation {
                "status" => strings(&["status", "--short", "--ignore-submodules=all"]),
                "diff" => strings(&[
                    "diff",
                    "--no-ext-diff",
                    "--no-textconv",
                    "--ignore-submodules=all",
                ]),
                "log" => strings(&["log", "-10", "--format=%h %s"]),
                _ => return Err("unsupported Git inspection".into()),
            });
            if operation != "log" {
                command.push("--".into());
                command.extend(git_pathspecs());
            }
            run(&root, cancel, &command, false, 30)
        }
        "diagnostics" => {
            let mut result = json!({});
            for (name, command) in [
                ("system", strings(&["uname", "-a"])),
                (
                    "services",
                    strings(&["systemctl", "--user", "--failed", "--no-pager"]),
                ),
                (
                    "gpu",
                    strings(&[
                        "nvidia-smi",
                        "--query-gpu=name,memory.total,memory.used",
                        "--format=csv",
                    ]),
                ),
            ] {
                result[name] = run(root, cancel, &command, false, 10)
                    .unwrap_or_else(|error| json!({"error":error}));
            }
            result["models"] =
                super::providers::models("ollama").unwrap_or_else(|error| json!({"error":error}));
            Ok(result)
        }
        "write" => {
            let target = path(root, string(args, "path")?, false)?;
            let current = if target.exists() {
                fs::read_to_string(&target).map_err(err)?
            } else {
                String::new()
            };
            let current = json!({"path":target,"exists":target.exists(),"text":current});
            if before != Some(&current) {
                return Err("file changed since preview; request a new action".into());
            }
            let parent = target.parent().unwrap();
            fs::create_dir_all(parent).map_err(err)?;
            let mut temp = tempfile::NamedTempFile::new_in(parent).map_err(err)?;
            temp.write_all(string(args, "text")?.as_bytes())
                .and_then(|_| temp.as_file().sync_all())
                .map_err(err)?;
            if let Ok(metadata) = fs::metadata(&target) {
                temp.as_file()
                    .set_permissions(metadata.permissions())
                    .map_err(err)?;
            }
            temp.persist(&target).map_err(err)?;
            Ok(json!({"written":target}))
        }
        "command" => {
            let task_args = argv(args)?;
            let root = workspace(root)?;
            let mut command = sandbox(&root, true, &[])?;
            command.extend(task_args);
            run(&root, cancel, &command, false, 120)
        }
        "http" => {
            let method = string(args, "method")?;
            if !["GET", "POST", "PUT", "PATCH", "DELETE", "HEAD"].contains(&method) {
                return Err("unsupported HTTP method".into());
            }
            let (status, bytes, retry) = net::request(
                method,
                string(args, "url")?,
                &[],
                args.get("body"),
                cancel,
                60,
                128000,
            )?;
            Ok(json!({"status":status,"body":String::from_utf8_lossy(&bytes),"retry_after":retry}))
        }
        "service" => {
            let name = string(args, "name")?;
            if name.is_empty()
                || name.starts_with('-')
                || !name
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || "@._:-".contains(c))
            {
                return Err("invalid service name".into());
            }
            let op = string(args, "operation")?;
            if !["status", "start", "stop", "restart"].contains(&op) {
                return Err("unsupported service operation".into());
            }
            let mut command = vec!["systemctl".into()];
            if args["system"] != true {
                command.push("--user".into());
            }
            command.extend(strings(&[op, name, "--no-pager"]));
            run(root, cancel, &command, false, 45)
        }
        "launch" => {
            let id = string(args, "desktop_id")?;
            if id.starts_with('-') || id.contains('/') {
                return Err("expected an installed desktop ID".into());
            }
            run(root, cancel, &strings(&["gtk-launch", id]), true, 30)
        }
        "window" => {
            let op = string(args, "action")?;
            if op == "list" {
                return run(
                    root,
                    cancel,
                    &strings(&["hyprctl", "-j", "clients"]),
                    true,
                    10,
                );
            }
            let address = string(args, "address")?;
            if !address
                .strip_prefix("0x")
                .is_some_and(|rest| !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_hexdigit()))
            {
                return Err("invalid window address".into());
            }
            let op = match op {
                "focus" => "focuswindow",
                "close" => "closewindow",
                _ => return Err("unsupported window action".into()),
            };
            run(
                root,
                cancel,
                &strings(&["hyprctl", "dispatch", op, &format!("address:{address}")]),
                true,
                10,
            )
        }
        "screenshot" => {
            let destination =
                super::socket_path()?.with_file_name(format!("capture-{}.png", super::token()?));
            let result = run(
                root,
                cancel,
                &strings(&[
                    "grim",
                    destination.to_str().ok_or("invalid screenshot path")?,
                ]),
                true,
                20,
            )?;
            if result["exit_code"] != 0 {
                return Err("screenshot failed".into());
            }
            Ok(
                json!({"path":destination,"monitors":run(root,cancel,&strings(&["hyprctl","-j","monitors"]),true,10)?}),
            )
        }
        "gui" => {
            let args = argv(args)?;
            gui_events(&args)?;
            let helper =
                std::env::var("LUCY_INPUT_HELPER").map_err(|_| "input helper is not configured")?;
            let auth = run(root, cancel, &strings(&["pkexec", &helper]), true, 60)?;
            if auth["exit_code"] != 0 {
                return Err("input helper authentication failed".into());
            }
            let mut command = vec!["ydotool".into()];
            command.extend(args);
            let result = run(root, cancel, &command, true, 10);
            let _ = Command::new("systemctl")
                .args(["stop", "lucy-input.service"])
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .status();
            result
        }
        "privileged" if args["operation"] == "hardware-info" => run(
            root,
            cancel,
            &strings(&[
                "pkexec",
                &std::env::var("LUCY_DMI_HELPER").map_err(|_| "hardware helper not configured")?,
            ]),
            true,
            60,
        ),
        _ => Err("unsupported action".into()),
    }
}
