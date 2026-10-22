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
    "credentials",
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
/// The canonical workspace. The home directory and its ancestors are refused: they hold the
/// credentials and shell startup files the deny list can only partly name.
fn workspace(root: &Path) -> Result<PathBuf> {
    let root = root.canonicalize().map_err(err)?;
    if let Some(home) = std::env::var_os("HOME").and_then(|h| Path::new(&h).canonicalize().ok())
        && home.starts_with(&root)
    {
        return Err(
            "tools need a project directory as the workspace, not the home directory or above it"
                .into(),
        );
    }
    Ok(root)
}
/// Every denied name in the workspace, found without following symlinks.
fn denied_paths(root: &Path) -> Result<Vec<PathBuf>> {
    let mut found = Vec::new();
    let mut directories = vec![root.to_path_buf()];
    let mut walked = 0;
    while let Some(directory) = directories.pop() {
        // A directory this user cannot read is unreadable inside the sandbox too.
        let Ok(entries) = fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries {
            let entry = entry.map_err(err)?;
            let kind = entry.file_type().map_err(err)?;
            if denied(&entry.file_name().to_string_lossy()) {
                if kind.is_dir() || kind.is_file() {
                    found.push(entry.path());
                }
            } else if kind.is_dir() {
                walked += 1;
                if walked > MAX_SANDBOX_DIRECTORIES {
                    return Err(
                        "the workspace is too large to sandbox; choose a smaller one".into(),
                    );
                }
                directories.push(entry.path());
            }
        }
    }
    Ok(found)
}
/// bwrap arguments that run a program in the workspace with no network, no environment and none
/// of the host but the Nix store and the system profile. Denied names are masked at every depth.
/// `writable` is for approved commands; the unapproved git inspection gets a read-only workspace,
/// and keeps `.git` itself, so repository configuration (filters, drivers) can run nothing that
/// changes or reaches anything.
fn sandbox(root: &Path, writable: bool) -> Result<Vec<String>> {
    let workspace = root.to_str().ok_or("workspace is not UTF-8")?;
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
        if writable { "--bind" } else { "--ro-bind" },
        workspace,
        workspace,
        "--chdir",
        workspace,
        "--clearenv",
        "--setenv",
        "PATH",
        &std::env::var("LUCY_COMMAND_PATH").unwrap_or_else(|_| "/run/current-system/sw/bin".into()),
    ]);
    for path in denied_paths(root)? {
        if !writable && path.file_name().is_some_and(|name| name == ".git") {
            continue;
        }
        let path = path
            .to_str()
            .ok_or("workspace path is not UTF-8")?
            .to_owned();
        if path_is_dir(&path) {
            command.extend(["--tmpfs".into(), path]);
        } else {
            command.extend(["--ro-bind".into(), "/dev/null".into(), path]);
        }
    }
    command.push("--".into());
    Ok(command)
}
fn path_is_dir(path: &str) -> bool {
    fs::symlink_metadata(path).is_ok_and(|m| m.is_dir())
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
/// Checks a `gui` argv and returns the key events it presses, by name. Synthetic input may not
/// submit a line (Enter, keypad Enter, Ctrl+J, Ctrl+M, or a control character in typed text):
/// the approval prompts read lines, and an approved action must not be able to answer one.
fn gui_events(args: &[String]) -> Result<Option<Vec<String>>> {
    let unsupported = || Err::<_, String>("unsupported literal mouse/keyboard action".into());
    match args[0].as_str() {
        "type" if args.len() == 3 && args[1] == "--" && args[2].len() <= 4096 => {
            if args[2].chars().any(|c| c.is_control() && c != '\t') {
                return Err(
                    "synthetic input may not type line breaks or control characters".into(),
                );
            }
            Ok(None)
        }
        "key" if args.len() > 1 && args.len() <= 65 => {
            let (mut left_ctrl, mut right_ctrl) = (false, false);
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
                match code {
                    29 => left_ctrl = down,
                    97 => right_ctrl = down,
                    _ => {}
                }
                if down
                    && (matches!(code, 28 | 96)
                        || ((left_ctrl || right_ctrl) && matches!(code, 36 | 50)))
                {
                    return Err("synthetic input may not press Enter or submit a line".into());
                }
                names.push(format!(
                    "{} {}",
                    key_name(code),
                    if down { "down" } else { "up" }
                ));
            }
            Ok(Some(names))
        }
        "click"
            if args.len() == 2
                && args[1].strip_prefix("0x").is_some_and(|s| {
                    s.len() <= 2 && !s.is_empty() && s.bytes().all(|b| b.is_ascii_hexdigit())
                }) =>
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
            let mut command = sandbox(&root, false)?;
            command.extend(strings(&[
                "git",
                "--no-pager",
                "--no-optional-locks",
                "-c",
                "core.fsmonitor=false",
                "-c",
                "core.hooksPath=/dev/null",
            ]));
            command.extend(match string(args, "operation")? {
                "status" => strings(&["status", "--short"]),
                "diff" => strings(&["diff", "--no-ext-diff", "--no-textconv", "--"]),
                "log" => strings(&["log", "-10", "--format=%h %s"]),
                _ => return Err("unsupported Git inspection".into()),
            });
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
            let mut command = sandbox(&root, true)?;
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
