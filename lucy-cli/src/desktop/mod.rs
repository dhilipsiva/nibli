//! Native Rust desktop service, agent CLI and app protocol adapters.
//! UI capabilities are optional; the service and store require no Python runtime.
pub mod actions;
mod adapters;
mod core;
mod net;
pub mod providers;
#[cfg(test)]
mod tests;
#[cfg(all(feature = "desktop-ui", target_os = "linux"))]
mod ui;

pub use core::Service;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, IsTerminal, Read, Write};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

pub type Result<T> = std::result::Result<T, String>;
pub const MAX_FRAME: usize = 8 * 1024 * 1024;
pub const DEFAULT_MODEL: &str = "qwen3.6:35b-a3b-q4_K_M";
pub const DEFAULT_DIGEST: &str = "07d35212591fc27746f0a317c975a6d68754fb38e9053d82e25f06057af28522";

pub fn err(error: impl std::fmt::Display) -> String {
    error.to_string()
}
pub fn string<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value[key]
        .as_str()
        .ok_or_else(|| format!("string field {key} is required"))
}
pub fn token() -> Result<String> {
    let mut bytes = [0u8; 32];
    getrandom::fill(&mut bytes).map_err(err)?;
    Ok(bytes.iter().map(|b| format!("{b:02x}")).collect())
}
pub fn model() -> String {
    std::env::var("LUCY_CHAT_MODEL").unwrap_or_else(|_| DEFAULT_MODEL.into())
}

/// Text from the model, memory or a proposal, made inert for a terminal or a text view: control
/// characters other than newline and tab, and bidirectional overrides, isolates and marks, are
/// shown as `\u{..}` escapes, so they cannot move the cursor, hide text or reorder it.
pub fn visible(text: &str) -> String {
    let mut shown = String::with_capacity(text.len());
    for c in text.chars() {
        if (c.is_control() && c != '\n' && c != '\t')
            || matches!(
                c,
                '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}' | '\u{200e}' | '\u{200f}' | '\u{61c}'
            )
        {
            shown.push_str(&format!("\\u{{{:x}}}", c as u32));
        } else {
            shown.push(c);
        }
    }
    shown
}

/// What the terminal agent prints before it asks: the model's text, then the pending proposal.
fn screen(text: Option<&str>, proposal: Option<&Value>) -> Result<String> {
    let mut shown = String::new();
    if let Some(text) = text {
        shown.push_str(&format!("Lucy: {}\n", visible(text)));
    }
    if let Some(proposal) = proposal {
        shown.push_str(&visible(
            &serde_json::to_string_pretty(proposal).map_err(err)?,
        ));
        shown.push('\n');
    }
    Ok(shown)
}

/// The answer to an approval prompt. Only a person at a terminal can give one: piped input is
/// denied unread, and keys queued before the prompt (typed ahead, or injected by an approved
/// `gui` action into the focused terminal) are discarded first.
fn read_approval(
    terminal: bool,
    flush: impl FnOnce() -> Result<()>,
    read: impl FnOnce() -> Result<String>,
) -> Result<bool> {
    if !terminal {
        return Ok(false);
    }
    flush()?;
    Ok(read()?.trim().eq_ignore_ascii_case("y"))
}

pub fn socket_path() -> Result<PathBuf> {
    Ok(
        PathBuf::from(std::env::var_os("XDG_RUNTIME_DIR").ok_or("XDG_RUNTIME_DIR is required")?)
            .join("lucy/service.sock"),
    )
}

pub fn call(request: Value) -> Result<Value> {
    let mut stream = UnixStream::connect(socket_path()?)
        .map_err(|e| format!("Lucy service unavailable: {e}; start `lucy serve`"))?;
    stream
        .set_read_timeout(Some(Duration::from_secs(660)))
        .map_err(err)?;
    writeln!(stream, "{request}").map_err(err)?;
    let response = read_frame(&mut BufReader::new(stream))?;
    if let Some(error) = response["error"].as_str() {
        return Err(error.into());
    }
    Ok(response)
}

fn read_frame(reader: &mut impl BufRead) -> Result<Value> {
    let mut bytes = Vec::new();
    reader
        .take((MAX_FRAME + 1) as u64)
        .read_until(b'\n', &mut bytes)
        .map_err(err)?;
    if bytes.len() > MAX_FRAME || bytes.last() != Some(&b'\n') {
        return Err("invalid or oversized request frame".into());
    }
    serde_json::from_slice(&bytes).map_err(err)
}

pub fn serve(root: &Path, identity: Option<PathBuf>) -> Result<()> {
    let path = socket_path()?;
    let directory = path.parent().unwrap();
    if std::fs::symlink_metadata(directory).is_ok_and(|m| m.file_type().is_symlink()) {
        return Err("refusing symlinked runtime directory".into());
    }
    std::fs::create_dir_all(directory).map_err(err)?;
    std::fs::set_permissions(directory, std::fs::Permissions::from_mode(0o700)).map_err(err)?;
    if path.exists() {
        if UnixStream::connect(&path).is_ok() {
            return Err("Lucy service is already running".into());
        }
        std::fs::remove_file(&path).map_err(err)?;
    }
    let listener = UnixListener::bind(&path).map_err(err)?;
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600)).map_err(err)?;
    let service = Arc::new(Service::new(root.to_path_buf(), identity));
    for incoming in listener.incoming() {
        let mut stream = incoming.map_err(err)?;
        #[cfg(target_os = "linux")]
        {
            use nix::sys::socket::{getsockopt, sockopt::PeerCredentials};
            if getsockopt(&stream, PeerCredentials).map_err(err)?.uid()
                != nix::unistd::getuid().as_raw()
            {
                continue;
            }
        }
        let service = service.clone();
        std::thread::spawn(move || {
            let _ = stream.set_read_timeout(Some(Duration::from_secs(10)));
            let result = stream
                .try_clone()
                .map_err(err)
                .and_then(|input| read_frame(&mut BufReader::new(input)))
                .and_then(|request| service.dispatch(request));
            let response = result.unwrap_or_else(|error| json!({"error":error}));
            if let Ok(bytes) = serde_json::to_vec(&response)
                && bytes.len() <= MAX_FRAME
            {
                let _ = stream.write_all(&bytes);
                let _ = stream.write_all(b"\n");
            }
        });
    }
    Ok(())
}

pub fn run(args: &[String]) -> Result<()> {
    let command = args.first().map(String::as_str).unwrap_or("");
    if command == "desktop-hook" {
        let source = args.get(1).ok_or("desktop-hook needs a source")?;
        let data: Value = serde_json::from_reader(std::io::stdin()).map_err(err)?;
        match adapters::hook(source, data) {
            Ok(value) => println!("{value}"),
            Err(error) => {
                eprintln!("Lucy hook: {error}");
                println!("{{}}");
            }
        }
        return Ok(());
    }
    if command == "native-host" {
        return adapters::native();
    }
    let mut options = BTreeMap::new();
    let mut positional = Vec::new();
    let mut files = Vec::new();
    let mut input = args.iter().skip(1);
    while let Some(arg) = input.next() {
        if arg == "--files" && command == "ui" {
            files.extend(input.map(PathBuf::from));
            break;
        } else if matches!(arg.as_str(), "--stdin" | "--handoff-stdin") {
            options.insert(arg.as_str(), "true");
        } else if matches!(
            arg.as_str(),
            "--data"
                | "--workspace"
                | "--source"
                | "--session"
                | "--text"
                | "--event"
                | "--channel"
                | "--browser-id"
                | "--name"
                | "--model"
        ) {
            options.insert(
                arg.as_str(),
                input
                    .next()
                    .ok_or_else(|| format!("{arg} requires a value"))?
                    .as_str(),
            );
        } else if arg.starts_with("--") {
            return Err(format!("unknown option: {arg}"));
        } else {
            positional.push(arg.as_str());
        }
    }
    let get = |name: &str| {
        options
            .get(name)
            .copied()
            .ok_or_else(|| format!("{name} is required"))
    };
    let root = options
        .get("--data")
        .map(PathBuf::from)
        .unwrap_or(crate::store::default_root()?);
    let mut workspace = options
        .get("--workspace")
        .map(PathBuf::from)
        .unwrap_or(std::env::current_dir().map_err(err)?);
    // The tools refuse the home directory as a workspace, so the desktop commands started there
    // work in ~/LucyTasks instead.
    if matches!(command, "ui" | "chat" | "agent")
        && !options.contains_key("--workspace")
        && std::env::var_os("HOME").is_some_and(|home| workspace == home)
    {
        workspace = workspace.join("LucyTasks");
        std::fs::create_dir_all(&workspace).map_err(err)?;
    }
    match command {
        "serve" => serve(&root, std::env::var_os("LUCY_IDENTITY").map(PathBuf::from)),
        "setup-model" => {
            let status = std::process::Command::new("ollama")
                .args(["pull", &model()])
                .env("OLLAMA_HOST", "127.0.0.1:11434")
                .status()
                .map_err(err)?;
            if !status.success() {
                return Err("model download failed".into());
            }
            core::verify_model()?;
            println!("{}", json!({"ok":true,"model":model()}));
            Ok(())
        }
        "memory" | "sleep" | "mcp" => {
            let source = get("--source")?;
            let session = get("--session")?;
            if command == "mcp" {
                return adapters::mcp(source, session);
            }
            let operation = if command == "sleep" {
                "sleep"
            } else {
                *positional
                    .first()
                    .ok_or("memory needs prompt, record, recall or transcript")?
            };
            let mut request = json!({"op":operation,"source":source,"session":session});
            let mut text = options.get("--text").copied().unwrap_or("").to_owned();
            if options.contains_key("--stdin") {
                if options.contains_key("--text") {
                    return Err("use either --text or --stdin".into());
                }
                std::io::stdin().read_to_string(&mut text).map_err(err)?;
            }
            match operation {
                "recall" => request["query"] = json!(text),
                "prompt" | "record" => {
                    request["text"] = json!(text);
                    request["workspace"] = json!(workspace);
                    request["event"] = json!(
                        options
                            .get("--event")
                            .map(|s| s.to_string())
                            .unwrap_or(token()?)
                    );
                    request["channel"] =
                        json!(options.get("--channel").copied().unwrap_or("final"));
                }
                "transcript" | "sleep" => {}
                _ => return Err("unknown memory operation".into()),
            }
            println!("{}", call(request)?);
            Ok(())
        }
        "archive" => {
            let operation = *positional
                .first()
                .ok_or("archive needs import or reindex")?;
            if !matches!(operation, "import" | "reindex") {
                return Err("unknown archive operation".into());
            }
            let client = call(json!({"op":"open"}))?;
            let result = (|| {
                let mut request = client.clone();
                request["op"] = json!("begin-archive");
                request["workspace"] = json!(workspace);
                call(request)?;
                let mut request = client.clone();
                request["op"] = json!(operation);
                if operation == "import" {
                    request["messages"] = serde_json::from_reader(std::io::stdin()).map_err(err)?;
                }
                call(request)
            })();
            let mut close = client;
            close["op"] = json!("close");
            let _ = call(close);
            println!("{}", result?);
            Ok(())
        }
        "integrations" => {
            println!(
                "{}",
                adapters::integrations(
                    positional.first().copied().unwrap_or("status"),
                    options.get("--browser-id").copied()
                )?
            );
            Ok(())
        }
        "providers" => {
            let operation = positional.first().copied().unwrap_or("list");
            match operation {
                "list"=>println!("{}",providers::list()?),
                "configure"=>{providers::configure(get("--name")?,get("--model")?)?;println!("{}",providers::list()?);},
                "use"=>{providers::select(get("--name")?)?;println!("{}",providers::list()?);},
                "models"=>println!("{}",providers::models(get("--name")?)?),
                "key"=>{
                    if !options.contains_key("--stdin"){return Err("provide the key through --stdin, never process arguments".into());}
                    let mut key=String::new();std::io::stdin().read_to_string(&mut key).map_err(err)?;
                    providers::save_key(get("--name")?,&key)?;
                    println!("{{\"saved\":true}}");
                }
                _=>return Err("providers: list, configure --name --model, use --name, models --name, key --name --stdin".into()),
            }
            Ok(())
        }
        "ui" => {
            let handoff: Option<Value> = if !files.is_empty() {
                let paths: Vec<_> = files
                    .iter()
                    .map(std::path::absolute)
                    .collect::<std::io::Result<_>>()
                    .map_err(err)?;
                if !options.contains_key("--workspace")
                    && let Some(parent) = paths[0].parent()
                {
                    workspace = parent.to_path_buf();
                }
                Some(
                    json!({"source":"explicit file selection","text":paths.iter().map(|p|p.to_string_lossy()).collect::<Vec<_>>().join("\n")}),
                )
            } else if options.contains_key("--handoff-stdin") {
                Some(serde_json::from_reader(std::io::stdin()).map_err(err)?)
            } else {
                None
            };
            #[cfg(all(feature = "desktop-ui", target_os = "linux"))]
            {
                ui::run(&workspace, handoff)
            }
            #[cfg(not(all(feature = "desktop-ui", target_os = "linux")))]
            {
                let _ = (workspace, handoff);
                Err("Build Lucy with --features desktop-ui for the native GTK window".into())
            }
        }
        "chat" | "agent" => agent(
            &workspace,
            if positional.is_empty() {
                None
            } else {
                Some(positional.join(" "))
            },
        ),
        _ => Err("unknown desktop command".into()),
    }
}

fn agent(workspace: &Path, task: Option<String>) -> Result<()> {
    // The local CLI is the UI authority. Its random control token is never
    // included in model context or tool schemas.
    let client = call(json!({"op":"open"}))?;
    // Keep action execution in the service so cancellation can kill the whole
    // command group even if the terminal process exits.
    let mut signals = nix::sys::signal::SigSet::empty();
    signals.add(nix::sys::signal::Signal::SIGINT);
    signals.add(nix::sys::signal::Signal::SIGTERM);
    signals.thread_block().map_err(err)?;
    let cancel_client = client.clone();
    std::thread::spawn(move || {
        if signals.wait().is_ok() {
            let mut close = cancel_client;
            close["op"] = json!("close");
            let _ = call(close);
            std::process::exit(130);
        }
    });
    let mut task = task;
    let result = (|| {
        loop {
            let once = task.is_some();
            let text = if let Some(text) = task.take() {
                text
            } else {
                print!("You: ");
                std::io::stdout().flush().map_err(err)?;
                let mut text = String::new();
                if std::io::stdin().read_line(&mut text).map_err(err)? == 0
                    || text.trim() == "/quit"
                {
                    break;
                }
                text
            };
            if text.trim().is_empty() {
                continue;
            }
            let mut request = client.clone();
            request["op"] = json!("chat");
            request["text"] = json!(text);
            request["event"] = json!(token()?);
            request["workspace"] = json!(workspace);
            let mut response = call(request)?;
            loop {
                print!("{}", screen(response["text"].as_str(), None)?);
                let Some((id, proposal)) = response["pending"]
                    .as_object()
                    .and_then(|p| p.iter().next())
                else {
                    break;
                };
                print!("{}", screen(None, Some(proposal))?);
                let terminal = std::io::stdin().is_terminal();
                if !terminal {
                    println!("Approval needs a terminal; denied.");
                }
                print!("Approve this exact action? [y/N] ");
                std::io::stdout().flush().map_err(err)?;
                let allow = read_approval(
                    terminal,
                    || {
                        nix::sys::termios::tcflush(
                            std::io::stdin(),
                            nix::sys::termios::FlushArg::TCIFLUSH,
                        )
                        .map_err(err)
                    },
                    || {
                        let mut answer = String::new();
                        std::io::stdin().read_line(&mut answer).map_err(err)?;
                        Ok(answer)
                    },
                )?;
                let mut request = client.clone();
                request["op"] = json!("approve");
                request["action"] = json!(id);
                request["allow"] = json!(allow);
                response = call(request)?;
            }
            if once {
                break;
            }
        }
        Ok(())
    })();
    let mut close = client;
    close["op"] = json!("close");
    let _ = call(close);
    result
}
