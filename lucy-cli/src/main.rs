//! The `lucy` binary: a thin shell over `lucy_cli::run`.

use std::io::{Read, Write};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let desktop = matches!(
        args.first().map(String::as_str),
        Some(
            "chat"
                | "ui"
                | "sleep"
                | "integrations"
                | "serve"
                | "desktop-hook"
                | "memory"
                | "mcp"
                | "native-host"
                | "setup-model"
                | "archive"
        )
    );
    let hook_runtime = args.first().map(String::as_str) == Some("hook")
        && std::env::var_os("LUCY_DESKTOP_EXECUTABLE").is_some();
    if desktop || hook_runtime {
        let program =
            std::env::var_os("LUCY_DESKTOP_EXECUTABLE").unwrap_or_else(|| "lucy-desktop".into());
        let delegated = if hook_runtime {
            vec!["desktop-hook".to_string(), "claude".to_string()]
        } else {
            args
        };
        match std::process::Command::new(program).args(delegated).status() {
            Ok(status) => std::process::exit(status.code().unwrap_or(1)),
            Err(error) => {
                eprintln!(
                    "Lucy desktop runtime unavailable: {error}. Install Nibli's lucy-cli/desktop runtime."
                );
                std::process::exit(2);
            }
        }
    }
    let mut stdin = String::new();
    if lucy_cli::cli::reads_stdin(&args) {
        let _ = std::io::stdin().read_to_string(&mut stdin);
    }
    let outcome = lucy_cli::run(&args, &stdin, None);
    let mut out = std::io::stdout().lock();
    let _ = out.write_all(outcome.stdout.as_bytes());
    let _ = out.flush();
    if !outcome.stderr.is_empty() {
        let mut err = std::io::stderr().lock();
        let _ = err.write_all(outcome.stderr.as_bytes());
        let _ = err.flush();
    }
    std::process::exit(outcome.code);
}
