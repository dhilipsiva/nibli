//! Export syntax without running the validating emitter or compiler.
use nibli_kr::reify::{InputIntent, ast_to_nibli};
use std::io::{self, Read, Write};
use std::process::ExitCode;

fn run() -> Result<(), String> {
    let mut path = None;
    let mut emit = false;
    let mut intent = InputIntent::Assertion;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--emit-ast-facts" => emit = true,
            "--query" => intent = InputIntent::Query,
            "--help" | "-h" => {
                println!(
                    "Usage: nibli-ast --emit-ast-facts FILE [--query]\nUse - for stdin. Output is syntax data; no subject statements are executed."
                );
                return Ok(());
            }
            _ if path.is_none() && (!arg.starts_with('-') || arg == "-") => {
                path = Some(arg);
            }
            _ => return Err(format!("unexpected argument: {arg}")),
        }
    }
    if !emit || path.is_none() {
        return Err("usage: nibli-ast --emit-ast-facts FILE [--query]".into());
    }
    let path = path.unwrap();
    let text = if path == "-" {
        let mut text = String::new();
        io::stdin()
            .read_to_string(&mut text)
            .map_err(|e| e.to_string())?;
        text
    } else {
        std::fs::read_to_string(&path).map_err(|e| format!("{path}: {e}"))?
    };
    let tree = nibli_kr::parser::parse_statements(&text)
        .map_err(|e| format!("{}:{}: {}", e.line, e.column, e.message))?;
    let facts = ast_to_nibli(&tree, intent).map_err(|e| e.to_string())?;
    io::stdout()
        .lock()
        .write_all(facts.as_bytes())
        .map_err(|e| e.to_string())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("nibli-ast: {error}");
            ExitCode::FAILURE
        }
    }
}
