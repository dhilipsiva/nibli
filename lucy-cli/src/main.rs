//! The `lucy` binary: a thin shell over `lucy_cli::run`.

use std::io::{Read, Write};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
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
