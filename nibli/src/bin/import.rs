//! nibli-import — RDF Turtle / OWL import CLI (the entrypoint for the
//! `nibli-import` crate, which was previously library-only).
//!
//! Usage:
//!   nibli-import <file.ttl> [--raw] [--export] [--query "<text>"]...
//!
//! Imports the Turtle file into a fresh engine KB and reports the count.
//!   --raw     import every triple as a 2-arg fact (skip OWL class handling:
//!             rdfs:subClassOf -> subsort, rdf:type -> entity sort)
//!   --export  print the KB export after import (round-trip view)
//!   --query   run a KR query against the imported KB (repeatable)
//!
//! Note: `--query` reaches only relation names the KR front-end can SPELL:
//! dictionary/alias-resolvable names — an unknown name is a fail-closed
//! compile error, never an arity guess (SURFACE_SYNTAX §13). English-named
//! RDF predicates (e.g. `hasPart` — local names import VERBATIM, camelCase
//! and all) import fine as facts but cannot be spelled in the query
//! language; making them queryable awaits the v2 schema registry
//! (SURFACE_SYNTAX §14.1) — decided 2026-07-12 over an unknown-word
//! passthrough, which would have weakened the fail-closed guarantee while
//! still not reaching camelCase names.
//!
//! Exit code: 0 on success, 1 on any parse/import/query error (fail closed).

use nibli_engine::NibliEngine;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();

    let mut file: Option<String> = None;
    let mut raw = false;
    let mut export = false;
    let mut queries: Vec<String> = Vec::new();

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--raw" => raw = true,
            "--export" => export = true,
            "--query" => {
                i += 1;
                match args.get(i) {
                    Some(q) => queries.push(q.clone()),
                    None => {
                        eprintln!("error: --query needs a sentence argument");
                        return ExitCode::FAILURE;
                    }
                }
            }
            "--help" | "-h" => {
                eprintln!(
                    "usage: nibli-import <file.ttl> [--raw] [--export] [--query \"<text>\"]..."
                );
                return ExitCode::SUCCESS;
            }
            other if file.is_none() && !other.starts_with('-') => file = Some(other.to_string()),
            other => {
                eprintln!("error: unexpected argument '{other}' (see --help)");
                return ExitCode::FAILURE;
            }
        }
        i += 1;
    }

    let Some(path) = file else {
        eprintln!("usage: nibli-import <file.ttl> [--raw] [--export] [--query \"<text>\"]...");
        return ExitCode::FAILURE;
    };

    let turtle = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("error: cannot read {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    let engine = NibliEngine::new();
    let result = if raw {
        nibli_import::import_triples_raw(&engine, &turtle)
    } else {
        nibli_import::import_turtle(&engine, &turtle)
    };
    let count = match result {
        Ok(n) => n,
        Err(e) => {
            eprintln!("[Import Error] {e}");
            return ExitCode::FAILURE;
        }
    };
    println!(
        "[Import] {count} fact(s)/declaration(s) imported from {path}{}",
        if raw { " (raw triples)" } else { "" }
    );

    for q in &queries {
        match engine.query_holds(q) {
            Ok(verdict) => println!("[Query] {q} -> {verdict:?}"),
            Err(e) => {
                eprintln!("[Query Error] {q}: {e}");
                return ExitCode::FAILURE;
            }
        }
    }

    if export {
        match nibli_import::export_facts(&engine) {
            Ok(text) => print!("{text}"),
            Err(e) => {
                eprintln!("[Export Error] {e}");
                return ExitCode::FAILURE;
            }
        }
    }

    ExitCode::SUCCESS
}
