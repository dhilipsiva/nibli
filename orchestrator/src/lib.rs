#[allow(warnings)]
mod bindings;

use bindings::Guest;
use bindings::lojban::nesy::{parser, reasoning, semantics};

struct EnginePipeline;

impl Guest for EnginePipeline {
    fn execute(input: String) -> bool {
        // --- Phase 1: Zero-Copy Parse ---
        let ast = match parser::parse_text(&input) {
            Ok(ast) => ast,
            Err(e) => {
                println!("[WASM] Parser Error: {}", e);
                return false;
            }
        };
        println!("[WASM] Parsed {} bridi.", ast.sentences.len());

        // --- Phase 2: Zero-Copy Semantics ---
        // AST memory pointer is passed directly; no host-side serialization!
        let sexps = match semantics::compile_buffer(&ast) {
            Ok(s) => s,
            Err(e) => {
                println!("[WASM] Semantics Error: {}", e);
                return false;
            }
        };

        let mut final_entailment = false;

        // --- Phase 3: Reasoning ---
        for sexp in sexps {
            println!("[WASM] Logical Form: {}", sexp);

            if let Err(e) = reasoning::assert_fact(&sexp) {
                println!("[WASM] Assert Error: {}", e);
                continue;
            }

            match reasoning::query_entailment(&sexp) {
                Ok(result) => {
                    println!(
                        "[WASM] Entailment: {}",
                        if result { "TRUE" } else { "FALSE" }
                    );
                    final_entailment = result;
                }
                Err(e) => println!("[WASM] Query Error: {}", e),
            }
        }

        final_entailment
    }
}

bindings::export!(EnginePipeline with_types_in bindings);
