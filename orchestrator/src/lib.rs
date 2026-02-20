#[allow(warnings)]
mod bindings;

use bindings::Guest;
use bindings::lojban::nesy::{parser, reasoning, semantics};

struct EnginePipeline;

impl Guest for EnginePipeline {
    fn execute(input: String) -> bool {
        let is_query = input.starts_with("?");
        let text = if is_query { input[1..].trim() } else { &input };

        // --- Phase 1: Zero-Copy Parse ---
        let ast = match parser::parse_text(text) {
            Ok(ast) => ast,
            Err(e) => {
                println!("[WASM] Parser Error: {}", e);
                return false;
            }
        };

        // --- Phase 2: Zero-Copy Semantics ---
        let logic_buffer = match semantics::compile_buffer(&ast) {
            Ok(buf) => buf,
            Err(e) => {
                println!("[WASM] Semantics Error: {}", e);
                return false;
            }
        };

        // --- Phase 3: Reasoning ---
        if is_query {
            match reasoning::query_entailment(&logic_buffer) {
                Ok(result) => {
                    println!(
                        "[WASM] Query Entailment: {}",
                        if result { "TRUE" } else { "FALSE" }
                    );
                    return result;
                }
                Err(e) => {
                    println!("[WASM] Query Error: {}", e);
                    return false;
                }
            }
        } else {
            if let Err(e) = reasoning::assert_fact(&logic_buffer) {
                println!("[WASM] Assert Error: {}", e);
                return false;
            }
            println!(
                "[WASM] {} facts inserted into Knowledge Base natively.",
                logic_buffer.roots.len()
            );
            return true;
        }
    }
}

bindings::export!(EnginePipeline with_types_in bindings);
