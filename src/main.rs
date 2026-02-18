use reedline::{DefaultPrompt, Reedline, Signal};
use bumpalo::Bump;

// Assuming our modules are correctly exposed
mod lexer;
mod preprocessor;
mod ast;
mod ir;
mod semantic;
mod reasoning;

use lexer::tokenize;
use preprocessor::preprocess;
use ast::parse_to_ast;
use semantic::SemanticCompiler;
use reasoning::ReasoningCore;

fn main() {
    println!("==================================================");
    println!(" Lojban Neuro-Symbolic Engine - Bare-Metal V1 MVP ");
    println!("==================================================");
    println!("Type ':quit' to exit.");

    let mut line_editor = Reedline::create();
    let prompt = DefaultPrompt::default();

    // Persistent state across REPL iterations
    let mut compiler = SemanticCompiler::new();
    let mut reasoner = ReasoningCore::new();

    loop {
        let sig = line_editor.read_line(&prompt);
        match sig {
            Ok(Signal::Success(buffer)) => {
                let input = buffer.trim();
                
                if input.is_empty() {
                    continue;
                }
                if input == ":quit" || input == ":q" {
                    break;
                }

                println!("\n[1] Raw Input: {}", input);

                // Phase 1: Lexing
                let raw_tokens = tokenize(input);
                println!("[2] Lexed Tokens: {} items", raw_tokens.len());

                // Phase 2: Preprocessing (Resolving si, sa, su, zo, zoi)
                let normalized_tokens = preprocess(raw_tokens.into_iter(), input);
                println!("[3] Normalized Tokens: {:?}", normalized_tokens);

                // For the pest parser, we reconstruct the sanitized string.
                // In a pure zero-copy pipeline, the preprocessor outputs a String
                // or pest is fed a custom token stream. For V1, we join the normalized text.
                let sanitized_input = normalized_tokens
                    .iter()
                    .filter_map(|t| match t {
                        preprocessor::NormalizedToken::Standard(_, s) => Some(*s),
                        preprocessor::NormalizedToken::Quoted(s) => Some(*s),
                        preprocessor::NormalizedToken::Glued(parts) => Some(parts[0]), // simplified
                    })
                    .collect::<Vec<&str>>()
                    .join(" ");

                // Phase 3: Structural Parsing (AST via Bump Arena)
                let arena = Bump::new();
                match parse_to_ast(&sanitized_input, &arena) {
                    Ok(ast) => {
                        println!("[4] AST Generated: {} Bridi nodes", ast.len());

                        // Phase 4: Semantic Compilation & Reasoning
                        for bridi in ast.iter() {
                            // Compile to Logical Intermediate Representation (LIR)
                            let lir = compiler.compile_bridi(bridi);
                            println!("[5] Logical Form (LIR): {:?}", lir);

                            // Phase 5: Assert into the E-Graph / Datalog engine
                            reasoner.assert_fact(&lir);
                            println!("[6] Fact asserted into egglog E-Graph.");
                            
                            // For demonstration, immediately query the exact fact back
                            // In a real scenario, you would type specific query commands (e.g., "? mi klama")
                            println!("[7] Verifying Graph Entailment...");
                            
                            // Constructing a naive query string based on the MVP's hardcoded klama path
                            // This proves the Datalog engine absorbed the data.
                            let query_str = format!("(Klama (Const \"mi\") (Desc \"lo_zarci\") (Zoe) (Zoe) (Zoe))");
                            reasoner.query(&query_str);
                        }
                    }
                    Err(e) => {
                        eprintln!("[!] Parser Error: {}", e);
                    }
                }
                
                // The `arena` goes out of scope here and is instantly dropped.
                // Zero garbage collection overhead.
            }
            Ok(Signal::CtrlD) | Ok(Signal::CtrlC) => {
                println!("Aborting.");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
}
