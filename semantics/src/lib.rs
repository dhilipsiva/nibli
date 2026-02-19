#[allow(warnings)]
pub mod bindings;
pub mod dictionary;
pub mod ir;
pub mod semantic;

use bindings::exports::lojban::nesy::semantics::Guest;
use bindings::lojban::nesy::ast_types::AstBuffer;
use semantic::SemanticCompiler;

struct SemanticsComponent;

impl Guest for SemanticsComponent {
    /// Consumes the Canonical ABI AST buffer and returns an array of optimized S-Expressions.
    fn compile_buffer(ast: AstBuffer) -> Vec<String> {
        // Instantiate the string-interning compiler (Zero dictionary allocation)
        let mut compiler = SemanticCompiler::new();
        let mut sexps = Vec::with_capacity(ast.sentences.len());

        for sentence in ast.sentences {
            // 1. Map AST to the First-Order Logic Intermediate Representation
            let logical_form = compiler.compile_bridi(&sentence, &ast.selbris, &ast.sumtis);

            // 2. Resolve interned strings to flat S-Expressions
            sexps.push(compiler.to_sexp(&logical_form));
        }

        sexps
    }
}

// Bind to WASM exports
bindings::export!(SemanticsComponent with_types_in bindings);
