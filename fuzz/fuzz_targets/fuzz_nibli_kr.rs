#![no_main]

use libfuzzer_sys::fuzz_target;

// Fuzz the nibli KR front-end: arbitrary UTF-8 through `nibli_kr::parse_checked`
// (pest parse -> fail-closed resolve -> emit). Any `Ok(AstBuffer)` has passed
// nibli-kr's own name/place checks, so handing smuni a STRUCTURALLY invalid
// buffer (out-of-bounds index, reference cycle — smuni's `validate_ast_buffer`
// rejects both with the stable "corrupt AST buffer" message) is a nibli-kr
// emitter bug: the oracle panics on that error class. Other smuni Semantic
// rejections (arity overflow, n-ary `du`, ambiguous injection, ...) are
// legitimate and ignored. Panics/leaks anywhere are caught by libFuzzer/LSan.
fuzz_target!(|data: &[u8]| {
    if let Ok(input) = std::str::from_utf8(data) {
        if let Ok(buffer) = nibli_kr::parse_checked(input) {
            if let Err(e) = smuni::compile_from_gerna_ast(buffer) {
                let msg = format!("{e}");
                assert!(
                    !msg.contains("corrupt AST buffer"),
                    "nibli-kr emitted a structurally invalid AstBuffer for {input:?}: {msg}"
                );
            }
        }
    }
});
