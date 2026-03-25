#![no_main]

use libfuzzer_sys::fuzz_target;
use nibli_engine::NibliEngine;

fuzz_target!(|data: &[u8]| {
    if data.len() < 2 {
        return;
    }
    // Split input: first half is asserted, second half is queried.
    let mid = data.len() / 2;
    let assert_bytes = &data[..mid];
    let query_bytes = &data[mid..];

    let assert_str = match std::str::from_utf8(assert_bytes) {
        Ok(s) => s,
        Err(_) => return,
    };
    let query_str = match std::str::from_utf8(query_bytes) {
        Ok(s) => s,
        Err(_) => return,
    };

    let engine = NibliEngine::new();
    let _ = engine.assert_text(assert_str);
    let _ = engine.query_text_with_proof(query_str);
});
