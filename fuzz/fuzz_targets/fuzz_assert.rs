#![no_main]

use libfuzzer_sys::fuzz_target;
use nibli_engine::NibliEngine;

fuzz_target!(|data: &[u8]| {
    if let Ok(input) = std::str::from_utf8(data) {
        let engine = NibliEngine::new();
        let _ = engine.assert_text(input);
    }
});
