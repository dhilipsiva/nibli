#![no_main]

use libfuzzer_sys::fuzz_target;
use nibli_engine::NibliEngine;
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
    mpsc,
};
use std::time::Duration;

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
    // Native reasoning has no default host budget. Quantified seed queries can
    // enumerate a combinatorial domain, so exercise the same cooperative
    // cancellation API used by bounded hosts. Keep the seed and its proof path;
    // crashes and OOMs within the budget still fail the fuzz gate.
    let cancelled = Arc::new(AtomicBool::new(false));
    engine.set_cancel_flag(Arc::clone(&cancelled));
    let (done, waiting) = mpsc::channel::<()>();
    std::thread::scope(|scope| {
        scope.spawn(move || {
            if matches!(
                waiting.recv_timeout(Duration::from_millis(100)),
                Err(mpsc::RecvTimeoutError::Timeout)
            ) {
                cancelled.store(true, Ordering::Relaxed);
            }
        });
        let _ = engine.assert_text(assert_str);
        let _ = engine.query_text_with_proof(query_str);
        // Disconnect immediately on completion; the scoped watchdog cannot
        // outlive this input or cancel a later input.
        drop(done);
    });
});
