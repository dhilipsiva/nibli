// SPDX-License-Identifier: MIT OR Apache-2.0
//! Bounded, explicit-path fixture ingestion benchmark; no persisted engine state.

use std::time::{Duration, Instant};

use nibli_session::CoreSession;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let path = args.next().ok_or("usage: fixture_profile PATH [SECONDS]")?;
    let seconds = args.next().as_deref().unwrap_or("45").parse::<u64>()?;
    let batch = args.next().is_some_and(|value| value == "batch");
    let source = std::fs::read_to_string(path)?;
    if batch {
        let texts: Vec<_> = source
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .collect();
        let started = Instant::now();
        let (session, ids) = CoreSession::from_text_batch(&texts).map_err(|e| e.to_string())?;
        eprintln!(
            "batch statements={} elapsed={:.3}s",
            ids.len(),
            started.elapsed().as_secs_f64()
        );
        let started = Instant::now();
        session
            .query_text("person(Adam).")
            .map_err(|e| e.to_string())?;
        eprintln!(
            "first query elapsed={:.3}s",
            started.elapsed().as_secs_f64()
        );
        if let Some(path) = args.next() {
            let source = std::fs::read_to_string(path)?;
            let started = Instant::now();
            let cancellation = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
            session
                .kb()
                .set_cancel_flag(std::sync::Arc::clone(&cancellation));
            std::thread::spawn(move || {
                std::thread::sleep(Duration::from_secs(seconds));
                cancellation.store(true, std::sync::atomic::Ordering::Relaxed);
            });
            let mut assertion = Duration::ZERO;
            let mut queries = Duration::ZERO;
            let mut pins = 0;
            for (index, line) in source.lines().enumerate() {
                let line = line.trim();
                if line.is_empty() || line.starts_with('#') || line.starts_with(":expect-pins ") {
                    continue;
                }
                let before = Instant::now();
                if let Some(query) = line.strip_prefix('?') {
                    let result = session
                        .query_text(query.trim())
                        .map_err(|e| e.to_string())?;
                    queries += before.elapsed();
                    pins += 1;
                    eprintln!(
                        "pin={} line={} result={:?} query={:.3}s assertions={:.3}s all_queries={:.3}s elapsed={:.3}s",
                        pins,
                        index + 1,
                        result,
                        before.elapsed().as_secs_f64(),
                        assertion.as_secs_f64(),
                        queries.as_secs_f64(),
                        started.elapsed().as_secs_f64()
                    );
                } else {
                    session.assert_text(line).map_err(|e| e.to_string())?;
                    assertion += before.elapsed();
                }
                if started.elapsed().as_secs() >= seconds {
                    return Err("benchmark duration reached".into());
                }
            }
        }
        return Ok(());
    }
    let session = CoreSession::new();
    let started = Instant::now();
    let mut compile = Duration::ZERO;
    let mut assertion = Duration::ZERO;
    let mut statements = 0;
    for (index, line) in source.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line.starts_with(':') || line.starts_with('?') {
            break;
        }
        let before = Instant::now();
        let buffer = session.compile_text(line).map_err(|e| e.to_string())?;
        compile += before.elapsed();
        let before = Instant::now();
        session
            .kb()
            .validate_assertion(&buffer)
            .map_err(|e| e.to_string())?;
        for root in buffer.split_roots() {
            session
                .kb()
                .assert_fact(root, line.to_owned())
                .map_err(|e| e.to_string())?;
        }
        assertion += before.elapsed();
        statements += 1;
        if statements % 100 == 0 || started.elapsed().as_secs() >= seconds {
            eprintln!(
                "line={} statements={} compile={:.3}s assert={:.3}s elapsed={:.3}s",
                index + 1,
                statements,
                compile.as_secs_f64(),
                assertion.as_secs_f64(),
                started.elapsed().as_secs_f64(),
            );
        }
        if started.elapsed().as_secs() >= seconds {
            return Err("benchmark duration reached".into());
        }
    }
    eprintln!(
        "complete statements={} compile={:.3}s assert={:.3}s elapsed={:.3}s",
        statements,
        compile.as_secs_f64(),
        assertion.as_secs_f64(),
        started.elapsed().as_secs_f64(),
    );
    Ok(())
}
