//! Nibli native REPL binary.
//!
//! This is a thin CLI wrapper over `nibli-engine`. The engine crate owns the
//! native parse -> compile -> reason pipeline and related adapters.

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;

use nibli_engine::{EngineLogicalTerm, NibliEngine, display_query_result, display_term};
use nibli_kr::lint::Linter;
use reedline::{DefaultPrompt, Reedline, Signal};

mod kr_highlighter;
use kr_highlighter::KrHighlighter;

/// Print the nibli KR lint notes for `text` (NIBLI_KR §12 L1–L9) —
/// non-blocking `[Note: …]` echoes, nibli KR mode only. The `Linter` is
/// session-stateful (L1 introductions, L4 first-use dedup, L7 latch) and is
/// reset with the KB.
fn print_lints(linter: &mut Linter, text: &str) {
    for note in linter.lint(text) {
        println!("[Note: {}]", note.message);
    }
}

fn parse_assert_args(input: &str) -> Result<(String, Vec<EngineLogicalTerm>), String> {
    let parts: Vec<&str> = input.split_whitespace().collect();
    if parts.is_empty() {
        return Err("Usage: :assert <relation> <arg1> <arg2> ...".to_string());
    }

    let relation = parts[0].to_string();
    let args = parts[1..]
        .iter()
        .map(|&s| {
            if let Ok(n) = s.parse::<f64>() {
                EngineLogicalTerm::Number(n)
            } else {
                EngineLogicalTerm::Constant(s.to_string())
            }
        })
        .collect();

    Ok((relation, args))
}

fn parse_depth(value: &str) -> Result<u32, String> {
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err("depth must be a positive u32 integer".into());
    }
    value
        .parse::<u32>()
        .ok()
        .filter(|depth| *depth > 0)
        .ok_or_else(|| "depth must be an integer from 1 through 4294967295".into())
}

fn main() {
    println!("==================================================");
    println!(" Nibli Native REPL - Direct Rust (no WASM)        ");
    println!("==================================================");

    let mut engine = NibliEngine::new();
    match std::env::var("NIBLI_MAX_CHAIN_DEPTH") {
        Ok(value) => {
            if let Err(error) = parse_depth(&value).and_then(|depth| {
                engine
                    .set_max_chain_depth(depth)
                    .map_err(|error| error.to_string())
            }) {
                eprintln!("NIBLI_MAX_CHAIN_DEPTH: {error}");
                std::process::exit(2);
            }
        }
        Err(std::env::VarError::NotPresent) => {}
        Err(error) => {
            eprintln!("NIBLI_MAX_CHAIN_DEPTH: {error}");
            std::process::exit(2);
        }
    }
    // Interactive debug REPL: opt into the engine's [Rule]/[Skolem]/[Constraint]
    // diagnostics (off by default — nibli-engine is a silent library).
    engine.set_verbose(true);
    let mut line_editor = nibli_kr::complete_reedline::with_completion(
        Reedline::create().with_highlighter(Box::new(KrHighlighter)),
    );
    let prompt = DefaultPrompt::default();
    // The KR lint session (NIBLI_KR §12): non-blocking [Note: …]
    // echoes on interactive inputs, reset together with the KB.
    let mut linter = Linter::new();

    println!(
        "Commands: :quit :reset :load <file> :facts [--all] :depth [N] :retract <id> :debug <text> :compute [name] :assert <rel> <args..> :help"
    );
    println!(
        "Prefix '?' for queries with proof trace, '??' for find, plain text for assertions.\n"
    );

    loop {
        match line_editor.read_line(&prompt) {
            Ok(Signal::Success(buffer)) => {
                let input = buffer.trim();
                if input.is_empty() {
                    continue;
                }

                match input {
                    ":quit" | ":q" => break,
                    ":reset" | ":r" => {
                        match engine.reset() {
                            Ok(()) => {
                                linter.reset();
                                println!("[Reset] Knowledge base cleared.");
                            }
                            Err(error) => println!("{error}"),
                        }
                        continue;
                    }
                    ":compute" => {
                        let names = engine.compute_predicates();
                        println!("[Compute] Registered: {}", names.join(", "));
                        println!(
                            "[Compute] product, sum, quotient are built-in (local arithmetic); \
                             other registered corpus relations need external dispatch, which \
                             this debug REPL does not wire — their queries answer UNKNOWN \
                             (backend-unavailable)"
                        );
                        println!(
                            "[Compute] Registration routes existing KR vocabulary; it does not \
                             declare names or infer arity."
                        );
                        continue;
                    }
                    ":depth" => {
                        println!("[Depth] {}", engine.max_chain_depth());
                        continue;
                    }
                    value if value.starts_with(":depth ") => {
                        match parse_depth(value.trim_start_matches(":depth ").trim()).and_then(
                            |depth| {
                                engine
                                    .set_max_chain_depth(depth)
                                    .map_err(|error| error.to_string())
                            },
                        ) {
                            Ok(()) => println!("[Depth] {}", engine.max_chain_depth()),
                            Err(error) => println!("[Depth] {error}"),
                        }
                        continue;
                    }
                    ":facts --all" => {
                        match engine.list_assertion_records() {
                            Ok(records) => {
                                println!("[Facts] {} retained assertion record(s):", records.len());
                                for record in records {
                                    let status = match record.status {
                                        nibli_engine::EngineAssertionStatus::Active => "active",
                                        nibli_engine::EngineAssertionStatus::Withdrawn => {
                                            "withdrawn"
                                        }
                                    };
                                    println!("  #{} [{status}]: {}", record.id, record.label);
                                }
                            }
                            Err(error) => println!("{error}"),
                        }
                        continue;
                    }
                    ":facts" => {
                        match engine.list_facts() {
                            Ok(facts) => {
                                if facts.is_empty() {
                                    println!("[Facts] Knowledge base is empty.");
                                } else {
                                    println!("[Facts] {} active fact(s):", facts.len());
                                    for fact in &facts {
                                        let roots_label = if fact.root_count == 1 {
                                            "root"
                                        } else {
                                            "roots"
                                        };
                                        println!(
                                            "  #{}: {} ({} {})",
                                            fact.id, fact.label, fact.root_count, roots_label
                                        );
                                    }
                                }
                            }
                            Err(e) => println!("{}", e),
                        }
                        continue;
                    }
                    ":traces" => {
                        let traced = engine.traced_predicates();
                        if traced.is_empty() {
                            println!("[Trace] No predicates being traced.");
                        } else {
                            println!("[Trace] Tracing {} predicate(s):", traced.len());
                            for p in &traced {
                                println!("  {}", p);
                            }
                        }
                        continue;
                    }
                    ":contradictions" => {
                        let report = engine.check_contradictions_report();
                        if report.is_clean() {
                            println!(
                                "[Contradictions] Scan complete: no contradictions found \
                                 in represented constraints (not a full closure proof)."
                            );
                        } else {
                            println!(
                                "[Contradictions] {} finding(s), {} unresolved check(s):",
                                report.violations.len(),
                                report.unresolved.len()
                            );
                            for (i, v) in report.violations.iter().enumerate() {
                                println!("  {}: {}", i + 1, v);
                            }
                            for gap in &report.unresolved {
                                println!("  UNRESOLVED: {gap}");
                            }
                        }
                        continue;
                    }
                    ":help" | ":h" => {
                        println!("  <text>              Assert KR text as fact");
                        println!("  ? <text>            Query with proof trace");
                        println!("    exactly N / no are query-only; use the ? route");
                        println!("  ?? <text>           Find witnesses (answer variables)");
                        println!("  :debug <text>       Show compiled logic tree");
                        println!("  :load <filepath>    Load a .nibli file (assert each line)");
                        println!(
                            "  :compute [name]     Show compute relations, or route a corpus \
                             predicate to dispatch"
                        );
                        println!("  :assert <rel> <args..> Assert a ground fact directly");
                        println!("  :retract <id>       Retract a fact by ID (rebuilds KB)");
                        println!("  :facts              List all active facts in the KB");
                        println!(
                            "  :contradictions     Scan represented constraints; report \
                             findings and unresolved checks"
                        );
                        println!("  :trace <pred>       Enable tracing for a predicate");
                        println!("  :untrace <pred>     Disable tracing for a predicate");
                        println!("  :traces             List traced predicates");
                        println!("  :reset              Clear all facts (fresh KB)");
                        println!("  :depth [N]          Show or set the positive reasoning depth");
                        println!(
                            "  :facts --all        List active and withdrawn assertion records"
                        );
                        println!("  :quit               Exit");
                        continue;
                    }
                    _ => {}
                }

                if let Some(trace_pred) = input.strip_prefix(":trace ") {
                    let pred = trace_pred.trim();
                    if pred.is_empty() {
                        println!("[Trace] Usage: :trace <predicate>");
                    } else {
                        engine.trace_predicate(pred);
                        println!("[Trace] Now tracing: {}", pred);
                    }
                    continue;
                } else if let Some(untrace_pred) = input.strip_prefix(":untrace ") {
                    let pred = untrace_pred.trim();
                    if pred.is_empty() {
                        println!("[Trace] Usage: :untrace <predicate>");
                    } else {
                        engine.untrace_predicate(pred);
                        println!("[Trace] Stopped tracing: {}", pred);
                    }
                    continue;
                } else if let Some(debug_text) = input.strip_prefix(":debug ") {
                    let text = debug_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: :debug <text>");
                        continue;
                    }
                    match engine.compile_debug(text) {
                        Ok(buf) => {
                            let tree =
                                nibli_render::render_logic_tree(&buf, nibli_render::Register::Spec);
                            let english = nibli_render::render_logic_buffer(
                                &buf,
                                nibli_render::Register::Spec,
                            );
                            println!("[Logic]\n{}", tree.trim_end());
                            println!("\n[English] {}", english);
                        }
                        Err(e) => println!("{}", e),
                    }
                } else if let Some(compute_name) = input.strip_prefix(":compute ") {
                    let name = compute_name.trim();
                    if name.is_empty() {
                        println!("[Host] Usage: :compute <predicate-name>");
                        continue;
                    }
                    match engine.register_compute_predicate(name.to_string()) {
                        Ok(()) => {
                            println!(
                                "[Compute] Registered corpus predicate '{}' for compute dispatch \
                                 (bare :compute shows its canonical compiled relation)",
                                name
                            )
                        }
                        Err(e) => println!("{}", e),
                    }
                } else if let Some(assert_args) = input.strip_prefix(":assert ") {
                    let text = assert_args.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: :assert <relation> <arg1> <arg2> ...");
                        continue;
                    }
                    match parse_assert_args(text) {
                        Ok((relation, args)) => {
                            let display_args: Vec<String> = args.iter().map(display_term).collect();
                            match engine.assert_fact_direct(relation.clone(), args) {
                                Ok(fact_id) => println!(
                                    "[Fact #{}] {}({}) asserted.",
                                    fact_id,
                                    relation,
                                    display_args.join(", ")
                                ),
                                Err(e) => println!("{}", e),
                            }
                        }
                        Err(e) => println!("[Error] {}", e),
                    }
                } else if let Some(retract_arg) = input.strip_prefix(":retract ") {
                    match retract_arg.trim().parse::<u64>() {
                        Ok(id) => match engine.retract_fact(id) {
                            Ok(()) => println!("[Retract] Fact #{} retracted. KB rebuilt.", id),
                            Err(e) => println!("{}", e),
                        },
                        Err(_) => println!("[Host] Usage: :retract <fact-id>"),
                    }
                } else if let Some(load_arg) = input.strip_prefix(":load ") {
                    let filepath = load_arg.trim();
                    if filepath.is_empty() {
                        println!("[Host] Usage: :load <filepath>");
                        continue;
                    }

                    let path = Path::new(filepath);
                    if !path.exists() {
                        println!("[Load] File not found: {}", filepath);
                        continue;
                    }

                    let file = match File::open(path) {
                        Ok(file) => file,
                        Err(e) => {
                            println!("[Load] Cannot open file: {}", e);
                            continue;
                        }
                    };

                    let reader = BufReader::new(file);
                    let mut asserted = 0u32;
                    let mut skipped = 0u32;
                    let mut errors = 0u32;

                    for (line_num, line_result) in reader.lines().enumerate() {
                        let line = match line_result {
                            Ok(line) => line,
                            Err(e) => {
                                println!("[Load] Read error at line {}: {}", line_num + 1, e);
                                errors += 1;
                                continue;
                            }
                        };

                        let trimmed = line.trim();
                        if trimmed.is_empty() || trimmed.starts_with('#') {
                            skipped += 1;
                            continue;
                        }

                        print_lints(&mut linter, trimmed);
                        match engine.assert_text(trimmed) {
                            Ok(ids) => {
                                for id in &ids {
                                    println!("[Fact #{}] {}", id, trimmed);
                                }
                                asserted += ids.len() as u32;
                            }
                            Err(e) => {
                                println!("[Load] line {}: {}", line_num + 1, e);
                                errors += 1;
                            }
                        }
                    }

                    println!(
                        "[Load] Done: {} asserted, {} skipped, {} errors",
                        asserted, skipped, errors
                    );
                } else if let Some(find_text) = input.strip_prefix("??") {
                    let text = find_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: ?? <query with a variable>");
                        continue;
                    }

                    print_lints(&mut linter, text);
                    match engine.query_find_text(text) {
                        Ok(binding_sets) => {
                            if binding_sets.is_empty() {
                                println!("[Find] No witnesses found.");
                            } else {
                                for bindings in &binding_sets {
                                    let parts: Vec<String> = bindings
                                        .iter()
                                        .map(|binding| {
                                            format!(
                                                "{} = {} [{}]",
                                                binding.variable,
                                                display_term(&binding.term),
                                                binding.origin.label(),
                                            )
                                        })
                                        .collect();
                                    println!("[Find] {}", parts.join(", "));
                                }
                            }
                        }
                        Err(e) => println!("{}", e),
                    }
                } else if let Some(query_text) = input.strip_prefix('?') {
                    let text = query_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: ? <query>");
                        continue;
                    }

                    print_lints(&mut linter, text);
                    match engine.query_text_with_proof(text) {
                        Ok((result, trace, _json)) => {
                            println!("[Query] {}", display_query_result(&result));
                            print!("{}", trace);
                        }
                        Err(e) => println!("{}", e),
                    }
                } else {
                    print_lints(&mut linter, input);
                    match engine.assert_text(input) {
                        Ok(ids) => {
                            for id in &ids {
                                println!("[Fact #{}] Asserted.", id);
                            }
                        }
                        Err(e) => println!("{}", e),
                    }
                }
            }
            Ok(Signal::CtrlD) | Ok(Signal::CtrlC) => break,
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
}
