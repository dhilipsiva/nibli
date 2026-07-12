//! Nibli native REPL binary.
//!
//! This is a thin CLI wrapper over `nibli-engine`. The engine crate owns the
//! native parse -> compile -> reason pipeline and related adapters.

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;

use nibli_engine::{EngineLogicalTerm, Language, NibliEngine, display_query_result, display_term};
use reedline::{DefaultPrompt, Reedline, Signal};

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

fn run_test_book() {
    eprintln!("[test-book] Starting book example test...");
    let engine = NibliEngine::new();
    // The book examples are Lojban (Klaro is the default since THE FLIP).
    engine.set_language(Language::Lojban);

    let commands = vec![
        (".i lo prenu cu ponse lo datni", "assert1"),
        (
            ".i ro lo prenu poi ponse lo datni cu bilga lo nu curmi",
            "assert2",
        ),
        ("? lo prenu cu bilga lo nu curmi", "query-with-proof"),
    ];

    for (input, label) in &commands {
        eprintln!("\n[test-book] === {label}: {input} ===");
        let trimmed = input.trim();

        if let Some(text) = trimmed.strip_prefix('?') {
            let text = text.trim();
            eprintln!("[test-book] Calling query_text_with_proof...");
            match engine.query_text_with_proof(text) {
                Ok((result, trace, _json)) => {
                    println!("Result: {}", display_query_result(&result));
                    print!("{}", trace);
                }
                Err(e) => println!("Error: {}", e),
            }
        } else {
            match engine.assert_text(trimmed) {
                Ok(ids) => {
                    for id in &ids {
                        println!("[Fact #{id}] Asserted.");
                    }
                }
                Err(e) => println!("Error: {}", e),
            }
        }
    }

    eprintln!("[test-book] Done.");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.iter().any(|a| a == "--test-book") {
        run_test_book();
        return;
    }

    println!("==================================================");
    println!(" Nibli Native REPL - Direct Rust (no WASM)        ");
    println!("==================================================");

    let mut engine = NibliEngine::new();
    // Interactive debug REPL: opt into the engine's [Rule]/[Skolem]/[Constraint]
    // diagnostics (off by default — nibli-engine is a silent library).
    engine.set_verbose(true);
    // NIBLI_LANG selects the startup front-end; a bad value only warns and
    // keeps the default (ambient config must not break the session).
    if let Ok(value) = std::env::var("NIBLI_LANG") {
        match value.parse::<Language>() {
            Ok(l) => engine.set_language(l),
            Err(e) => eprintln!("[Lang] NIBLI_LANG ignored: {e}"),
        }
    }

    let mut line_editor = Reedline::create();
    let prompt = DefaultPrompt::default();

    println!(
        "Commands: :quit :reset :load <file> :facts :retract <id> :debug <text> :compute <name> :assert <rel> <args..> :lang :klaro :lojban :help"
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
                        engine.reset();
                        println!("[Reset] Knowledge base cleared.");
                        continue;
                    }
                    ":klaro" => {
                        engine.set_language(Language::Klaro);
                        println!("[Lang] klaro");
                        continue;
                    }
                    ":lojban" => {
                        engine.set_language(Language::Lojban);
                        println!("[Lang] lojban");
                        continue;
                    }
                    ":lang" => {
                        println!("[Lang] {}", engine.language());
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
                        let violations = engine.check_contradictions();
                        if violations.is_empty() {
                            println!("[Contradictions] No contradictions found.");
                        } else {
                            println!("[Contradictions] {} issue(s) found:", violations.len());
                            for (i, v) in violations.iter().enumerate() {
                                println!("  {}: {}", i + 1, v);
                            }
                        }
                        continue;
                    }
                    ":help" | ":h" => {
                        println!("  <text>              Assert text as fact (current language)");
                        println!("  ? <text>            Query with proof trace");
                        println!("  ?? <text>           Find witnesses (answer variables)");
                        println!("  :lang               Show the current input language");
                        println!("  :klaro / :lojban    Switch the input language");
                        println!("  :debug <text>       Show compiled logic tree");
                        println!(
                            "  :load <filepath>    Load a .lojban/.klaro file (assert each line; language by extension)"
                        );
                        println!("  :compute <name>     Register predicate for compute dispatch");
                        println!("  :assert <rel> <args..> Assert a ground fact directly");
                        println!("  :retract <id>       Retract a fact by ID (rebuilds KB)");
                        println!("  :facts              List all active facts in the KB");
                        println!("  :contradictions     Scan KB for contradictions");
                        println!("  :trace <pred>       Enable tracing for a predicate");
                        println!("  :untrace <pred>     Disable tracing for a predicate");
                        println!("  :traces             List traced predicates");
                        println!("  :reset              Clear all facts (fresh KB)");
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
                    engine.register_compute_predicate(name.to_string());
                    println!("[Compute] Registered '{}' for compute dispatch", name);
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

                    // Language by extension, FILE-SCOPED: .lojban/.klaro set the
                    // front-end for this load and the previous language is
                    // restored after; any other extension uses the current mode.
                    let file_lang = match path.extension().and_then(|e| e.to_str()) {
                        Some("lojban") => Some(Language::Lojban),
                        Some("klaro") => Some(Language::Klaro),
                        _ => None,
                    };
                    let prev_lang = engine.language();
                    if let Some(l) = file_lang
                        && l != prev_lang
                    {
                        engine.set_language(l);
                        println!("[Load] {} mode for this file", l);
                    }

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
                    // Restore the pre-load language (the extension pick is
                    // file-scoped, never a sticky mode switch).
                    if engine.language() != prev_lang {
                        engine.set_language(prev_lang);
                    }
                } else if let Some(find_text) = input.strip_prefix("??") {
                    let text = find_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: ?? <query with a variable>");
                        continue;
                    }

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
                                                "{} = {}",
                                                binding.variable,
                                                display_term(&binding.term)
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

                    match engine.query_text_with_proof(text) {
                        Ok((result, trace, _json)) => {
                            println!("[Query] {}", display_query_result(&result));
                            print!("{}", trace);
                        }
                        Err(e) => println!("{}", e),
                    }
                } else {
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
