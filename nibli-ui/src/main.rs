//! Nibli Transparency Triad web UI (Dioxus).
//!
//! A standalone, in-browser interface with two tabs: Lojban (formal encoding
//! with per-line validation) and Back-translation (structure-exposing English
//! gloss). A bottom query bar runs proof-queries. The reasoning engine
//! (gerna → smuni → logji) is compiled into the WASM bundle and runs entirely
//! client-side — no server, no network calls. Mirrors the `nibli-wasm` pipeline.

use std::collections::HashSet;

use dioxus::prelude::*;
use logji::KnowledgeBase;
use nibli_protocol::{KbStatus, LineResult, ProofTrace};
use nibli_types::error::NibliError;
use nibli_types::logic::LogicBuffer;

fn main() {
    dioxus::launch(App);
}

/// IR-driven back-translation of the (multi-line) Lojban tab, computed entirely
/// client-side: each non-comment line is parsed + compiled to FOL and rendered as
/// structure-exposing English by `nibli-render`. A line that does not compile
/// falls back to the lexical word-by-word gloss so the panel always shows
/// something. This is the "What Nibli Understood" reading.
fn back_translate_ir(lojban: &str) -> String {
    lojban
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                None
            } else {
                Some(render_lojban_line(trimmed))
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn render_lojban_line(line: &str) -> String {
    match gerna::parse_text_native(line.to_string()) {
        Ok(parsed) if parsed.errors.is_empty() => smuni::compile_from_gerna_ast(parsed.buffer)
            .map(|buf| nibli_render::render_logic_buffer(&buf, nibli_render::Register::Spec))
            .unwrap_or_else(|_| smuni_dictionary::back_translate(line)),
        _ => smuni_dictionary::back_translate(line),
    }
}

const MAX_OUTPUT_ENTRIES: usize = 200;

const DEFAULT_LOJBAN: &str = "ro lo gerku cu danlu\nro lo danlu cu citka\nla .adam. cu gerku";
const DEFAULT_QUERY: &str = "la .adam. cu citka";

// ── Types ──

#[derive(Clone, Copy, PartialEq)]
enum ActiveTab {
    Lojban,
    BackTranslation,
}

#[derive(Clone)]
struct OutputEntry {
    input: String,
    result: String,
    is_error: bool,
    proof_trace: Option<String>,
    proof_trace_data: Option<ProofTrace>,
    kb_status: Option<KbStatus>,
}

// ── Local reasoning (in-browser) ──
// The full gerna → smuni → logji pipeline runs in the WASM bundle (mirrors
// `nibli-wasm`). Every query builds a fresh KnowledgeBase, re-asserts the Lojban
// tab as the KB, then queries — matching the "queries reset the engine each
// time" semantics. Built-in arithmetic (pilji/sumji/dilcu/zmadu/mleca/dunli)
// resolves locally; external compute predicates (tenfa/dugri) have no TCP
// backend in the browser and surface as errors, same as the live demo.

/// Parse one Lojban line, compile to FOL, and mark compute nodes. Fail-closed on
/// any parse/compile error (the `NibliError` Display carries the `[Syntax Error]`
/// / `[Semantic Error]` prefixes the output log classifies on).
fn compile_text(text: &str, preds: &HashSet<String>) -> Result<LogicBuffer, NibliError> {
    let ast = gerna::parse_checked(text)?;
    let mut buf = smuni::compile_from_gerna_ast(ast)?;
    logji::transform_compute_nodes(&mut buf, preds);
    Ok(buf)
}

/// Build a fresh KB from the Lojban tab, assert it (recording a per-line status),
/// then run the query and return the result + proof trace as an `OutputEntry`.
fn run_query(kb_text: &str, query_text: &str) -> OutputEntry {
    let preds = logji::default_compute_predicates();
    let kb = KnowledgeBase::new();

    let mut asserted = 0u32;
    let mut errors = 0u32;
    let mut skipped = 0u32;
    let mut line_results: Vec<LineResult> = Vec::new();
    for (i, raw) in kb_text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            skipped += 1;
            continue;
        }
        let line_number = (i + 1) as u32;
        match compile_text(line, &preds).and_then(|buf| kb.assert_fact(buf, line.to_string())) {
            Ok(id) => {
                asserted += 1;
                line_results.push(LineResult {
                    line_number,
                    text: line.to_string(),
                    success: true,
                    fact_id: Some(id),
                    error: None,
                });
            }
            Err(e) => {
                errors += 1;
                line_results.push(LineResult {
                    line_number,
                    text: line.to_string(),
                    success: false,
                    fact_id: None,
                    error: Some(e.to_string()),
                });
            }
        }
    }
    let kb_status = Some(KbStatus {
        asserted,
        errors,
        skipped,
        line_results,
    });

    match compile_text(query_text, &preds).and_then(|buf| kb.query_entailment_with_proof(buf)) {
        Ok((result, trace)) => {
            let status = result.status_label();
            let result = match result.detail_label() {
                Some(detail) => format!("{} ({})", status, detail),
                None => status.to_string(),
            };
            OutputEntry {
                input: query_text.to_string(),
                result,
                is_error: false,
                proof_trace: None,
                proof_trace_data: Some(trace),
                kb_status,
            }
        }
        Err(e) => OutputEntry {
            input: query_text.to_string(),
            result: e.to_string(),
            is_error: true,
            proof_trace: None,
            proof_trace_data: None,
            kb_status,
        },
    }
}

/// Maps a known error-message prefix to its semantic CSS class + the cleaned body.
/// The leading icon glyph is drawn by the stylesheet from this class, so the body
/// no longer carries the prefix.
fn classify_error(message: &str) -> (&'static str, String) {
    const TABLE: [(&str, &str); 5] = [
        ("[Syntax Error]", "error-syntax"),
        ("[Semantic Error]", "error-semantic"),
        ("[Reasoning Error]", "error-reasoning"),
        ("[Backend Error]", "error-backend"),
        ("[Limit]", "error-limit"),
    ];
    for (prefix, class) in TABLE {
        if let Some(rest) = message.strip_prefix(prefix) {
            return (class, rest.trim().to_string());
        }
    }
    ("error-generic", message.to_string())
}

/// Verdict modifier for the result chip, derived from the leading status word.
/// The chip glyph (⊤/⊥/?/◴) is drawn by the stylesheet from this class.
fn result_modifier(result: &str) -> &'static str {
    if result.starts_with("TRUE") {
        "is-true"
    } else if result.starts_with("FALSE") {
        "is-false"
    } else if result.starts_with("UNKNOWN") {
        "is-unknown"
    } else if result.starts_with("RESOURCE_EXCEEDED") {
        "is-limit"
    } else {
        ""
    }
}

// ── Components ──

#[component]
fn App() -> Element {
    let mut output_log: Signal<Vec<OutputEntry>> = use_signal(Vec::new);
    let proof_text: Signal<Option<String>> = use_signal(|| None);
    let proof_data: Signal<Option<ProofTrace>> = use_signal(|| None);
    let lojban_text: Signal<String> = use_signal(|| DEFAULT_LOJBAN.to_string());
    let kb_status: Signal<Option<KbStatus>> = use_signal(|| None);

    let on_global_keydown = move |e: KeyboardEvent| {
        if e.modifiers().ctrl() {
            match e.key() {
                Key::Character(ref c) if c == "l" => {
                    e.prevent_default();
                    output_log.set(vec![]);
                }
                Key::Character(ref c) if c == "k" => {
                    e.prevent_default();
                    spawn(async move {
                        let _ =
                            document::eval("document.getElementById('query-input').focus()").await;
                    });
                }
                Key::Character(ref c) if c == "o" => {
                    e.prevent_default();
                    spawn(async move {
                        let _ =
                            document::eval("document.getElementById('lojban-file-input').click()")
                                .await;
                    });
                }
                _ => {}
            }
        }
    };

    let active_tab: Signal<ActiveTab> = use_signal(|| ActiveTab::Lojban);
    // "" = dark (the instrument default); "light" = the QUINE paper theme. The
    // attribute rides on `.app-shell`, so the [data-theme="light"] overrides cascade.
    let mut theme = use_signal(|| "");

    rsx! {
        document::Link { rel: "stylesheet", href: asset!("/assets/tokens.css") }
        document::Link { rel: "stylesheet", href: asset!("/assets/style.css") }
        // Outer shell owns the viewport: the QUINE masthead sits above the
        // instrument. data-theme rides here (not on `.app`) so the header
        // themes alongside the panels.
        div { class: "app-shell", "data-theme": "{theme}",
            header { class: "app-header",
                div { class: "app-header__brand",
                    span { class: "app-header__name", "nibli" }
                    span { class: "app-header__tagline", "the transparency triad" }
                }
                span { class: "app-header__sp" }
                span { class: "app-header__credit",
                    "Built with "
                    span { class: "app-header__heart", "\u{2665}" }
                    " by "
                    a {
                        class: "app-header__credit-link",
                        href: "https://dhilipsiva.dev/",
                        target: "_blank",
                        rel: "noopener noreferrer",
                        "@dhilipsiva"
                    }
                }
                button {
                    class: "app-header__theme",
                    title: "Toggle theme",
                    onclick: move |_| {
                        let next = if *theme.read() == "light" { "" } else { "light" };
                        theme.set(next);
                    },
                    if *theme.read() == "light" { "\u{263E} dark" } else { "\u{2600} light" }
                }
            }
            div { class: "app", tabindex: "0", onkeydown: on_global_keydown,
                div { class: "main-row",
                    div { class: "col-tabs",
                        SourceTabs { lojban_text, kb_status, active_tab }
                    }
                    div { class: "col-proof",
                        ProofPanel { proof_text, proof_data }
                    }
                }
                div { class: "query-row",
                    div { class: "query-section",
                        div { class: "query-header",
                            span { class: "query-header__label", "query" }
                            span { class: "query-header__sp" }
                            // No server: the engine runs in the browser. A static
                            // "ready" badge stands in for the old connection status.
                            span { class: "status-badge connected", "in-browser" }
                        }
                        QueryBar { output_log, proof_text, proof_data, lojban_text, kb_status }
                    }
                    OutputLog { output_log }
                }
            }
        }
    }
}

#[component]
fn KbStatusBar(kb_status: Signal<Option<KbStatus>>) -> Element {
    let mut expanded = use_signal(|| false);
    let status = kb_status.read();
    let Some(ref s) = *status else {
        return rsx! {};
    };

    let summary_text = format!(
        "{} asserted, {} error{}{}",
        s.asserted,
        s.errors,
        if s.errors != 1 { "s" } else { "" },
        if s.skipped > 0 {
            format!(", {} skipped", s.skipped)
        } else {
            String::new()
        }
    );

    let has_errors = s.errors > 0;
    let summary_state = if has_errors {
        "kb-status-warn"
    } else {
        "kb-status-ok"
    };

    rsx! {
        div { class: "kb-status-bar",
            if has_errors {
                button {
                    class: "kb-status-summary {summary_state}",
                    "aria-expanded": "{expanded}",
                    onclick: move |_| {
                        let v = *expanded.read();
                        expanded.set(!v);
                    },
                    span { class: "kb-status-summary__caret", "\u{25B8}" }
                    "{summary_text}"
                    span { class: "kb-status-summary__sp" }
                }
                div { class: "kb-status-details",
                    div { class: "kb-line-results",
                        for lr in s.line_results.iter() {
                            div {
                                key: "{lr.line_number}",
                                class: if lr.success { "kb-line-result kb-line-ok" } else { "kb-line-result kb-line-error" },
                                span { class: "kb-line-num", "{lr.line_number}" }
                                span { class: "kb-line-icon" }
                                span { class: "kb-line-text", "{lr.text}" }
                                if let Some(ref err) = lr.error {
                                    span { class: "kb-line-err", "{err}" }
                                }
                            }
                        }
                    }
                }
            } else {
                div { class: "kb-status-summary {summary_state}", "{summary_text}" }
            }
        }
    }
}

#[component]
fn QueryBar(
    output_log: Signal<Vec<OutputEntry>>,
    proof_text: Signal<Option<String>>,
    proof_data: Signal<Option<ProofTrace>>,
    lojban_text: Signal<String>,
    kb_status: Signal<Option<KbStatus>>,
) -> Element {
    let mut query_text = use_signal(|| DEFAULT_QUERY.to_string());

    let mut do_submit = move || {
        let text = query_text.read().clone();
        let trimmed = text.trim();
        if trimmed.is_empty() {
            return;
        }

        // The engine runs in-browser and synchronously — no await, no server.
        let kb = lojban_text.read().clone();
        let entry = run_query(&kb, trimmed);
        query_text.set(String::new());

        // Always reflect the latest query in the proof panel (clear on error).
        proof_text.set(entry.proof_trace.clone());
        proof_data.set(entry.proof_trace_data.clone());
        kb_status.set(entry.kb_status.clone());

        // Push entry and cap at MAX_OUTPUT_ENTRIES.
        {
            let mut log = output_log.write();
            log.push(entry);
            if log.len() > MAX_OUTPUT_ENTRIES {
                let drain_count = log.len() - MAX_OUTPUT_ENTRIES;
                log.drain(0..drain_count);
            }
        }

        // Auto-scroll output log to bottom.
        spawn(async move {
            let _ = document::eval(
                "const el = document.getElementById('output-log'); if (el) el.scrollTop = el.scrollHeight;"
            ).await;
        });
    };

    let submit_click = move |_: Event<MouseData>| {
        do_submit();
    };

    let on_keydown = move |e: KeyboardEvent| {
        if e.key() == Key::Enter {
            do_submit();
        }
    };

    rsx! {
        div { class: "query-bar",
            span { class: "query-bar__affix", "xu" }
            input {
                id: "query-input",
                class: "query-input",
                r#type: "text",
                placeholder: "Enter Lojban query \u{2014} Ctrl+K focus",
                value: "{query_text}",
                oninput: move |e| query_text.set(e.value()),
                onkeydown: on_keydown,
            }
            button {
                class: "query-btn",
                onclick: submit_click,
                "Run"
            }
        }
    }
}

#[component]
fn OutputLog(output_log: Signal<Vec<OutputEntry>>) -> Element {
    /// Flattened display row — all formatting decided up front so the rsx only
    /// reads plain fields (rsx text interpolation can't call functions).
    struct Row {
        key: usize,
        class: String,
        input: String,
        is_error: bool,
        text: String,
        result_mod: &'static str,
    }

    let entries = output_log.read();
    let is_empty = entries.is_empty();
    let rows: Vec<Row> = entries
        .iter()
        .enumerate()
        .map(|(i, e)| {
            if e.is_error {
                let (err_class, body) = classify_error(&e.result);
                Row {
                    key: i,
                    class: format!("output-entry output-error {err_class}"),
                    input: e.input.clone(),
                    is_error: true,
                    text: body,
                    result_mod: "",
                }
            } else {
                Row {
                    key: i,
                    class: "output-entry".to_string(),
                    input: e.input.clone(),
                    is_error: false,
                    text: e.result.clone(),
                    result_mod: result_modifier(&e.result),
                }
            }
        })
        .collect();

    rsx! {
        div { class: "output-log-container",
            if !is_empty {
                div { class: "output-log-header",
                    span { class: "output-log-header__label", "log" }
                    span { class: "output-log-header__sp" }
                    button {
                        class: "output-clear-btn",
                        onclick: move |_| output_log.set(vec![]),
                        "Clear"
                        kbd { class: "kbd-hint", "Ctrl+L" }
                    }
                }
            }
            div { id: "output-log", class: "output-log",
                for row in rows.iter() {
                    div {
                        key: "{row.key}",
                        class: "{row.class}",
                        span { class: "output-input", "{row.input}" }
                        if row.is_error {
                            span { class: "output-error-display",
                                span { class: "error-icon" }
                                span { class: "error-message", "{row.text}" }
                            }
                        } else {
                            span { class: "output-result {row.result_mod}", "{row.text}" }
                        }
                    }
                }
            }
        }
    }
}

#[component]
fn SourceTabs(
    lojban_text: Signal<String>,
    kb_status: Signal<Option<KbStatus>>,
    active_tab: Signal<ActiveTab>,
) -> Element {
    let back_translation = use_memo(move || {
        let text = lojban_text.read();
        if text.is_empty() {
            String::new()
        } else {
            back_translate_ir(&text)
        }
    });

    rsx! {
        div { class: "tabs-container",
            div { class: "tab-bar",
                button {
                    class: if *active_tab.read() == ActiveTab::Lojban { "tab active" } else { "tab" },
                    onclick: move |_| active_tab.set(ActiveTab::Lojban),
                    "Lojban"
                }
                button {
                    class: if *active_tab.read() == ActiveTab::BackTranslation { "tab active" } else { "tab" },
                    onclick: move |_| active_tab.set(ActiveTab::BackTranslation),
                    "Back-translation"
                }
            }
            div { class: "tab-content",
                match *active_tab.read() {
                    ActiveTab::Lojban => rsx! {
                        div { class: "lojban-toolbar",
                            button {
                                class: "toolbar-btn",
                                onclick: move |_| {
                                    spawn(async move {
                                        let res = document::eval(r#"
                                            document.getElementById('lojban-file-input').click();
                                            return '';
                                        "#);
                                        let _ = res.await;
                                    });
                                },
                                "Load .lojban"
                                kbd { class: "kbd-hint", "Ctrl+O" }
                            }
                            button {
                                class: "toolbar-btn",
                                onclick: move |_| {
                                    lojban_text.set(String::new());
                                    kb_status.set(None);
                                },
                                "Clear"
                            }
                            input {
                                r#type: "file",
                                accept: ".lojban,.txt",
                                style: "display: none",
                                id: "lojban-file-input",
                                onchange: move |_| {
                                    spawn(async move {
                                        let res = document::eval(r#"
                                            const input = document.getElementById('lojban-file-input');
                                            const file = input.files[0];
                                            if (!file) return '';
                                            const text = await file.text();
                                            input.value = '';
                                            return text;
                                        "#);
                                        if let Ok(val) = res.await {
                                            if let Some(text) = val.as_str() {
                                                if !text.is_empty() {
                                                    lojban_text.set(text.to_string());
                                                    kb_status.set(None);
                                                }
                                            }
                                        }
                                    });
                                },
                            }
                        }
                        textarea {
                            class: "lojban-input",
                            placeholder: "Enter Lojban facts and rules (one per line)...",
                            value: "{lojban_text}",
                            oninput: move |e| lojban_text.set(e.value()),
                        }
                        KbStatusBar { kb_status }
                    },
                    ActiveTab::BackTranslation => {
                        let bt = back_translation.read();
                        let lines: Vec<(usize, String)> = bt
                            .lines()
                            .enumerate()
                            .map(|(i, l)| (i + 1, l.to_string()))
                            .collect();
                        let empty = lines.is_empty();
                        rsx! {
                            span { class: "nb-eyebrow", "what nibli understood" }
                            div { class: "back-translation",
                                if empty {
                                    span { class: "back-translation__placeholder",
                                        "Type Lojban in the Lojban tab to see the structure-exposing gloss."
                                    }
                                } else {
                                    for (n, line) in lines.iter() {
                                        div { key: "{n}", class: "back-translation__line",
                                            span { class: "back-translation__num", "{n}" }
                                            span { class: "back-translation__gloss", "{line}" }
                                        }
                                    }
                                }
                            }
                        }
                    },
                }
            }
        }
    }
}

#[component]
fn ProofPanel(
    proof_text: Signal<Option<String>>,
    proof_data: Signal<Option<ProofTrace>>,
) -> Element {
    let text = proof_text.read();
    let data = proof_data.read();

    rsx! {
        div { class: "proof-panel",
            if let Some(trace_data) = data.as_ref() {
                div { class: "proof-tree-container",
                    ProofTreeView { trace: trace_data.clone() }
                }
            } else if let Some(trace) = text.as_ref() {
                pre { class: "proof-trace", "{trace}" }
            } else {
                div { class: "proof-placeholder",
                    span { class: "proof-placeholder__glyph", "\u{2234}" }
                    div { class: "proof-hint",
                        "No proof yet. Run a query to see the derivation."
                    }
                    code { class: "proof-hint-code",
                        "la .adam. cu "
                        span { class: "q", "citka" }
                    }
                }
            }
        }
    }
}

#[component]
fn ProofTreeView(trace: ProofTrace) -> Element {
    if trace.root as usize >= trace.steps.len() {
        return rsx! { div { class: "proof-error", "Invalid proof trace: root index out of bounds" } };
    }
    // A render-only plain-English "why" summary above the detailed tree, from the
    // same shared renderer (the trace data is unchanged). `None` for an
    // unsummarizable trace — then nothing extra is shown.
    let summary = nibli_render::summarize_proof(&trace, nibli_render::Register::Spec);
    // Collapse the verbose trace into the macro-logical DAG once via the shared
    // renderer; the component then walks the structured RenderedNode tree (no
    // per-variant logic in the UI). The folded role/event scaffolding rides along
    // as `proof-role-detail` clusters the user can expand.
    let root = nibli_render::collapse_proof(&trace, nibli_render::Register::Spec);
    rsx! {
        div { class: "proof-tree",
            if let Some(why) = summary {
                div { class: "proof-why",
                    span { class: "proof-why-label", "Why" }
                    span { class: "proof-why-text", "{why}" }
                }
            }
            RenderedNodeView { node: root, depth: 0 }
        }
    }
}

#[component]
fn RenderedNodeView(node: nibli_render::RenderedNode, depth: u32) -> Element {
    // Macro nodes open by default; the folded role-level scaffolding cluster
    // starts collapsed — it is the expandable "under the hood" detail of the
    // collapsed macro view. The rule-type glyph (⊢ → ⊨ ↺ ∧ ∃ ¬ ✗ ⋯) and the
    // result glyph (⊤/⊥) are drawn by the stylesheet from the rule class, so the
    // icon span is rendered empty.
    let auto_open = depth < 3 && node.css_class != "proof-role-detail";
    // Hook must run unconditionally (only used by the branch arm below).
    let mut expanded = use_signal(|| auto_open);
    let css_class = node.css_class;
    let label = node.label.clone();
    let result_class = if node.holds {
        "proof-result-true"
    } else {
        "proof-result-false"
    };
    let result_label = if node.holds { "TRUE" } else { "FALSE" };

    // A memoized back-reference (ProofRef) — render inline, no disclosure.
    if node.inline {
        return rsx! {
            div { class: "proof-node proof-ref-node {css_class}",
                div { class: "proof-row",
                    span { class: "proof-icon" }
                    span { class: "proof-label", "{label}" }
                }
            }
        };
    }

    if node.children.is_empty() {
        // Leaf node — a row with no disclosure / no children.
        rsx! {
            div { class: "proof-node proof-leaf {css_class}",
                div { class: "proof-row",
                    span { class: "proof-icon" }
                    span { class: "proof-label", "{label}" }
                    span { class: "proof-result {result_class}", "{result_label}" }
                }
            }
        }
    } else {
        // Branch node — collapse is pure CSS off `aria-expanded` on the row.
        rsx! {
            div { class: "proof-node {css_class}",
                div {
                    class: "proof-row",
                    "aria-expanded": "{expanded}",
                    onclick: move |_| {
                        let v = *expanded.read();
                        expanded.set(!v);
                    },
                    button { class: "proof-disclosure" }
                    span { class: "proof-icon" }
                    span { class: "proof-label", "{label}" }
                    span { class: "proof-result {result_class}", "{result_label}" }
                }
                div { class: "proof-children",
                    for (i, child) in node.children.iter().enumerate() {
                        RenderedNodeView {
                            key: "{i}",
                            node: child.clone(),
                            depth: depth + 1,
                        }
                    }
                }
            }
        }
    }
}
