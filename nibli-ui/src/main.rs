//! Nibli Transparency Triad web UI (Dioxus).
//!
//! A standalone, in-browser interface with three tabs: Source (plain English,
//! optionally translated to Lojban by a bring-your-own-key LLM), Lojban (formal
//! encoding with per-line validation), and Back-translation (structure-exposing
//! English gloss). A bottom query bar runs proof-queries. The reasoning engine
//! (gerna → smuni → logji) is compiled into the WASM bundle and runs entirely
//! client-side (mirrors `nibli-wasm`). The ONLY network call is the optional
//! Source→Lojban translate, sent directly from the browser to the user's chosen
//! LLM provider — the client lives in `nibli_fanva::llm` (the single source of
//! truth); nibli-ui only wraps it in a `Settings` bundle. nibli itself has no server.

use std::collections::HashSet;

use dioxus::prelude::*;
use logji::KnowledgeBase;
use nibli_protocol::{KbStatus, LineResult, ProofTrace};
use nibli_types::error::NibliError;
use nibli_types::logic::LogicBuffer;

mod examples;
use examples::EXAMPLES;
use nibli_fanva::llm::{LlmConfig, Provider};

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

/// Collapse the active KB into one multi-sentence Lojban text for jbotci `tersmu`:
/// drop empty + `#`-comment lines (same filter as [`back_translate_ir`]) and join
/// with the neutral sentence separator `.i`, so tersmu analyses the whole KB in a
/// single call and returns one coherent semantic graph.
fn kb_to_tersmu_text(lojban: &str) -> String {
    lojban
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .collect::<Vec<_>>()
        .join(" .i ")
}

const MAX_OUTPUT_ENTRIES: usize = 200;

const DEFAULT_SOURCE: &str = "All dogs are animals.\nAll animals eat.\nAdam is a dog.";
const DEFAULT_LOJBAN: &str = "ro lo gerku cu danlu\nro lo danlu cu citka\nla .adam. cu gerku";
const DEFAULT_QUERY: &str = "la .adam. cu citka";

// ── Agentic translate (nibli-fanva) ──
// The Source→Lojban button runs the self-correcting loop: translate → validate
// with gerna+smuni → feed the compiler error back → retry, bounded below. All
// gates are local/in-browser; the only network call is the LLM itself.

/// Cap on jbotci tool calls within a single translate attempt.
const MAX_TOOL_STEPS: u32 = 4;

/// One row of the self-correction trace rendered under the Source tab.
#[derive(Clone, Copy)]
enum GateState {
    Pass,
    Fail,
    Skip,
}

/// One jbotci tool call, summarized for a trace sub-row.
#[derive(Clone)]
struct ToolRow {
    name: String,
    detail: String,
    is_error: bool,
}

#[derive(Clone)]
struct TraceRow {
    n: u32,
    ok: bool,
    detail: String,
    /// Per-gate chips: (label like "gerna ✓", css class).
    gates: Vec<(String, &'static str)>,
    /// jbotci tool calls made in this attempt (empty when jbotci is off).
    tools: Vec<ToolRow>,
}

/// The default jbotci proxy: the app-owned "blind" CORS reverse-proxy Worker
/// (`fanva-proxy/`). Prefilled so opting in is one click, but jbotci ships OFF
/// (`jbotci_enabled = false`) — the URL stays inert until the user enables it, so the
/// default translate run is fully local and makes NO call to the proxy. The proxy
/// only strips the browser Origin and forwards to jbotci verbatim; it stores nothing
/// (source is linked from the settings modal).
const DEFAULT_JBOTCI_PROXY_URL: &str = "https://fanva-proxy.dhilipsiva.workers.dev/mcp";

/// nibli-ui's settings bundle: the LLM provider config (`nibli_fanva::llm::LlmConfig`,
/// the single source of truth) plus the agent/jbotci knobs that aren't LLM-provider
/// settings. Held in one in-memory signal; never persisted.
#[derive(Clone, PartialEq)]
struct Settings {
    llm: LlmConfig,
    proxy_url: String,
    /// jbotci tool-use opt-in. OFF by default: the prefilled `proxy_url` is inert
    /// until the user flips this, keeping the default run local-only (no proxy call).
    jbotci_enabled: bool,
    max_attempts: u32,
}

impl Settings {
    fn new(provider: Provider) -> Self {
        Settings {
            llm: LlmConfig::new(provider),
            proxy_url: DEFAULT_JBOTCI_PROXY_URL.to_string(),
            jbotci_enabled: false,
            max_attempts: 5,
        }
    }

    /// The proxy URL actually handed to the MCP client: the configured URL only when
    /// jbotci is explicitly enabled, else empty. Empty ⇒ the translate loop and the
    /// tersmu view degrade to the local gates and make NO network call — this is what
    /// makes "disabled by default" a real privacy guarantee, not a hidden-but-live URL.
    fn active_proxy_url(&self) -> String {
        if self.jbotci_enabled {
            self.proxy_url.trim().to_string()
        } else {
            String::new()
        }
    }
}

/// Single-shot English→Lojban via nibli-fanva's transport — used by the query
/// translate and the modal key-test (the agentic Source translate uses
/// `translate_agentic`). Returns the cleaned Lojban or a user-facing error.
async fn fanva_translate(cfg: &LlmConfig, english: &str) -> Result<String, String> {
    use nibli_fanva::llm::{Chat, HttpChat, Turn, clean_lojban_output, system_prompt};
    let turns = [Turn::user(format!(
        "Translate to Lojban: {}",
        english.trim()
    ))];
    let raw = HttpChat
        .chat(cfg, system_prompt(), &turns)
        .await
        .map_err(|e| e.to_string())?;
    let cleaned = clean_lojban_output(&raw);
    if cleaned.is_empty() {
        return Err("The provider returned an empty translation.".to_string());
    }
    Ok(cleaned)
}

/// The local gates, in the fail-fast order `validate` runs them.
const GATE_ORDER: [&str; 3] = ["gerna", "smuni", "camxes"];

/// Derive the per-gate chips from an attempt's error. `validate` is fail-fast in
/// `GATE_ORDER`, so `error.gate()` is the failing gate; earlier gates passed,
/// later ones were skipped. (Assumes camxes ran in-browser; if its shim failed to
/// load it silently passes — a rare edge.)
fn gate_chips(error: &Option<nibli_fanva::gates::GateError>) -> Vec<(String, &'static str)> {
    let states: [GateState; 3] = match error {
        None => [GateState::Pass; 3],
        Some(e) => {
            let fail_idx = GATE_ORDER.iter().position(|g| *g == e.gate()).unwrap_or(0);
            std::array::from_fn(|i| {
                if i < fail_idx {
                    GateState::Pass
                } else if i == fail_idx {
                    GateState::Fail
                } else {
                    GateState::Skip
                }
            })
        }
    };
    GATE_ORDER
        .iter()
        .zip(states)
        .map(|(name, st)| {
            let (glyph, class) = match st {
                GateState::Pass => ("\u{2713}", "gate-chip pass"),
                GateState::Fail => ("\u{2717}", "gate-chip fail"),
                GateState::Skip => ("\u{00B7}", "gate-chip skip"),
            };
            (format!("{name} {glyph}"), class)
        })
        .collect()
}

/// A compact `args → result` snippet for a tool-call trace row.
fn tool_summary(t: &nibli_fanva::tools::ToolCallTrace) -> String {
    let args = truncate(&t.args.to_string(), 40);
    let result = truncate(&t.result.replace('\n', " "), 80);
    format!("{args} \u{2192} {result}")
}

fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() > max {
        let cut: String = s.chars().take(max).collect();
        format!("{cut}\u{2026}")
    } else {
        s.to_string()
    }
}

/// Collapse the agent's attempts into UI trace rows (per-gate chips + first error
/// line + any jbotci tool calls made).
fn trace_rows(attempts: &[nibli_fanva::agent::Attempt]) -> Vec<TraceRow> {
    attempts
        .iter()
        .map(|a| TraceRow {
            n: a.n,
            ok: a.error.is_none(),
            detail: match &a.error {
                None => "valid \u{2014} passed the gates".to_string(),
                Some(e) => {
                    let msg = e.message();
                    let first = msg.lines().next().unwrap_or(msg);
                    format!("{}: {first}", e.gate())
                }
            },
            gates: gate_chips(&a.error),
            tools: a
                .tool_calls
                .iter()
                .map(|t| ToolRow {
                    name: t.name.clone(),
                    detail: tool_summary(t),
                    is_error: t.is_error,
                })
                .collect(),
        })
        .collect()
}

// ── Types ──

#[derive(Clone, Copy, PartialEq)]
enum ActiveTab {
    Source,
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
    // The LLM translate config lives ONLY here, in memory — never persisted to
    // storage, cleared on tab close/reload. `None` until the user configures it.
    let settings: Signal<Option<Settings>> = use_signal(|| None);
    let modal_open: Signal<bool> = use_signal(|| false);
    // Preloaded example selection: `None` = Custom (editable + translatable);
    // `Some(i)` indexes `examples::EXAMPLES` (read-only KB + a query dropdown).
    let mut example: Signal<Option<usize>> = use_signal(|| None);

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

    // Source is the triad's natural entry point (English → Lojban → back-trans).
    let active_tab: Signal<ActiveTab> = use_signal(|| ActiveTab::Source);
    // "" = dark (the instrument default); "light" = the QUINE paper theme. The
    // attribute rides on `.app-shell`, so the [data-theme="light"] overrides cascade.
    let mut theme = use_signal(|| "");

    rsx! {
        document::Link { rel: "stylesheet", href: asset!("/assets/tokens.css") }
        document::Link { rel: "stylesheet", href: asset!("/assets/style.css") }
        // Local "official" grammar gate: the vendored ilmentufa camxes parser +
        // preprocessor, then a shim exposing window.camxes_validate. Served as
        // static assets (no network at reason-time); nibli-fanva's official_gate
        // calls the shim. The shim resolves the globals at call time, so load
        // order is not critical.
        document::Script { src: asset!("/assets/js/vendor/camxes/camxes_preproc.js") }
        document::Script { src: asset!("/assets/js/vendor/camxes/camxes.js") }
        document::Script { src: asset!("/assets/js/vendor/camxes/camxes_shim.js") }
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
                select {
                    class: "nb-select app-header__examples",
                    title: "Load a preloaded example from the book, or Custom to write your own",
                    onchange: move |e| match e.value().parse::<usize>() {
                        Ok(i) => example.set(Some(i)),
                        Err(_) => example.set(None),
                    },
                    option { value: "custom", selected: example.read().is_none(), "Custom" }
                    for (i, ex) in EXAMPLES.iter().enumerate() {
                        option { value: "{i}", selected: *example.read() == Some(i), "{ex.name}" }
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
                        SourceTabs { lojban_text, kb_status, active_tab, settings, modal_open, example }
                    }
                    div { class: "col-proof",
                        ProofPanel { proof_text, proof_data, example }
                    }
                }
                div { class: "query-row",
                    div { class: "col-tabs",
                        QueryTabs {
                            output_log,
                            proof_text,
                            proof_data,
                            lojban_text,
                            kb_status,
                            settings,
                            modal_open,
                            example,
                        }
                    }
                    OutputLog { output_log }
                }
            }
            footer { class: "app-footer",
                span { class: "app-footer__text",
                    span { class: "app-footer__brand", "nibli" }
                    " \u{2014} a Symbolic Reasoning Engine & Hallucination Firewall, built in Rust and compiled to WebAssembly. There are no servers: the engine runs entirely in your browser, and nothing leaves the tab."
                }
                a {
                    class: "app-footer__star",
                    href: "https://github.com/dhilipsiva/nibli",
                    target: "_blank",
                    rel: "noopener noreferrer",
                    title: "Star nibli on GitHub",
                    span { class: "app-footer__star-icon", "\u{2605}" }
                    " Star on GitHub"
                }
            }
            if *modal_open.read() {
                LlmConfigModal { settings, modal_open }
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

/// The live reading of the query being typed: empty input, a clean IR
/// back-translation, or an "incomplete / invalid" indicator (transient while
/// typing). A 3-state value (not just an optional string) so the gloss never
/// blanks out mid-keystroke — it flips between the reading and the indicator.
#[derive(Clone, PartialEq)]
enum QueryReading {
    Empty,
    Reads(String),
    Incomplete,
}

/// The bottom-left query card — a tabbed mirror of the top column: Source (ask in
/// English, translate to a Lojban query via the LLM), Lojban (the query + Run),
/// and Back-translation (the "Query if …" reading). Output goes to the OutputLog.
#[component]
fn QueryTabs(
    output_log: Signal<Vec<OutputEntry>>,
    proof_text: Signal<Option<String>>,
    proof_data: Signal<Option<ProofTrace>>,
    lojban_text: Signal<String>,
    kb_status: Signal<Option<KbStatus>>,
    settings: Signal<Option<Settings>>,
    modal_open: Signal<bool>,
    example: Signal<Option<usize>>,
) -> Element {
    let mut query_text = use_signal(|| DEFAULT_QUERY.to_string());
    let mut query_source = use_signal(String::new);
    let mut translating = use_signal(|| false);
    let mut translate_error = use_signal(|| Option::<String>::None);
    // Default to the Lojban tab so the pre-filled query can be Run immediately.
    let mut query_tab = use_signal(|| ActiveTab::Lojban);
    // In example mode the query box is a dropdown; this indexes the active
    // example's `queries`.
    let mut selected_query = use_signal(|| 0usize);

    // Live back-translation of the ACTIVE query — the typed Custom query, or the
    // selected example query. Shown only for a cleanly-parsed query; a transient
    // parse error shows a stable "incomplete" indicator, never a blank.
    let query_reading = use_memo(move || {
        let owned = match *example.read() {
            Some(i) => EXAMPLES[i]
                .queries
                .get(*selected_query.read())
                .map(|q| q.lojban.to_string())
                .unwrap_or_default(),
            None => query_text.read().clone(),
        };
        let q = owned.trim();
        if q.is_empty() {
            return QueryReading::Empty;
        }
        match gerna::parse_text_native(q.to_string()) {
            Ok(parsed) if parsed.errors.is_empty() => {
                match smuni::compile_from_gerna_ast(parsed.buffer) {
                    Ok(buf) => QueryReading::Reads(nibli_render::render_logic_buffer(
                        &buf,
                        nibli_render::Register::Spec,
                    )),
                    Err(_) => QueryReading::Incomplete,
                }
            }
            _ => QueryReading::Incomplete,
        }
    });

    // Reason over a (kb, query) pair in-browser and push the result to the proof
    // panel + output log. Arg-driven so the auto-run effect can call it WITHOUT
    // reading `selected_query` (which would make the effect re-fire — and reset —
    // every time the dropdown changes).
    let mut run_into_log = move |kb: &str, query: &str| {
        let trimmed = query.trim();
        if trimmed.is_empty() {
            return;
        }
        // The engine runs in-browser and synchronously — no await, no server.
        let entry = run_query(kb, trimmed);
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

    // Resolve the active (KB, query) by mode, then run it. The editable Custom
    // query clears after running; an example selection persists.
    let mut do_submit = move || {
        let ex = *example.read();
        let (kb, query) = match ex {
            Some(i) => (
                EXAMPLES[i].lojban.to_string(),
                EXAMPLES[i]
                    .queries
                    .get(*selected_query.read())
                    .map(|q| q.lojban.to_string())
                    .unwrap_or_default(),
            ),
            None => (lojban_text.read().clone(), query_text.read().clone()),
        };
        run_into_log(&kb, &query);
        if ex.is_none() {
            query_text.set(String::new());
        }
    };

    // Loading an example auto-runs its first query so a verdict shows at once.
    // Reads only `example` (resolving query 0 directly), so changing the dropdown
    // does not re-fire this.
    use_effect(move || {
        if let Some(i) = *example.read() {
            selected_query.set(0);
            if let Some(q) = EXAMPLES[i].queries.first() {
                run_into_log(EXAMPLES[i].lojban, q.lojban);
            }
        }
    });
    let submit_click = move |_: Event<MouseData>| {
        do_submit();
    };
    let on_query_keydown = move |e: KeyboardEvent| {
        if e.key() == Key::Enter {
            do_submit();
        }
    };

    // Translate the English claim (Source tab) into the Lojban query. With no
    // provider configured, open the integration modal instead of erroring.
    let mut do_translate = move || {
        let text = query_source.read().clone();
        if text.trim().is_empty() || *translating.read() {
            return;
        }
        let Some(cfg) = settings.read().clone() else {
            modal_open.set(true);
            return;
        };
        translating.set(true);
        translate_error.set(None);
        spawn(async move {
            match fanva_translate(&cfg.llm, &text).await {
                Ok(lojban) => {
                    query_text.set(lojban);
                    query_tab.set(ActiveTab::Lojban);
                }
                Err(e) => translate_error.set(Some(e)),
            }
            translating.set(false);
        });
    };
    let translate_click = move |_: Event<MouseData>| {
        do_translate();
    };
    let on_source_keydown = move |e: KeyboardEvent| {
        if e.key() == Key::Enter && e.modifiers().ctrl() {
            e.prevent_default();
            do_translate();
        }
    };

    let ex = *example.read();
    let is_example = ex.is_some();
    let reading = query_reading.read().clone();

    rsx! {
        div { class: "tabs-container",
            div { class: "tab-bar",
                if !is_example {
                    button {
                        class: if *query_tab.read() == ActiveTab::Source { "tab active" } else { "tab" },
                        onclick: move |_| query_tab.set(ActiveTab::Source),
                        "Source"
                    }
                }
                button {
                    class: if is_example || *query_tab.read() == ActiveTab::Lojban { "tab active" } else { "tab" },
                    onclick: move |_| query_tab.set(ActiveTab::Lojban),
                    "Lojban"
                }
            }
            div { class: "tab-content",
                match (is_example, *query_tab.read()) {
                    (false, ActiveTab::Source) => {
                        let hint = match settings.read().as_ref().map(|c| c.llm.provider.short_name()) {
                            Some(p) => format!("english claim \u{2192} lojban via {p}"),
                            None => "english claim \u{2192} lojban \u{2014} configure an llm".to_string(),
                        };
                        rsx! {
                            span { class: "nb-eyebrow", "query \u{2014} state a claim in english" }
                            textarea {
                                class: "source-input",
                                placeholder: "State the claim to check, e.g. \"Adam eats\"\u{2026}",
                                value: "{query_source}",
                                oninput: move |e| query_source.set(e.value()),
                                onkeydown: on_source_keydown,
                            }
                            if let Some(err) = translate_error.read().as_ref() {
                                div { class: "translate-error", "{err}" }
                            }
                            div { class: "translate-row",
                                button {
                                    class: if *translating.read() { "translate-btn busy" } else { "translate-btn" },
                                    onclick: translate_click,
                                    disabled: *translating.read(),
                                    "Translate"
                                }
                                button {
                                    class: "translate-row__config",
                                    title: "Configure LLM integration",
                                    onclick: move |_| modal_open.set(true),
                                    "\u{2699}"
                                }
                                span { class: "translate-row__hint", "{hint}" }
                            }
                        }
                    }
                    // Lojban tab: you STATE a proposition to check (not ask a
                    // question) — the engine answers TRUE / FALSE / UNKNOWN. The
                    // `xu` shown is a decorative reading cue: it is not part of
                    // `query_text` and never reaches the engine (typing it is a
                    // syntax error). The live "Query if …" back-translation shows
                    // inline below. Source is the only other tab, so `_` covers
                    // Lojban here.
                    _ => rsx! {
                        if is_example {
                            // Example mode: pick a preset query; it runs on select.
                            div { class: "query-bar",
                                span { class: "query-bar__affix", "xu" }
                                select {
                                    class: "nb-select query-select",
                                    onchange: move |e| {
                                        if let Ok(idx) = e.value().parse::<usize>() {
                                            selected_query.set(idx);
                                            do_submit();
                                        }
                                    },
                                    for (i , q) in ex.map(|j| EXAMPLES[j].queries).unwrap_or(&[]).iter().enumerate() {
                                        option {
                                            value: "{i}",
                                            selected: i == *selected_query.read(),
                                            "{q.lojban} \u{2014} {q.label}"
                                        }
                                    }
                                }
                            }
                            div { class: "query-hint",
                                "Preset queries \u{2014} pick one to run it against the loaded knowledge base."
                            }
                        } else {
                            div { class: "query-bar",
                                span {
                                    class: "query-bar__affix",
                                    title: "xu just marks this box as a query \u{2014} a reading cue only, never typed or sent. You state a claim (e.g. la .adam. cu citka); the engine answers TRUE / FALSE / UNKNOWN.",
                                    "xu"
                                }
                                input {
                                    id: "query-input",
                                    class: "query-input",
                                    r#type: "text",
                                    placeholder: "State a proposition to check \u{2014} Ctrl+K focus",
                                    value: "{query_text}",
                                    oninput: move |e| query_text.set(e.value()),
                                    onkeydown: on_query_keydown,
                                }
                                button { class: "query-btn", onclick: submit_click, "Query" }
                            }
                            div { class: "query-hint",
                                "State a claim to check \u{2014} e.g. \u{201C}Adam eats\u{201D} \u{2014} not a question (\u{201C}Does Adam eat?\u{201D})."
                            }
                        }
                        match reading {
                            QueryReading::Empty => rsx! {},
                            QueryReading::Reads(g) => {
                                // Drop a trailing period so it reads as prose.
                                let g = g.trim().trim_end_matches('.').trim().to_string();
                                rsx! {
                                    div { class: "query-gloss",
                                        span { class: "nb-eyebrow", "back-translation" }
                                        div { class: "query-gloss__reading",
                                            span { class: "query-gloss__prefix", "Query if " }
                                            span { class: "query-gloss__text", "{g}" }
                                        }
                                    }
                                }
                            }
                            QueryReading::Incomplete => rsx! {
                                div { class: "query-gloss",
                                    span { class: "nb-eyebrow", "back-translation" }
                                    div { class: "query-gloss__reading query-gloss__reading--pending",
                                        "\u{26A0} incomplete or invalid Lojban"
                                    }
                                }
                            },
                        }
                    },
                }
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
    settings: Signal<Option<Settings>>,
    modal_open: Signal<bool>,
    example: Signal<Option<usize>>,
) -> Element {
    let mut source_text = use_signal(|| DEFAULT_SOURCE.to_string());
    let mut translating = use_signal(|| false);
    let mut translate_error = use_signal(|| Option::<String>::None);
    let mut translate_trace = use_signal(Vec::<TraceRow>::new);
    let mut translate_degraded = use_signal(|| false);

    // Deep-meaning (jbotci tersmu) view state — a network result, so held in signals
    // (not a memo). On-demand + proxy-gated; see `do_tersmu` below.
    let mut tersmu_loading = use_signal(|| false);
    let mut tersmu_error = use_signal(|| Option::<String>::None);
    let mut tersmu_result = use_signal(|| Option::<String>::None);

    // Invalidate a shown graph whenever the active KB changes (edited Lojban, a Clear/
    // Load, a translate, or a different example) so tersmu output never shows stale.
    use_effect(move || {
        let _ = example.read();
        let _ = lojban_text.read();
        tersmu_result.set(None);
        tersmu_error.set(None);
    });

    // Back-translation reflects the ACTIVE KB: a loaded example's corpus, else
    // the user's editable Lojban tab.
    let back_translation = use_memo(move || {
        let text = match *example.read() {
            Some(i) => EXAMPLES[i].lojban.to_string(),
            None => lojban_text.read().clone(),
        };
        if text.is_empty() {
            String::new()
        } else {
            back_translate_ir(&text)
        }
    });

    // Translate the Source tab → Lojban via the configured LLM. With no provider
    // configured yet, open the integration modal instead of erroring.
    let mut do_translate = move || {
        let text = source_text.read().clone();
        if text.trim().is_empty() || *translating.read() {
            return;
        }
        let Some(cfg) = settings.read().clone() else {
            modal_open.set(true);
            return;
        };
        translating.set(true);
        translate_error.set(None);
        translate_trace.set(Vec::new());
        translate_degraded.set(false);
        spawn(async move {
            use nibli_fanva::agent::Outcome;
            // The self-correcting loop: translate → (optionally call jbotci tools) →
            // validate (gerna+smuni+camxes) → feed the error back → retry, up to the
            // configured max attempts.
            let http = nibli_fanva::llm::HttpChat;
            // jbotci proxy — inert unless the user enabled jbotci. Disabled/empty ⇒ the
            // loop degrades to the local gates and never calls the proxy.
            let mcp = nibli_fanva::mcp::McpClient::new(cfg.active_proxy_url());
            let outcome = nibli_fanva::agent::translate_agentic(
                &http,
                &mcp,
                &cfg.llm,
                &text,
                cfg.max_attempts.max(1),
                MAX_TOOL_STEPS,
            )
            .await;
            match outcome {
                Outcome::Success {
                    lojban,
                    attempts,
                    degraded,
                } => {
                    translate_trace.set(trace_rows(&attempts));
                    translate_degraded.set(degraded);
                    lojban_text.set(lojban);
                    active_tab.set(ActiveTab::Lojban);
                }
                Outcome::Exhausted {
                    best,
                    last_error,
                    attempts,
                    degraded,
                } => {
                    let n = attempts.len();
                    translate_trace.set(trace_rows(&attempts));
                    translate_degraded.set(degraded);
                    // Show the best effort so the user can edit from there.
                    lojban_text.set(best);
                    active_tab.set(ActiveTab::Lojban);
                    translate_error.set(Some(format!(
                        "Couldn't fully validate after {n} attempts \u{2014} showing best effort. Last: {}",
                        last_error.message()
                    )));
                }
                Outcome::ChatFailed {
                    error, attempts, ..
                } => {
                    translate_trace.set(trace_rows(&attempts));
                    translate_error.set(Some(error));
                }
            }
            translating.set(false);
        });
    };
    let translate_click = move |_: Event<MouseData>| {
        do_translate();
    };
    let on_source_keydown = move |e: KeyboardEvent| {
        if e.key() == Key::Enter && e.modifiers().ctrl() {
            e.prevent_default();
            do_translate();
        }
    };

    // Deep meaning: send the ACTIVE KB (as one `.i`-joined text) to jbotci's tersmu
    // tool and show the raw semantic graph. On-demand (network) + proxy-gated; any
    // failure (incl. no proxy / native) degrades to a notice, never a hard error.
    let mut do_tersmu = move || {
        if *tersmu_loading.read() {
            return;
        }
        let Some(cfg) = settings.read().clone() else {
            return;
        };
        if cfg.active_proxy_url().is_empty() {
            return;
        }
        let active = match *example.read() {
            Some(i) => EXAMPLES[i].lojban.to_string(),
            None => lojban_text.read().clone(),
        };
        let joined = kb_to_tersmu_text(&active);
        if joined.is_empty() {
            return;
        }
        tersmu_loading.set(true);
        tersmu_error.set(None);
        tersmu_result.set(None);
        spawn(async move {
            let mcp = nibli_fanva::mcp::McpClient::new(cfg.active_proxy_url());
            let outcome = mcp.tersmu(&joined).await;
            // Drop the result if the KB changed while the request was in flight.
            let current = match *example.read() {
                Some(i) => EXAMPLES[i].lojban.to_string(),
                None => lojban_text.read().clone(),
            };
            if kb_to_tersmu_text(&current) == joined {
                match outcome {
                    Ok(res) if !res.is_error => tersmu_result.set(Some(res.text)),
                    Ok(res) => tersmu_error.set(Some(format!(
                        "jbotci tersmu reported an error: {}",
                        res.text
                    ))),
                    // McpError::Display is self-describing (429/5xx/network/…).
                    Err(e) => tersmu_error.set(Some(e.to_string())),
                }
            }
            tersmu_loading.set(false);
        });
    };
    let tersmu_click = move |_: Event<MouseData>| {
        do_tersmu();
    };

    // In example mode the KB is a read-only preview of the loaded corpus; the
    // user's Custom buffers (`source_text`/`lojban_text`) are left untouched.
    let ex = *example.read();
    let is_example = ex.is_some();
    let active_source = match ex {
        Some(i) => EXAMPLES[i].source.to_string(),
        None => source_text.read().clone(),
    };
    let active_lojban = match ex {
        Some(i) => EXAMPLES[i].lojban.to_string(),
        None => lojban_text.read().clone(),
    };
    // The deep-meaning (tersmu) view only appears when jbotci is enabled with a proxy.
    let jbotci_on = settings
        .read()
        .as_ref()
        .map(|s| !s.active_proxy_url().is_empty())
        .unwrap_or(false);

    rsx! {
        div { class: "tabs-container",
            div { class: "tab-bar",
                button {
                    class: if *active_tab.read() == ActiveTab::Source { "tab active" } else { "tab" },
                    onclick: move |_| active_tab.set(ActiveTab::Source),
                    "Source"
                }
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
                    ActiveTab::Source => {
                        let hint = if is_example {
                            "loaded example \u{2014} read-only".to_string()
                        } else {
                            match settings.read().as_ref().map(|c| c.llm.provider.short_name()) {
                                Some(p) => format!("english \u{2192} lojban via {p}"),
                                None => "english \u{2192} lojban \u{2014} configure an llm".to_string(),
                            }
                        };
                        rsx! {
                            span { class: "nb-eyebrow", "source \u{2014} plain english" }
                            textarea {
                                class: "source-input",
                                placeholder: "Enter English text\u{2026}",
                                value: "{active_source}",
                                readonly: is_example,
                                oninput: move |e| {
                                    if example.read().is_none() {
                                        source_text.set(e.value());
                                    }
                                },
                                onkeydown: on_source_keydown,
                            }
                            if let Some(err) = translate_error.read().as_ref() {
                                div { class: "translate-error", "{err}" }
                            }
                            div { class: "translate-row",
                                button {
                                    class: if *translating.read() { "translate-btn busy" } else { "translate-btn" },
                                    onclick: translate_click,
                                    disabled: *translating.read() || is_example,
                                    "Translate"
                                }
                                button {
                                    class: "translate-row__config",
                                    title: "Configure LLM integration",
                                    onclick: move |_| modal_open.set(true),
                                    "\u{2699}"
                                }
                                span { class: "translate-row__hint", "{hint}" }
                            }
                            if !translate_trace.read().is_empty() {
                                div { class: "translate-trace",
                                    for row in translate_trace().iter() {
                                        div { key: "{row.n}", class: "trace-item",
                                            div {
                                                class: if row.ok { "trace-row trace-ok" } else { "trace-row trace-fail" },
                                                span { class: "trace-n", "#{row.n}" }
                                                span { class: "trace-gates",
                                                    for (label, chip_class) in row.gates.iter() {
                                                        span { key: "{label}", class: "{chip_class}", "{label}" }
                                                    }
                                                }
                                                span { class: "trace-detail", "{row.detail}" }
                                            }
                                            for (ti, tool) in row.tools.iter().enumerate() {
                                                div {
                                                    key: "{ti}",
                                                    class: if tool.is_error { "trace-tool err" } else { "trace-tool ok" },
                                                    "\u{21B3} {tool.name} \u{00B7} {tool.detail}"
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            if *translate_degraded.read() {
                                div { class: "translate-degraded",
                                    "jbotci tools off \u{2014} validated with the local gerna+smuni+camxes gates only. Enable jbotci in settings for dictionary/grammar lookups."
                                }
                            }
                        }
                    }
                    ActiveTab::Lojban => rsx! {
                        if !is_example {
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
                        }
                        textarea {
                            class: "lojban-input",
                            placeholder: "Enter Lojban facts and rules (one per line)...",
                            value: "{active_lojban}",
                            readonly: is_example,
                            oninput: move |e| {
                                if example.read().is_none() {
                                    lojban_text.set(e.value());
                                }
                            },
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
                        // Deep-meaning view state, snapshotted for this render.
                        let tersmu_err = tersmu_error.read().clone();
                        let tersmu_graph = tersmu_result.read().clone();
                        let tersmu_busy = *tersmu_loading.read();
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
                            // Optional deep-meaning view — jbotci's tersmu semantic graph,
                            // shown verbatim (nibli adds zero interpretation). Only when a
                            // jbotci proxy is configured.
                            if jbotci_on {
                                div { class: "tersmu",
                                    div { class: "tersmu__head",
                                        span { class: "nb-eyebrow", "deep meaning \u{00b7} jbotci tersmu" }
                                        button {
                                            class: "tersmu-button",
                                            disabled: tersmu_busy,
                                            onclick: tersmu_click,
                                            if tersmu_busy { "Analyzing\u{2026}" } else { "Deep meaning (tersmu)" }
                                        }
                                    }
                                    if let Some(err) = tersmu_err {
                                        div { class: "tersmu__error", "{err}" }
                                    } else if let Some(graph) = tersmu_graph {
                                        pre { class: "tersmu-graph", "{graph}" }
                                    } else if !tersmu_busy {
                                        span { class: "tersmu__hint",
                                            "jbotci's deep semantic graph for the current KB \u{2014} an independent second opinion on the meaning."
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

/// Bring-your-own-key LLM integration modal. Edits a draft config held in local
/// signals; on Save it lands in the App's in-memory `settings`. The key never
/// leaves this tab (see the security note + `llm.rs`).
#[component]
fn LlmConfigModal(settings: Signal<Option<Settings>>, modal_open: Signal<bool>) -> Element {
    let initial = settings
        .read()
        .clone()
        .unwrap_or_else(|| Settings::new(Provider::OpenRouter));
    let mut provider = use_signal(|| initial.llm.provider);
    let mut api_key = use_signal(|| initial.llm.api_key.clone());
    let mut model = use_signal(|| initial.llm.model.clone());
    let mut base_url = use_signal(|| initial.llm.base_url.clone());
    let mut proxy_url = use_signal(|| initial.proxy_url.clone());
    let mut jbotci_enabled = use_signal(|| initial.jbotci_enabled);
    let mut max_attempts = use_signal(|| initial.max_attempts);
    let mut testing = use_signal(|| false);
    let mut test_msg = use_signal(|| Option::<(bool, String)>::None);

    let prov = *provider.read();

    let build_settings = move || Settings {
        llm: LlmConfig {
            provider: *provider.read(),
            api_key: api_key.read().trim().to_string(),
            model: model.read().trim().to_string(),
            base_url: base_url.read().trim().to_string(),
            max_tokens: 1024,
        },
        proxy_url: proxy_url.read().trim().to_string(),
        jbotci_enabled: *jbotci_enabled.read(),
        max_attempts: (*max_attempts.read()).max(1),
    };
    // A key is required for everyone except Custom (which may be a local server).
    let needs_key =
        move |s: &Settings| s.llm.api_key.is_empty() && s.llm.provider != Provider::Custom;

    let on_save = move |_: Event<MouseData>| {
        let s = build_settings();
        if needs_key(&s) {
            test_msg.set(Some((false, "Enter your API key first.".to_string())));
            return;
        }
        settings.set(Some(s));
        modal_open.set(false);
    };
    let on_test = move |_: Event<MouseData>| {
        if *testing.read() {
            return;
        }
        let s = build_settings();
        if needs_key(&s) {
            test_msg.set(Some((false, "Enter your API key first.".to_string())));
            return;
        }
        testing.set(true);
        test_msg.set(None);
        spawn(async move {
            match fanva_translate(&s.llm, "Adam is a dog").await {
                Ok(lojban) => test_msg.set(Some((true, format!("OK \u{2014} {lojban}")))),
                Err(e) => test_msg.set(Some((false, e))),
            }
            testing.set(false);
        });
    };

    rsx! {
        // Backdrop click closes; the card stops propagation so inner clicks don't.
        div { class: "modal-backdrop", onclick: move |_| modal_open.set(false),
            div { class: "modal-card", onclick: move |e: Event<MouseData>| e.stop_propagation(),
                div { class: "modal-title", "Integrate an LLM to translate" }
                p { class: "modal-subtitle",
                    "Use your own LLM to draft Lojban from plain English. The draft is reviewed before the engine reasons over it."
                }

                // Only this middle region scrolls; the title above and the actions
                // below stay pinned, so the modal never grows taller than the viewport.
                div { class: "modal-body",

                div { class: "llm-provider-picker",
                    for p in Provider::ALL {
                        button {
                            key: "{p.short_name()}",
                            class: if *provider.read() == p { "llm-provider-btn active" } else { "llm-provider-btn" },
                            onclick: move |_| {
                                provider.set(p);
                                model.set(p.default_model().to_string());
                                base_url.set(p.default_base_url().to_string());
                                test_msg.set(None);
                            },
                            "{p.short_name()}"
                            if let Some(promo) = p.promo() {
                                span { class: "llm-provider-btn__badge", "{promo.badge}" }
                            }
                        }
                    }
                }

                if let Some(promo) = prov.promo() {
                    div { class: "llm-promo-note",
                        span { class: "llm-promo-note__text", "{promo.note} " }
                        a {
                            class: "llm-promo-note__link",
                            href: "{promo.signup_url}",
                            target: "_blank",
                            rel: "noopener noreferrer",
                            "Get a free key \u{2192}"
                        }
                    }
                }

                label { class: "llm-field",
                    span { class: "llm-field__label", "API key" }
                    input {
                        class: "llm-field__input",
                        r#type: "password",
                        autocomplete: "off",
                        placeholder: if prov == Provider::Custom { "optional for local servers" } else { "your provider api key" },
                        value: "{api_key}",
                        oninput: move |e| api_key.set(e.value()),
                    }
                }
                if prov.needs_base_url() {
                    label { class: "llm-field",
                        span { class: "llm-field__label", "Base URL" }
                        input {
                            class: "llm-field__input",
                            r#type: "text",
                            placeholder: "http://localhost:11434/v1",
                            value: "{base_url}",
                            oninput: move |e| base_url.set(e.value()),
                        }
                    }
                }
                div { class: "llm-row",
                    label { class: "llm-field",
                        span { class: "llm-field__label", "Model" }
                        input {
                            class: "llm-field__input",
                            r#type: "text",
                            placeholder: "{prov.default_model()}",
                            value: "{model}",
                            oninput: move |e| model.set(e.value()),
                        }
                    }
                    label { class: "llm-field",
                        span { class: "llm-field__label", "Max attempts" }
                        input {
                            class: "llm-field__input",
                            r#type: "number",
                            min: "1",
                            max: "10",
                            value: "{max_attempts}",
                            oninput: move |e| {
                                if let Ok(v) = e.value().parse::<u32>() {
                                    max_attempts.set(v.clamp(1, 10));
                                }
                            },
                        }
                    }
                }

                label { class: "llm-field llm-field--toggle",
                    input {
                        class: "llm-field__checkbox",
                        r#type: "checkbox",
                        checked: jbotci_enabled(),
                        onchange: move |e| jbotci_enabled.set(e.checked()),
                    }
                    span { class: "llm-field__label", "Enable jbotci tools (dictionary / grammar / morphology)" }
                }
                label { class: "llm-field",
                    span { class: "llm-field__label", "jbotci proxy URL" }
                    input {
                        class: "llm-field__input",
                        r#type: "text",
                        placeholder: "https://your-proxy.example/mcp",
                        disabled: !jbotci_enabled(),
                        value: "{proxy_url}",
                        oninput: move |e| proxy_url.set(e.value()),
                    }
                    span { class: "llm-field__hint",
                        "Off by default \u{2014} translation runs fully local (gerna+smuni+camxes) and makes no network call to the proxy. Enable it to let the model call jbotci for dictionary/grammar/morphology lookups while translating. Your LLM key is never sent here."
                    }
                }
                div { class: "llm-security-note",
                    span { class: "llm-security-note__title", "\u{1F441}\u{FE0F} It's a blind proxy \u{2014} nothing is stored" }
                    p {
                        "jbotci refuses direct browser calls (CORS), so the URL above points at "
                        b { "fanva-proxy" }
                        " \u{2014} an app-owned Cloudflare Worker that strips your browser \u{2018}Origin\u{2019} and forwards the request verbatim to jbotci. It's a stateless blind relay: no logs, no database, no cookies. The upstream is hardcoded (not an open proxy), and every line is public \u{2014} read it yourself:"
                    }
                    div { class: "llm-security-note__links",
                        a {
                            href: "https://github.com/dhilipsiva/nibli/blob/main/fanva-proxy/src/index.js",
                            target: "_blank",
                            rel: "noopener noreferrer",
                            "index.js \u{2014} the entire proxy"
                        }
                        a {
                            href: "https://github.com/dhilipsiva/nibli/blob/main/fanva-proxy/README.md",
                            target: "_blank",
                            rel: "noopener noreferrer",
                            "README \u{2014} why & what it strips"
                        }
                    }
                }
                div { class: "llm-security-note",
                    span { class: "llm-security-note__title", "\u{1F512} Your key stays in this tab" }
                    p {
                        "Held only in this browser tab's memory \u{2014} never written to disk or storage, and erased the moment you close or reload the tab. nibli has no server: the request goes straight from your browser to "
                        b { "{prov.display_name()}" }
                        ". It is open source \u{2014} verify in DevTools \u{2192} Network that the only call is to the provider."
                    }
                    div { class: "llm-security-note__links",
                        a {
                            href: "https://github.com/dhilipsiva/nibli/blob/main/nibli-fanva/src/llm/http.rs",
                            target: "_blank",
                            rel: "noopener noreferrer",
                            "http.rs \u{2014} the request code"
                        }
                        a {
                            href: "https://github.com/dhilipsiva/nibli/blob/main/nibli-ui/Cargo.toml",
                            target: "_blank",
                            rel: "noopener noreferrer",
                            "Cargo.toml \u{2014} no server dependency"
                        }
                    }
                }

                div { class: "llm-warning",
                    "\u{26A0} LLMs can hallucinate and give a wrong translation. Always review the Lojban (and its back-translation) before trusting it \u{2014} only the formal Lojban you verify is what nibli reasons over."
                }

                if let Some((ok, msg)) = test_msg.read().clone() {
                    div {
                        class: if ok { "llm-test-result is-ok" } else { "llm-test-result is-err" },
                        "{msg}"
                    }
                }

                } // end .modal-body

                div { class: "modal-actions",
                    button {
                        class: "toolbar-btn",
                        disabled: *testing.read(),
                        onclick: on_test,
                        if *testing.read() { "Testing\u{2026}" } else { "Test" }
                    }
                    span { class: "modal-actions__sp" }
                    button {
                        class: "toolbar-btn",
                        onclick: move |_| modal_open.set(false),
                        "Cancel"
                    }
                    button { class: "translate-btn", onclick: on_save, "Save" }
                }
            }
        }
    }
}

#[component]
fn ProofPanel(
    proof_text: Signal<Option<String>>,
    proof_data: Signal<Option<ProofTrace>>,
    example: Signal<Option<usize>>,
) -> Element {
    let text = proof_text.read();
    let data = proof_data.read();

    rsx! {
        div { class: "proof-panel",
            if let Some(trace_data) = data.as_ref() {
                div { class: "proof-tree-container",
                    ProofTreeView { trace: trace_data.clone(), example }
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
fn ProofTreeView(trace: ProofTrace, example: Signal<Option<usize>>) -> Element {
    if trace.root as usize >= trace.steps.len() {
        return rsx! { div { class: "proof-error", "Invalid proof trace: root index out of bounds" } };
    }
    // A loaded curated example reads its proof in domain terms (the documented
    // overlay); Custom KBs fall through to the engine's literal glosses.
    let overlay = (*example.read()).and_then(|i| EXAMPLES[i].overlay);
    // A render-only plain-English "why" summary above the detailed tree, from the
    // same shared renderer (the trace data is unchanged). `None` for an
    // unsummarizable trace — then nothing extra is shown.
    let summary = nibli_render::summarize_proof_with(&trace, nibli_render::Register::Spec, overlay);
    // Collapse the verbose trace into the macro-logical DAG once via the shared
    // renderer; the component then walks the structured RenderedNode tree (no
    // per-variant logic in the UI). The folded role/event scaffolding rides along
    // as `proof-role-detail` clusters the user can expand.
    let root = nibli_render::collapse_proof_with(&trace, nibli_render::Register::Spec, overlay);
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
