//! Nibli Transparency Triad web UI (Dioxus).
//!
//! Browser-based interface with three tabs: Source (original document),
//! Lojban (formal encoding with per-line validation), and Back-translation
//! (robotic word-by-word gloss). Bottom query bar for proof-queries.
//! Network tab for gossip assertions, event feed, and contradiction resolution.
//! Communicates with nibli-server via GraphQL on port 8081.

use dioxus::prelude::*;
use gloo_net::http::Request;
use nibli_protocol::{KbStatus, ProofTrace};
use serde::Deserialize;

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

/// GraphQL endpoint URL. Override at build time: NIBLI_GRAPHQL_URL=http://host:port/graphql
const GRAPHQL_URL: &str = match option_env!("NIBLI_GRAPHQL_URL") {
    Some(url) => url,
    None => "http://localhost:8081/graphql",
};
/// Readiness check URL. Override at build time: NIBLI_READY_URL=http://host:port/readyz
const READY_URL: &str = match option_env!("NIBLI_READY_URL") {
    Some(url) => url,
    None => "http://localhost:8081/readyz",
};
const MAX_OUTPUT_ENTRIES: usize = 200;

const DEFAULT_SOURCE: &str = "All dogs are animals.\nAll animals eat.\nAdam is a dog.";
const DEFAULT_LOJBAN: &str = "ro lo gerku cu danlu\nro lo danlu cu citka\nla .adam. cu gerku";
const DEFAULT_QUERY: &str = "la .adam. cu citka";

// ── Types ──

#[derive(Clone, Copy, PartialEq)]
enum ActiveTab {
    Source,
    Lojban,
    BackTranslation,
    Network,
}

#[derive(Clone, Copy, PartialEq)]
enum ConnectionStatus {
    Checking,
    Ready,
    WaitingForPeer,
    NotReady,
    Disconnected,
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

// ── GraphQL helpers ──

#[derive(Deserialize)]
struct GraphQLResponse {
    data: Option<serde_json::Value>,
    errors: Option<Vec<serde_json::Value>>,
}

// NOTE: keys are snake_case to match nibli-server's /readyz wire format
// (its ReadyResponse derives plain serde::Serialize with no rename). Do NOT
// add `#[serde(rename_all = "camelCase")]` here — it makes deserialization
// fail and the StatusBadge falsely reports "Disconnected".
#[derive(Deserialize)]
struct ReadyResponse {
    ready: bool,
    require_gossip_peer: bool,
    gossip_peer_count: usize,
}

async fn check_server_status() -> ConnectionStatus {
    match Request::get(READY_URL).send().await {
        Ok(resp) => match resp.json::<ReadyResponse>().await {
            Ok(ready) => {
                if ready.ready {
                    ConnectionStatus::Ready
                } else if ready.require_gossip_peer && ready.gossip_peer_count == 0 {
                    ConnectionStatus::WaitingForPeer
                } else {
                    ConnectionStatus::NotReady
                }
            }
            Err(_) => ConnectionStatus::Disconnected,
        },
        Err(_) => ConnectionStatus::Disconnected,
    }
}

async fn graphql_mutate(query: &str, input: &str) -> Result<serde_json::Value, String> {
    let body = serde_json::json!({
        "query": query,
        "variables": { "input": input }
    });
    graphql_post(&body).await
}

async fn graphql_mutate_kb(query: &str, kb: &str, q: &str) -> Result<serde_json::Value, String> {
    let body = serde_json::json!({
        "query": query,
        "variables": { "kb": kb, "query": q }
    });
    graphql_post(&body).await
}

async fn graphql_post(body: &serde_json::Value) -> Result<serde_json::Value, String> {
    let req = Request::post(GRAPHQL_URL)
        .header("Content-Type", "application/json")
        .body(body.to_string())
        .map_err(|e| format!("Request build error: {}", e))?;
    let resp = req
        .send()
        .await
        .map_err(|e| format!("Network error: {}", e))?;
    let gql: GraphQLResponse = resp
        .json()
        .await
        .map_err(|e| format!("Parse error: {}", e))?;
    if let Some(errors) = gql.errors {
        if let Some(first) = errors.first() {
            return Err(first
                .get("message")
                .and_then(|m| m.as_str())
                .unwrap_or("Unknown GraphQL error")
                .to_string());
        }
    }
    gql.data.ok_or_else(|| "No data in response".to_string())
}

// ── Network types ──

#[derive(Clone, Debug, Default, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct NetworkSnapshotData {
    agents: Vec<AgentData>,
    envelopes: Vec<EnvelopeData>,
    contradictions: Vec<ContradictionData>,
    peers: Vec<String>,
    local_agent: String,
    total_facts: u32,
}

#[derive(Clone, Debug, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AgentData {
    name: String,
    envelope_count: u32,
    stance_counts: StanceCountsData,
    topics: Vec<String>,
    is_local: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Deserialize)]
struct StanceCountsData {
    deduced: u32,
    expected: u32,
    opinion: u32,
    hearsay: u32,
}

#[derive(Clone, Debug, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct EnvelopeData {
    id: String,
    author: String,
    lojban: Option<String>,
    stance: String,
    topics: Vec<String>,
    timestamp: String,
    is_retraction: bool,
    is_quarantined: bool,
}

#[derive(Clone, Debug, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct ContradictionData {
    id: u32,
    envelope_id: String,
    assertion: String,
    author: String,
    resolved: bool,
}

#[derive(Clone, Debug, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct GossipEventData {
    kind: String,
    envelope_id: Option<String>,
    author: Option<String>,
    lojban: Option<String>,
    stance: Option<String>,
    timestamp: Option<String>,
    #[allow(dead_code)]
    peer_id: Option<String>,
    #[allow(dead_code)]
    connected: Option<bool>,
    #[allow(dead_code)]
    contradiction_id: Option<u32>,
    #[allow(dead_code)]
    assertion: Option<String>,
}

async fn fetch_network_snapshot() -> Result<NetworkSnapshotData, String> {
    let gql = r#"{ networkSnapshot { agents { name envelopeCount stanceCounts { deduced expected opinion hearsay } topics isLocal } envelopes { id author lojban stance topics timestamp isRetraction isQuarantined } contradictions { id envelopeId assertion author resolved } peers localAgent totalFacts } }"#;
    let body = serde_json::json!({"query": gql});
    let data = graphql_post(&body).await?;
    let snap = &data["networkSnapshot"];
    serde_json::from_value(snap.clone()).map_err(|e| format!("Parse error: {}", e))
}

async fn fetch_gossip_events(limit: u32) -> Result<Vec<GossipEventData>, String> {
    let gql = format!(
        r#"{{ gossipEvents(limit: {}) {{ kind envelopeId author lojban stance timestamp peerId connected contradictionId assertion }} }}"#,
        limit
    );
    let body = serde_json::json!({"query": gql});
    let data = graphql_post(&body).await?;
    let events = &data["gossipEvents"];
    serde_json::from_value(events.clone()).map_err(|e| format!("Parse error: {}", e))
}

async fn gossip_assert(lojban: &str, stance: &str) -> Result<String, String> {
    let gql = r#"mutation($lojban: String!, $stance: String) { gossipAssert(lojban: $lojban, stance: $stance) { envelopeId error } }"#;
    let body = serde_json::json!({
        "query": gql,
        "variables": { "lojban": lojban, "stance": stance }
    });
    let data = graphql_post(&body).await?;
    let r = &data["gossipAssert"];
    if let Some(err) = r["error"].as_str() {
        Err(err.to_string())
    } else {
        Ok(r["envelopeId"].as_str().unwrap_or("unknown").to_string())
    }
}

async fn resolve_contradiction_api(id: u32) -> Result<(), String> {
    let gql = r#"mutation($id: Int!) { resolveContradiction(id: $id) { success error } }"#;
    let body = serde_json::json!({
        "query": gql,
        "variables": { "id": id }
    });
    let data = graphql_post(&body).await?;
    let r = &data["resolveContradiction"];
    if let Some(err) = r["error"].as_str() {
        Err(err.to_string())
    } else {
        Ok(())
    }
}

// ── Query execution ──
// Every query resets the engine, re-asserts the Lojban tab as the KB, then queries.

fn parse_kb_status(data: &serde_json::Value) -> Option<KbStatus> {
    let s = data.get("kbStatus")?;
    if s.is_null() {
        return None;
    }
    Some(KbStatus {
        asserted: s["asserted"].as_u64().unwrap_or(0) as u32,
        errors: s["errors"].as_u64().unwrap_or(0) as u32,
        skipped: s["skipped"].as_u64().unwrap_or(0) as u32,
        line_results: s["lineResults"]
            .as_array()
            .map(|arr| {
                arr.iter()
                    .map(|lr| nibli_protocol::LineResult {
                        line_number: lr["lineNumber"].as_u64().unwrap_or(0) as u32,
                        text: lr["text"].as_str().unwrap_or("").to_string(),
                        success: lr["success"].as_bool().unwrap_or(false),
                        fact_id: lr["factId"].as_u64(),
                        error: lr["error"].as_str().map(|s| s.to_string()),
                    })
                    .collect()
            })
            .unwrap_or_default(),
    })
}

async fn execute_query(kb: &str, query_text: &str) -> OutputEntry {
    let gql = r#"mutation($kb: String!, $query: String!) { queryWithKb(kb: $kb, query: $query) { status unknownReason resourceKind proofTrace proofTraceJson error kbStatus { asserted errors skipped lineResults { lineNumber text success factId error } } } }"#;
    match graphql_mutate_kb(gql, kb, query_text).await {
        Ok(data) => {
            let r = &data["queryWithKb"];
            let kb_status = parse_kb_status(r);
            if let Some(err) = r["error"].as_str() {
                OutputEntry {
                    input: query_text.to_string(),
                    result: err.to_string(),
                    is_error: true,
                    proof_trace: None,
                    proof_trace_data: None,
                    kb_status,
                }
            } else {
                let status = r["status"].as_str().unwrap_or("FALSE");
                let status_label = match status {
                    "TRUE" | "True" => "TRUE",
                    "FALSE" | "False" => "FALSE",
                    "UNKNOWN" | "Unknown" => "UNKNOWN",
                    "RESOURCE_EXCEEDED" | "ResourceExceeded" => "RESOURCE_EXCEEDED",
                    other => other,
                };
                let detail = r["resourceKind"]
                    .as_str()
                    .or_else(|| r["unknownReason"].as_str());
                let trace = r["proofTrace"].as_str().map(|s| s.to_string());
                let trace_data = r["proofTraceJson"]
                    .as_str()
                    .and_then(nibli_protocol::proof_trace_from_json);
                OutputEntry {
                    input: query_text.to_string(),
                    result: match detail {
                        Some(detail) => format!("{} ({})", status_label, detail),
                        None => status_label.to_string(),
                    },
                    is_error: false,
                    proof_trace: trace,
                    proof_trace_data: trace_data,
                    kb_status,
                }
            }
        }
        Err(e) => OutputEntry {
            input: query_text.to_string(),
            result: e,
            is_error: true,
            proof_trace: None,
            proof_trace_data: None,
            kb_status: None,
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
    let is_busy: Signal<bool> = use_signal(|| false);

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

    let network_snapshot: Signal<Option<NetworkSnapshotData>> = use_signal(|| None);
    let active_tab: Signal<ActiveTab> = use_signal(|| ActiveTab::Source);
    // "" = dark (the instrument default); "light" = the QUINE paper theme. The
    // attribute rides on `.app`, so the [data-theme="light"] overrides cascade.
    let mut theme = use_signal(|| "");

    rsx! {
        document::Link { rel: "stylesheet", href: asset!("/assets/tokens.css") }
        document::Link { rel: "stylesheet", href: asset!("/assets/style.css") }
        div { class: "app", "data-theme": "{theme}", tabindex: "0", onkeydown: on_global_keydown,
            div { class: "main-row",
                div { class: "col-tabs",
                    SourceTabs { lojban_text, kb_status, active_tab, network_snapshot }
                }
                div { class: "col-proof",
                    ProofPanel { proof_text, proof_data, is_busy }
                }
            }
            div { class: "query-row",
                div { class: "query-section",
                    div { class: "query-header",
                        span { class: "query-header__label", "query" }
                        span { class: "query-header__sp" }
                        StatusBadge {}
                        button {
                            class: "toolbar-btn",
                            title: "Toggle theme",
                            onclick: move |_| {
                                let next = if *theme.read() == "light" { "" } else { "light" };
                                theme.set(next);
                            },
                            "\u{25D0}"
                        }
                    }
                    QueryBar { output_log, proof_text, proof_data, lojban_text, kb_status, is_busy }
                }
                OutputLog { output_log }
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
fn StatusBadge() -> Element {
    let mut status = use_signal(|| ConnectionStatus::Checking);

    use_future(move || async move {
        loop {
            let result = check_server_status().await;
            status.set(result);
            gloo_timers::future::sleep(std::time::Duration::from_secs(5)).await;
        }
    });

    let (label, class) = match *status.read() {
        ConnectionStatus::Checking => ("Checking...", "status-badge checking"),
        ConnectionStatus::Ready => ("Ready", "status-badge connected"),
        ConnectionStatus::WaitingForPeer => ("Waiting for peer", "status-badge waiting"),
        ConnectionStatus::NotReady => ("Not ready", "status-badge not-ready"),
        ConnectionStatus::Disconnected => ("Disconnected", "status-badge disconnected"),
    };

    rsx! {
        span { class: "{class}", "{label}" }
    }
}

#[component]
fn QueryBar(
    output_log: Signal<Vec<OutputEntry>>,
    proof_text: Signal<Option<String>>,
    proof_data: Signal<Option<ProofTrace>>,
    lojban_text: Signal<String>,
    kb_status: Signal<Option<KbStatus>>,
    is_busy: Signal<bool>,
) -> Element {
    let mut query_text = use_signal(|| DEFAULT_QUERY.to_string());

    let mut do_submit = move || {
        let text = query_text.read().clone();
        if text.trim().is_empty() || *is_busy.read() {
            return;
        }
        is_busy.set(true);
        query_text.set(String::new());

        spawn(async move {
            let kb = lojban_text.read().clone();
            let trimmed = text.trim();
            let entry = execute_query(&kb, trimmed).await;

            if let Some(ref trace) = entry.proof_trace {
                proof_text.set(Some(trace.clone()));
            }
            if let Some(ref data) = entry.proof_trace_data {
                proof_data.set(Some(data.clone()));
            }
            kb_status.set(entry.kb_status.clone());

            // Push entry and cap at MAX_OUTPUT_ENTRIES
            {
                let mut log = output_log.write();
                log.push(entry);
                if log.len() > MAX_OUTPUT_ENTRIES {
                    let drain_count = log.len() - MAX_OUTPUT_ENTRIES;
                    log.drain(0..drain_count);
                }
            }

            is_busy.set(false);

            // Auto-scroll output log to bottom
            spawn(async move {
                let _ = document::eval(
                    "const el = document.getElementById('output-log'); if (el) el.scrollTop = el.scrollHeight;"
                ).await;
            });
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

    let busy = *is_busy.read();
    let btn_class = if busy { "query-btn busy" } else { "query-btn" };

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
                disabled: busy,
            }
            button {
                class: "{btn_class}",
                onclick: submit_click,
                disabled: busy,
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
    network_snapshot: Signal<Option<NetworkSnapshotData>>,
) -> Element {
    let mut source_text = use_signal(|| DEFAULT_SOURCE.to_string());
    let mut translating = use_signal(|| false);
    let mut translate_error = use_signal(|| Option::<String>::None);
    let back_translation = use_memo(move || {
        let text = lojban_text.read();
        if text.is_empty() {
            String::new()
        } else {
            back_translate_ir(&text)
        }
    });

    let mut do_translate = move || {
        let text = source_text.read().clone();
        if text.trim().is_empty() || *translating.read() {
            return;
        }
        translating.set(true);
        translate_error.set(None);

        spawn(async move {
            let query = r#"mutation($input: String!) { translateToLojban(input: $input) { lojban error } }"#;
            match graphql_mutate(query, &text).await {
                Ok(data) => {
                    let r = &data["translateToLojban"];
                    if let Some(err) = r["error"].as_str() {
                        translate_error.set(Some(err.to_string()));
                    } else if let Some(lojban) = r["lojban"].as_str() {
                        lojban_text.set(lojban.to_string());
                        active_tab.set(ActiveTab::Lojban);
                    }
                }
                Err(e) => {
                    translate_error.set(Some(e));
                }
            }
            translating.set(false);
        });
    };

    let on_translate = move |_: Event<MouseData>| {
        do_translate();
    };

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
                button {
                    class: if *active_tab.read() == ActiveTab::Network { "tab active" } else { "tab" },
                    onclick: move |_| active_tab.set(ActiveTab::Network),
                    "Network"
                }
            }
            div { class: "tab-content",
                match *active_tab.read() {
                    ActiveTab::Source => rsx! {
                        span { class: "nb-eyebrow", "source \u{2014} plain english" }
                        textarea {
                            class: "source-input",
                            placeholder: "Enter English text...",
                            value: "{source_text}",
                            oninput: move |e| source_text.set(e.value()),
                            onkeydown: move |e: KeyboardEvent| {
                                if e.key() == Key::Enter && e.modifiers().ctrl() {
                                    e.prevent_default();
                                    do_translate();
                                }
                            },
                        }
                        if let Some(err) = translate_error.read().as_ref() {
                            div { class: "translate-error", "{err}" }
                        }
                        div { class: "translate-row",
                            button {
                                class: if *translating.read() { "translate-btn busy" } else { "translate-btn" },
                                onclick: on_translate,
                                disabled: *translating.read(),
                                "Translate"
                            }
                            span { class: "translate-row__hint", "english \u{2192} lojban via llm" }
                        }
                    },
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
                    ActiveTab::Network => rsx! {
                        NetworkView { network_snapshot }
                    },
                }
            }
        }
    }
}

// ── Network components ──

#[component]
fn NetworkView(network_snapshot: Signal<Option<NetworkSnapshotData>>) -> Element {
    let mut loading = use_signal(|| false);
    let mut error_msg = use_signal(|| Option::<String>::None);
    let mut gossip_input = use_signal(|| String::new());
    let mut gossip_stance = use_signal(|| "Deduced".to_string());
    let mut gossip_busy = use_signal(|| false);
    let mut selected_agent = use_signal(|| Option::<String>::None);
    let mut events: Signal<Vec<GossipEventData>> = use_signal(Vec::new);

    // Auto-refresh network snapshot every 3 seconds
    use_future(move || async move {
        loop {
            loading.set(true);
            match fetch_network_snapshot().await {
                Ok(snap) => {
                    network_snapshot.set(Some(snap));
                    error_msg.set(None);
                }
                Err(e) => {
                    error_msg.set(Some(e));
                }
            }
            // Also fetch events
            if let Ok(ev) = fetch_gossip_events(20).await {
                events.set(ev);
            }
            loading.set(false);
            gloo_timers::future::sleep(std::time::Duration::from_secs(3)).await;
        }
    });

    let do_gossip_assert = move |_: Event<MouseData>| {
        let text = gossip_input.read().clone();
        let stance = gossip_stance.read().clone();
        if text.trim().is_empty() || *gossip_busy.read() {
            return;
        }
        gossip_busy.set(true);
        spawn(async move {
            match gossip_assert(&text, &stance).await {
                Ok(_id) => {
                    gossip_input.set(String::new());
                    // Refresh snapshot immediately
                    if let Ok(snap) = fetch_network_snapshot().await {
                        network_snapshot.set(Some(snap));
                    }
                }
                Err(e) => {
                    error_msg.set(Some(format!("Assert failed: {}", e)));
                }
            }
            gossip_busy.set(false);
        });
    };

    let snapshot = network_snapshot.read();

    rsx! {
        div { class: "network-container",
            // Gossip assert bar
            div { class: "gossip-bar",
                input {
                    class: "gossip-input",
                    r#type: "text",
                    placeholder: "Assert Lojban into gossip network...",
                    value: "{gossip_input}",
                    oninput: move |e| gossip_input.set(e.value()),
                    onkeydown: move |e: KeyboardEvent| {
                        if e.key() == Key::Enter {
                            let text = gossip_input.read().clone();
                            let stance = gossip_stance.read().clone();
                            if text.trim().is_empty() || *gossip_busy.read() {
                                return;
                            }
                            gossip_busy.set(true);
                            spawn(async move {
                                match gossip_assert(&text, &stance).await {
                                    Ok(_) => {
                                        gossip_input.set(String::new());
                                        if let Ok(snap) = fetch_network_snapshot().await {
                                            network_snapshot.set(Some(snap));
                                        }
                                    }
                                    Err(e) => error_msg.set(Some(format!("Assert failed: {}", e))),
                                }
                                gossip_busy.set(false);
                            });
                        }
                    },
                    disabled: *gossip_busy.read(),
                }
                select {
                    class: "gossip-stance-select",
                    value: "{gossip_stance}",
                    onchange: move |e| gossip_stance.set(e.value()),
                    option { value: "Deduced", "ja'o (deduced)" }
                    option { value: "Expected", "ba'a (expected)" }
                    option { value: "Opinion", "pe'i (opinion)" }
                    option { value: "Hearsay", "ti'e (hearsay)" }
                }
                button {
                    class: "gossip-btn",
                    onclick: do_gossip_assert,
                    disabled: *gossip_busy.read(),
                    if *gossip_busy.read() { "..." } else { "Assert" }
                }
            }
            if let Some(ref err) = *error_msg.read() {
                div { class: "network-error", "{err}" }
            }
            if let Some(ref snap) = *snapshot {
                // Summary bar
                div { class: "network-summary",
                    div { class: "network-stat",
                        span { class: "network-stat__num", "{snap.agents.len()}" }
                        span { class: "network-stat__label", "agents" }
                    }
                    div { class: "network-stat",
                        span { class: "network-stat__num", "{snap.total_facts}" }
                        span { class: "network-stat__label", "active facts" }
                    }
                    div { class: "network-stat",
                        span { class: "network-stat__num", "{snap.envelopes.len()}" }
                        span { class: "network-stat__label", "envelopes" }
                    }
                    {
                        let unresolved = snap.contradictions.iter().filter(|c| !c.resolved).count();
                        let stat_class = if unresolved > 0 { "network-stat is-alert" } else { "network-stat" };
                        rsx! {
                            div { class: "{stat_class}",
                                span { class: "network-stat__num", "{unresolved}" }
                                span { class: "network-stat__label", "contradictions" }
                            }
                        }
                    }
                    if *loading.read() {
                        span { class: "network-refresh", "sync" }
                    }
                }
                div { class: "network-panels",
                    // Agent list
                    div { class: "network-panel",
                        div { class: "panel-header", "Agents" }
                        div { class: "agent-list",
                            for agent in snap.agents.iter() {
                                AgentCard {
                                    key: "{agent.name}",
                                    agent: agent.clone(),
                                    selected: *selected_agent.read() == Some(agent.name.clone()),
                                    on_select: move |name: String| {
                                        let current = selected_agent.read().clone();
                                        if current == Some(name.clone()) {
                                            selected_agent.set(None);
                                        } else {
                                            selected_agent.set(Some(name));
                                        }
                                    },
                                }
                            }
                        }
                    }
                    // Envelopes / Events
                    div { class: "network-panel network-panel-wide",
                        div { class: "panel-header",
                            if let Some(ref agent_name) = *selected_agent.read() {
                                "Envelopes from {agent_name}"
                            } else {
                                "Recent Events"
                            }
                        }
                        div { class: "envelope-list",
                            if let Some(ref agent_name) = *selected_agent.read() {
                                for env in snap.envelopes.iter().filter(|e| &e.author == agent_name.as_str()) {
                                    EnvelopeCard { key: "{env.id}", envelope: env.clone() }
                                }
                            } else {
                                for event in events.read().iter() {
                                    EventCard { key: "{event.timestamp:?}-{event.kind}", event: event.clone() }
                                }
                                if events.read().is_empty() {
                                    div { class: "network-empty", "No events yet. Assert Lojban above to create gossip." }
                                }
                            }
                        }
                    }
                }
                // Contradictions
                if !snap.contradictions.is_empty() {
                    ContradictionsPanel { contradictions: snap.contradictions.clone(), network_snapshot }
                }
            } else {
                div { class: "network-empty",
                    "Connecting to gossip network..."
                }
            }
        }
    }
}

#[component]
fn AgentCard(agent: AgentData, selected: bool, on_select: EventHandler<String>) -> Element {
    let total = agent.stance_counts.deduced
        + agent.stance_counts.expected
        + agent.stance_counts.opinion
        + agent.stance_counts.hearsay;
    let card_class = if selected {
        "agent-card agent-card-selected"
    } else if agent.is_local {
        "agent-card agent-card-local"
    } else {
        "agent-card"
    };
    let name = agent.name.clone();

    rsx! {
        div {
            class: "{card_class}",
            onclick: move |_| on_select.call(name.clone()),
            div { class: "agent-name",
                if agent.is_local {
                    span { class: "agent-local-badge", "LOCAL" }
                }
                "{agent.name}"
            }
            div { class: "agent-stats",
                span { class: "agent-stat",
                    b { "{agent.envelope_count}" }
                    " env"
                }
                if total > 0 {
                    span { class: "stance-bar",
                        if agent.stance_counts.deduced > 0 {
                            span {
                                class: "stance-segment stance-deduced",
                                style: "width: {(agent.stance_counts.deduced as f64 / total as f64 * 100.0) as u32}%",
                                title: "ja'o (deduced): {agent.stance_counts.deduced}",
                            }
                        }
                        if agent.stance_counts.expected > 0 {
                            span {
                                class: "stance-segment stance-expected",
                                style: "width: {(agent.stance_counts.expected as f64 / total as f64 * 100.0) as u32}%",
                                title: "ba'a (expected): {agent.stance_counts.expected}",
                            }
                        }
                        if agent.stance_counts.opinion > 0 {
                            span {
                                class: "stance-segment stance-opinion",
                                style: "width: {(agent.stance_counts.opinion as f64 / total as f64 * 100.0) as u32}%",
                                title: "pe'i (opinion): {agent.stance_counts.opinion}",
                            }
                        }
                        if agent.stance_counts.hearsay > 0 {
                            span {
                                class: "stance-segment stance-hearsay",
                                style: "width: {(agent.stance_counts.hearsay as f64 / total as f64 * 100.0) as u32}%",
                                title: "ti'e (hearsay): {agent.stance_counts.hearsay}",
                            }
                        }
                    }
                }
            }
            if !agent.topics.is_empty() {
                div { class: "agent-topics",
                    for topic in agent.topics.iter().take(5) {
                        span { class: "topic-tag", "{topic}" }
                    }
                }
            }
        }
    }
}

#[component]
fn EnvelopeCard(envelope: EnvelopeData) -> Element {
    let short_id = &envelope.id[..12.min(envelope.id.len())];
    let stance_class = match envelope.stance.as_str() {
        "ja'o" => "stance-badge stance-deduced",
        "ba'a" => "stance-badge stance-expected",
        "pe'i" => "stance-badge stance-opinion",
        "ti'e" => "stance-badge stance-hearsay",
        _ => "stance-badge",
    };
    let card_class = if envelope.is_quarantined {
        "envelope-card envelope-card-quarantined"
    } else if envelope.is_retraction {
        "envelope-card envelope-card-retraction"
    } else {
        "envelope-card"
    };

    rsx! {
        div { class: "{card_class}",
            div { class: "envelope-header",
                span { class: "envelope-id", "{short_id}" }
                span { class: "{stance_class}", "{envelope.stance}" }
                span { class: "envelope-author", "{envelope.author}" }
                if envelope.is_quarantined {
                    span { class: "quarantine-badge", "QUARANTINED" }
                }
                if envelope.is_retraction {
                    span { class: "retraction-badge", "RETRACTED" }
                }
            }
            if let Some(ref lojban) = envelope.lojban {
                div { class: "envelope-lojban", "{lojban}" }
            }
            if !envelope.topics.is_empty() {
                div { class: "envelope-topics",
                    for topic in envelope.topics.iter() {
                        span { class: "topic-tag", "{topic}" }
                    }
                }
            }
        }
    }
}

#[component]
fn EventCard(event: GossipEventData) -> Element {
    // The kind modifier drives the left-rule color + the CSS-drawn glyph.
    let (kind_class, label) = match event.kind.as_str() {
        "envelope" => (
            "event-card is-envelope",
            format!(
                "{} {} [{}]",
                event.author.as_deref().unwrap_or("?"),
                event.lojban.as_deref().unwrap_or(""),
                event.stance.as_deref().unwrap_or("?"),
            ),
        ),
        "contradiction" => (
            "event-card is-contradiction",
            format!(
                "Contradiction: {}",
                event.assertion.as_deref().unwrap_or("?"),
            ),
        ),
        "peer_change" => (
            "event-card is-peer",
            format!(
                "Peer {} {}",
                event.peer_id.as_deref().unwrap_or("?"),
                if event.connected.unwrap_or(false) {
                    "connected"
                } else {
                    "disconnected"
                },
            ),
        ),
        "sync" => (
            "event-card is-sync",
            format!("Sync with {}", event.peer_id.as_deref().unwrap_or("?"),),
        ),
        _ => ("event-card", event.kind.clone()),
    };

    rsx! {
        div { class: "{kind_class}",
            span { class: "event-icon" }
            span { class: "event-label", "{label}" }
        }
    }
}

#[component]
fn ContradictionsPanel(
    contradictions: Vec<ContradictionData>,
    network_snapshot: Signal<Option<NetworkSnapshotData>>,
) -> Element {
    let unresolved: Vec<&ContradictionData> =
        contradictions.iter().filter(|c| !c.resolved).collect();
    if unresolved.is_empty() {
        return rsx! {};
    }

    rsx! {
        div { class: "contradictions-panel",
            div { class: "panel-header contradictions-header",
                "Contradictions ({unresolved.len()})"
            }
            for c in unresolved.iter() {
                div { class: "contradiction-card",
                    div { class: "contradiction-info",
                        span { class: "contradiction-id", "#{c.id}" }
                        span { class: "contradiction-author", "{c.author}" }
                        span { class: "contradiction-assertion", "{c.assertion}" }
                    }
                    {
                        let cid = c.id;
                        rsx! {
                            button {
                                class: "contradiction-resolve-btn",
                                onclick: move |_| {
                                    spawn(async move {
                                        let _ = resolve_contradiction_api(cid).await;
                                        if let Ok(snap) = fetch_network_snapshot().await {
                                            network_snapshot.set(Some(snap));
                                        }
                                    });
                                },
                                "Resolve"
                            }
                        }
                    }
                }
            }
        }
    }
}

#[component]
fn ProofPanel(
    proof_text: Signal<Option<String>>,
    proof_data: Signal<Option<ProofTrace>>,
    is_busy: Signal<bool>,
) -> Element {
    let text = proof_text.read();
    let data = proof_data.read();
    let busy = *is_busy.read();

    rsx! {
        div { class: "proof-panel",
            if busy {
                div { class: "proof-busy",
                    span { class: "proof-busy__glyph", "\u{25F4}" }
                    div { class: "proof-busy__bar" }
                    "running query\u{2026}"
                }
            } else if let Some(trace_data) = data.as_ref() {
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
