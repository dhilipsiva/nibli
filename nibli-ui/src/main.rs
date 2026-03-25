use dioxus::prelude::*;
use gloo_net::http::Request;
use nibli_protocol::{KbStatus, ProofRule, ProofTrace};
use serde::Deserialize;

fn main() {
    dioxus::launch(App);
}

const GRAPHQL_URL: &str = "http://localhost:8081/graphql";
const READY_URL: &str = "http://localhost:8081/readyz";
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

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
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
    let gql = r#"mutation($kb: String!, $query: String!) { queryWithKb(kb: $kb, query: $query) { holds proofTrace proofTraceJson error kbStatus { asserted errors skipped lineResults { lineNumber text success factId error } } } }"#;
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
                let holds = r["holds"].as_bool().unwrap_or(false);
                let trace = r["proofTrace"].as_str().map(|s| s.to_string());
                let trace_data = r["proofTraceJson"].as_str().and_then(ProofTrace::from_json);
                OutputEntry {
                    input: query_text.to_string(),
                    result: if holds {
                        "TRUE".to_string()
                    } else {
                        "FALSE".to_string()
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

    rsx! {
        document::Link { rel: "stylesheet", href: asset!("/assets/style.css") }
        div { class: "app", tabindex: "0", onkeydown: on_global_keydown,
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
                        StatusBadge {}
                        QueryBar { output_log, proof_text, proof_data, lojban_text, kb_status, is_busy }
                    }
                    OutputLog { output_log }
                }
            }
        }
    }
}

#[component]
fn KbStatusBar(kb_status: Signal<Option<KbStatus>>) -> Element {
    let status = kb_status.read();
    let Some(ref s) = *status else {
        return rsx! {};
    };

    let status_class = if s.errors > 0 {
        "kb-status-bar kb-status-warn"
    } else {
        "kb-status-bar kb-status-ok"
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

    rsx! {
        div { class: "{status_class}",
            if has_errors {
                details { class: "kb-status-details",
                    summary { class: "kb-status-summary", "{summary_text}" }
                    div { class: "kb-line-results",
                        for lr in s.line_results.iter() {
                            div {
                                key: "{lr.line_number}",
                                class: if lr.success { "kb-line-result kb-line-ok" } else { "kb-line-result kb-line-error" },
                                span { class: "kb-line-num", "L{lr.line_number}" }
                                if lr.success {
                                    span { class: "kb-line-icon", "✓" }
                                } else {
                                    span { class: "kb-line-icon", "✗" }
                                }
                                span { class: "kb-line-text", "{lr.text}" }
                                if let Some(ref err) = lr.error {
                                    span { class: "kb-line-err", "{err}" }
                                }
                            }
                        }
                    }
                }
            } else {
                span { class: "kb-status-summary", "{summary_text}" }
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
    let btn_class = if busy {
        "query-btn btn-busy"
    } else {
        "query-btn"
    };

    rsx! {
        div { class: "query-bar",
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
                if busy { "\u{23F3}" } else { "Run" }
            }
        }
    }
}

#[component]
fn OutputLog(output_log: Signal<Vec<OutputEntry>>) -> Element {
    let entries = output_log.read();
    let is_empty = entries.is_empty();

    rsx! {
        div { class: "output-log-container",
            if !is_empty {
                div { class: "output-log-header",
                    button {
                        class: "output-clear-btn",
                        onclick: move |_| output_log.set(vec![]),
                        "Clear"
                        kbd { class: "kbd-hint", "Ctrl+L" }
                    }
                }
            }
            div { id: "output-log", class: "output-log",
                for (i, entry) in entries.iter().enumerate() {
                    div {
                        key: "{i}",
                        class: if entry.is_error { "output-entry output-error" } else { "output-entry" },
                        span { class: "output-input", "> {entry.input}" }
                        if entry.is_error {
                            ErrorDisplay { message: entry.result.clone() }
                        } else {
                            span { class: "output-result", "  {entry.result}" }
                        }
                    }
                }
            }
        }
    }
}

/// Parses error strings for known prefixes and renders with distinct icons/colors.
#[component]
fn ErrorDisplay(message: String) -> Element {
    let (icon, css_class, body) = if let Some(rest) = message.strip_prefix("[Syntax Error]") {
        ("\u{1F524}", "error-syntax", rest.trim())
    } else if let Some(rest) = message.strip_prefix("[Semantic Error]") {
        ("\u{1F517}", "error-semantic", rest.trim())
    } else if let Some(rest) = message.strip_prefix("[Reasoning Error]") {
        ("\u{1F50D}", "error-reasoning", rest.trim())
    } else if let Some(rest) = message.strip_prefix("[Backend Error]") {
        ("\u{2699}\u{FE0F}", "error-backend", rest.trim())
    } else if let Some(rest) = message.strip_prefix("[Limit]") {
        ("\u{23F1}\u{FE0F}", "error-limit", rest.trim())
    } else {
        ("\u{274C}", "error-generic", message.as_str())
    };

    rsx! {
        span { class: "output-error-display {css_class}",
            span { class: "error-icon", "{icon}" }
            span { class: "error-message", "  {body}" }
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
            smuni_dictionary::back_translate(&text)
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
                        button {
                            class: if *translating.read() { "translate-btn btn-busy" } else { "translate-btn" },
                            onclick: on_translate,
                            disabled: *translating.read(),
                            if *translating.read() { "Translating..." } else { "Translate" }
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
                    ActiveTab::BackTranslation => rsx! {
                        pre { class: "back-translation",
                            if back_translation.read().is_empty() {
                                "Type Lojban text in the Lojban tab to see back-translation..."
                            } else {
                                "{back_translation}"
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
                    class: if *gossip_busy.read() { "gossip-btn btn-busy" } else { "gossip-btn" },
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
                    span { class: "network-stat",
                        strong { "{snap.agents.len()}" }
                        " agents"
                    }
                    span { class: "network-stat",
                        strong { "{snap.total_facts}" }
                        " active facts"
                    }
                    span { class: "network-stat",
                        strong { "{snap.envelopes.len()}" }
                        " envelopes"
                    }
                    span { class: "network-stat",
                        strong { "{snap.contradictions.iter().filter(|c| !c.resolved).count()}" }
                        " contradictions"
                    }
                    if *loading.read() {
                        span { class: "network-refresh", "..." }
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
                span { class: "agent-stat", "{agent.envelope_count} env" }
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
        "envelope-card envelope-quarantined"
    } else if envelope.is_retraction {
        "envelope-card envelope-retraction"
    } else {
        "envelope-card"
    };

    rsx! {
        div { class: "{card_class}",
            div { class: "envelope-header",
                span { class: "envelope-id", "{short_id}..." }
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
    let (icon, label) = match event.kind.as_str() {
        "envelope" => (
            ">>",
            format!(
                "{} {} [{}]",
                event.author.as_deref().unwrap_or("?"),
                event.lojban.as_deref().unwrap_or(""),
                event.stance.as_deref().unwrap_or("?"),
            ),
        ),
        "contradiction" => (
            "!!",
            format!(
                "Contradiction: {}",
                event.assertion.as_deref().unwrap_or("?"),
            ),
        ),
        "peer_change" => (
            "--",
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
            "<>",
            format!("Sync with {}", event.peer_id.as_deref().unwrap_or("?"),),
        ),
        _ => ("??", event.kind.clone()),
    };

    rsx! {
        div { class: "event-card",
            span { class: "event-icon", "{icon}" }
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
                div { class: "proof-placeholder proof-busy",
                    "Running query\u{2026}"
                }
            } else if let Some(trace_data) = data.as_ref() {
                div { class: "proof-tree-container",
                    ProofTreeView { trace: trace_data.clone() }
                }
            } else if let Some(trace) = text.as_ref() {
                pre { class: "proof-trace", "{trace}" }
            } else {
                div { class: "proof-placeholder",
                    "No proof trace yet."
                    br {}
                    span { class: "proof-hint", "Run a query to see the proof trace" }
                    br {}
                    span { class: "proof-hint", "Example: " }
                    code { class: "proof-hint-code", "la .adam. cu citka" }
                }
            }
        }
    }
}

#[component]
fn ProofTreeView(trace: ProofTrace) -> Element {
    let root_idx = trace.root as usize;
    if root_idx >= trace.steps.len() {
        return rsx! { div { class: "proof-error", "Invalid proof trace: root index out of bounds" } };
    }

    rsx! {
        div { class: "proof-tree",
            ProofNodeView { trace: trace.clone(), step_idx: trace.root, depth: 0 }
        }
    }
}

#[component]
fn ProofNodeView(trace: ProofTrace, step_idx: u32, depth: u32) -> Element {
    let idx = step_idx as usize;
    if idx >= trace.steps.len() {
        return rsx! { span { class: "proof-error", "?" } };
    }

    let step = &trace.steps[idx];
    let rule = &step.rule;
    let holds = step.holds;
    let children = &step.children;
    let css_class = rule.css_class();
    let icon = rule.icon();
    let label = rule.label();
    let auto_open = depth < 3;

    let result_class = if holds {
        "proof-result-true"
    } else {
        "proof-result-false"
    };
    let result_label = if holds { "TRUE" } else { "FALSE" };

    // ProofRef is a leaf node — render inline, no expand
    if matches!(rule, ProofRule::ProofRef { .. }) {
        return rsx! {
            div { class: "proof-node proof-ref-node",
                span { class: "proof-icon proof-ref", "{icon}" }
                span { class: "proof-label proof-ref", "{label}" }
            }
        };
    }

    if children.is_empty() {
        // Leaf node — no details/summary needed
        rsx! {
            div { class: "proof-node proof-leaf {css_class}",
                span { class: "proof-icon", "{icon}" }
                span { class: "proof-label", "{label}" }
                span { class: "proof-result {result_class}", "{result_label}" }
            }
        }
    } else {
        // Branch node — use details/summary
        rsx! {
            details { class: "proof-node {css_class}", open: auto_open,
                summary { class: "proof-summary",
                    span { class: "proof-icon", "{icon}" }
                    span { class: "proof-label", "{label}" }
                    span { class: "proof-result {result_class}", "{result_label}" }
                }
                div { class: "proof-children",
                    for child_idx in children.iter() {
                        ProofNodeView {
                            key: "{child_idx}",
                            trace: trace.clone(),
                            step_idx: *child_idx,
                            depth: depth + 1,
                        }
                    }
                }
            }
        }
    }
}
