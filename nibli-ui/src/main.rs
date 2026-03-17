use dioxus::prelude::*;
use gloo_net::http::Request;
use nibli_protocol::{KbStatus, ProofRule, ProofTrace};
use serde::Deserialize;

fn main() {
    dioxus::launch(App);
}

const GRAPHQL_URL: &str = "http://localhost:8081/graphql";

// ── Types ──

#[derive(Clone, Copy, PartialEq)]
enum ActiveTab {
    Source,
    Lojban,
    BackTranslation,
}

#[derive(Clone, Copy, PartialEq)]
enum ConnectionStatus {
    Checking,
    Connected,
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

async fn check_server_status() -> ConnectionStatus {
    let body = serde_json::json!({"query": "{ status { ready } }"});
    match Request::post(GRAPHQL_URL)
        .header("Content-Type", "application/json")
        .body(body.to_string())
    {
        Ok(req) => match req.send().await {
            Ok(resp) => match resp.json::<GraphQLResponse>().await {
                Ok(gql) => {
                    let ready = gql
                        .data
                        .as_ref()
                        .and_then(|d| d.get("status"))
                        .and_then(|s| s.get("ready"))
                        .and_then(|r| r.as_bool())
                        .unwrap_or(false);
                    if ready {
                        ConnectionStatus::Connected
                    } else {
                        ConnectionStatus::Disconnected
                    }
                }
                Err(_) => ConnectionStatus::Disconnected,
            },
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

async fn graphql_mutate_kb(
    query: &str,
    kb: &str,
    q: &str,
) -> Result<serde_json::Value, String> {
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
    let gql = r#"mutation($kb: String!, $query: String!) { queryWithKb(kb: $kb, query: $query) { holds error kbStatus { asserted errors skipped lineResults { lineNumber text success factId error } } } }"#;
    match graphql_mutate_kb(gql, kb, query_text).await {
        Ok(data) => {
            let r = &data["queryWithKb"];
            let kb_status = parse_kb_status(r);
            if let Some(err) = r["error"].as_str() {
                OutputEntry {
                    input: format!("? {}", query_text),
                    result: err.to_string(),
                    is_error: true,
                    proof_trace: None,
                    proof_trace_data: None,
                    kb_status,
                }
            } else {
                let holds = r["holds"].as_bool().unwrap_or(false);
                OutputEntry {
                    input: format!("? {}", query_text),
                    result: if holds {
                        "TRUE".to_string()
                    } else {
                        "FALSE".to_string()
                    },
                    is_error: false,
                    proof_trace: None,
                    proof_trace_data: None,
                    kb_status,
                }
            }
        }
        Err(e) => OutputEntry {
            input: format!("? {}", query_text),
            result: e,
            is_error: true,
            proof_trace: None,
            proof_trace_data: None,
            kb_status: None,
        },
    }
}

async fn execute_proof_query(kb: &str, query_text: &str) -> OutputEntry {
    let gql = r#"mutation($kb: String!, $query: String!) { queryWithKbProof(kb: $kb, query: $query) { holds proofTrace proofTraceJson error kbStatus { asserted errors skipped lineResults { lineNumber text success factId error } } } }"#;
    match graphql_mutate_kb(gql, kb, query_text).await {
        Ok(data) => {
            let r = &data["queryWithKbProof"];
            let kb_status = parse_kb_status(r);
            if let Some(err) = r["error"].as_str() {
                OutputEntry {
                    input: format!("?! {}", query_text),
                    result: err.to_string(),
                    is_error: true,
                    proof_trace: None,
                    proof_trace_data: None,
                    kb_status,
                }
            } else {
                let holds = r["holds"].as_bool().unwrap_or(false);
                let trace = r["proofTrace"].as_str().map(|s| s.to_string());
                let trace_data = r["proofTraceJson"]
                    .as_str()
                    .and_then(ProofTrace::from_json);
                OutputEntry {
                    input: format!("?! {}", query_text),
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
            input: format!("?! {}", query_text),
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
    let output_log: Signal<Vec<OutputEntry>> = use_signal(Vec::new);
    let proof_text: Signal<Option<String>> = use_signal(|| None);
    let proof_data: Signal<Option<ProofTrace>> = use_signal(|| None);
    let lojban_text: Signal<String> = use_signal(|| String::new());
    let kb_status: Signal<Option<KbStatus>> = use_signal(|| None);

    rsx! {
        document::Link { rel: "stylesheet", href: asset!("/assets/style.css") }
        div { class: "app",
            div { class: "main-row",
                div { class: "col-tabs",
                    SourceTabs { lojban_text, kb_status }
                }
                div { class: "col-proof",
                    ProofPanel { proof_text, proof_data }
                }
            }
            div { class: "query-row",
                div { class: "query-section",
                    div { class: "query-header",
                        StatusBadge {}
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
        ConnectionStatus::Connected => ("Connected", "status-badge connected"),
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
) -> Element {
    let mut query_text = use_signal(|| String::new());
    let mut submitting = use_signal(|| false);

    let mut do_submit = move || {
        let text = query_text.read().clone();
        if text.trim().is_empty() || *submitting.read() {
            return;
        }
        submitting.set(true);
        query_text.set(String::new());

        spawn(async move {
            let kb = lojban_text.read().clone();
            let trimmed = text.trim();

            // Determine if this is a proof query (?!) or regular query (?)
            let entry = if let Some(q) = trimmed.strip_prefix("?!") {
                execute_proof_query(&kb, q.trim()).await
            } else if let Some(q) = trimmed.strip_prefix('?') {
                execute_query(&kb, q.trim()).await
            } else {
                // No prefix — treat as regular query (query bar is query-only)
                execute_query(&kb, trimmed).await
            };

            if let Some(ref trace) = entry.proof_trace {
                proof_text.set(Some(trace.clone()));
            }
            if let Some(ref data) = entry.proof_trace_data {
                proof_data.set(Some(data.clone()));
            }
            kb_status.set(entry.kb_status.clone());
            output_log.write().push(entry);
            submitting.set(false);
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
            input {
                class: "query-input",
                r#type: "text",
                placeholder: "Enter Lojban query (use ?! prefix for proof trace)...",
                value: "{query_text}",
                oninput: move |e| query_text.set(e.value()),
                onkeydown: on_keydown,
                disabled: *submitting.read(),
            }
            button {
                class: "query-btn",
                onclick: submit_click,
                disabled: *submitting.read(),
                if *submitting.read() { "..." } else { "Query" }
            }
        }
    }
}

#[component]
fn OutputLog(output_log: Signal<Vec<OutputEntry>>) -> Element {
    let entries = output_log.read();

    rsx! {
        div { class: "output-log",
            for (i, entry) in entries.iter().enumerate() {
                div {
                    key: "{i}",
                    class: if entry.is_error { "output-entry output-error" } else { "output-entry" },
                    span { class: "output-input", "> {entry.input}" }
                    span { class: "output-result", "  {entry.result}" }
                }
            }
        }
    }
}

#[component]
fn SourceTabs(lojban_text: Signal<String>, kb_status: Signal<Option<KbStatus>>) -> Element {
    let mut active_tab = use_signal(|| ActiveTab::Source);
    let mut source_text = use_signal(|| String::new());
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

    let on_translate = move |_: Event<MouseData>| {
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
                    ActiveTab::Source => rsx! {
                        textarea {
                            class: "source-input",
                            placeholder: "Enter English text...",
                            value: "{source_text}",
                            oninput: move |e| source_text.set(e.value()),
                        }
                        if let Some(err) = translate_error.read().as_ref() {
                            div { class: "translate-error", "{err}" }
                        }
                        button {
                            class: "translate-btn",
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
                    "Run a ?! query to see proof trace"
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

    let result_class = if holds { "proof-result-true" } else { "proof-result-false" };
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
