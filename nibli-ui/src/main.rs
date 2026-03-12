use dioxus::prelude::*;
use gloo_net::http::Request;
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

// ── Command execution ──

async fn execute_command(input: &str) -> OutputEntry {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return OutputEntry {
            input: input.to_string(),
            result: String::new(),
            is_error: false,
            proof_trace: None,
        };
    }

    if let Some(text) = trimmed.strip_prefix("?!") {
        execute_proof_query(trimmed, text.trim()).await
    } else if let Some(text) = trimmed.strip_prefix('?') {
        execute_query(trimmed, text.trim()).await
    } else {
        execute_assert(trimmed).await
    }
}

async fn execute_assert(text: &str) -> OutputEntry {
    let query = r#"mutation($input: String!) { assertText(input: $input) { factId error } }"#;
    match graphql_mutate(query, text).await {
        Ok(data) => {
            let r = &data["assertText"];
            if let Some(err) = r["error"].as_str() {
                OutputEntry {
                    input: text.to_string(),
                    result: err.to_string(),
                    is_error: true,
                    proof_trace: None,
                }
            } else {
                let fact_id = r["factId"].as_u64().unwrap_or(0);
                OutputEntry {
                    input: text.to_string(),
                    result: format!("Fact #{} asserted", fact_id),
                    is_error: false,
                    proof_trace: None,
                }
            }
        }
        Err(e) => OutputEntry {
            input: text.to_string(),
            result: e,
            is_error: true,
            proof_trace: None,
        },
    }
}

async fn execute_query(display_input: &str, text: &str) -> OutputEntry {
    let query = r#"mutation($input: String!) { queryText(input: $input) { holds error } }"#;
    match graphql_mutate(query, text).await {
        Ok(data) => {
            let r = &data["queryText"];
            if let Some(err) = r["error"].as_str() {
                OutputEntry {
                    input: display_input.to_string(),
                    result: err.to_string(),
                    is_error: true,
                    proof_trace: None,
                }
            } else {
                let holds = r["holds"].as_bool().unwrap_or(false);
                OutputEntry {
                    input: display_input.to_string(),
                    result: if holds {
                        "TRUE".to_string()
                    } else {
                        "FALSE".to_string()
                    },
                    is_error: false,
                    proof_trace: None,
                }
            }
        }
        Err(e) => OutputEntry {
            input: display_input.to_string(),
            result: e,
            is_error: true,
            proof_trace: None,
        },
    }
}

async fn execute_proof_query(display_input: &str, text: &str) -> OutputEntry {
    let query = r#"mutation($input: String!) { queryTextWithProof(input: $input) { holds proofTrace error } }"#;
    match graphql_mutate(query, text).await {
        Ok(data) => {
            let r = &data["queryTextWithProof"];
            if let Some(err) = r["error"].as_str() {
                OutputEntry {
                    input: display_input.to_string(),
                    result: err.to_string(),
                    is_error: true,
                    proof_trace: None,
                }
            } else {
                let holds = r["holds"].as_bool().unwrap_or(false);
                let trace = r["proofTrace"].as_str().map(|s| s.to_string());
                OutputEntry {
                    input: display_input.to_string(),
                    result: if holds {
                        "TRUE".to_string()
                    } else {
                        "FALSE".to_string()
                    },
                    is_error: false,
                    proof_trace: trace,
                }
            }
        }
        Err(e) => OutputEntry {
            input: display_input.to_string(),
            result: e,
            is_error: true,
            proof_trace: None,
        },
    }
}

// ── Components ──

#[component]
fn App() -> Element {
    let output_log: Signal<Vec<OutputEntry>> = use_signal(Vec::new);
    let proof_text: Signal<Option<String>> = use_signal(|| None);

    rsx! {
        document::Link { rel: "stylesheet", href: asset!("/assets/style.css") }
        div { class: "app",
            div { class: "main-row",
                div { class: "col-tabs",
                    SourceTabs {}
                }
                div { class: "col-proof",
                    ProofPanel { proof_text }
                }
            }
            div { class: "query-row",
                div { class: "query-section",
                    div { class: "query-header",
                        StatusBadge {}
                        QueryBar { output_log, proof_text }
                    }
                    OutputLog { output_log }
                }
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
fn QueryBar(output_log: Signal<Vec<OutputEntry>>, proof_text: Signal<Option<String>>) -> Element {
    let mut query_text = use_signal(|| String::new());
    let mut submitting = use_signal(|| false);

    let submit = move |_: Event<MouseData>| {
        let text = query_text.read().clone();
        if text.trim().is_empty() || *submitting.read() {
            return;
        }
        submitting.set(true);
        query_text.set(String::new());

        spawn(async move {
            let entry = execute_command(&text).await;
            if let Some(ref trace) = entry.proof_trace {
                proof_text.set(Some(trace.clone()));
            }
            output_log.write().push(entry);
            submitting.set(false);
        });
    };

    let on_keydown = move |e: KeyboardEvent| {
        if e.key() == Key::Enter {
            let text = query_text.read().clone();
            if text.trim().is_empty() || *submitting.read() {
                return;
            }
            submitting.set(true);
            query_text.set(String::new());

            spawn(async move {
                let entry = execute_command(&text).await;
                if let Some(ref trace) = entry.proof_trace {
                    proof_text.set(Some(trace.clone()));
                }
                output_log.write().push(entry);
                submitting.set(false);
            });
        }
    };

    rsx! {
        div { class: "query-bar",
            input {
                class: "query-input",
                r#type: "text",
                placeholder: "Assert facts or query with ? prefix...",
                value: "{query_text}",
                oninput: move |e| query_text.set(e.value()),
                onkeydown: on_keydown,
                disabled: *submitting.read(),
            }
            button {
                class: "query-btn",
                onclick: submit,
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
fn SourceTabs() -> Element {
    let mut active_tab = use_signal(|| ActiveTab::Source);
    let mut source_text = use_signal(|| String::new());
    let mut lojban_text = use_signal(|| String::new());

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
                        button { class: "translate-btn", "Translate" }
                    },
                    ActiveTab::Lojban => rsx! {
                        textarea {
                            class: "lojban-input",
                            placeholder: "Lojban translation will appear here...",
                            value: "{lojban_text}",
                            oninput: move |e| lojban_text.set(e.value()),
                        }
                    },
                    ActiveTab::BackTranslation => rsx! {
                        pre { class: "back-translation",
                            "Back-translation will appear here..."
                        }
                    },
                }
            }
        }
    }
}

#[component]
fn ProofPanel(proof_text: Signal<Option<String>>) -> Element {
    let text = proof_text.read();

    rsx! {
        div { class: "proof-panel",
            if let Some(trace) = text.as_ref() {
                pre { class: "proof-trace", "{trace}" }
            } else {
                div { class: "proof-placeholder",
                    "Run a ?! query to see proof trace"
                }
            }
        }
    }
}
