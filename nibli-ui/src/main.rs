use dioxus::prelude::*;
use gloo_net::http::Request;
use serde::Deserialize;

fn main() {
    dioxus::launch(App);
}

const GRAPHQL_URL: &str = "http://localhost:8081/graphql";

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

#[derive(Deserialize)]
struct GraphQLResponse {
    data: Option<StatusData>,
}

#[derive(Deserialize)]
struct StatusData {
    status: StatusResult,
}

#[derive(Deserialize)]
struct StatusResult {
    ready: bool,
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
                    if gql.data.map_or(false, |d| d.status.ready) {
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

#[component]
fn App() -> Element {
    rsx! {
        document::Link { rel: "stylesheet", href: asset!("/assets/style.css") }
        div { class: "app",
            div { class: "main-row",
                div { class: "col-tabs",
                    SourceTabs {}
                }
                div { class: "col-proof",
                    ProofPanel {}
                }
            }
            div { class: "query-row",
                StatusBadge {}
                QueryBar {}
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
fn ProofPanel() -> Element {
    rsx! {
        div { class: "proof-placeholder",
            "Run a query to see proof trace"
        }
    }
}

#[component]
fn QueryBar() -> Element {
    let mut query_text = use_signal(|| String::new());

    rsx! {
        div { class: "query-bar",
            input {
                class: "query-input",
                r#type: "text",
                placeholder: "Assert facts or query with ? prefix...",
                value: "{query_text}",
                oninput: move |e| query_text.set(e.value()),
            }
            button { class: "query-btn", "Query" }
        }
    }
}
