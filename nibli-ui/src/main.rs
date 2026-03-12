use dioxus::prelude::*;

fn main() {
    dioxus::launch(App);
}

#[derive(Clone, Copy, PartialEq)]
enum ActiveTab {
    Source,
    Lojban,
    BackTranslation,
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
                QueryBar {}
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
