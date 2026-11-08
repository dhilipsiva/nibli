//! Nibli Transparency Triad web UI (Dioxus).
//!
//! A standalone, in-browser interface with three tabs: Source (plain English,
//! optionally FORMALIZED into the KB language by a bring-your-own-key LLM),
//! the KB tab (the formal nibli KR encoding, with per-line validation), and
//! Back-translation (structure-exposing English gloss). A bottom query bar runs proof-queries.
//! The reasoning engine (nibli-kr → nibli-semantics → nibli-reason) is compiled into the
//! WASM bundle and runs entirely client-side (mirrors `nibli-wasm`). The ONLY
//! network call is the optional Formalize step, sent directly from the browser
//! to the user's chosen LLM provider — the client lives in `nibli_formalize::llm`
//! (the single source of truth); nibli-ui only wraps it in a `Settings`
//! bundle. nibli itself has no server. ("Formalize", never "compile": the LLM
//! step is interpretive formalization behind gates; "compile" is reserved for
//! the deterministic KB→logic step.)

use dioxus::prelude::*;
use nibli_protocol::{KbStatus, LineResult, ProofTrace};

mod examples;
mod review;
use review::{ReviewState, Snapshot};

const ENGINE_BUILD: &str = env!("NIBLI_BUILD_ID");
const REVIEW_PROFILE: bool = false;
use examples::EXAMPLES;
use nibli_formalize::llm::{LlmConfig, Provider};

fn main() {
    dioxus::launch(App);
}

/// IR-driven back-translation of the (multi-line) KB tab, computed entirely
/// client-side: each non-comment line is parsed + compiled to FOL and rendered as
/// structure-exposing English by `nibli-render` (IR-level). A line that does
/// not compile falls back to the raw line itself, so the panel always shows
/// something. This is the "What Nibli Understood" reading.
fn back_translate_ir(kb: &str) -> String {
    kb.lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                None
            } else {
                Some(render_kb_line(trimmed))
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn render_kb_line(line: &str) -> String {
    match nibli_session::CoreSession::new().compile_text(line) {
        Ok(buf) => nibli_render::render_logic_buffer(&buf, nibli_render::Register::Spec),
        Err(error) => format!("Cannot compile this line: {error}"),
    }
}

/// Autocomplete menu — items come only from [`nibli_kr::complete`] (same as REPL).
#[derive(Clone, Default, PartialEq)]
struct AcMenu {
    open: bool,
    items: Vec<nibli_kr::complete::Completion>,
    selected: usize,
    span_start: usize,
    span_end: usize,
}

async fn dom_cursor(editor_id: &str) -> usize {
    let id = serde_json::to_string(editor_id).unwrap_or_else(|_| "\"\"".into());
    document::eval(&format!(
        "return document.getElementById({id})?.selectionStart ?? 0;"
    ))
    .await
    .ok()
    .and_then(|v| v.as_f64())
    .map(|n| n as usize)
    .unwrap_or(0)
}

async fn dom_set_cursor(editor_id: &str, cursor: usize) {
    let id = serde_json::to_string(editor_id).unwrap_or_else(|_| "\"\"".into());
    let _ = document::eval(&format!(
        r#"
        const ta = document.getElementById({id});
        if (ta) {{
          ta.focus();
          const c = Math.min({cursor}, (ta.value || '').length);
          ta.setSelectionRange(c, c);
        }}
        return '';
        "#
    ))
    .await;
}

fn run_complete(line: &str, cursor: usize, for_tab: bool) -> nibli_kr::complete::CompleteResult {
    use nibli_kr::complete::{CompleteOpts, complete};
    let opts = CompleteOpts {
        include_repl_commands: false,
        limit: 30,
        min_prefix: if for_tab { 1 } else { 2 },
        extra: &[],
    };
    let r = complete(line, cursor, opts);
    if r.items.is_empty() && for_tab {
        complete(
            line,
            cursor,
            CompleteOpts {
                min_prefix: 0,
                ..opts
            },
        )
    } else {
        r
    }
}

fn ac_from_result(r: nibli_kr::complete::CompleteResult) -> AcMenu {
    if r.items.is_empty() {
        AcMenu::default()
    } else {
        AcMenu {
            open: true,
            selected: 0,
            span_start: r.span_start,
            span_end: r.span_end,
            items: r.items,
        }
    }
}

fn apply_ac_item(text: &str, menu: &AcMenu, idx: usize) -> Option<(String, usize)> {
    let item = menu.items.get(idx)?;
    nibli_kr::complete::apply_replacement(text, menu.span_start, menu.span_end, &item.value)
}

/// Multi-line nibli KR editor: highlight layer + shared autocomplete.
#[component]
fn KrMultilineEditor(
    value: String,
    readonly: bool,
    placeholder: String,
    on_change: EventHandler<String>,
) -> Element {
    let spans = nibli_kr::highlight::css_spans(&value);
    let pad_key = spans.len();
    let mut ac = use_signal(AcMenu::default);
    let mut pending_cursor = use_signal(|| None::<usize>);
    let editor_id = "kb-kr-editor";

    use_effect(move || {
        let pending = pending_cursor();
        if let Some(c) = pending {
            pending_cursor.set(None);
            spawn(async move {
                dom_set_cursor(editor_id, c).await;
            });
        }
    });

    let mut commit = move |new_line: String, cur: usize| {
        pending_cursor.set(Some(cur));
        ac.set(AcMenu::default());
        on_change.call(new_line);
    };

    let value_for_pick = value.clone();

    rsx! {
        div { class: "kr-editor",
            pre {
                id: "kb-kr-highlight",
                class: "kr-editor__highlight",
                aria_hidden: "true",
                code {
                    for (i, (cls, text)) in spans.into_iter().enumerate() {
                        span { key: "{i}", class: "{cls}", "{text}" }
                    }
                    if value.is_empty() || !value.ends_with('\n') {
                        span { key: "{pad_key}", class: "tok-ws", "\n" }
                    }
                }
            }
            textarea {
                id: "{editor_id}",
                class: "kr-editor__input kb-input",
                placeholder: "{placeholder}",
                value: "{value}",
                readonly: readonly,
                spellcheck: false,
                oninput: move |e| {
                    let text = e.value();
                    on_change.call(text.clone());
                    if readonly { return; }
                    let was_open = ac().open;
                    spawn(async move {
                        let pos = dom_cursor(editor_id).await;
                        let r = run_complete(&text, pos, false);
                        if was_open || !r.items.is_empty() {
                            ac.set(ac_from_result(r));
                        }
                    });
                },
                onkeydown: move |e| {
                    if readonly { return; }
                    let menu = ac();
                    let key = e.key();
                    let text = value.clone();
                    match key {
                        Key::Escape if menu.open => {
                            e.prevent_default();
                            ac.set(AcMenu::default());
                        }
                        Key::ArrowDown if menu.open && !menu.items.is_empty() => {
                            e.prevent_default();
                            let mut m = menu;
                            m.selected = (m.selected + 1) % m.items.len();
                            ac.set(m);
                        }
                        Key::ArrowUp if menu.open && !menu.items.is_empty() => {
                            e.prevent_default();
                            let mut m = menu;
                            m.selected = (m.selected + m.items.len() - 1) % m.items.len();
                            ac.set(m);
                        }
                        Key::Enter if menu.open && !menu.items.is_empty() => {
                            e.prevent_default();
                            if let Some((n, c)) = apply_ac_item(&text, &menu, menu.selected) {
                                commit(n, c);
                            }
                        }
                        Key::Tab => {
                            e.prevent_default();
                            if menu.open && !menu.items.is_empty() {
                                if let Some((n, c)) = apply_ac_item(&text, &menu, menu.selected) {
                                    commit(n, c);
                                }
                            } else {
                                let mut commit = commit;
                                spawn(async move {
                                    let pos = dom_cursor(editor_id).await;
                                    let r = run_complete(&text, pos, true);
                                    if r.items.len() == 1 {
                                        if let Some((n, c)) = r.apply(&text, 0) {
                                            commit(n, c);
                                        }
                                    } else {
                                        ac.set(ac_from_result(r));
                                    }
                                });
                            }
                        }
                        Key::Character(ref ch) if ch == " " && e.modifiers().ctrl() => {
                            e.prevent_default();
                            spawn(async move {
                                let pos = dom_cursor(editor_id).await;
                                ac.set(ac_from_result(run_complete(&text, pos, true)));
                            });
                        }
                        _ => {}
                    }
                },
                onscroll: move |_| {
                    spawn(async move {
                        let _ = document::eval(
                            r#"
                            const ta = document.getElementById('kb-kr-editor');
                            const hl = document.getElementById('kb-kr-highlight');
                            if (ta && hl) {
                              hl.scrollTop = ta.scrollTop;
                              hl.scrollLeft = ta.scrollLeft;
                            }
                            return '';
                            "#,
                        )
                        .await;
                    });
                },
                onblur: move |_| {
                    spawn(async move {
                        let _ = document::eval(
                            "return await new Promise(r => setTimeout(() => r(''), 150));",
                        )
                        .await;
                        ac.set(AcMenu::default());
                    });
                },
            }
            if ac().open && !ac().items.is_empty() {
                KrAcDropdown {
                    menu: ac(),
                    on_pick: move |idx| {
                        let menu = ac();
                        if let Some((n, c)) = apply_ac_item(&value_for_pick, &menu, idx) {
                            commit(n, c);
                        }
                    },
                }
            }
        }
    }
}

/// Single-line KR field (query bar): highlight + same autocomplete engine.
#[component]
fn KrLineEditor(
    id: String,
    value: String,
    placeholder: String,
    on_change: EventHandler<String>,
    onkeydown: EventHandler<KeyboardEvent>,
) -> Element {
    let spans = nibli_kr::highlight::css_spans(&value);
    let pad_key = spans.len();
    let hl_id = format!("{id}-hl");
    let mut ac = use_signal(AcMenu::default);
    let mut pending_cursor = use_signal(|| None::<usize>);
    let editor_id = id.clone();

    use_effect({
        let editor_id = editor_id.clone();
        move || {
            let pending = pending_cursor();
            if let Some(c) = pending {
                pending_cursor.set(None);
                let eid = editor_id.clone();
                spawn(async move {
                    dom_set_cursor(&eid, c).await;
                });
            }
        }
    });

    let commit = {
        move |new_line: String, cur: usize| {
            pending_cursor.set(Some(cur));
            ac.set(AcMenu::default());
            on_change.call(new_line);
        }
    };

    rsx! {
        div { class: "kr-editor kr-editor--line",
            pre {
                id: "{hl_id}",
                class: "kr-editor__highlight kr-editor__highlight--line",
                aria_hidden: "true",
                code {
                    for (i, (cls, text)) in spans.into_iter().enumerate() {
                        span { key: "{i}", class: "{cls}", "{text}" }
                    }
                    if value.is_empty() {
                        span { key: "{pad_key}", class: "tok-ws", " " }
                    }
                }
            }
            input {
                id: "{id}",
                class: "kr-editor__input query-input",
                r#type: "text",
                placeholder: "{placeholder}",
                value: "{value}",
                spellcheck: false,
                autocomplete: "off",
                oninput: {
                    let editor_id = editor_id.clone();
                    move |e| {
                        let text = e.value();
                        on_change.call(text.clone());
                        let eid = editor_id.clone();
                        let was_open = ac().open;
                        spawn(async move {
                            let pos = dom_cursor(&eid).await;
                            let r = run_complete(&text, pos, false);
                            if was_open || !r.items.is_empty() {
                                ac.set(ac_from_result(r));
                            }
                        });
                    }
                },
                onkeydown: {
                    let editor_id = editor_id.clone();
                    let value = value.clone();
                    let mut commit = commit;
                    move |e| {
                        let menu = ac();
                        let key = e.key();
                        let text = value.clone();
                        let eid = editor_id.clone();
                        let handled = match key {
                            Key::Escape if menu.open => {
                                ac.set(AcMenu::default());
                                true
                            }
                            Key::ArrowDown if menu.open && !menu.items.is_empty() => {
                                let mut m = menu;
                                m.selected = (m.selected + 1) % m.items.len();
                                ac.set(m);
                                true
                            }
                            Key::ArrowUp if menu.open && !menu.items.is_empty() => {
                                let mut m = menu;
                                m.selected = (m.selected + m.items.len() - 1) % m.items.len();
                                ac.set(m);
                                true
                            }
                            Key::Enter if menu.open && !menu.items.is_empty() => {
                                if let Some((n, c)) = apply_ac_item(&text, &menu, menu.selected) {
                                    commit(n, c);
                                }
                                true
                            }
                            Key::Tab => {
                                if menu.open && !menu.items.is_empty() {
                                    if let Some((n, c)) = apply_ac_item(&text, &menu, menu.selected) {
                                        commit(n, c);
                                    }
                                } else {
                                    let mut commit = commit;
                                    spawn(async move {
                                        let pos = dom_cursor(&eid).await;
                                        let r = run_complete(&text, pos, true);
                                        if r.items.len() == 1 {
                                            if let Some((n, c)) = r.apply(&text, 0) {
                                                commit(n, c);
                                            }
                                        } else {
                                            ac.set(ac_from_result(r));
                                        }
                                    });
                                }
                                true
                            }
                            Key::Character(ref ch) if ch == " " && e.modifiers().ctrl() => {
                                spawn(async move {
                                    let pos = dom_cursor(&eid).await;
                                    ac.set(ac_from_result(run_complete(&text, pos, true)));
                                });
                                true
                            }
                            _ => false,
                        };
                        if handled {
                            e.prevent_default();
                        } else {
                            onkeydown.call(e);
                        }
                    }
                },
                onscroll: {
                    let editor_id = editor_id.clone();
                    let hl_id = hl_id.clone();
                    move |_| {
                        let id = editor_id.clone();
                        let hl = hl_id.clone();
                        spawn(async move {
                            let _ = document::eval(&format!(
                                r#"
                                const ta = document.getElementById('{id}');
                                const hl = document.getElementById('{hl}');
                                if (ta && hl) {{ hl.scrollLeft = ta.scrollLeft; }}
                                return '';
                                "#
                            ))
                            .await;
                        });
                    }
                },
                onblur: move |_| {
                    spawn(async move {
                        let _ = document::eval(
                            "return await new Promise(r => setTimeout(() => r(''), 150));",
                        )
                        .await;
                        ac.set(AcMenu::default());
                    });
                },
            }
            if ac().open && !ac().items.is_empty() {
                KrAcDropdown {
                    menu: ac(),
                    on_pick: {
                        let value = value.clone();
                        let mut commit = commit;
                        move |idx| {
                            let menu = ac();
                            if let Some((n, c)) = apply_ac_item(&value, &menu, idx) {
                                commit(n, c);
                            }
                        }
                    },
                }
            }
        }
    }
}

#[component]
fn KrAcDropdown(menu: AcMenu, on_pick: EventHandler<usize>) -> Element {
    rsx! {
        div {
            class: "kr-ac-menu",
            role: "listbox",
            for (i, item) in menu.items.iter().enumerate() {
                button {
                    key: "{i}",
                    r#type: "button",
                    class: if i == menu.selected { "kr-ac-item kr-ac-item--active" } else { "kr-ac-item" },
                    role: "option",
                    // mousedown so we beat input blur
                    onmousedown: move |e| {
                        e.prevent_default();
                        on_pick.call(i);
                    },
                    span { class: "kr-ac-item__value", "{item.value}" }
                    span { class: "kr-ac-item__kind", "{item.kind.label()}" }
                    if let Some(desc) = item.description.as_ref() {
                        span { class: "kr-ac-item__desc", "{desc}" }
                    }
                }
            }
            div { class: "kr-ac-hint", "Tab / Enter accept · \u{2191}\u{2193} move · Esc dismiss · Ctrl+Space" }
        }
    }
}

const MAX_OUTPUT_ENTRIES: usize = 200;

const DEFAULT_SOURCE: &str = "All dogs are animals.\nAll animals eat.\nAdam is a dog.";
// The default syllogism KB + query — the nibli KR spelling (single surface).
const DEFAULT_KB: &str = "animal(every dog).\neats(every animal).\ndog(Adam).";
const DEFAULT_QUERY: &str = "eats(Adam).";

/// The KB tab's label.
const KB_TAB_LABEL: &str = "nibli KR";

// ── Agentic formalize (nibli-formalize) ──
// The Source→KB button runs the self-correcting loop: formalize → validate
// (nibli-kr+nibli-semantics+round-trip) → feed the compiler error back → retry, bounded
// below. All gates are local/in-browser; the only network call is the LLM.

/// One row of the self-correction trace rendered under the Source tab.
#[derive(Clone, Copy)]
enum GateState {
    Pass,
    Fail,
    Skip,
}

#[derive(Clone)]
struct TraceRow {
    n: u32,
    ok: bool,
    detail: String,
    /// Per-gate chips: (label like "nibli-kr ✓", css class).
    gates: Vec<(String, &'static str)>,
}

/// nibli-ui's settings bundle: the LLM provider config (`nibli_formalize::llm::LlmConfig`,
/// the single source of truth) plus the agent knobs that aren't LLM-provider
/// settings. Held in one in-memory signal; never persisted.
#[derive(Clone, PartialEq)]
struct Settings {
    llm: LlmConfig,
    max_attempts: u32,
}

impl Settings {
    fn new(provider: Provider) -> Self {
        Settings {
            llm: LlmConfig::new(provider),
            max_attempts: 5,
        }
    }
}

/// Single-shot English→KB formalize via nibli-formalize's transport — used by the
/// query formalize and the modal key-test (the agentic Source formalize uses
/// `translate_agentic`). Returns the cleaned KB text or a user-facing error.
async fn formalize_translate(cfg: &LlmConfig, english: &str) -> Result<String, String> {
    use nibli_formalize::llm::{Chat, HttpChat, Turn, clean_output, system_prompt};
    let request = format!("Formalize into nibli KR: {}", english.trim());
    let turns = [Turn::user(request)];
    let raw = HttpChat
        .chat(cfg, system_prompt(), &turns)
        .await
        .map_err(|e| e.to_string())?;
    let cleaned = clean_output(&raw);
    if cleaned.is_empty() {
        return Err("The provider returned an empty result.".to_string());
    }
    Ok(cleaned)
}

/// The local gates, in the fail-fast order `validate` runs them.
const GATE_ORDER: [&str; 3] = ["nibli-kr", "semantics", "round-trip"];

/// Derive the per-gate chips from an attempt's error. `validate` is fail-fast in
/// [`GATE_ORDER`], so `error.gate()` is the failing gate; earlier gates
/// passed, later ones were skipped.
fn gate_chips(error: &Option<nibli_formalize::gates::GateError>) -> Vec<(String, &'static str)> {
    let order = GATE_ORDER;
    let states: [GateState; 3] = match error {
        None => [GateState::Pass; 3],
        Some(nibli_formalize::gates::GateError::Verification(_)) => [GateState::Pass; 3],
        Some(e) => {
            let fail_idx = order.iter().position(|g| *g == e.gate()).unwrap_or(0);
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
    order
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

/// Collapse the agent's attempts into UI trace rows (per-gate chips + first
/// error line).
fn trace_rows(attempts: &[nibli_formalize::agent::Attempt]) -> Vec<TraceRow> {
    attempts
        .iter()
        .map(|a| TraceRow {
            n: a.n,
            ok: a.error.is_none(),
            detail: match &a.error {
                None => {
                    let reason = match &a.verification {
                        nibli_formalize::verify::VerificationStatus::Unavailable(reason) => {
                            format!(" ({reason})")
                        }
                        _ => String::new(),
                    };
                    format!(
                        "Deterministic gates passed; {}{reason}. Draft awaiting human review.",
                        a.verification.label()
                    )
                }
                Some(e) => {
                    let msg = e.message();
                    let first = msg.lines().next().unwrap_or(msg);
                    format!("{}: {first}", e.gate())
                }
            },
            gates: gate_chips(&a.error),
        })
        .collect()
}

// ── Types ──

#[derive(Clone, Copy, PartialEq)]
enum ActiveTab {
    Source,
    /// The formal KB tab — the nibli KR encoding.
    Kb,
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
    existential_import: bool,
}

// ── Local reasoning (in-browser) ──
// The full nibli-kr → nibli-semantics → nibli-reason pipeline runs in the WASM bundle
// (mirrors `nibli-wasm`). Every query builds a fresh KnowledgeBase, re-asserts
// the KB tab, then queries — matching the "queries reset the engine each
// time" semantics. Built-in arithmetic (product/sum/quotient/greater/less/
// num_equal) resolves locally; external compute predicates (exponential/
// logarithm) have no TCP backend in the browser and surface as errors, same
// as the live demo.

/// Admit every source line into an isolated candidate, then publish it. The
/// first error discards the candidate; a query never sees a successful prefix.
fn admit_kb(kb_text: &str) -> Result<(nibli_session::CoreSession, KbStatus), KbStatus> {
    let session = nibli_session::CoreSession::new();
    let mut status = KbStatus {
        asserted: 0,
        errors: 0,
        skipped: 0,
        line_results: Vec::new(),
    };
    let mut linter = nibli_kr::lint::Linter::new();
    for (i, raw) in kb_text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            status.skipped += 1;
            continue;
        }
        let notes = linter.lint(line).into_iter().map(|n| n.message).collect();
        match session.assert_text(line) {
            Ok(facts) => {
                status.asserted += facts.len() as u32;
                status.line_results.push(LineResult {
                    line_number: (i + 1) as u32,
                    text: line.into(),
                    success: true,
                    fact_id: facts.first().map(|f| f.0),
                    error: None,
                    notes,
                });
            }
            Err(error) => {
                status.errors = 1;
                status.asserted = 0;
                status.line_results.push(LineResult {
                    line_number: (i + 1) as u32,
                    text: line.into(),
                    success: false,
                    fact_id: None,
                    error: Some(error.to_string()),
                    notes,
                });
                return Err(status);
            }
        }
    }
    Ok((session, status))
}

fn admission_error(status: &KbStatus) -> String {
    let failed = status.line_results.iter().find(|line| !line.success);
    match failed {
        Some(line) => format!(
            "KB not loaded: line {}: {}. Candidate discarded; no query was run.",
            line.line_number,
            line.error.as_deref().unwrap_or("admission failed")
        ),
        None => "KB not loaded; no query was run.".into(),
    }
}

fn run_query(kb_text: &str, query_text: &str) -> OutputEntry {
    let (session, status) = match admit_kb(kb_text) {
        Ok(loaded) => loaded,
        Err(status) => {
            return OutputEntry {
                input: query_text.into(),
                result: admission_error(&status),
                is_error: true,
                proof_trace: None,
                proof_trace_data: None,
                kb_status: Some(status),
                existential_import: REVIEW_PROFILE,
            };
        }
    };
    let existential_import = session.is_existential_import();
    let kb_status = Some(status);

    match session.query_text_with_proof(query_text) {
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
                existential_import,
            }
        }
        Err(e) => OutputEntry {
            input: query_text.to_string(),
            result: e.to_string(),
            is_error: true,
            proof_trace: None,
            proof_trace_data: None,
            kb_status,
            existential_import,
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

#[derive(Clone, Copy)]
struct ReviewContext {
    state: Signal<ReviewState>,
    source: Signal<String>,
    kb: Signal<String>,
    output: Signal<Vec<OutputEntry>>,
    proof_text: Signal<Option<String>>,
    proof_data: Signal<Option<ProofTrace>>,
    kb_status: Signal<Option<KbStatus>>,
}

impl ReviewContext {
    fn snapshot(self) -> Snapshot {
        self.state.read().snapshot(
            &self.source.read(),
            &self.kb.read(),
            ENGINE_BUILD,
            REVIEW_PROFILE,
        )
    }
    fn clear_results(mut self) {
        self.output.set(Vec::new());
        self.proof_text.set(None);
        self.proof_data.set(None);
        self.kb_status.set(None);
    }
    fn invalidate(mut self) {
        self.state.write().invalidate();
        self.clear_results();
    }
    fn approved(self) -> bool {
        self.state.read().is_approved(&self.snapshot())
    }
}

// ── Components ──

#[component]
fn App() -> Element {
    let mut output_log: Signal<Vec<OutputEntry>> = use_signal(Vec::new);
    let proof_text: Signal<Option<String>> = use_signal(|| None);
    let proof_data: Signal<Option<ProofTrace>> = use_signal(|| None);
    let kb_text: Signal<String> = use_signal(|| DEFAULT_KB.to_string());
    let kb_status: Signal<Option<KbStatus>> = use_signal(|| None);
    let source_text = use_signal(|| DEFAULT_SOURCE.to_string());
    let review_state = use_signal(ReviewState::default);
    let review = use_context_provider(|| ReviewContext {
        state: review_state,
        source: source_text,
        kb: kb_text,
        output: output_log,
        proof_text,
        proof_data,
        kb_status,
    });
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
                        let _ = document::eval("document.getElementById('kb-file-input').click()")
                            .await;
                    });
                }
                _ => {}
            }
        }
    };

    // Source is the triad's natural entry point (English → KR → back-trans).
    let active_tab: Signal<ActiveTab> = use_signal(|| ActiveTab::Source);
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
                select {
                    class: "nb-select app-header__examples",
                    title: "Load a preloaded example from the book, or Custom to write your own",
                    onchange: move |e| {
                        review.invalidate();
                        example.set(e.value().parse::<usize>().ok().filter(|i| *i < EXAMPLES.len()));
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
                        SourceTabs { kb_text, kb_status, active_tab, settings, modal_open, example }
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
                            kb_text,
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
                    " \u{2014} a Symbolic Reasoning Engine & Hallucination Firewall, built in Rust and compiled to WebAssembly. Reasoning runs in your browser. Optional formalization sends source and review text to your configured LLM provider."
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

    let note_count: usize = s.line_results.iter().map(|lr| lr.notes.len()).sum();
    let summary_text = format!(
        "{} asserted, {} error{}{}{}",
        s.asserted,
        s.errors,
        if s.errors != 1 { "s" } else { "" },
        if s.skipped > 0 {
            format!(", {} skipped", s.skipped)
        } else {
            String::new()
        },
        if note_count > 0 {
            format!(
                ", {} note{}",
                note_count,
                if note_count != 1 { "s" } else { "" }
            )
        } else {
            String::new()
        }
    );

    let summary_text = if s.errors > 0 {
        format!("KB not loaded; candidate discarded. {summary_text}")
    } else if s.asserted == 0 {
        "Empty KB loaded (no assertions).".to_string()
    } else {
        format!("Complete KB loaded: {summary_text}")
    };
    let has_errors = s.errors > 0;
    // Lint notes open the same expandable detail as errors (non-blocking, so
    // they never turn the summary amber).
    let has_detail = has_errors || note_count > 0;
    let summary_state = if has_errors {
        "kb-status-warn"
    } else {
        "kb-status-ok"
    };

    rsx! {
        div { class: "kb-status-bar",
            if has_detail {
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
                                for (ni, note) in lr.notes.iter().enumerate() {
                                    span { key: "{ni}", class: "kb-line-note", "[Note: {note}]" }
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

/// The bottom-left query card — a tabbed mirror of the top column: Source (state
/// a claim in English, formalize it into a KB query via the LLM), the KB tab
/// (the query + Run), and the "Query if …" reading. Output goes to the OutputLog.
#[component]
fn QueryTabs(
    output_log: Signal<Vec<OutputEntry>>,
    proof_text: Signal<Option<String>>,
    proof_data: Signal<Option<ProofTrace>>,
    kb_text: Signal<String>,
    kb_status: Signal<Option<KbStatus>>,
    settings: Signal<Option<Settings>>,
    modal_open: Signal<bool>,
    example: Signal<Option<usize>>,
) -> Element {
    let review = use_context::<ReviewContext>();
    let mut query_review = use_signal(ReviewState::default);
    let mut query_text = use_signal(|| DEFAULT_QUERY.to_string());
    let mut query_source = use_signal(String::new);
    let mut translating = use_signal(|| false);
    let mut translate_error = use_signal(|| Option::<String>::None);
    // Default to the KB tab so the pre-filled query can be Run immediately.
    let mut query_tab = use_signal(|| ActiveTab::Kb);
    // In example mode the query box is a dropdown; this indexes the active
    // example's `queries`.
    let mut selected_query = use_signal(|| 0usize);

    let query_snapshot = move || {
        query_review.read().snapshot(
            &query_source.read(),
            &query_text.read(),
            ENGINE_BUILD,
            REVIEW_PROFILE,
        )
    };
    let mut invalidate_query = move || {
        query_review.write().invalidate();
        review.clear_results();
    };

    // Live back-translation of the ACTIVE query — the typed Custom query, or the
    // selected example query. Shown only for a cleanly-parsed query; a transient
    // parse error shows a stable "incomplete" indicator, never a blank.
    let query_reading = use_memo(move || {
        let owned = match *example.read() {
            Some(i) => EXAMPLES[i]
                .queries
                .get(*selected_query.read())
                .map(|q| q.query.to_string())
                .unwrap_or_default(),
            None => query_text.read().clone(),
        };
        let q = owned.trim();
        if q.is_empty() {
            return QueryReading::Empty;
        }
        let parsed = nibli_kr::parse_text(q);
        if parsed.errors.is_empty() {
            match nibli_semantics::compile_query_from_ast(parsed.buffer) {
                Ok(buf) => QueryReading::Reads(nibli_render::render_logic_buffer(
                    &buf,
                    nibli_render::Register::Spec,
                )),
                Err(_) => QueryReading::Incomplete,
            }
        } else {
            QueryReading::Incomplete
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

    // Resolve the active (KB, query) by mode, enforcing the same approval gate
    // for both the button and Enter. Keep the reviewed query visible.
    let mut do_submit = move || {
        let ex = *example.read();
        let (kb, query) = match ex {
            Some(i) => (
                EXAMPLES[i].kb.to_string(),
                EXAMPLES[i]
                    .queries
                    .get(*selected_query.read())
                    .map(|q| q.query.to_string())
                    .unwrap_or_default(),
            ),
            None => (kb_text.read().clone(), query_text.read().clone()),
        };
        if ex.is_none() {
            if !review.approved() {
                translate_error.set(Some("Review the KB back-translation and choose Use reviewed encoding before querying.".into()));
                return;
            }
            if !query_source.read().trim().is_empty()
                && !query_review.read().is_approved(&query_snapshot())
            {
                translate_error.set(Some(
                    "Review the translated query and choose Use reviewed query before running it."
                        .into(),
                ));
                return;
            }
        }
        translate_error.set(None);
        run_into_log(&kb, &query);
    };

    // Loading an example auto-runs its first query so a verdict shows at once.
    // Reads only `example` (resolving query 0 directly), so changing the dropdown
    // does not re-fire this. Examples are nibli KR-sourced.
    use_effect(move || {
        if let Some(i) = *example.read() {
            selected_query.set(0);
            if let Some(q) = EXAMPLES[i].queries.first() {
                run_into_log(EXAMPLES[i].kb, q.query);
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

    // Formalize the English claim (Source tab) into the KB-language query. With
    // no provider configured, open the integration modal instead of erroring.
    let mut do_translate = move || {
        let text = query_source.read().clone();
        if text.trim().is_empty() || *translating.read() {
            return;
        }
        let Some(cfg) = settings.read().clone() else {
            modal_open.set(true);
            return;
        };
        invalidate_query();
        let requested = query_snapshot();
        let requested_kb = review.snapshot();
        translating.set(true);
        translate_error.set(None);
        spawn(async move {
            let result = formalize_translate(&cfg.llm, &text).await;
            if requested != query_snapshot() || requested_kb != review.snapshot() {
                translating.set(false);
                translate_error.set(Some(
                    "Discarded a stale query formalization because the draft changed.".into(),
                ));
                return;
            }
            match result {
                Ok(formal) => {
                    invalidate_query();
                    query_text.set(formal);
                    query_tab.set(ActiveTab::Kb);
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
    // The decorative query cue (the same cue the script format uses).
    let (affix, affix_title) = (
        "?",
        "The ? just marks this box as a query \u{2014} a reading cue only, never typed or sent. You state a claim (e.g. eats(Adam).); the engine answers TRUE / FALSE / UNKNOWN.",
    );

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
                    class: if is_example || *query_tab.read() == ActiveTab::Kb { "tab active" } else { "tab" },
                    onclick: move |_| query_tab.set(ActiveTab::Kb),
                    {KB_TAB_LABEL}
                    span {
                        class: "tab__help",
                        title: "nibli knowledge representation (KR) language",
                        "?"
                    }
                }
            }
            div { class: "tab-content",
                match (is_example, *query_tab.read()) {
                    (false, ActiveTab::Source) => {
                        let hint = match settings.read().as_ref().map(|c| c.llm.provider.short_name()) {
                            Some(p) => format!("english claim \u{2192} nibli KR via {p}"),
                            None => "english claim \u{2192} nibli KR \u{2014} configure an llm".to_string(),
                        };
                        rsx! {
                            span { class: "nb-eyebrow", "query \u{2014} state a claim in english" }
                            textarea {
                                class: "source-input",
                                placeholder: "State the claim to check, e.g. \"Adam eats\"\u{2026}",
                                value: "{query_source}",
                                oninput: move |e| { invalidate_query(); query_source.set(e.value()); },
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
                                    "Formalize"
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
                    // KB tab: you STATE a proposition to check (not ask a
                    // question) — the engine answers TRUE / FALSE / UNKNOWN. The
                    // affix shown is a decorative reading cue: it is not part of
                    // `query_text` and never reaches the engine. The live
                    // "Query if …" back-translation shows inline below. Source is
                    // the only other tab, so `_` covers the KB tab here.
                    _ => rsx! {
                        if is_example {
                            // Example mode: pick a preset query; it runs on select.
                            div { class: "query-bar",
                                span { class: "query-bar__affix", "{affix}" }
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
                                            "{q.query} \u{2014} {q.label}"
                                        }
                                    }
                                }
                            }
                            div { class: "query-hint",
                                "Provided example queries — run against the complete provided KB, without recording personal approval."
                            }
                        } else {
                            div { class: "query-bar",
                                span {
                                    class: "query-bar__affix",
                                    title: "{affix_title}",
                                    "{affix}"
                                }
                                KrLineEditor {
                                    id: "query-input".to_string(),
                                    value: query_text.read().clone(),
                                    placeholder: "State a proposition to check \u{2014} Ctrl+K focus".to_string(),
                                    on_change: move |text: String| { invalidate_query(); query_text.set(text); },
                                    onkeydown: on_query_keydown,
                                }
                                button { class: "query-btn", onclick: submit_click, "Query" }
                            }
                            div { class: "query-hint",
                                "State a claim to check \u{2014} e.g. \u{201C}Adam eats\u{201D} \u{2014} not a question (\u{201C}Does Adam eat?\u{201D})."
                            }
                        }
                        if !is_example {
                            if let Some(error) = translate_error.read().as_ref() {
                                div { class: "translate-error", "{error}" }
                            }
                            if !query_source.read().trim().is_empty() {
                                button {
                                    class: "toolbar-btn",
                                    disabled: *translating.read() || !matches!(&reading, QueryReading::Reads(_)) || query_review.read().is_approved(&query_snapshot()),
                                    onclick: move |_| {
                                        // Parsing/compilation is reflected in the live reading. A fresh
                                        // snapshot is taken at the click, never at formalizer completion.
                                        if matches!(&*query_reading.read(), QueryReading::Reads(_)) {
                                            let snapshot = query_snapshot();
                                            query_review.write().approve(snapshot);
                                            translate_error.set(None);
                                        }
                                    },
                                    "Use reviewed query"
                                }
                                div { class: "query-hint", "Compare the query source, KR, and reading before approving this exact claim." }
                            } else {
                                div { class: "query-hint", "Authored KR query; no English-source equivalence is claimed." }
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
                                        "\u{26A0} incomplete or invalid "
                                        {KB_TAB_LABEL}
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
    let profile = entries.last().map_or("clean-core · import OFF", |entry| {
        if entry.existential_import {
            "legacy import ON · witnesses count"
        } else {
            "clean-core · import OFF"
        }
    });
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
                    span { class: "output-profile", "{profile}" }
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

#[cfg(test)]
mod semantic_profile_tests {
    use super::*;

    #[test]
    fn browser_ui_reports_and_uses_clean_core_by_default() {
        let output = run_query("animal(every dog).", "dog(some dog).");
        assert!(!output.existential_import);
        assert_eq!(output.result, "FALSE");
    }

    #[test]
    fn any_admission_error_blocks_the_whole_kb_and_query() {
        for kb in [
            "person(Adam). big(exactly 1 dog).\nperson(Bel).",
            "person(Adam).\nbig(exactly 1 dog).\nperson(Bel).",
            "person(Adam).\nthis is invalid\nperson(Bel).",
        ] {
            let output = run_query(kb, "person(Adam).");
            assert!(output.is_error);
            assert!(
                output.result.starts_with("KB not loaded:"),
                "{}",
                output.result
            );
            assert!(output.proof_trace_data.is_none());
            let status = output.kb_status.unwrap();
            assert_eq!(status.asserted, 0);
            assert_eq!(status.errors, 1);
            assert!(!status.line_results.last().unwrap().success);
            assert!(
                !status
                    .line_results
                    .iter()
                    .any(|line| line.text == "person(Bel).")
            );
        }
    }

    #[test]
    fn empty_kb_is_valid_but_carries_no_assertions() {
        for kb in ["", "# only a comment\n\n"] {
            let output = run_query(kb, "dog(Rex).");
            assert!(!output.is_error);
            assert_eq!(output.result, "FALSE");
            assert_eq!(output.kb_status.unwrap().asserted, 0);
        }
    }

    #[test]
    fn valid_multiline_and_multiroot_kb_is_completely_loaded() {
        let output = run_query("dog(Rex). cat(Bel).\nanimal(every dog).", "animal(Rex).");
        assert_eq!(output.result, "TRUE");
        let status = output.kb_status.unwrap();
        assert_eq!(status.asserted, 3);
        assert_eq!(status.errors, 0);
    }
}

#[component]
fn SourceTabs(
    kb_text: Signal<String>,
    kb_status: Signal<Option<KbStatus>>,
    active_tab: Signal<ActiveTab>,
    settings: Signal<Option<Settings>>,
    modal_open: Signal<bool>,
    example: Signal<Option<usize>>,
) -> Element {
    let mut review = use_context::<ReviewContext>();
    let mut source_text = review.source;
    let mut translating = use_signal(|| false);
    let mut translate_error = use_signal(|| Option::<String>::None);
    let mut translate_trace = use_signal(Vec::<TraceRow>::new);

    // Back-translation reflects the ACTIVE KB: a loaded example's corpus, else
    // the user's editable KB tab.
    let back_translation = use_memo(move || {
        let text = match *example.read() {
            Some(i) => EXAMPLES[i].kb.to_string(),
            None => kb_text.read().clone(),
        };
        if text.is_empty() {
            String::new()
        } else {
            back_translate_ir(&text)
        }
    });

    // Formalize the Source tab → the KB language via the configured LLM. With no
    // provider configured yet, open the integration modal instead of erroring.
    let mut do_translate = move || {
        let text = source_text.read().clone();
        if text.trim().is_empty() || *translating.read() {
            return;
        }
        let Some(cfg) = settings.read().clone() else {
            modal_open.set(true);
            return;
        };
        review.invalidate();
        let requested = review.snapshot();
        translating.set(true);
        translate_error.set(None);
        translate_trace.set(Vec::new());
        spawn(async move {
            use nibli_formalize::agent::Outcome;
            // The self-correcting loop: formalize → validate
            // (nibli-kr+nibli-semantics+round-trip) → semantic verification (a
            // fresh-context judge reads the engine's back-translation) → feed
            // any error back → retry, up to the configured max attempts.
            let http = nibli_formalize::llm::HttpChat;
            // The same zero-sized HttpChat serves as the semantic validator: the
            // Chat seam is stateless, so the judge call is a genuinely fresh
            // conversation (same provider/key, no shared history).
            let outcome = nibli_formalize::agent::translate_agentic(
                &http,
                &http,
                &cfg.llm,
                &text,
                cfg.max_attempts.max(1),
            )
            .await;
            if review.snapshot() != requested {
                translating.set(false);
                translate_error.set(Some(
                    "Discarded a stale formalization because the draft changed.".into(),
                ));
                return;
            }
            match outcome {
                Outcome::Success { kr, attempts } => {
                    translate_trace.set(trace_rows(&attempts));
                    review.invalidate();
                    kb_text.set(kr);
                    active_tab.set(ActiveTab::BackTranslation);
                }
                Outcome::Exhausted {
                    best,
                    last_error,
                    attempts,
                } => {
                    let n = attempts.len();
                    translate_trace.set(trace_rows(&attempts));
                    // Show the best effort so the user can edit from there.
                    review.invalidate();
                    kb_text.set(best);
                    active_tab.set(ActiveTab::BackTranslation);
                    translate_error.set(Some(format!(
                        "Couldn't fully validate after {n} attempts \u{2014} showing best effort. Last: {}",
                        last_error.message()
                    )));
                }
                Outcome::ChatFailed { error, attempts } => {
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

    // In example mode the KB is a read-only preview of the loaded corpus; the
    // user's Custom buffers (`source_text`/`kb_text`) are left untouched.
    let ex = *example.read();
    let is_example = ex.is_some();
    let active_source = match ex {
        Some(i) => EXAMPLES[i].source.to_string(),
        None => source_text.read().clone(),
    };
    let active_kb = match ex {
        Some(i) => EXAMPLES[i].kb.to_string(),
        None => kb_text.read().clone(),
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
                    class: if *active_tab.read() == ActiveTab::Kb { "tab active" } else { "tab" },
                    onclick: move |_| active_tab.set(ActiveTab::Kb),
                    {KB_TAB_LABEL}
                    span {
                        class: "tab__help",
                        title: "nibli knowledge representation (KR) language",
                        "?"
                    }
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
                            "provided example \u{2014} read-only, not personally reviewed".to_string()
                        } else {
                            match settings.read().as_ref().map(|c| c.llm.provider.short_name()) {
                                Some(p) => format!("english \u{2192} nibli KR via {p}"),
                                None => "english \u{2192} nibli KR \u{2014} configure an llm".to_string(),
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
                                        review.invalidate();
                                        translate_trace.set(Vec::new());
                                        translate_error.set(None);
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
                                    "Formalize"
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
                                        }
                                    }
                                }
                            }
                        }
                    }
                    ActiveTab::Kb => rsx! {
                        if !is_example {
                        div { class: "kb-toolbar",
                            button {
                                class: "toolbar-btn",
                                onclick: move |_| {
                                    spawn(async move {
                                        let res = document::eval(r#"
                                            document.getElementById('kb-file-input').click();
                                            return '';
                                        "#);
                                        let _ = res.await;
                                    });
                                },
                                "Load .nibli"
                                kbd { class: "kbd-hint", "Ctrl+O" }
                            }
                            button {
                                class: "toolbar-btn",
                                onclick: move |_| {
                                    review.invalidate();
                                    translate_trace.set(Vec::new());
                                    translate_error.set(None);
                                    kb_text.set(String::new());
                                    kb_status.set(None);
                                },
                                "Clear"
                            }
                            input {
                                r#type: "file",
                                accept: ".nibli,.txt",
                                style: "display: none",
                                id: "kb-file-input",
                                onchange: move |_| {
                                    review.invalidate();
                                    translate_trace.set(Vec::new());
                                    translate_error.set(None);
                                    let requested = review.snapshot();
                                    spawn(async move {
                                        let res = document::eval(r#"
                                            const input = document.getElementById('kb-file-input');
                                            const file = input.files[0];
                                            if (!file) return '';
                                            const text = await file.text();
                                            input.value = '';
                                            return text;
                                        "#);
                                        if let Ok(val) = res.await
                                            && let Some(text) = val.as_str()
                                            && review.snapshot() == requested
                                        {
                                            review.invalidate();
                                            kb_text.set(text.to_string());
                                            kb_status.set(None);
                                        }
                                    });
                                },
                            }
                        }
                        }
                        KrMultilineEditor {
                            value: active_kb.clone(),
                            readonly: is_example,
                            placeholder: "Enter nibli KR facts and rules (one per line)...".to_string(),
                            on_change: move |text: String| {
                                if example.read().is_none() {
                                    review.invalidate();
                                    translate_trace.set(Vec::new());
                                    translate_error.set(None);
                                    kb_text.set(text);
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
                        rsx! {
                            span { class: "nb-eyebrow", "what nibli understood" }
                            if is_example {
                                div { class: "query-hint", "Provided example encoding; personal approval is not recorded." }
                            } else {
                                if let Some(last) = translate_trace.read().last() {
                                    div { class: "query-hint", "{last.detail}" }
                                }
                                div { class: "query-hint",
                                    if review.approved() { "Reviewed encoding ready for queries in this tab." }
                                    else if source_text.read().trim().is_empty() {
                                        "Review this authored KR and its reading. Approval records your KR review; there is no source-equivalence claim."
                                    } else {
                                        "Compare the exact source, KR, and reading. Automated checks are advisory about meaning; this draft needs your review."
                                    }
                                }
                                button {
                                    class: "toolbar-btn",
                                    disabled: review.approved() || *translating.read(),
                                    onclick: move |_| {
                                        match admit_kb(&kb_text.read()) {
                                            Ok((_session, status)) => {
                                                let snapshot = review.snapshot();
                                                review.state.write().approve(snapshot);
                                                kb_status.set(Some(status));
                                                translate_error.set(None);
                                            }
                                            Err(status) => {
                                                translate_error.set(Some(admission_error(&status)));
                                                kb_status.set(Some(status));
                                            }
                                        }
                                    },
                                    "Use reviewed encoding"
                                }
                                KbStatusBar { kb_status }
                                if let Some(error) = translate_error.read().as_ref() {
                                    div { class: "translate-error", "{error}" }
                                }
                            }
                            div { class: "back-translation",
                                if empty {
                                    span { class: "back-translation__placeholder",
                                        "Type nibli KR in the nibli KR tab to see the structure-exposing gloss."
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
            match formalize_translate(&s.llm, "Adam is a dog").await {
                Ok(formal) => test_msg.set(Some((true, format!("OK \u{2014} {formal}")))),
                Err(e) => test_msg.set(Some((false, e))),
            }
            testing.set(false);
        });
    };
    rsx! {
        // Backdrop click closes; the card stops propagation so inner clicks don't.
        div { class: "modal-backdrop", onclick: move |_| modal_open.set(false),
            div { class: "modal-card", onclick: move |e: Event<MouseData>| e.stop_propagation(),
                div { class: "modal-title", "Integrate an LLM to formalize" }
                p { class: "modal-subtitle",
                    "Use your own LLM to draft the formal knowledge base from plain English. The draft is reviewed before the engine reasons over it."
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

                div { class: "llm-security-note",
                    span { class: "llm-security-note__title", "\u{1F512} Your key stays in this tab" }
                    p {
                        "Held only in this browser tab's memory \u{2014} never written to disk or storage, and erased the moment you close or reload the tab. nibli has no server: the request goes straight from your browser to "
                        b { "{prov.display_name()}" }
                        ". It is open source \u{2014} verify in DevTools \u{2192} Network that the only call is to the provider."
                    }
                    div { class: "llm-security-note__links",
                        a {
                            href: "https://github.com/dhilipsiva/nibli/blob/main/nibli-formalize/src/llm/http.rs",
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
                    "\u{26A0} LLMs can hallucinate and give a wrong formalization. Always review the formal statements (and their back-translation) before trusting them \u{2014} only the formal KB you verify is what nibli reasons over."
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
                        span { class: "q", "eats" }
                        "(Adam)."
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
