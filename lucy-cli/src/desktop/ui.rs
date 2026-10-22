//! GTK objects stay on the main thread; service requests run on worker threads.
use super::{Result, call, err, token};
use gtk4::{self as gtk, glib, prelude::*};
use serde_json::{Value, json};
use std::{
    cell::Cell,
    path::{Path, PathBuf},
    rc::Rc,
    sync::mpsc,
    time::Duration,
};

struct Reply {
    generation: u64,
    kind: &'static str,
    result: Result<Value>,
}

struct Window {
    client: Value,
    workspace: PathBuf,
    generation: Cell<u64>,
    sender: mpsc::Sender<Reply>,
    status: gtk::Label,
    transcript: gtk::TextView,
    memories: gtk::TextView,
    pending: gtk::Box,
    entry: gtk::TextView,
    send: gtk::Button,
    provider: gtk::ComboBoxText,
    model: gtk::Entry,
    key: gtk::PasswordEntry,
    catalog: gtk::TextView,
}

fn view() -> gtk::TextView {
    gtk::TextView::builder()
        .editable(false)
        .cursor_visible(false)
        .wrap_mode(gtk::WrapMode::WordChar)
        .build()
}

fn scroll(child: &impl IsA<gtk::Widget>, height: i32) -> gtk::ScrolledWindow {
    gtk::ScrolledWindow::builder()
        .child(child)
        .min_content_height(height)
        .max_content_height(250)
        .build()
}

impl Window {
    fn append(&self, text: &str) {
        let buffer = self.transcript.buffer();
        buffer.insert(&mut buffer.end_iter(), &format!("{text}\n\n"));
        let mark = buffer.create_mark(None, &buffer.end_iter(), false);
        self.transcript.scroll_to_mark(&mark, 0.0, false, 0.0, 1.0);
        buffer.delete_mark(&mark);
    }

    fn clear_pending(&self) {
        while let Some(child) = self.pending.first_child() {
            self.pending.remove(&child);
        }
    }

    fn work(&self, mut request: Value, kind: &'static str) {
        self.generation.set(self.generation.get() + 1);
        let generation = self.generation.get();
        for (key, value) in self.client.as_object().unwrap() {
            request[key] = value.clone();
        }
        self.send.set_sensitive(false);
        if kind == "chat" {
            self.clear_pending();
        }
        self.status.set_text("Working…");
        let sender = self.sender.clone();
        std::thread::spawn(move || {
            let result = if kind == "select" {
                (|| {
                    let name = request["name"].clone();
                    if request["key"].as_str().is_some_and(|key| !key.is_empty()) {
                        let mut save = request.clone();
                        save["op"] = json!("provider-key");
                        call(save)?;
                    }
                    request.as_object_mut().unwrap().remove("key");
                    if name != "ollama" {
                        let mut configure = request.clone();
                        configure["op"] = json!("provider-config");
                        call(configure)?;
                    }
                    request["op"] = json!("provider-select");
                    call(request)
                })()
            } else {
                call(request)
            };
            let _ = sender.send(Reply {
                generation,
                kind,
                result,
            });
        });
    }

    fn finish(self: &Rc<Self>, reply: Reply) {
        if reply.generation != self.generation.get() {
            return;
        }
        self.send.set_sensitive(true);
        let result = match reply.result {
            Ok(result) => result,
            Err(error) => {
                self.status.set_text(&error);
                return;
            }
        };
        if matches!(reply.kind, "providers" | "select") {
            let selected = result["selected"].as_str().unwrap_or("ollama");
            self.provider.set_active_id(Some(selected));
            let models = result["providers"]
                .as_array()
                .into_iter()
                .flatten()
                .chain(result["presets"].as_array().into_iter().flatten());
            if let Some(model) = models
                .filter(|p| p["name"] == selected)
                .find_map(|p| p["model"].as_str())
            {
                self.model.set_text(model);
            }
            self.status.set_text(&format!("Ready · {selected}"));
            return;
        }
        if reply.kind == "catalog" {
            self.catalog.buffer().set_text(&super::visible(
                &serde_json::to_string_pretty(&result).unwrap_or_default(),
            ));
            self.status.set_text("Model catalog loaded");
            return;
        }
        self.clear_pending();
        self.status.set_text(if result["active"] == true {
            "Active"
        } else {
            "Asleep"
        });
        if let Some(text) = result["text"].as_str().filter(|s| !s.is_empty()) {
            self.append(&format!("Lucy: {}", super::visible(text)));
        }
        if let Some(memories) = result["memories"].as_array() {
            self.memories.buffer().set_text(
                &memories
                    .iter()
                    .map(|m| {
                        super::visible(&format!(
                            "{} · {}\n{}",
                            m["source"].as_str().unwrap_or("memory"),
                            m["id"].as_str().unwrap_or(""),
                            m["excerpt"].as_str().unwrap_or("")
                        ))
                    })
                    .collect::<Vec<_>>()
                    .join("\n\n"),
            );
        }
        for (id, proposal) in result["pending"].as_object().into_iter().flatten() {
            let preview = view();
            preview.buffer().set_text(&super::visible(
                &serde_json::to_string_pretty(proposal).unwrap_or_default(),
            ));
            self.pending.append(&scroll(&preview, 140));
            let buttons = gtk::Box::new(gtk::Orientation::Horizontal, 8);
            for (label, allow) in [("Approve this action", true), ("Deny", false)] {
                let button = gtk::Button::with_label(label);
                let state = Rc::downgrade(self);
                let id = id.clone();
                button.connect_clicked(move |_| {
                    if let Some(state) = state.upgrade() {
                        state.work(json!({"op":"approve","action":id,"allow":allow}), "chat");
                    }
                });
                buttons.append(&button);
            }
            self.pending.append(&buttons);
        }
    }
}

pub fn run(workspace: &Path, handoff: Option<Value>) -> Result<()> {
    let client = call(json!({"op":"open"}))?;
    let app = gtk::Application::builder()
        .application_id("dev.nibli.Lucy")
        .flags(gtk::gio::ApplicationFlags::NON_UNIQUE)
        .build();
    let workspace = workspace.to_path_buf();
    let close_client = client.clone();
    app.connect_activate(move |app| {
        let window = gtk::ApplicationWindow::builder()
            .application(app).title("Ask Lucy").default_width(900).default_height(800).build();
        let layout = gtk::Box::new(gtk::Orientation::Vertical, 8);
        layout.set_margin_start(16);
        layout.set_margin_end(16);
        layout.set_margin_top(16);
        layout.set_margin_bottom(16);
        window.set_child(Some(&layout));
        let status = gtk::Label::builder().label("Asleep").xalign(0.0).wrap(true).build();
        layout.append(&status);
        let settings = gtk::Box::new(gtk::Orientation::Vertical, 6);
        let provider = gtk::ComboBoxText::new();
        for name in ["ollama", "nvidia", "groq", "gemini", "openrouter"] {
            provider.append(Some(name), name);
        }
        provider.set_active_id(Some("ollama"));
        settings.append(&provider);
        let model = gtk::Entry::builder().placeholder_text("Model ID from the provider catalog").build();
        settings.append(&model);
        let key = gtk::PasswordEntry::builder().placeholder_text("API key (saved locally; leave blank to keep it)")
            .show_peek_icon(true).build();
        settings.append(&key);
        let notice = gtk::Label::builder().xalign(0.0).wrap(true)
            .label("Local Ollama is the default. Choosing a hosted provider sends your prompts, retrieved memories and tool results to it. Free access depends on the model and account; Lucy does not switch providers automatically.")
            .build();
        settings.append(&notice);
        let settings_buttons = gtk::Box::new(gtk::Orientation::Horizontal, 8);
        let select = gtk::Button::with_label("Use provider");
        let models = gtk::Button::with_label("Load model catalog");
        settings_buttons.append(&select);
        settings_buttons.append(&models);
        settings.append(&settings_buttons);
        let catalog = view();
        let catalog_expander = gtk::Expander::builder().label("Model catalog").child(&scroll(&catalog, 100)).build();
        settings.append(&catalog_expander);
        layout.append(&gtk::Expander::builder().label("Model and provider settings").child(&settings).build());

        let transcript = view();
        let history = scroll(&transcript, 200);
        history.set_vexpand(true);
        layout.append(&history);
        let memories = view();
        layout.append(&gtk::Expander::builder().label("Retrieved memories")
            .child(&scroll(&memories, 100)).build());
        let pending = gtk::Box::new(gtk::Orientation::Vertical, 6);
        layout.append(&pending);
        let entry = gtk::TextView::builder().wrap_mode(gtk::WrapMode::WordChar).build();
        entry.set_size_request(-1, 90);
        if let Some(handoff) = &handoff {
            entry.buffer().set_text(&format!("Lucy, help with this context.\nSource: {}\n\n{}",
                handoff["source"].as_str().unwrap_or(""), handoff["text"].as_str().unwrap_or("")));
        }
        layout.append(&entry);
        let buttons = gtk::Box::new(gtk::Orientation::Horizontal, 8);
        let send = gtk::Button::with_label("Send");
        send.add_css_class("suggested-action");
        let stop = gtk::Button::with_label("Stop");
        let sleep = gtk::Button::with_label("Lucy, sleep");
        for button in [&send, &stop, &sleep] { buttons.append(button); }
        layout.append(&buttons);
        let (sender, receiver) = mpsc::channel();
        let state = Rc::new(Window { client: client.clone(), workspace: workspace.clone(),
            generation: Cell::new(0), sender, status, transcript, memories, pending,
            entry, send: send.clone(), provider, model, key, catalog });
        let state_send = state.clone();
        send.connect_clicked(move |_| {
            let s = &state_send;
            let buffer = s.entry.buffer();
            let text = buffer.text(&buffer.start_iter(), &buffer.end_iter(), true).to_string();
            if text.trim().is_empty() { return; }
            match token().and_then(|id| {
                std::fs::create_dir_all(&s.workspace).map_err(err)?;
                Ok(id)
            }) {
                Ok(event) => {
                    s.append(&format!("You: {text}"));
                    buffer.set_text("");
                    s.work(json!({"op":"chat","text":text,"event":event,"workspace":s.workspace}), "chat");
                }
                Err(error) => s.status.set_text(&error),
            }
        });
        let s = state.clone();
        select.connect_clicked(move |_| {
            let name = s.provider.active_id().map(|v| v.to_string()).unwrap_or_default();
            let request = json!({"op":"provider-select","name":name,"model":s.model.text().as_str(),"key":s.key.text().as_str()});
            s.key.set_text("");
            s.work(request, "select");
        });
        let s = state.clone();
        models.connect_clicked(move |_| {
            s.work(json!({"op":"provider-models","name":s.provider.active_id().map(|v|v.to_string())}), "catalog");
        });
        for (button, operation) in [(stop, "cancel"), (sleep, "sleep")] {
            let s = state.clone();
            button.connect_clicked(move |_| {
                s.clear_pending();
                s.work(json!({"op":operation}), "control");
            });
        }
        let s = state.clone();
        let timer = glib::timeout_add_local(Duration::from_millis(50), move || {
            while let Ok(reply) = receiver.try_recv() { s.finish(reply); }
            glib::ControlFlow::Continue
        });
        let timer = std::cell::RefCell::new(Some(timer));
        window.connect_close_request(move |_| {
            if let Some(timer) = timer.borrow_mut().take() { timer.remove(); }
            glib::Propagation::Proceed
        });
        state.work(json!({"op":"providers"}), "providers");
        window.present();
    });
    app.run_with_args::<&str>(&[]);
    let mut close = close_client;
    close["op"] = json!("close");
    call(close)?;
    Ok(())
}
