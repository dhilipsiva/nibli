//! Explicit provider selection. API keys never enter conversation memory,
//! backups, process arguments, model context, or diagnostic output.
use super::{Result, err, model, net};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;

#[derive(Clone, Serialize, Deserialize)]
pub struct Provider {
    pub name: String,
    pub endpoint: String,
    pub model: String,
    pub key_env: String,
}
#[derive(Default, Serialize, Deserialize)]
struct Config {
    selected: Option<String>,
    providers: BTreeMap<String, Provider>,
}

fn directory() -> Result<PathBuf> {
    let base = std::env::var_os("XDG_CONFIG_HOME")
        .map(PathBuf::from)
        .unwrap_or(
            PathBuf::from(std::env::var_os("HOME").ok_or("HOME is missing")?).join(".config"),
        );
    Ok(base.join("lucy"))
}
fn load() -> Result<Config> {
    let path = directory()?.join("providers.json");
    if path.is_symlink() {
        return Err("refusing symlinked provider configuration".into());
    }
    match fs::read(path) {
        Ok(bytes) => serde_json::from_slice(&bytes).map_err(err),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(Config::default()),
        Err(e) => Err(err(e)),
    }
}
fn write(path: &std::path::Path, bytes: &[u8]) -> Result<()> {
    for parent in path.ancestors() {
        if parent.is_symlink() || parent.join(".git").exists() || parent.join("flake.nix").exists()
        {
            return Err(
                "provider settings and keys must be outside symlinks and repositories".into(),
            );
        }
    }
    let parent = path.parent().ok_or("missing parent")?;
    fs::create_dir_all(parent).map_err(err)?;
    fs::set_permissions(parent, fs::Permissions::from_mode(0o700)).map_err(err)?;
    let temp = parent.join(format!(".{}.tmp", super::token()?));
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&temp)
        .map_err(err)?;
    file.write_all(bytes)
        .and_then(|_| file.sync_all())
        .map_err(err)?;
    fs::rename(temp, path).map_err(err)
}
pub fn presets() -> Value {
    json!([
        {"name":"ollama","endpoint":"http://127.0.0.1:11434","model":model(),"key_env":"","offer":"Local inference"},
        {"name":"nvidia","endpoint":"https://integrate.api.nvidia.com/v1","key_env":"NVIDIA_API_KEY","offer":"Development access; check account quota","docs":"https://build.nvidia.com/"},
        {"name":"groq","endpoint":"https://api.groq.com/openai/v1","key_env":"GROQ_API_KEY","offer":"Free plan with model-specific limits","docs":"https://console.groq.com/docs/rate-limits"},
        {"name":"gemini","endpoint":"https://generativelanguage.googleapis.com/v1beta/openai","key_env":"GEMINI_API_KEY","offer":"Free tier on eligible models; data-use terms differ","docs":"https://ai.google.dev/gemini-api/docs/billing/"},
        {"name":"openrouter","endpoint":"https://openrouter.ai/api/v1","key_env":"OPENROUTER_API_KEY","model":"openrouter/free","offer":"Free models subject to daily limits","docs":"https://openrouter.ai/pricing/"}
    ])
}
pub fn selected() -> Result<Option<Provider>> {
    let config = load()?;
    match config.selected {
        Some(name) if name != "ollama" => config
            .providers
            .get(&name)
            .cloned()
            .map(Some)
            .ok_or("selected provider is not configured".into()),
        _ => Ok(None),
    }
}
pub fn list() -> Result<Value> {
    let config = load()?;
    let providers: Vec<_> = config
        .providers
        .values()
        .map(|p| {
            json!({
                "name":p.name,"endpoint":p.endpoint,"model":p.model,
                "key_env":p.key_env,"key_available":key(p).is_ok()
            })
        })
        .collect();
    Ok(
        json!({"selected":config.selected.unwrap_or_else(||"ollama".into()),"providers":providers,"presets":presets()}),
    )
}
pub fn configure(name: &str, model: &str) -> Result<()> {
    let presets = presets();
    let preset = presets
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["name"] == name)
        .ok_or("unknown provider preset")?;
    if model.trim().is_empty() || model.chars().any(char::is_control) {
        return Err("choose a model ID from that provider's catalog".into());
    }
    let mut config = load()?;
    config.providers.insert(
        name.into(),
        Provider {
            name: name.into(),
            endpoint: preset["endpoint"].as_str().unwrap().into(),
            model: model.into(),
            key_env: preset["key_env"].as_str().unwrap().into(),
        },
    );
    write(
        &directory()?.join("providers.json"),
        &serde_json::to_vec_pretty(&config).map_err(err)?,
    )
}
pub fn select(name: &str) -> Result<()> {
    let mut config = load()?;
    if name != "ollama" {
        let provider = config
            .providers
            .get(name)
            .ok_or("configure a model for this provider first")?;
        key(provider)?;
    }
    config.selected = Some(name.into());
    write(
        &directory()?.join("providers.json"),
        &serde_json::to_vec_pretty(&config).map_err(err)?,
    )
}
pub fn save_key(name: &str, secret: &str) -> Result<()> {
    if name == "ollama"
        || !presets()
            .as_array()
            .unwrap()
            .iter()
            .any(|p| p["name"] == name)
    {
        return Err("unknown hosted provider".into());
    }
    let secret = secret.trim();
    if secret.is_empty() || secret.chars().any(char::is_control) {
        return Err("invalid API key".into());
    }
    write(&directory()?.join("keys").join(name), secret.as_bytes())
}
fn key(provider: &Provider) -> Result<String> {
    if let Ok(value) = std::env::var(&provider.key_env)
        && !value.trim().is_empty()
    {
        return Ok(value.trim().into());
    }
    let path = directory()?.join("keys").join(&provider.name);
    if path.is_symlink() {
        return Err("refusing symlinked API key".into());
    }
    let metadata = fs::metadata(&path).map_err(|_| {
        format!(
            "API key missing; set {} or use `lucy providers key --name {} --stdin`",
            provider.key_env, provider.name
        )
    })?;
    if metadata.permissions().mode() & 0o077 != 0 {
        return Err("API key file must have mode 0600".into());
    }
    fs::read_to_string(path)
        .map(|v| v.trim().into())
        .map_err(err)
}
pub fn models(name: &str) -> Result<Value> {
    let presets = presets();
    let preset = presets
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["name"] == name)
        .ok_or("unknown provider")?;
    if name == "ollama" {
        let (code, bytes, _) = net::request(
            "GET",
            "http://127.0.0.1:11434/api/tags",
            &[],
            None,
            &AtomicBool::new(false),
            20,
            2_000_000,
        )?;
        if code != 200 {
            return Err(format!("Ollama returned HTTP {code}"));
        }
        return serde_json::from_slice(&bytes).map_err(err);
    }
    let provider = Provider {
        name: name.into(),
        endpoint: preset["endpoint"].as_str().unwrap().into(),
        model: String::new(),
        key_env: preset["key_env"].as_str().unwrap().into(),
    };
    let headers = vec![(
        "Authorization".into(),
        format!("Bearer {}", key(&provider)?),
    )];
    let (code, bytes, retry) = net::request(
        "GET",
        &format!("{}/models", provider.endpoint),
        &headers,
        None,
        &AtomicBool::new(false),
        30,
        4_000_000,
    )?;
    if code != 200 {
        return Err(format!(
            "Model catalog returned HTTP {code}; Retry-After: {}",
            retry.unwrap_or_default()
        ));
    }
    serde_json::from_slice(&bytes).map_err(err)
}
pub fn chat(
    provider: &Provider,
    messages: &[Value],
    tools: Value,
    cancel: &AtomicBool,
) -> Result<Value> {
    complete(provider, &key(provider)?, messages, tools, cancel)
}
pub(super) fn complete(
    provider: &Provider,
    key: &str,
    messages: &[Value],
    tools: Value,
    cancel: &AtomicBool,
) -> Result<Value> {
    let headers = vec![("Authorization".into(), format!("Bearer {key}"))];
    let messages: Vec<Value> = messages.iter().map(|message| {
        let mut message = message.clone();
        // Translate Ollama image messages to the hosted chat-completions format.
        if let Some(images) = message.as_object_mut().and_then(|m| m.remove("images")) {
            let mut parts = vec![json!({"type":"text","text":message["content"]})];
            for image in images.as_array().into_iter().flatten().filter_map(Value::as_str) {
                parts.push(json!({"type":"image_url","image_url":{"url":format!("data:image/png;base64,{image}")}}));
            }
            message["content"] = json!(parts);
        }
        message.as_object_mut().unwrap().remove("tool_name");
        message
    }).collect();
    let mut body = json!({"model":provider.model,"messages":messages,"tools":tools,"stream":false,"max_tokens":2048});
    if matches!(provider.name.as_str(), "groq" | "openrouter") {
        body["parallel_tool_calls"] = json!(false);
    }
    let (code, bytes, retry) = net::request(
        "POST",
        &format!("{}/chat/completions", provider.endpoint),
        &headers,
        Some(&body),
        cancel,
        600,
        2_000_000,
    )?;
    if code != 200 {
        return Err(format!(
            "{} returned HTTP {code}; Retry-After: {}. No paid or alternate-provider fallback was attempted.",
            provider.name,
            retry.unwrap_or_default()
        ));
    }
    let response: Value = serde_json::from_slice(&bytes).map_err(err)?;
    let message = response["choices"][0]["message"].clone();
    if !message.is_object() {
        return Err("provider returned no message".into());
    }
    Ok(message)
}
