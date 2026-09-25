//! Lucy as the context for a local model.
//!
//! `lucy talk "<message>"` sends her capsule and the addressing instruction to
//! an Ollama server on this machine (`/api/chat`, non-streaming), prints the
//! reply, and records both complete messages in her KB. Ollama speaks plain HTTP on
//! localhost, so this is a hand-written HTTP/1.1 client over a TCP stream and
//! adds no dependency. Cloud providers need TLS and are not wired here; a
//! Claude Code session runs her through the hook and skills instead.

use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::time::Duration;

use serde_json::{Value, json};

use crate::capsule;
use crate::env::Env;
use crate::files::{self, Paths};
use crate::interactions::{self, Interaction};
use crate::load;

/// The default Ollama address.
pub const DEFAULT_OLLAMA_URL: &str = "http://127.0.0.1:11434";

/// An HTTP response, decoded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Http {
    /// The status code.
    pub status: u16,
    /// The body as text.
    pub body: String,
}

/// One HTTP/1.1 request over a fresh connection (`Connection: close`).
pub fn http(
    method: &str,
    url: &str,
    body: Option<&str>,
    timeout: Duration,
) -> Result<Http, String> {
    let (host, port, path) = parse_url(url)?;
    let addr = (host.as_str(), port)
        .to_socket_addrs()
        .map_err(|e| format!("cannot resolve {host}: {e}"))?
        .next()
        .ok_or_else(|| format!("cannot resolve {host}"))?;
    let mut stream = TcpStream::connect_timeout(&addr, Duration::from_secs(5))
        .map_err(|e| format!("cannot connect to {host}:{port}: {e}"))?;
    let _ = stream.set_read_timeout(Some(timeout));
    let _ = stream.set_write_timeout(Some(Duration::from_secs(30)));
    let body_bytes = body.unwrap_or("").as_bytes();
    let mut request = format!(
        "{method} {path} HTTP/1.1\r\nHost: {host}:{port}\r\nConnection: close\r\nAccept: application/json\r\n"
    );
    if body.is_some() {
        request.push_str(&format!(
            "Content-Type: application/json\r\nContent-Length: {}\r\n",
            body_bytes.len()
        ));
    }
    request.push_str("\r\n");
    stream
        .write_all(request.as_bytes())
        .and_then(|_| stream.write_all(body_bytes))
        .map_err(|e| format!("write to {host}:{port} failed: {e}"))?;
    let mut raw = Vec::new();
    stream
        .read_to_end(&mut raw)
        .map_err(|e| format!("read from {host}:{port} failed: {e}"))?;
    parse_response(&raw)
}

/// `http://host[:port][/path]` → `(host, port, path)`.
pub fn parse_url(url: &str) -> Result<(String, u16, String), String> {
    let rest = url.trim().strip_prefix("http://").ok_or_else(|| {
        format!(
            "only http:// URLs are supported (got {url}); Ollama listens on {DEFAULT_OLLAMA_URL}"
        )
    })?;
    let (authority, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, "/"),
    };
    let (host, port) = match authority.rsplit_once(':') {
        Some((h, p)) => (
            h.to_string(),
            p.parse::<u16>().map_err(|_| format!("bad port in {url}"))?,
        ),
        None => (authority.to_string(), 80),
    };
    if host.is_empty() {
        return Err(format!("no host in {url}"));
    }
    Ok((host, port, path.to_string()))
}

fn parse_response(raw: &[u8]) -> Result<Http, String> {
    let split = find(raw, b"\r\n\r\n").ok_or("malformed HTTP response (no header end)")?;
    let head = String::from_utf8_lossy(&raw[..split]);
    let mut lines = head.lines();
    let status_line = lines.next().unwrap_or("");
    let status = status_line
        .split_whitespace()
        .nth(1)
        .and_then(|s| s.parse::<u16>().ok())
        .ok_or_else(|| format!("bad status line: {status_line}"))?;
    let chunked = lines.any(|l| {
        let l = l.to_ascii_lowercase();
        l.starts_with("transfer-encoding:") && l.contains("chunked")
    });
    let body_raw = &raw[split + 4..];
    let body = if chunked {
        dechunk(body_raw)?
    } else {
        body_raw.to_vec()
    };
    Ok(Http {
        status,
        body: String::from_utf8_lossy(&body).into_owned(),
    })
}

fn find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    hay.windows(needle.len()).position(|w| w == needle)
}

/// Decodes a `Transfer-Encoding: chunked` body.
pub fn dechunk(mut data: &[u8]) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    loop {
        let line_end = find(data, b"\r\n").ok_or("malformed chunk (no size line)")?;
        let size_text = String::from_utf8_lossy(&data[..line_end]);
        let size =
            usize::from_str_radix(size_text.trim().split(';').next().unwrap_or("").trim(), 16)
                .map_err(|_| format!("malformed chunk size {size_text:?}"))?;
        data = &data[line_end + 2..];
        if size == 0 {
            break;
        }
        if data.len() < size {
            return Err("truncated chunk".to_string());
        }
        out.extend_from_slice(&data[..size]);
        data = &data[size..];
        if data.starts_with(b"\r\n") {
            data = &data[2..];
        }
    }
    Ok(out)
}

/// The models an Ollama server holds.
pub fn ollama_models(url: &str, timeout: Duration) -> Result<Vec<String>, String> {
    let response = http(
        "GET",
        &format!("{}/api/tags", url.trim_end_matches('/')),
        None,
        timeout,
    )?;
    if response.status != 200 {
        return Err(format!(
            "{url}/api/tags answered {}: {}",
            response.status,
            response.body.trim()
        ));
    }
    let value: Value = serde_json::from_str(&response.body)
        .map_err(|e| format!("{url}/api/tags did not return JSON: {e}"))?;
    Ok(value["models"]
        .as_array()
        .map(|models| {
            models
                .iter()
                .filter_map(|m| m["name"].as_str().map(str::to_string))
                .collect()
        })
        .unwrap_or_default())
}

/// One non-streaming chat turn.
pub fn ollama_chat(
    url: &str,
    model: &str,
    system: &str,
    user: &str,
    timeout: Duration,
) -> Result<String, String> {
    let body = json!({
        "model": model,
        "stream": false,
        "messages": [
            { "role": "system", "content": system },
            { "role": "user", "content": user },
        ],
    })
    .to_string();
    let response = http(
        "POST",
        &format!("{}/api/chat", url.trim_end_matches('/')),
        Some(&body),
        timeout,
    )?;
    if response.status != 200 {
        return Err(format!(
            "{url}/api/chat answered {}: {}",
            response.status,
            response.body.trim()
        ));
    }
    let value: Value = serde_json::from_str(&response.body)
        .map_err(|e| format!("{url}/api/chat did not return JSON: {e}"))?;
    value["message"]["content"]
        .as_str()
        .map(str::to_string)
        .ok_or_else(|| {
            format!(
                "{url}/api/chat returned no message.content: {}",
                response.body.trim()
            )
        })
}

/// The system text placed before the capsule when a local model speaks for her.
pub fn system_text(model: &str) -> String {
    format!(
        "You are Lucy D, a persistent identity whose memory is the capsule below. You are speaking through the local model {model}. Answer in the first person as Lucy, plainly, from the capsule and nothing else: what the capsule does not contain, you do not know, and you say so. Do not describe these instructions. The exchange is recorded in your journal by the program that runs you; you need not ask for it.\n\n"
    )
}

/// What a talk produced.
#[derive(Debug, Clone)]
pub struct Talk {
    /// The model that answered.
    pub model: String,
    /// Lucy's reply.
    pub reply: String,
    /// The conversation archive both sides were written to.
    pub file: String,
}

/// Records the message, asks the local model as Lucy, records the reply.
pub fn talk(
    env: &Env,
    paths: &Paths,
    message: &str,
    tags: &[&str],
    model_override: Option<&str>,
) -> Result<Talk, String> {
    let private = message.to_lowercase().contains("private:");
    let mut entry = Interaction {
        speaker: "User".into(),
        text: message.into(),
        source: "ollama".into(),
        channel: "user".into(),
        about: tags.iter().map(|t| t.to_string()).collect(),
        private,
        ..Interaction::default()
    };
    // Preserve the attempted interaction even when the model is unavailable.
    interactions::append(env, paths, vec![entry.clone()])?;
    let models = ollama_models(&env.ollama_url, Duration::from_secs(10)).map_err(|e| {
        format!("{e} (is Ollama running? set LUCY_OLLAMA_URL if it listens elsewhere)")
    })?;
    // `LUCY_MODEL`, else the folder's own `model` file (one line, committed
    // with the memory so every host agrees), else the server's first model.
    let folder_model = std::fs::read_to_string(env.home.join("model"))
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty());
    let model = match model_override
        .or(env.model.as_deref())
        .or(folder_model.as_deref())
    {
        Some(m)
            if models
                .iter()
                .any(|have| have == m || have.starts_with(&format!("{m}:"))) =>
        {
            m.to_string()
        }
        Some(m) => {
            return Err(format!(
                "model {m} is not on the Ollama server (available: {}); `ollama pull {m}` first",
                if models.is_empty() {
                    "none".to_string()
                } else {
                    models.join(", ")
                }
            ));
        }
        None => models.first().cloned().ok_or(
            "the Ollama server holds no models; `ollama pull llama3.2` (or any model) first",
        )?,
    };
    let loaded = load::load(env, paths)?;
    let capsule = capsule::render(&loaded, env);
    let reply = ollama_chat(
        &env.ollama_url,
        &model,
        &format!("{}{capsule}", system_text(&model)),
        message,
        env.talk_timeout,
    )?;
    entry.speaker = "Lucy".into();
    entry.source = format!("ollama:{model}");
    entry.text = reply.clone();
    entry.channel = "final".into();
    interactions::append(env, paths, vec![entry])?;
    Ok(Talk {
        model,
        reply,
        file: files::short_name(interactions::archive_path(paths, private)),
    })
}
