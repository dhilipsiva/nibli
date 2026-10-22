//! Bounded Rust TLS requests with cancellation and no implicit redirects.
use super::{Result, err};
use serde_json::Value;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

pub fn request(
    method: &str,
    url: &str,
    headers: &[(String, String)],
    body: Option<&Value>,
    cancel: &AtomicBool,
    timeout: u64,
    limit: usize,
) -> Result<(u16, Vec<u8>, Option<String>)> {
    let url = reqwest::Url::parse(url).map_err(|_| "invalid HTTP URL")?;
    if !matches!(url.scheme(), "http" | "https")
        || !url.username().is_empty()
        || url.password().is_some()
    {
        return Err("HTTP(S) URL required, without credentials in its authority".into());
    }
    let client = reqwest::Client::builder()
        .redirect(reqwest::redirect::Policy::none())
        .connect_timeout(Duration::from_secs(10))
        .timeout(Duration::from_secs(timeout))
        .build()
        .map_err(err)?;
    let mut request = client.request(
        reqwest::Method::from_bytes(method.as_bytes()).map_err(err)?,
        url,
    );
    for (name, value) in headers {
        request = request.header(name, value);
    }
    if let Some(body) = body {
        request = request.json(body);
    }
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(err)?
        .block_on(async {
            let operation = async {
                let mut response = request
                    .send()
                    .await
                    .map_err(|_| "HTTP request failed or timed out".to_owned())?;
                let status = response.status().as_u16();
                let retry = response
                    .headers()
                    .get("retry-after")
                    .and_then(|v| v.to_str().ok())
                    .map(str::to_owned);
                let mut bytes = Vec::new();
                while let Some(chunk) = response
                    .chunk()
                    .await
                    .map_err(|_| "HTTP response interrupted".to_owned())?
                {
                    if bytes.len() + chunk.len() > limit {
                        return Err("HTTP response exceeds its size limit".into());
                    }
                    bytes.extend_from_slice(&chunk);
                }
                Ok((status, bytes, retry))
            };
            tokio::pin!(operation);
            loop {
                if cancel.load(Ordering::Relaxed) {
                    return Err("Request cancelled".into());
                }
                tokio::select! {
                    result = &mut operation => return result,
                    _ = tokio::time::sleep(Duration::from_millis(50)) => {}
                }
            }
        })
}
