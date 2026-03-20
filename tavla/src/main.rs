//! tavla — nibli gossip daemon
//!
//! lo tavla — lo fatri ke logji ciste
//!
//! Dual transport gossip daemon: TCP for dev, WebRTC for production P2P.

use std::sync::Arc;

use clap::{Parser, ValueEnum};
use tavla::transport::Transport;

/// tavla — nibli gossip daemon
#[derive(Parser)]
#[command(name = "tavla", about = "nibli gossip daemon — lo fatri ke logji ciste")]
struct Cli {
    /// Agent name (your identity on the gossip network).
    #[arg(long)]
    name: String,

    /// Listen address for TCP transport.
    #[arg(long, default_value = "127.0.0.1:7001")]
    listen: String,

    /// Peer addresses to connect to (TCP: host:port, WebRTC: peer name).
    #[arg(long)]
    peer: Vec<String>,

    /// Transport mode: tcp, webrtc, or both (default).
    #[arg(long, value_enum, default_value = "both")]
    transport: TransportMode,

    /// Signaling server URL for WebRTC (e.g., http://localhost:9090).
    #[arg(long)]
    signal: Option<String>,

    /// Run an embedded signaling server on this port.
    #[arg(long)]
    signal_server: Option<u16>,

    /// STUN server URL. Use "none" to disable (LAN-only).
    #[arg(long, env = "NIBLI_STUN_URL")]
    stun: Option<String>,

    /// Trust policy: accept-all, trust-required, quarantine-untrusted.
    #[arg(long, value_enum, default_value = "accept-all")]
    policy: CliTrustPolicy,
}

#[derive(Clone, ValueEnum)]
enum TransportMode {
    Tcp,
    Webrtc,
    Both,
}

#[derive(Clone, ValueEnum)]
enum CliTrustPolicy {
    AcceptAll,
    TrustRequired,
    QuarantineUntrusted,
}

impl CliTrustPolicy {
    fn to_trust_policy(&self) -> tavla::TrustPolicy {
        match self {
            CliTrustPolicy::AcceptAll => tavla::TrustPolicy::AcceptAll,
            CliTrustPolicy::TrustRequired => tavla::TrustPolicy::TrustRequired,
            CliTrustPolicy::QuarantineUntrusted => tavla::TrustPolicy::QuarantineUntrusted,
        }
    }
}

#[tokio::main]
async fn main() {
    let cli = Cli::parse();

    println!(".i tavla — lo fatri ke logji ciste");
    println!("agent: {}", cli.name);

    // Optionally start embedded signaling server.
    if let Some(port) = cli.signal_server {
        tokio::spawn(async move {
            if let Err(e) = tavla::signal::run_signal_server(port).await {
                eprintln!("[signal] error: {e}");
            }
        });
        // Give the server a moment to bind.
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    }

    let mut node = tavla::GossipNode::with_policy(&cli.name, cli.policy.to_trust_policy());

    match cli.transport {
        TransportMode::Tcp => {
            run_tcp(&cli, &mut node).await;
        }
        TransportMode::Webrtc => {
            run_webrtc(&cli, &mut node).await;
        }
        TransportMode::Both => {
            run_both(&cli, &mut node).await;
        }
    }
}

/// TCP-only mode.
async fn run_tcp(cli: &Cli, node: &mut tavla::GossipNode) {
    let transport = tavla::tcp::TcpTransport::new(
        &cli.listen,
        &cli.peer,
        &cli.name,
    )
    .await
    .expect("TCP transport failed to start");
    println!("[tavla] TCP listening on {}", cli.listen);
    tavla::repl::run_repl(node, transport as Arc<dyn Transport>).await;
}

/// WebRTC-only mode.
#[cfg(feature = "webrtc-transport")]
async fn run_webrtc(cli: &Cli, node: &mut tavla::GossipNode) {
    let signal_url = cli.signal.as_deref().expect("--signal required for WebRTC mode");
    let stun_servers = parse_stun(&cli.stun);
    let transport = tavla::webrtc::WebRtcTransport::new(
        &cli.name,
        signal_url,
        stun_servers,
    )
    .await
    .expect("WebRTC transport failed to start");

    for peer in &cli.peer {
        if let Err(e) = transport.connect_to_peer(peer).await {
            eprintln!("[tavla] WebRTC connect to {peer}: {e}");
        }
    }

    let t2 = transport.clone();
    tokio::spawn(async move {
        loop {
            if let Err(_e) = t2.listen_for_offers().await {
                tokio::time::sleep(std::time::Duration::from_secs(2)).await;
            }
        }
    });

    tavla::repl::run_repl(node, transport as Arc<dyn Transport>).await;
}

#[cfg(not(feature = "webrtc-transport"))]
async fn run_webrtc(cli: &Cli, node: &mut tavla::GossipNode) {
    eprintln!("[tavla] WebRTC not available — build with --features webrtc-transport");
    eprintln!("[tavla] falling back to TCP");
    run_tcp(cli, node).await;
}

/// Both transports (default). TCP always starts; WebRTC added if feature is enabled.
#[cfg(feature = "webrtc-transport")]
async fn run_both(cli: &Cli, node: &mut tavla::GossipNode) {
    // Start TCP as the primary transport.
    let transport = tavla::tcp::TcpTransport::new(
        &cli.listen,
        &cli.peer,
        &cli.name,
    )
    .await
    .expect("TCP transport failed to start");
    println!("[tavla] TCP listening on {}", cli.listen);

    // If signaling server is configured, also set up WebRTC in background.
    if let Some(signal_url) = &cli.signal {
        let stun_servers = parse_stun(&cli.stun);
        match tavla::webrtc::WebRtcTransport::new(&cli.name, signal_url, stun_servers).await {
            Ok(webrtc) => {
                println!("[tavla] WebRTC transport ready (signal: {signal_url})");
                let w = webrtc.clone();
                tokio::spawn(async move {
                    loop {
                        if let Err(_e) = w.listen_for_offers().await {
                            tokio::time::sleep(std::time::Duration::from_secs(2)).await;
                        }
                    }
                });
            }
            Err(e) => {
                eprintln!("[tavla] WebRTC setup failed: {e} (TCP-only)");
            }
        }
    }

    tavla::repl::run_repl(node, transport as Arc<dyn Transport>).await;
}

#[cfg(not(feature = "webrtc-transport"))]
async fn run_both(cli: &Cli, node: &mut tavla::GossipNode) {
    // WebRTC not compiled — just run TCP.
    run_tcp(cli, node).await;
}

fn parse_stun(stun: &Option<String>) -> Vec<String> {
    match stun.as_deref() {
        Some("none") | Some("") => vec![],
        Some(url) => vec![url.to_string()],
        None => vec!["stun:stun.l.google.com:19302".to_string()],
    }
}
