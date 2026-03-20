//! TCP transport — JSON Lines over TCP streams.
//!
//! Each peer connection spawns a reader task that deserializes WireMessages
//! and forwards them into a shared mpsc channel. Write access is per-peer
//! via a dedicated sender.

use std::collections::HashMap;
use std::sync::Arc;

use async_trait::async_trait;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{mpsc, Mutex};

use crate::transport::{InboundMessage, Transport};
use crate::WireMessage;

/// Per-peer writer handle.
struct PeerHandle {
    tx: mpsc::UnboundedSender<Vec<u8>>,
}

/// TCP transport state.
pub struct TcpTransport {
    /// Inbound messages from all peers.
    inbound_rx: Mutex<mpsc::UnboundedReceiver<InboundMessage>>,
    inbound_tx: mpsc::UnboundedSender<InboundMessage>,
    /// Per-peer writer channels.
    peers: Arc<Mutex<HashMap<String, PeerHandle>>>,
    /// Our listen address (for logging).
    listen_addr: String,
}

impl TcpTransport {
    /// Create a new TCP transport, bind the listener, and start accepting.
    pub async fn new(
        listen_addr: &str,
        initial_peers: &[String],
        our_name: &str,
    ) -> Result<Arc<Self>, String> {
        let listener = TcpListener::bind(listen_addr)
            .await
            .map_err(|e| format!("TCP bind {listen_addr}: {e}"))?;

        let (inbound_tx, inbound_rx) = mpsc::unbounded_channel();
        let peers: Arc<Mutex<HashMap<String, PeerHandle>>> =
            Arc::new(Mutex::new(HashMap::new()));

        let transport = Arc::new(TcpTransport {
            inbound_rx: Mutex::new(inbound_rx),
            inbound_tx: inbound_tx.clone(),
            peers: peers.clone(),
            listen_addr: listen_addr.to_string(),
        });

        // Spawn listener task.
        let inbound_tx2 = inbound_tx.clone();
        let peers2 = peers.clone();
        tokio::spawn(async move {
            loop {
                match listener.accept().await {
                    Ok((stream, addr)) => {
                        let addr_str = addr.to_string();
                        println!("[tavla] + incoming connection from {addr_str}");
                        let peers3 = peers2.clone();
                        let inbound_tx3 = inbound_tx2.clone();
                        // Spawn so we don't block the accept loop while
                        // waiting for the handshake line.
                        tokio::spawn(async move {
                            Self::accept_with_handshake(
                                stream, addr_str, peers3, inbound_tx3,
                            )
                            .await;
                        });
                    }
                    Err(e) => {
                        eprintln!("[tavla] accept error: {e}");
                    }
                }
            }
        });

        // Connect to initial peers.
        let our_name = our_name.to_string();
        for addr in initial_peers {
            let addr = addr.clone();
            let inbound_tx = inbound_tx.clone();
            let peers = peers.clone();
            let name = our_name.clone();
            tokio::spawn(async move {
                Self::connect_with_retry(&addr, &name, peers, inbound_tx).await;
            });
        }

        Ok(transport)
    }

    /// Read the first line from an incoming connection as the peer name,
    /// then register the stream.  Falls back to the socket address if the
    /// handshake times out or fails.
    async fn accept_with_handshake(
        stream: TcpStream,
        addr: String,
        peers: Arc<Mutex<HashMap<String, PeerHandle>>>,
        inbound_tx: mpsc::UnboundedSender<InboundMessage>,
    ) {
        let (read_half, write_half) = stream.into_split();
        let mut reader = BufReader::new(read_half);
        let mut first_line = String::new();

        // Give the peer 5 seconds to send its name.
        let peer_id = match tokio::time::timeout(
            std::time::Duration::from_secs(5),
            reader.read_line(&mut first_line),
        )
        .await
        {
            Ok(Ok(n)) if n > 0 => {
                let name = first_line.trim().to_string();
                if name.is_empty() { addr } else {
                    println!("[tavla] + peer identified as {name}");
                    name
                }
            }
            _ => addr,
        };

        // Reconstruct stream parts for register_peer_stream_split.
        Self::register_peer_stream_split(peer_id, reader, write_half, peers, inbound_tx).await;
    }

    /// Connect to a peer with retry (3 attempts, 3s backoff).
    async fn connect_with_retry(
        addr: &str,
        our_name: &str,
        peers: Arc<Mutex<HashMap<String, PeerHandle>>>,
        inbound_tx: mpsc::UnboundedSender<InboundMessage>,
    ) {
        for attempt in 1..=3 {
            match TcpStream::connect(addr).await {
                Ok(mut stream) => {
                    // Send our name as the first line so the peer knows who we are.
                    let hello = format!("{}\n", our_name);
                    if stream.write_all(hello.as_bytes()).await.is_err() {
                        continue;
                    }
                    println!("[tavla] → connected to {addr}");
                    Self::register_peer_stream(
                        addr.to_string(),
                        stream,
                        peers,
                        inbound_tx,
                    )
                    .await;
                    return;
                }
                Err(e) => {
                    eprintln!(
                        "[tavla] ~ connect to {addr} failed (attempt {attempt}/3): {e}"
                    );
                    if attempt < 3 {
                        tokio::time::sleep(std::time::Duration::from_secs(3)).await;
                    }
                }
            }
        }
        eprintln!("[tavla] ✗ giving up on {addr} after 3 attempts");
    }

    /// Register a TCP stream: spawn reader and writer tasks.
    async fn register_peer_stream(
        peer_id: String,
        stream: TcpStream,
        peers: Arc<Mutex<HashMap<String, PeerHandle>>>,
        inbound_tx: mpsc::UnboundedSender<InboundMessage>,
    ) {
        let (read_half, write_half) = stream.into_split();
        let reader = BufReader::new(read_half);
        Self::register_peer_stream_split(peer_id, reader, write_half, peers, inbound_tx).await;
    }

    /// Register pre-split reader/writer (used after handshake consumes the first line).
    async fn register_peer_stream_split(
        peer_id: String,
        reader: BufReader<tokio::net::tcp::OwnedReadHalf>,
        write_half: tokio::net::tcp::OwnedWriteHalf,
        peers: Arc<Mutex<HashMap<String, PeerHandle>>>,
        inbound_tx: mpsc::UnboundedSender<InboundMessage>,
    ) {
        // Writer task: drains the per-peer channel and writes to the stream.
        let (write_tx, mut write_rx) = mpsc::unbounded_channel::<Vec<u8>>();
        let peer_id_w = peer_id.clone();
        let peers_w = peers.clone();
        tokio::spawn(async move {
            let mut writer = write_half;
            while let Some(data) = write_rx.recv().await {
                if writer.write_all(&data).await.is_err() {
                    eprintln!("[tavla] ~ write failed to {peer_id_w}");
                    break;
                }
                if writer.flush().await.is_err() {
                    break;
                }
            }
            peers_w.lock().await.remove(&peer_id_w);
        });

        // Store the peer handle.
        peers
            .lock()
            .await
            .insert(peer_id.clone(), PeerHandle { tx: write_tx });

        // Reader task: reads JSON Lines, deserializes, forwards to inbound channel.
        let peers_r = peers.clone();
        let peer_id_r = peer_id.clone();
        tokio::spawn(async move {
            let mut reader = reader;
            let mut line = String::new();
            loop {
                line.clear();
                match reader.read_line(&mut line).await {
                    Ok(0) => {
                        // EOF — peer disconnected.
                        println!("[tavla] ~ {peer_id_r} disconnected");
                        break;
                    }
                    Ok(_) => {
                        let trimmed = line.trim();
                        if trimmed.is_empty() {
                            continue;
                        }
                        match serde_json::from_str::<WireMessage>(trimmed) {
                            Ok(msg) => {
                                let _ = inbound_tx.send(InboundMessage {
                                    peer_id: peer_id_r.clone(),
                                    message: msg,
                                });
                            }
                            Err(e) => {
                                eprintln!(
                                    "[tavla] ~ bad JSON from {peer_id_r}: {e}"
                                );
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("[tavla] ~ read error from {peer_id_r}: {e}");
                        break;
                    }
                }
            }
            // Remove peer on disconnect.
            peers_r.lock().await.remove(&peer_id_r);
        });
    }

    /// Serialize a WireMessage to JSON Lines bytes.
    fn encode(msg: &WireMessage) -> Result<Vec<u8>, String> {
        let mut bytes =
            serde_json::to_vec(msg).map_err(|e| format!("serialize: {e}"))?;
        bytes.push(b'\n');
        Ok(bytes)
    }
}

#[async_trait]
impl Transport for TcpTransport {
    async fn send_to(&self, peer: &str, msg: &WireMessage) -> Result<(), String> {
        let data = Self::encode(msg)?;
        let peers = self.peers.lock().await;
        if let Some(handle) = peers.get(peer) {
            handle
                .tx
                .send(data)
                .map_err(|_| format!("peer {peer} writer closed"))
        } else {
            Err(format!("peer {peer} not connected"))
        }
    }

    async fn broadcast(&self, msg: &WireMessage) -> Result<(), String> {
        let data = Self::encode(msg)?;
        let peers = self.peers.lock().await;
        for (id, handle) in peers.iter() {
            if handle.tx.send(data.clone()).is_err() {
                eprintln!("[tavla] ~ broadcast failed to {id} (writer closed)");
            }
        }
        Ok(())
    }

    async fn recv(&self) -> Result<InboundMessage, String> {
        let mut rx = self.inbound_rx.lock().await;
        rx.recv()
            .await
            .ok_or_else(|| "all transports closed".to_string())
    }

    fn peers(&self) -> Vec<String> {
        // Can't async here, try_lock is best effort.
        match self.peers.try_lock() {
            Ok(p) => p.keys().cloned().collect(),
            Err(_) => vec![],
        }
    }

    async fn shutdown(&self) {
        let mut peers = self.peers.lock().await;
        peers.clear(); // Dropping senders closes writer tasks.
        println!("[tavla] TCP transport shut down ({})", self.listen_addr);
    }
}
