//! Transport abstraction — TCP and WebRTC share the same trait.
//!
//! The gossip logic (REPL, ingest, broadcast) is transport-agnostic.
//! WireMessage JSON Lines format is identical across both transports.

use async_trait::async_trait;

use crate::WireMessage;

/// Inbound message: who sent it, and what did they say.
pub struct InboundMessage {
    pub peer_id: String,
    pub message: WireMessage,
}

/// Abstract transport for gossip networking.
#[async_trait]
pub trait Transport: Send + Sync {
    /// Send a WireMessage to a specific peer.
    async fn send_to(&self, peer: &str, msg: &WireMessage) -> Result<(), String>;

    /// Broadcast a WireMessage to all connected peers.
    async fn broadcast(&self, msg: &WireMessage) -> Result<(), String>;

    /// Receive the next inbound message. Blocks until one arrives.
    async fn recv(&self) -> Result<InboundMessage, String>;

    /// List connected peer IDs.
    fn peers(&self) -> Vec<String>;

    /// Shut down all connections.
    async fn shutdown(&self);
}
