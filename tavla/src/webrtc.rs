//! WebRTC DataChannel transport — NAT-traversing P2P gossip.
//!
//! Uses webrtc-rs DataChannels in reliable ordered mode (equivalent to TCP).
//! The wire protocol (WireMessage JSON Lines) is identical to TCP.
//! Connection setup uses the signaling server (signal.rs) for SDP exchange.

#[cfg(feature = "webrtc-transport")]
mod inner {
    use std::collections::HashMap;
    use std::sync::Arc;

    use async_trait::async_trait;
    use tokio::sync::{Mutex, mpsc};
    use webrtc::api::APIBuilder;
    use webrtc::api::interceptor_registry::register_default_interceptors;
    use webrtc::api::media_engine::MediaEngine;
    use webrtc::data_channel::RTCDataChannel;
    use webrtc::data_channel::data_channel_message::DataChannelMessage;
    use webrtc::ice_transport::ice_server::RTCIceServer;
    use webrtc::interceptor::registry::Registry;
    use webrtc::peer_connection::RTCPeerConnection;
    use webrtc::peer_connection::configuration::RTCConfiguration;
    use webrtc::peer_connection::sdp::session_description::RTCSessionDescription;

    use crate::WireMessage;
    use crate::signal::SdpExchange;
    use crate::transport::{InboundMessage, Transport};

    /// Per-peer WebRTC state.
    struct WebRtcPeer {
        dc: Arc<RTCDataChannel>,
        _pc: Arc<RTCPeerConnection>,
    }

    /// WebRTC transport state.
    pub struct WebRtcTransport {
        inbound_rx: Mutex<mpsc::UnboundedReceiver<InboundMessage>>,
        inbound_tx: mpsc::UnboundedSender<InboundMessage>,
        peers: Arc<Mutex<HashMap<String, WebRtcPeer>>>,
        stun_servers: Vec<String>,
        signal_url: String,
        our_name: String,
    }

    impl WebRtcTransport {
        pub async fn new(
            our_name: &str,
            signal_url: &str,
            stun_servers: Vec<String>,
        ) -> Result<Arc<Self>, String> {
            let (inbound_tx, inbound_rx) = mpsc::unbounded_channel();
            Ok(Arc::new(Self {
                inbound_rx: Mutex::new(inbound_rx),
                inbound_tx,
                peers: Arc::new(Mutex::new(HashMap::new())),
                stun_servers,
                signal_url: signal_url.to_string(),
                our_name: our_name.to_string(),
            }))
        }

        fn build_config(&self) -> RTCConfiguration {
            let ice_servers = if self.stun_servers.is_empty() {
                vec![]
            } else {
                vec![RTCIceServer {
                    urls: self.stun_servers.clone(),
                    ..Default::default()
                }]
            };
            RTCConfiguration {
                ice_servers,
                ..Default::default()
            }
        }

        async fn create_peer_connection(&self) -> Result<Arc<RTCPeerConnection>, String> {
            let mut m = MediaEngine::default();
            m.register_default_codecs()
                .map_err(|e| format!("media engine: {e}"))?;
            let mut registry = Registry::new();
            registry = register_default_interceptors(registry, &mut m)
                .map_err(|e| format!("interceptors: {e}"))?;
            let api = APIBuilder::new()
                .with_media_engine(m)
                .with_interceptor_registry(registry)
                .build();
            let pc = api
                .new_peer_connection(self.build_config())
                .await
                .map_err(|e| format!("peer connection: {e}"))?;
            Ok(Arc::new(pc))
        }

        /// Initiate a WebRTC connection to a named peer via signaling.
        pub async fn connect_to_peer(self: &Arc<Self>, peer_name: &str) -> Result<(), String> {
            let pc = self.create_peer_connection().await?;

            // Create data channel.
            let dc = pc
                .create_data_channel("tavla", None)
                .await
                .map_err(|e| format!("create data channel: {e}"))?;

            // Set up inbound message handler.
            let inbound_tx = self.inbound_tx.clone();
            let peer_id = peer_name.to_string();
            dc.on_message(Box::new(move |msg: DataChannelMessage| {
                let peer_id = peer_id.clone();
                let inbound_tx = inbound_tx.clone();
                Box::pin(async move {
                    let text = String::from_utf8_lossy(&msg.data);
                    for line in text.lines() {
                        if line.trim().is_empty() {
                            continue;
                        }
                        if let Ok(wire_msg) = serde_json::from_str::<WireMessage>(line) {
                            let _ = inbound_tx.send(InboundMessage {
                                peer_id: peer_id.clone(),
                                message: wire_msg,
                            });
                        }
                    }
                })
            }));

            // Create offer.
            let offer = pc
                .create_offer(None)
                .await
                .map_err(|e| format!("create offer: {e}"))?;
            pc.set_local_description(offer.clone())
                .await
                .map_err(|e| format!("set local desc: {e}"))?;

            // Wait for ICE gathering to complete.
            let (ice_done_tx, ice_done_rx) = tokio::sync::oneshot::channel::<()>();
            let ice_done_tx = Arc::new(Mutex::new(Some(ice_done_tx)));
            pc.on_ice_gathering_state_change(Box::new(move |state| {
                let ice_done_tx = ice_done_tx.clone();
                Box::pin(async move {
                    if state
                        == webrtc::ice_transport::ice_gatherer_state::RTCIceGathererState::Complete
                    {
                        if let Some(tx) = ice_done_tx.lock().await.take() {
                            let _ = tx.send(());
                        }
                    }
                })
            }));

            // Wait up to 10s for ICE.
            let _ = tokio::time::timeout(std::time::Duration::from_secs(10), ice_done_rx).await;

            let local_desc = pc.local_description().await.ok_or("no local description")?;
            let sdp_json =
                serde_json::to_string(&local_desc).map_err(|e| format!("serialize offer: {e}"))?;

            // Post offer to signaling server.
            let client = reqwest::Client::new();
            client
                .post(format!("{}/offer", self.signal_url))
                .json(&SdpExchange {
                    from: self.our_name.clone(),
                    to: peer_name.to_string(),
                    sdp: sdp_json,
                })
                .send()
                .await
                .map_err(|e| format!("post offer: {e}"))?;

            println!("[tavla] WebRTC offer sent to {peer_name}");

            // Fetch answer from signaling server.
            let resp: SdpExchange = client
                .get(format!("{}/answer/{}", self.signal_url, self.our_name))
                .send()
                .await
                .map_err(|e| format!("get answer: {e}"))?
                .json()
                .await
                .map_err(|e| format!("parse answer: {e}"))?;

            let answer: RTCSessionDescription = serde_json::from_str(&resp.sdp)
                .map_err(|e| format!("deserialize answer SDP: {e}"))?;
            pc.set_remote_description(answer)
                .await
                .map_err(|e| format!("set remote desc: {e}"))?;

            println!("[tavla] WebRTC connected to {peer_name}");

            // Store peer.
            self.peers
                .lock()
                .await
                .insert(peer_name.to_string(), WebRtcPeer { dc, _pc: pc });

            Ok(())
        }

        /// Listen for incoming WebRTC offers (poll signaling server).
        pub async fn listen_for_offers(self: &Arc<Self>) -> Result<(), String> {
            let client = reqwest::Client::new();

            // Poll for offers directed at us.
            let resp = client
                .get(format!("{}/offer/{}", self.signal_url, self.our_name))
                .send()
                .await
                .map_err(|e| format!("get offer: {e}"))?;

            if !resp.status().is_success() {
                return Err("no pending offer".to_string());
            }

            let exchange: SdpExchange =
                resp.json().await.map_err(|e| format!("parse offer: {e}"))?;

            let peer_name = exchange.from.clone();
            let offer: RTCSessionDescription = serde_json::from_str(&exchange.sdp)
                .map_err(|e| format!("deserialize offer SDP: {e}"))?;

            let pc = self.create_peer_connection().await?;
            pc.set_remote_description(offer)
                .await
                .map_err(|e| format!("set remote desc: {e}"))?;

            // Wait for the data channel from the offerer.
            let (dc_tx, dc_rx) = tokio::sync::oneshot::channel::<Arc<RTCDataChannel>>();
            let dc_tx = Arc::new(Mutex::new(Some(dc_tx)));
            let inbound_tx = self.inbound_tx.clone();
            let peer_id = peer_name.clone();
            pc.on_data_channel(Box::new(move |dc: Arc<RTCDataChannel>| {
                let dc_tx = dc_tx.clone();
                let inbound_tx = inbound_tx.clone();
                let peer_id = peer_id.clone();
                Box::pin(async move {
                    // Set up message handler.
                    dc.on_message(Box::new(move |msg: DataChannelMessage| {
                        let peer_id = peer_id.clone();
                        let inbound_tx = inbound_tx.clone();
                        Box::pin(async move {
                            let text = String::from_utf8_lossy(&msg.data);
                            for line in text.lines() {
                                if line.trim().is_empty() {
                                    continue;
                                }
                                if let Ok(wire_msg) = serde_json::from_str::<WireMessage>(line) {
                                    let _ = inbound_tx.send(InboundMessage {
                                        peer_id: peer_id.clone(),
                                        message: wire_msg,
                                    });
                                }
                            }
                        })
                    }));
                    if let Some(tx) = dc_tx.lock().await.take() {
                        let _ = tx.send(dc);
                    }
                })
            }));

            // Create answer.
            let answer = pc
                .create_answer(None)
                .await
                .map_err(|e| format!("create answer: {e}"))?;
            pc.set_local_description(answer.clone())
                .await
                .map_err(|e| format!("set local desc: {e}"))?;

            // Wait for ICE gathering.
            let (ice_done_tx, ice_done_rx) = tokio::sync::oneshot::channel::<()>();
            let ice_done_tx = Arc::new(Mutex::new(Some(ice_done_tx)));
            pc.on_ice_gathering_state_change(Box::new(move |state| {
                let ice_done_tx = ice_done_tx.clone();
                Box::pin(async move {
                    if state
                        == webrtc::ice_transport::ice_gatherer_state::RTCIceGathererState::Complete
                    {
                        if let Some(tx) = ice_done_tx.lock().await.take() {
                            let _ = tx.send(());
                        }
                    }
                })
            }));

            let _ = tokio::time::timeout(std::time::Duration::from_secs(10), ice_done_rx).await;

            let local_desc = pc.local_description().await.ok_or("no local description")?;
            let sdp_json =
                serde_json::to_string(&local_desc).map_err(|e| format!("serialize answer: {e}"))?;

            // Post answer to signaling server.
            client
                .post(format!("{}/answer", self.signal_url))
                .json(&SdpExchange {
                    from: self.our_name.clone(),
                    to: peer_name.clone(),
                    sdp: sdp_json,
                })
                .send()
                .await
                .map_err(|e| format!("post answer: {e}"))?;

            // Wait for data channel.
            let dc = tokio::time::timeout(std::time::Duration::from_secs(10), dc_rx)
                .await
                .map_err(|_| "timeout waiting for data channel".to_string())?
                .map_err(|_| "data channel sender dropped".to_string())?;

            println!("[tavla] WebRTC accepted from {peer_name}");

            self.peers
                .lock()
                .await
                .insert(peer_name, WebRtcPeer { dc, _pc: pc });

            Ok(())
        }
    }

    #[async_trait]
    impl Transport for WebRtcTransport {
        async fn send_to(&self, peer: &str, msg: &WireMessage) -> Result<(), String> {
            let data = serde_json::to_string(msg).map_err(|e| format!("serialize: {e}"))?;
            let data = format!("{data}\n");
            let peers = self.peers.lock().await;
            if let Some(p) = peers.get(peer) {
                p.dc.send_text(data)
                    .await
                    .map_err(|e| format!("send to {peer}: {e}"))?;
                Ok(())
            } else {
                Err(format!("peer {peer} not connected"))
            }
        }

        async fn broadcast(&self, msg: &WireMessage) -> Result<(), String> {
            let data = serde_json::to_string(msg).map_err(|e| format!("serialize: {e}"))?;
            let data = format!("{data}\n");
            let peers = self.peers.lock().await;
            for (id, p) in peers.iter() {
                if let Err(e) = p.dc.send_text(data.clone()).await {
                    eprintln!("[tavla] ~ WebRTC broadcast to {id} failed: {e}");
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
            match self.peers.try_lock() {
                Ok(p) => p.keys().cloned().collect(),
                Err(_) => vec![],
            }
        }

        async fn shutdown(&self) {
            let mut peers = self.peers.lock().await;
            peers.clear();
            println!("[tavla] WebRTC transport shut down");
        }
    }
}

#[cfg(feature = "webrtc-transport")]
pub use inner::WebRtcTransport;

/// Stub when webrtc feature is disabled.
#[cfg(not(feature = "webrtc-transport"))]
pub fn webrtc_unavailable() {
    eprintln!("[tavla] WebRTC transport not available — build with --features webrtc-transport");
}
