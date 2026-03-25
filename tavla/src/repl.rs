//! Async REPL — blocking stdin thread + mpsc channel.
//!
//! Uses a dedicated OS thread for synchronous stdin reading,
//! sends lines to the async runtime via mpsc. The main select!
//! loop processes both user input and inbound gossip messages.

use std::sync::Arc;

use tokio::sync::mpsc;

use crate::transport::{InboundMessage, Transport};
use crate::{EpistemicStance, GossipNode, GossipOp, TrustPolicy, WireMessage};

/// Run the interactive REPL.
pub async fn run_repl(node: &mut GossipNode, transport: Arc<dyn Transport>) {
    let (stdin_tx, mut stdin_rx) = mpsc::unbounded_channel::<String>();

    // Spawn blocking stdin reader on a dedicated OS thread.
    std::thread::spawn(move || {
        let stdin = std::io::stdin();
        let mut buf = String::new();
        loop {
            buf.clear();
            match std::io::BufRead::read_line(&mut stdin.lock(), &mut buf) {
                Ok(0) => break,
                Ok(_) => {
                    let line = buf.trim().to_string();
                    if !line.is_empty() {
                        if stdin_tx.send(line).is_err() {
                            break;
                        }
                    }
                }
                Err(_) => break,
            }
        }
    });

    println!("[tavla] REPL ready. Commands:");
    println!("  <lojban>         — assert (ja'o deduced) and broadcast");
    println!("  ~<lojban>        — assert (ba'a expected) and broadcast");
    println!("  ?~<lojban>       — assert (pe'i opinion) and broadcast");
    println!("  ?<query>         — query local KB with proof + epistemic sources");
    println!("  :peers           — list connected peers");
    println!("  :sync <peer>     — request sync from peer");
    println!("  :log             — show CRDT log");
    println!("  :retract <id>    — retract an envelope by ID prefix");
    println!("  :rebuild         — rebuild KB from CRDT log");
    println!("  :trust <peer>    — trust a peer (general)");
    println!("  :trust <p> <t>   — trust a peer for a topic");
    println!("  :distrust <peer> — revoke trust for a peer");
    println!("  :trustlist       — show all trust assertions");
    println!("  :policy [mode]   — show or set trust policy");
    println!("  :contradictions  — show detected contradictions");
    println!("  :resolve <id>    — resolve a contradiction");
    println!("  :quit            — exit");
    print!("tavla> ");
    use std::io::Write;
    let _ = std::io::stdout().flush();

    loop {
        tokio::select! {
            Some(line) = stdin_rx.recv() => {
                handle_command(&line, node, &transport).await;
                print!("tavla> ");
                let _ = std::io::stdout().flush();
            }
            Ok(inbound) = transport.recv() => {
                handle_inbound(inbound, node, &transport).await;
                print!("tavla> ");
                let _ = std::io::stdout().flush();
            }
        }
    }
}

/// Handle a user command from the REPL.
async fn handle_command(line: &str, node: &mut GossipNode, transport: &Arc<dyn Transport>) {
    if line.starts_with(':') {
        let parts: Vec<&str> = line.splitn(2, ' ').collect();
        let cmd = parts[0];
        let arg = parts.get(1).map(|s| s.trim()).unwrap_or("");

        match cmd {
            ":peers" => {
                let peers = transport.peers();
                if peers.is_empty() {
                    println!("  (no peers connected)");
                } else {
                    for p in &peers {
                        println!("  {p}");
                    }
                }
            }
            ":sync" => {
                if arg.is_empty() {
                    println!("  usage: :sync <peer>");
                    return;
                }
                let clock = node.get_clock().clone();
                let msg = WireMessage::SyncRequest { clock };
                match transport.send_to(arg, &msg).await {
                    Ok(()) => println!("  sync request sent to {arg}"),
                    Err(e) => println!("  error: {e}"),
                }
            }
            ":log" => {
                let all = node.log();
                let active = node.active_count();
                let quarantined = node.quarantined_count();
                let tombstoned = node.crdt_log().tombstones.len();
                println!(
                    "  {} envelopes ({} active, {} quarantined, {} tombstoned)",
                    all.len(),
                    active,
                    quarantined,
                    tombstoned
                );
                for env in &all {
                    let status = if node.crdt_log().is_tombstoned(&env.id) {
                        "✗"
                    } else if env.quarantined {
                        "⚠"
                    } else {
                        match &env.op {
                            GossipOp::Retract(_) => "⊘",
                            _ => "✓",
                        }
                    };
                    let op_str = match &env.op {
                        GossipOp::AssertLojban(s) => format!("\"{}\"", s),
                        GossipOp::AssertDirect { relation, args } => {
                            format!("{}({})", relation, args.join(", "))
                        }
                        GossipOp::Retract(id) => {
                            format!("retract({}...)", &id[..12.min(id.len())])
                        }
                    };
                    println!(
                        "  {} [{}] {} by {} [{}...]",
                        status,
                        env.stance,
                        op_str,
                        env.author,
                        &env.id[..12.min(env.id.len())]
                    );
                }
            }
            ":retract" => {
                if arg.is_empty() {
                    println!("  usage: :retract <envelope-id-prefix>");
                    return;
                }
                let all = node.log();
                let matches: Vec<_> = all.iter().filter(|env| env.id.starts_with(arg)).collect();
                match matches.len() {
                    0 => println!("  no envelope matching prefix '{arg}'"),
                    1 => {
                        let target_id = matches[0].id.clone();
                        match node.retract_local(&target_id) {
                            Ok(tombstone_env) => {
                                let msg = WireMessage::Envelope(tombstone_env);
                                if let Err(e) = transport.broadcast(&msg).await {
                                    eprintln!("[tavla] broadcast retraction error: {e}");
                                }
                            }
                            Err(e) => println!("  retract error: {e}"),
                        }
                    }
                    n => println!("  ambiguous: {n} envelopes match prefix '{arg}'"),
                }
            }
            ":rebuild" => {
                node.rebuild_kb();
            }
            ":trust" => {
                if arg.is_empty() {
                    println!("  usage: :trust <peer> [topic]");
                    return;
                }
                let trust_parts: Vec<&str> = arg.splitn(2, ' ').collect();
                let peer = trust_parts[0];
                let result = if trust_parts.len() > 1 {
                    let topic = trust_parts[1].trim();
                    node.trust_topic(peer, topic)
                } else {
                    node.trust(peer)
                };
                match result {
                    Ok(envelope) => {
                        // Broadcast the trust assertion.
                        let msg = WireMessage::Envelope(envelope);
                        if let Err(e) = transport.broadcast(&msg).await {
                            eprintln!("[tavla] broadcast trust error: {e}");
                        }
                        // Re-evaluate quarantined envelopes.
                        node.reevaluate_quarantine();
                    }
                    Err(e) => println!("  trust error: {e}"),
                }
            }
            ":distrust" => {
                if arg.is_empty() {
                    println!("  usage: :distrust <peer>");
                    return;
                }
                match node.distrust(arg) {
                    Ok(tombstones) => {
                        for t in tombstones {
                            let msg = WireMessage::Envelope(t);
                            if let Err(e) = transport.broadcast(&msg).await {
                                eprintln!("[tavla] broadcast distrust error: {e}");
                            }
                        }
                    }
                    Err(e) => println!("  distrust error: {e}"),
                }
            }
            ":trustlist" => {
                let trusts = node.trust_list();
                if trusts.is_empty() {
                    println!("  (no trust assertions)");
                } else {
                    for t in &trusts {
                        println!("  {t}");
                    }
                }
            }
            ":policy" => {
                if arg.is_empty() {
                    let policy_str = match &node.trust_policy {
                        TrustPolicy::AcceptAll => "accept-all",
                        TrustPolicy::TrustRequired => "trust-required",
                        TrustPolicy::QuarantineUntrusted => "quarantine-untrusted",
                    };
                    println!("  trust policy: {policy_str}");
                } else {
                    match arg {
                        "accept-all" => {
                            node.trust_policy = TrustPolicy::AcceptAll;
                            println!("  trust policy set to: accept-all");
                        }
                        "trust-required" => {
                            node.trust_policy = TrustPolicy::TrustRequired;
                            println!("  trust policy set to: trust-required");
                        }
                        "quarantine-untrusted" | "quarantine" => {
                            node.trust_policy = TrustPolicy::QuarantineUntrusted;
                            println!("  trust policy set to: quarantine-untrusted");
                        }
                        other => {
                            println!("  unknown policy: {other}");
                            println!("  options: accept-all, trust-required, quarantine-untrusted");
                        }
                    }
                }
            }
            ":contradictions" => {
                let contras = node.contradictions();
                if contras.is_empty() {
                    println!("  (no contradictions detected)");
                } else {
                    let unresolved = node.unresolved_contradiction_count();
                    println!(
                        "  {} contradiction(s) ({} unresolved)",
                        contras.len(),
                        unresolved
                    );
                    for c in contras {
                        let status = if c.resolved { "✓" } else { "⚡" };
                        println!(
                            "  {} #{}: {:?} by {} [{}...]",
                            status,
                            c.id,
                            c.assertion,
                            c.author,
                            &c.envelope_id[..12.min(c.envelope_id.len())]
                        );
                    }
                }
            }
            ":resolve" => {
                if arg.is_empty() {
                    println!("  usage: :resolve <contradiction-id>");
                    return;
                }
                match arg.parse::<usize>() {
                    Ok(id) => match node.resolve_contradiction(id) {
                        Ok(()) => println!("  contradiction #{id} resolved"),
                        Err(e) => println!("  {e}"),
                    },
                    Err(_) => println!("  invalid ID: {arg}"),
                }
            }
            ":quit" => {
                println!("[tavla] co'o");
                transport.shutdown().await;
                std::process::exit(0);
            }
            other => {
                println!("  unknown command: {other}");
            }
        }
    } else if let Some(query) = line.strip_prefix('?') {
        // Query — but NOT "?~" which is opinion prefix.
        if query.starts_with('~') {
            // ?~ = Opinion assertion prefix.
            let text = query[1..].trim();
            if text.is_empty() {
                println!("  usage: ?~<lojban> — assert as opinion (pe'i)");
                return;
            }
            match node.assert_local_with_stance(text, EpistemicStance::Opinion) {
                Ok(envelope) => {
                    let msg = WireMessage::Envelope(envelope);
                    if let Err(e) = transport.broadcast(&msg).await {
                        eprintln!("[tavla] broadcast error: {e}");
                    }
                }
                Err(e) => println!("[tavla] assert error: {e}"),
            }
        } else {
            let query = query.trim();
            match node.query_with_proof(query) {
                Ok((holds, proof, _json)) => {
                    println!(
                        "  {} → {}",
                        query,
                        if holds {
                            "JETNU (TRUE)"
                        } else {
                            "JITFA (FALSE)"
                        }
                    );
                    if holds {
                        // Show epistemic sources.
                        let sources = node.epistemic_sources(query);
                        if !sources.is_empty() {
                            let formatted: Vec<String> =
                                sources.iter().map(GossipNode::format_source).collect();
                            println!("  Sources: {}", formatted.join(", "));
                            if let Some(strongest) = GossipNode::strongest_source(&sources) {
                                println!("  Strongest: {}", GossipNode::format_source(strongest));
                            }
                        }
                        println!("{proof}");
                    }
                }
                Err(e) => println!("  query error: {e}"),
            }
        }
    } else if let Some(text) = line.strip_prefix('~') {
        // ~ = Expected assertion prefix (ba'a).
        let text = text.trim();
        if text.is_empty() {
            println!("  usage: ~<lojban> — assert as expected (ba'a)");
            return;
        }
        match node.assert_local_with_stance(text, EpistemicStance::Expected) {
            Ok(envelope) => {
                let msg = WireMessage::Envelope(envelope);
                if let Err(e) = transport.broadcast(&msg).await {
                    eprintln!("[tavla] broadcast error: {e}");
                }
            }
            Err(e) => println!("[tavla] assert error: {e}"),
        }
    } else {
        // Bare text = Deduced assertion (ja'o).
        match node.assert_local(line) {
            Ok(envelope) => {
                let msg = WireMessage::Envelope(envelope);
                if let Err(e) = transport.broadcast(&msg).await {
                    eprintln!("[tavla] broadcast error: {e}");
                }
            }
            Err(e) => println!("[tavla] assert error: {e}"),
        }
    }
}

/// Handle an inbound gossip message from the network.
async fn handle_inbound(
    inbound: InboundMessage,
    node: &mut GossipNode,
    transport: &Arc<dyn Transport>,
) {
    let InboundMessage { peer_id, message } = inbound;
    match message {
        WireMessage::Envelope(envelope) => {
            // Forward to other peers (epidemic gossip) before ingesting.
            let forward_msg = WireMessage::Envelope(envelope.clone());
            let forward_peers: Vec<String> = transport
                .peers()
                .into_iter()
                .filter(|p| *p != peer_id)
                .collect();
            for p in &forward_peers {
                let _ = transport.send_to(p, &forward_msg).await;
            }

            match node.ingest_from(envelope, Some(&peer_id)) {
                Ok(_result) => {}
                Err(e) => {
                    eprintln!("[tavla] ✗ rejected from {peer_id}: {e}");
                }
            }
        }
        WireMessage::SyncRequest { clock } => {
            let missing = node.sync_diff(&clock);
            let count = missing.len();
            let msg = WireMessage::SyncResponse { envelopes: missing };
            if let Err(e) = transport.send_to(&peer_id, &msg).await {
                eprintln!("[tavla] sync response error: {e}");
            } else {
                println!("[tavla] → {peer_id}: sync_response ({count} envelopes)");
            }
        }
        WireMessage::SyncResponse { envelopes } => {
            let count = envelopes.len();
            println!("[tavla] ← {peer_id}: sync_response ({count} envelopes)");
            for envelope in envelopes {
                if let Err(e) = node.ingest_from(envelope, Some(&peer_id)) {
                    eprintln!("[tavla] ✗ sync ingest error: {e}");
                }
            }
        }
    }
}
