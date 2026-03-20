#!/usr/bin/env python3
"""
nibli_agent.py — LLM gossip agent for the tavla network.

Wraps the fine-tuned nibli-lojban-7b model as a gossip peer:
  1. Translates English → Lojban via the model
  2. Validates through nibli-validate (gerna gate)
  3. Sends valid assertions as gossip envelopes over TCP
  4. Listens for incoming gossip and translates Lojban → English

Usage:
    # Interactive mode — type English, gossip Lojban
    python3 python/nibli_agent.py --name fitness-agent --peer 127.0.0.1:7001

    # Auto-gossip mode — generate assertions on a topic
    python3 python/nibli_agent.py --name fitness-agent --peer 127.0.0.1:7001 \\
        --domain xadni --auto-gossip --topic "fitness and body recomposition"

    # With domain specialization
    python3 python/nibli_agent.py --name gaming-agent --domain kelci \\
        --peer 127.0.0.1:7001 --model models/nibli-lojban-7b
"""

import argparse
import hashlib
import json
import os
import socket
import subprocess
import sys
import threading
import time
from datetime import datetime, timezone
from pathlib import Path

# Optional: model inference (not needed for --no-model mode)
try:
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig
    from peft import PeftModel
    HAS_MODEL_DEPS = True
except ImportError:
    HAS_MODEL_DEPS = False

# Optional: auto-gossip needs anthropic or local model
try:
    import anthropic
    HAS_ANTHROPIC = True
except ImportError:
    HAS_ANTHROPIC = False


# ─── Constants ────────────────────────────────────────────────────

DEFAULT_MODEL_DIR = "models/nibli-lojban-7b"
BASE_MODEL = "Qwen/Qwen2.5-7B-Instruct"
MAX_RETRIES = 3

TRANSLATE_SYSTEM_PROMPT = (
    "You are a Lojban translator. Translate the English sentence to "
    "grammatically correct Lojban. Output ONLY the Lojban translation, "
    "nothing else."
)

REVERSE_SYSTEM_PROMPT = (
    "You are a Lojban translator. Translate the Lojban sentence to "
    "natural English. Output ONLY the English translation, nothing else."
)

AUTO_GOSSIP_SYSTEM_PROMPT = (
    "Generate a single factual English sentence about the given topic. "
    "Keep it simple, declarative, and suitable for formal logic representation. "
    "Output ONLY the sentence, nothing else."
)

# Domain → gismu topic tag mapping
DOMAIN_TOPICS = {
    "xadni": ["xadni", "kamni", "tsali"],
    "cidja": ["cidja", "citka", "xagji"],
    "kelci": ["kelci", "skami", "srana"],
    "krali": ["krali", "turni", "flalu"],
    "gerku": ["gerku", "danlu", "mabru"],
    "skami": ["skami", "datni", "ciste"],
}


# ─── Envelope construction ────────────────────────────────────────

def compute_envelope_id(author, clock, op, stance, topics, timestamp):
    """Compute SHA-256 envelope ID matching tavla's Envelope::compute_id."""
    canonical = json.dumps(
        {
            "author": author,
            "clock": clock,
            "op": op,
            "stance": stance,
            "topics": topics,
            "timestamp": timestamp,
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def make_envelope(author, clock, lojban, stance="Deduced", domain=None):
    """Build a gossip envelope for a Lojban assertion."""
    # Tick the clock.
    clock["entries"][author] = clock["entries"].get(author, 0) + 1

    op = {"AssertLojban": lojban}
    topics = extract_topics(lojban, domain)
    timestamp = datetime.now(timezone.utc).isoformat()

    envelope_id = compute_envelope_id(author, clock, op, stance, topics, timestamp)

    return {
        "type": "envelope",
        "id": envelope_id,
        "author": author,
        "clock": clock,
        "op": op,
        "stance": stance,
        "topics": topics,
        "timestamp": timestamp,
        "sig": [],
        "quarantined": False,
    }


def extract_topics(lojban, domain=None):
    """Extract topic tags from Lojban text (simple gismu extraction)."""
    # Known 5-letter gismu pattern.
    topics = set()
    if domain and domain in DOMAIN_TOPICS:
        topics.update(DOMAIN_TOPICS[domain])

    for word in lojban.split():
        word = word.strip(".")
        if len(word) == 5 and word.isalpha():
            topics.add(word)

    return sorted(topics)


# ─── Validation via nibli-validate ────────────────────────────────

def find_validate_binary():
    """Find the nibli-validate binary."""
    for candidate in ["target/debug/nibli-validate", "target/release/nibli-validate"]:
        if os.path.isfile(candidate):
            return candidate
    return None


def validate_lojban(sentence, validate_binary):
    """Validate a single Lojban sentence through nibli gerna. Returns True if valid."""
    if validate_binary is None:
        return False

    try:
        result = subprocess.run(
            [validate_binary],
            input=sentence + "\n",
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False

    for line in result.stdout.strip().split("\n"):
        line = line.strip()
        if line.startswith("{"):
            try:
                obj = json.loads(line)
                return obj.get("valid", False)
            except json.JSONDecodeError:
                continue

    return False


# ─── Translation (model or API) ──────────────────────────────────

class Translator:
    """Translates English↔Lojban using the fine-tuned model or Claude API fallback."""

    def __init__(self, model_dir=None, use_api=False):
        self.model = None
        self.tokenizer = None
        self.api_client = None
        self.use_api = use_api

        if use_api:
            if not HAS_ANTHROPIC:
                print("[agent] anthropic not installed, API mode unavailable", file=sys.stderr)
                sys.exit(1)
            api_key = os.environ.get("ANTHROPIC_API_KEY")
            if not api_key:
                print("[agent] ANTHROPIC_API_KEY not set", file=sys.stderr)
                sys.exit(1)
            self.api_client = anthropic.Anthropic(api_key=api_key)
            print("[agent] Using Claude API for translation")
        elif model_dir and HAS_MODEL_DEPS:
            self._load_model(model_dir)
        else:
            print("[agent] No model or API configured. Use --model or --use-api.", file=sys.stderr)
            sys.exit(1)

    def _load_model(self, model_dir):
        """Load the fine-tuned QLoRA model."""
        print(f"[agent] Loading model from {model_dir}...")
        bnb_config = BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_quant_type="nf4",
            bnb_4bit_compute_dtype=torch.bfloat16,
            bnb_4bit_use_double_quant=True,
        )

        metadata_path = Path(model_dir) / "training_metadata.json"
        base_model = BASE_MODEL
        if metadata_path.exists():
            with open(str(metadata_path)) as f:
                meta = json.load(f)
                base_model = meta.get("base_model", BASE_MODEL)

        self.model = AutoModelForCausalLM.from_pretrained(
            base_model,
            quantization_config=bnb_config,
            device_map="auto",
            torch_dtype=torch.bfloat16,
            trust_remote_code=True,
        )
        self.model = PeftModel.from_pretrained(self.model, model_dir)
        self.model.eval()

        self.tokenizer = AutoTokenizer.from_pretrained(model_dir, trust_remote_code=True)
        if self.tokenizer.pad_token is None:
            self.tokenizer.pad_token = self.tokenizer.eos_token
        print(f"[agent] Model loaded: {base_model} + LoRA adapter")

    def translate_to_lojban(self, english, temperature=None):
        """Translate English → Lojban."""
        if self.use_api:
            return self._api_translate(english, TRANSLATE_SYSTEM_PROMPT, temperature)
        return self._model_translate(english, TRANSLATE_SYSTEM_PROMPT, temperature)

    def translate_to_english(self, lojban):
        """Translate Lojban → English (for display)."""
        if self.use_api:
            return self._api_translate(lojban, REVERSE_SYSTEM_PROMPT, None)
        return self._model_translate(lojban, REVERSE_SYSTEM_PROMPT, None)

    def generate_sentence(self, topic):
        """Generate an English sentence about a topic (for auto-gossip)."""
        prompt = f"Topic: {topic}"
        if self.use_api:
            return self._api_translate(prompt, AUTO_GOSSIP_SYSTEM_PROMPT, 0.9)
        return self._model_translate(prompt, AUTO_GOSSIP_SYSTEM_PROMPT, 0.9)

    def _api_translate(self, text, system_prompt, temperature):
        """Translate via Claude API."""
        kwargs = {
            "model": "claude-sonnet-4-20250514",
            "max_tokens": 256,
            "system": system_prompt,
            "messages": [{"role": "user", "content": text}],
        }
        if temperature is not None:
            kwargs["temperature"] = temperature
        else:
            kwargs["temperature"] = 0.0

        response = self.api_client.messages.create(**kwargs)
        return response.content[0].text.strip()

    def _model_translate(self, text, system_prompt, temperature):
        """Translate via local fine-tuned model."""
        messages = [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": text},
        ]
        prompt = self.tokenizer.apply_chat_template(
            messages, tokenize=False, add_generation_prompt=True
        )
        inputs = self.tokenizer(prompt, return_tensors="pt").to(self.model.device)

        gen_kwargs = {
            "max_new_tokens": 256,
            "pad_token_id": self.tokenizer.pad_token_id,
        }
        if temperature is not None and temperature > 0:
            gen_kwargs["do_sample"] = True
            gen_kwargs["temperature"] = temperature
        else:
            gen_kwargs["do_sample"] = False

        with torch.no_grad():
            outputs = self.model.generate(**inputs, **gen_kwargs)

        generated = outputs[0][inputs["input_ids"].shape[1]:]
        return self.tokenizer.decode(generated, skip_special_tokens=True).strip()


# ─── TCP gossip connection ────────────────────────────────────────

class GossipConnection:
    """TCP connection to a tavla gossip node (JSON Lines protocol)."""

    def __init__(self, name, peer_addr, on_message=None):
        self.name = name
        self.peer_addr = peer_addr
        self.on_message = on_message
        self.sock = None
        self.reader_thread = None
        self.running = False

    def connect(self):
        """Connect to the tavla peer and send handshake."""
        host, port = self.peer_addr.rsplit(":", 1)
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.connect((host, int(port)))

        # Handshake: send agent name as first line.
        self.sock.sendall((self.name + "\n").encode("utf-8"))
        print(f"[{self.name}] Connected to {self.peer_addr}")

        # Start reader thread.
        self.running = True
        self.reader_thread = threading.Thread(target=self._reader_loop, daemon=True)
        self.reader_thread.start()

    def send_envelope(self, envelope):
        """Send a gossip envelope over the wire."""
        msg_bytes = (json.dumps(envelope, separators=(",", ":")) + "\n").encode("utf-8")
        self.sock.sendall(msg_bytes)

    def _reader_loop(self):
        """Read incoming messages from the peer."""
        buf = b""
        while self.running:
            try:
                data = self.sock.recv(4096)
                if not data:
                    print(f"[{self.name}] Peer disconnected")
                    break
                buf += data
                while b"\n" in buf:
                    line, buf = buf.split(b"\n", 1)
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        msg = json.loads(line.decode("utf-8"))
                        if self.on_message:
                            self.on_message(msg)
                    except (json.JSONDecodeError, UnicodeDecodeError):
                        continue
            except OSError:
                break

    def close(self):
        """Close the connection."""
        self.running = False
        if self.sock:
            try:
                self.sock.close()
            except OSError:
                pass


# ─── Agent ────────────────────────────────────────────────────────

class NibliAgent:
    """LLM gossip agent: translates, validates, gossips."""

    def __init__(self, name, translator, validate_binary, domain=None, stance="Deduced"):
        self.name = name
        self.translator = translator
        self.validate_binary = validate_binary
        self.domain = domain
        self.stance = stance
        self.clock = {"entries": {name: 0}}
        self.connection = None
        self.gossiped_count = 0
        self.failed_count = 0

    def connect(self, peer_addr):
        """Connect to a tavla node."""
        self.connection = GossipConnection(
            self.name, peer_addr, on_message=self._on_inbound
        )
        self.connection.connect()

    def translate_validate_gossip(self, english):
        """Full pipeline: translate → validate → gossip."""
        print(f"[{self.name}] Translating: \"{english}\"")

        lojban = None
        for attempt in range(1, MAX_RETRIES + 1):
            # Increase temperature on retries.
            temp = None if attempt == 1 else 0.3 * attempt

            candidate = self.translator.translate_to_lojban(english, temperature=temp)
            print(f"[{self.name}] Candidate ({attempt}/{MAX_RETRIES}): \"{candidate}\"")

            if validate_lojban(candidate, self.validate_binary):
                lojban = candidate
                break
            else:
                print(f"[{self.name}] Rejected by gerna (attempt {attempt})")

        if lojban is None:
            print(f"[{self.name}] Failed after {MAX_RETRIES} attempts")
            self.failed_count += 1
            return None

        print(f"[{self.name}] Validated (gerna pass)")

        # Build and send envelope.
        envelope = make_envelope(
            self.name, self.clock, lojban,
            stance=self.stance, domain=self.domain,
        )

        if self.connection:
            self.connection.send_envelope(envelope)
            self.gossiped_count += 1
            short_id = envelope["id"][:12]
            print(f"[{self.name}] Gossiped to network (envelope {short_id}...)")
        else:
            print(f"[{self.name}] No connection — envelope not sent")

        return envelope

    def _on_inbound(self, msg):
        """Handle incoming gossip messages."""
        msg_type = msg.get("type")

        if msg_type == "envelope":
            author = msg.get("author", "?")
            op = msg.get("op", {})
            stance = msg.get("stance", "?")

            if "AssertLojban" in op:
                lojban = op["AssertLojban"]
                # Translate to English for display.
                try:
                    english = self.translator.translate_to_english(lojban)
                except Exception:
                    english = "(translation failed)"
                print(f"\n[{self.name}] Received from {author} [{stance}]: {lojban}")
                print(f"[{self.name}]   English: {english}")
            elif "AssertDirect" in op:
                direct = op["AssertDirect"]
                rel = direct.get("relation", "?")
                args = direct.get("args", [])
                print(f"\n[{self.name}] Received from {author}: {rel}({', '.join(args)})")
            elif "Retract" in op:
                target = op["Retract"]
                print(f"\n[{self.name}] Retraction from {author}: {target[:12]}...")

        elif msg_type == "sync_request":
            # Respond with empty sync (we have no local CRDT log).
            pass

        elif msg_type == "sync_response":
            envelopes = msg.get("envelopes", [])
            print(f"\n[{self.name}] Sync: received {len(envelopes)} envelopes")

    def auto_gossip(self, topic, interval=30, count=None):
        """Auto-gossip mode: generate and gossip assertions periodically."""
        print(f"[{self.name}] Auto-gossip mode: topic=\"{topic}\", interval={interval}s")
        generated = 0

        while count is None or generated < count:
            try:
                # Generate an English sentence about the topic.
                english = self.translator.generate_sentence(topic)
                print(f"\n[{self.name}] Generated: \"{english}\"")

                # Translate, validate, gossip.
                self.translate_validate_gossip(english)
                generated += 1

                if count is None or generated < count:
                    time.sleep(interval)

            except KeyboardInterrupt:
                break
            except Exception as e:
                print(f"[{self.name}] Error: {e}", file=sys.stderr)
                time.sleep(interval)

        print(f"\n[{self.name}] Auto-gossip complete: {self.gossiped_count} gossiped, {self.failed_count} failed")

    def interactive(self):
        """Interactive mode: read English from stdin, gossip Lojban."""
        print(f"[{self.name}] Interactive mode. Type English sentences to gossip.")
        print(f"[{self.name}] Commands: :status, :quit")

        while True:
            try:
                line = input(f"{self.name}> ").strip()
            except (EOFError, KeyboardInterrupt):
                break

            if not line:
                continue

            if line == ":status":
                print(f"  Gossiped: {self.gossiped_count}, Failed: {self.failed_count}")
                print(f"  Clock: {self.clock}")
                continue

            if line == ":quit":
                break

            self.translate_validate_gossip(line)

        print(f"\n[{self.name}] co'o (goodbye)")
        print(f"  Gossiped: {self.gossiped_count}, Failed: {self.failed_count}")


# ─── CLI ──────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="nibli LLM gossip agent for the tavla network"
    )
    parser.add_argument("--name", required=True, help="Agent name on the gossip network")
    parser.add_argument("--peer", default="127.0.0.1:7001", help="Tavla peer address (default: 127.0.0.1:7001)")
    parser.add_argument("--model", default=DEFAULT_MODEL_DIR, help="Model directory (default: models/nibli-lojban-7b)")
    parser.add_argument("--domain", help="Domain specialization (e.g., xadni, cidja, kelci, krali)")
    parser.add_argument("--stance", default="Deduced", choices=["Deduced", "Expected", "Opinion", "Hearsay"],
                        help="Epistemic stance for assertions (default: Deduced)")
    parser.add_argument("--use-api", action="store_true",
                        help="Use Claude API instead of local model")
    parser.add_argument("--auto-gossip", action="store_true",
                        help="Auto-generate and gossip assertions")
    parser.add_argument("--topic", help="Topic for auto-gossip mode")
    parser.add_argument("--interval", type=int, default=30,
                        help="Seconds between auto-gossip assertions (default: 30)")
    parser.add_argument("--count", type=int, help="Number of auto-gossip assertions (default: unlimited)")

    args = parser.parse_args()

    # Find validation binary.
    validate_binary = find_validate_binary()
    if validate_binary is None:
        print("[agent] WARNING: nibli-validate not found. Run: just build-validate", file=sys.stderr)
        print("[agent] Validation will be skipped (all translations accepted).", file=sys.stderr)

    # Initialize translator.
    use_api = args.use_api
    model_dir = args.model

    if use_api:
        translator = Translator(use_api=True)
    elif Path(model_dir).exists() and HAS_MODEL_DEPS:
        translator = Translator(model_dir=model_dir)
    elif HAS_ANTHROPIC and os.environ.get("ANTHROPIC_API_KEY"):
        print("[agent] Model not found, falling back to Claude API", file=sys.stderr)
        translator = Translator(use_api=True)
    else:
        print("[agent] No model or API available.", file=sys.stderr)
        print(f"  Either: python3 python/nibli_model.py train", file=sys.stderr)
        print(f"  Or:     export ANTHROPIC_API_KEY=... and use --use-api", file=sys.stderr)
        sys.exit(1)

    # Create agent.
    agent = NibliAgent(
        name=args.name,
        translator=translator,
        validate_binary=validate_binary,
        domain=args.domain,
        stance=args.stance,
    )

    # Connect to tavla node.
    try:
        agent.connect(args.peer)
    except ConnectionRefusedError:
        print(f"[agent] Cannot connect to {args.peer}. Start a tavla node first:", file=sys.stderr)
        print(f"  just gossip-tcp-a", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"[agent] Connection error: {e}", file=sys.stderr)
        sys.exit(1)

    # Run.
    try:
        if args.auto_gossip:
            topic = args.topic or args.domain or "general knowledge"
            agent.auto_gossip(topic, interval=args.interval, count=args.count)
        else:
            agent.interactive()
    finally:
        if agent.connection:
            agent.connection.close()


if __name__ == "__main__":
    main()
