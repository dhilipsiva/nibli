#!/usr/bin/env python3
"""
generate_training_data.py — Gerna-validated synthetic Lojban training data.

The fine-tuning flywheel:
  1. Claude Sonnet generates English→Lojban translation batches
  2. nibli-validate subprocess validates each Lojban sentence (gerna + smuni)
  3. Valid pairs written to JSONL output

Domains (balanced sampling):
  - IAM (identity & access management) — 20%
  - GDPR (data protection) — 20%
  - Rights/utopia — 20%
  - Agent gossip (distributed systems) — 20%
  - General Lojban — 20%

Usage:
    # Generate raw data (requires ANTHROPIC_API_KEY env var)
    python3 python/generate_training_data.py --output data/training_raw.jsonl

    # Resume from existing file (skips already-generated domains)
    python3 python/generate_training_data.py --output data/training_raw.jsonl --resume

    # Specify target count per domain
    python3 python/generate_training_data.py --output data/training_raw.jsonl --target 1500

    # Dry run (no API calls, test validation pipeline)
    python3 python/generate_training_data.py --dry-run
"""

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path

try:
    import anthropic
    HAS_ANTHROPIC = True
except ImportError:
    HAS_ANTHROPIC = False


# ─── Domain definitions ──────────────────────────────────────────────

DOMAINS = {
    "iam": {
        "name": "Identity & Access Management",
        "description": "Sentences about authentication, authorization, roles, permissions, users, groups, policies, access control, identity verification, credentials, sessions, tokens.",
        "examples": [
            ("The administrator grants read access to the database.", "lo se jarco cu curmi lo tcidu lo datni"),
            ("Every user must authenticate before accessing the system.", "ro lo pilno cu bilga lo ka jetnu binxo kei pu lo nu pilno lo ciste"),
            ("The role has permission to modify records.", "lo selcmi cu curmi lo ka galfi lo datni"),
        ],
    },
    "gdpr": {
        "name": "Data Protection (GDPR)",
        "description": "Sentences about personal data, consent, data subjects, controllers, processors, privacy rights, data breaches, lawful basis, retention, erasure, portability.",
        "examples": [
            ("The data subject has the right to erasure.", "lo datni poi ke'a selpilno cu se krali lo ka vimcu"),
            ("Personal data must be processed lawfully.", "lo datni poi ke'a sivni cu bilga lo ka se gasnu fi lo ka flalu"),
            ("The controller must obtain consent.", "lo se gasnu cu bilga lo ka cpedu lo ka zanru"),
        ],
    },
    "rights": {
        "name": "Rights & Utopia",
        "description": "Sentences about human rights, freedoms, justice, equality, governance, democracy, welfare, social contracts, obligations, duties, fairness, dignity.",
        "examples": [
            ("Every person has the right to freedom.", "ro lo prenu cu se krali lo ka zifre"),
            ("Justice requires equal treatment.", "lo nu pajni cu nitcu lo ka dunli lo nu zukte"),
            ("The government must protect the citizens.", "lo turni cu bilga lo ka bandu lo sivni"),
        ],
    },
    "gossip": {
        "name": "Agent Gossip (Distributed Systems)",
        "description": "Sentences about nodes, messages, synchronization, peers, protocols, broadcasting, consensus, replication, network topology, fault tolerance, state propagation.",
        "examples": [
            ("The node broadcasts the message to all peers.", "lo skami cu mrilu lo notci lo ro pendo"),
            ("Peer A synchronizes its state with Peer B.", "la .ab. cu simxu lo ka dunli lo se djuno kei la .bab."),
            ("The network detects a Byzantine fault.", "lo julne cu facki lo nu lo skami cu xlamau"),
        ],
    },
    "general": {
        "name": "General Lojban",
        "description": "Everyday sentences: animals, food, weather, family, travel, colors, sizes, emotions, spatial relations, time, counting, descriptions, professions.",
        "examples": [
            ("The big dog chases the small cat.", "lo barda gerku cu jersi lo cmalu mlatu"),
            ("Alice sees three birds in the garden.", "la .alis. cu viska ci lo cipni ne lo purdi"),
            ("The red flower is beautiful.", "lo xunre xrula cu melbi"),
        ],
    },
}

BATCH_SIZE = 50

SYSTEM_PROMPT = """\
You are an expert Lojban translator. Translate English sentences to grammatically correct Lojban.

Rules:
- Use standard Lojban grammar (CLL-compliant)
- Use gismu (root words) and standard cmavo
- Use proper gadri: lo for veridical descriptions, la for names
- Use cu before selbri when there are preceding sumti
- Names must be wrapped in dots: .alis. .bob. .adam.
- Use proper sentence structure: sumti cu selbri sumti
- Numeric sumti use li + PA
- Universal quantifiers use ro lo
- Output ONLY the Lojban translation, one per line, no explanations
- Do NOT use lujvo unless you are certain of the correct form
- Prefer simple constructions over complex ones
- Each output line must be a single complete Lojban sentence
"""


def make_translation_prompt(domain_info, count):
    """Build a prompt asking Claude to translate English sentences to Lojban."""
    examples_text = "\n".join(
        f"  English: {eng}\n  Lojban:  {loj}"
        for eng, loj in domain_info["examples"]
    )

    return f"""\
Generate {count} diverse English sentences about: {domain_info['description']}

Then translate each to Lojban.

Example translations for this domain:
{examples_text}

Output format — exactly {count} lines, each line is:
ENGLISH ||| LOJBAN

Important:
- Vary sentence structure and vocabulary
- Use different gismu and grammatical constructs
- Include both simple and compound sentences
- Make sure each Lojban sentence is a single complete bridi
- Do NOT include line numbers or bullets
"""


def call_anthropic(client, domain_key, domain_info, count):
    """Call Claude Sonnet to generate English→Lojban pairs."""
    prompt = make_translation_prompt(domain_info, count)

    response = client.messages.create(
        model="claude-sonnet-4-20250514",
        max_tokens=4096,
        temperature=0.7,
        system=SYSTEM_PROMPT,
        messages=[{"role": "user", "content": prompt}],
    )

    text = response.content[0].text
    pairs = []
    for line in text.strip().split("\n"):
        line = line.strip()
        if "|||" not in line:
            continue
        parts = line.split("|||", 1)
        if len(parts) != 2:
            continue
        english = parts[0].strip()
        lojban = parts[1].strip()
        if english and lojban:
            pairs.append({"english": english, "lojban": lojban, "domain": domain_key})

    return pairs


def validate_batch(pairs, validate_binary):
    """Validate Lojban sentences through nibli-validate subprocess."""
    if not pairs:
        return []

    lojban_lines = "\n".join(p["lojban"] for p in pairs) + "\n"

    try:
        result = subprocess.run(
            [validate_binary],
            input=lojban_lines,
            capture_output=True,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired:
        print("  [WARN] Validation subprocess timed out", file=sys.stderr)
        return []
    except FileNotFoundError:
        print(f"  [ERROR] Validation binary not found: {validate_binary}", file=sys.stderr)
        print("  Run: just build-native", file=sys.stderr)
        sys.exit(1)

    # Parse JSON output lines (skip non-JSON lines like "Native engine ready", [Skolem] etc.)
    results = []
    for line in result.stdout.strip().split("\n"):
        line = line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            results.append(json.loads(line))
        except json.JSONDecodeError:
            continue

    # Match results back to pairs
    validated = []
    result_idx = 0
    for pair in pairs:
        if result_idx >= len(results):
            pair["valid"] = False
            pair["error"] = "no validation result"
            validated.append(pair)
            continue

        vr = results[result_idx]
        result_idx += 1

        if vr.get("valid", False):
            pair["valid"] = True
            validated.append(pair)
        else:
            pair["valid"] = False
            pair["error"] = vr.get("error", "unknown")
            validated.append(pair)

    return validated


def find_validate_binary():
    """Find the nibli-validate binary."""
    # Check common locations
    candidates = [
        "target/debug/nibli-validate",
        "target/release/nibli-validate",
    ]
    for c in candidates:
        if os.path.isfile(c):
            return c

    # Try building it
    print("[INFO] Building nibli-validate...", file=sys.stderr)
    result = subprocess.run(
        ["cargo", "build", "-p", "nibli", "--bin", "nibli-validate"],
        capture_output=True,
        text=True,
    )
    if result.returncode == 0:
        if os.path.isfile("target/debug/nibli-validate"):
            return "target/debug/nibli-validate"

    print("[ERROR] Could not find or build nibli-validate binary", file=sys.stderr)
    print("Run: cargo build -p nibli --bin nibli-validate", file=sys.stderr)
    sys.exit(1)


def load_existing(output_path):
    """Load existing JSONL records to enable resumption."""
    records = []
    if not os.path.exists(output_path):
        return records
    with open(output_path, "r") as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    records.append(json.loads(line))
                except json.JSONDecodeError:
                    continue
    return records


def count_by_domain(records):
    """Count valid records per domain."""
    counts = {}
    for r in records:
        if r.get("valid", False):
            d = r.get("domain", "unknown")
            counts[d] = counts.get(d, 0) + 1
    return counts


def generate_dry_run(validate_binary):
    """Dry run: test validation with known Lojban sentences."""
    test_sentences = [
        {"english": "The dog is big.", "lojban": "lo gerku cu barda", "domain": "general"},
        {"english": "The cat is small.", "lojban": "lo mlatu cu cmalu", "domain": "general"},
        {"english": "Invalid sentence.", "lojban": "this is not lojban", "domain": "general"},
        {"english": "Adam sees the bird.", "lojban": "la .adam. cu viska lo cipni", "domain": "general"},
        {"english": "Every mammal is alive.", "lojban": "ro lo mabru cu jmive", "domain": "general"},
    ]

    print("[DRY RUN] Testing validation pipeline...")
    validated = validate_batch(test_sentences, validate_binary)

    valid_count = sum(1 for v in validated if v.get("valid"))
    print(f"[DRY RUN] {valid_count}/{len(validated)} validated successfully")

    for v in validated:
        status = "VALID" if v.get("valid") else f"INVALID: {v.get('error', '?')}"
        print(f"  {v['lojban'][:50]:50s} → {status}")

    return validated


def main():
    parser = argparse.ArgumentParser(
        description="Generate gerna-validated Lojban training data"
    )
    parser.add_argument(
        "--output", "-o",
        default="data/training_raw.jsonl",
        help="Output JSONL file path (default: data/training_raw.jsonl)",
    )
    parser.add_argument(
        "--target", "-t",
        type=int,
        default=1500,
        help="Target valid pairs per domain (default: 1500)",
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        help="Resume from existing output file",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Test validation pipeline without API calls",
    )
    parser.add_argument(
        "--max-retries",
        type=int,
        default=5,
        help="Max API retry rounds per domain (default: 5)",
    )
    args = parser.parse_args()

    # Find or build validation binary.
    validate_binary = find_validate_binary()
    print(f"[INFO] Using validator: {validate_binary}", file=sys.stderr)

    if args.dry_run:
        generate_dry_run(validate_binary)
        return

    # Check dependencies.
    if not HAS_ANTHROPIC:
        print("[ERROR] anthropic package not installed. Run: pip install anthropic", file=sys.stderr)
        sys.exit(1)

    # Check API key.
    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        print("[ERROR] ANTHROPIC_API_KEY environment variable not set", file=sys.stderr)
        sys.exit(1)

    client = anthropic.Anthropic(api_key=api_key)

    # Create output directory.
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    # Load existing records for resumption.
    existing = []
    if args.resume and output_path.exists():
        existing = load_existing(str(output_path))
        print(f"[INFO] Loaded {len(existing)} existing records", file=sys.stderr)

    domain_counts = count_by_domain(existing)
    target_per_domain = args.target

    # Open output file in append mode if resuming, write mode otherwise.
    mode = "a" if args.resume and existing else "w"
    total_valid = sum(domain_counts.values())
    total_invalid = 0
    total_api_calls = 0

    with open(str(output_path), mode) as outf:
        for domain_key, domain_info in DOMAINS.items():
            current_count = domain_counts.get(domain_key, 0)
            if current_count >= target_per_domain:
                print(
                    f"[{domain_key}] Already have {current_count}/{target_per_domain} — skipping",
                    file=sys.stderr,
                )
                continue

            needed = target_per_domain - current_count
            print(
                f"\n[{domain_key}] Need {needed} more valid pairs "
                f"(have {current_count}/{target_per_domain})",
                file=sys.stderr,
            )

            retries = 0
            while needed > 0 and retries < args.max_retries:
                retries += 1
                # Request ~40% more than needed to account for validation failures.
                batch_request = min(BATCH_SIZE, int(needed * 1.4) + 5)

                print(
                    f"  [{domain_key}] Round {retries}: requesting {batch_request} pairs...",
                    file=sys.stderr,
                )

                try:
                    pairs = call_anthropic(client, domain_key, domain_info, batch_request)
                    total_api_calls += 1
                except Exception as e:
                    print(f"  [ERROR] API call failed: {e}", file=sys.stderr)
                    time.sleep(5)
                    continue

                if not pairs:
                    print(f"  [WARN] No pairs returned from API", file=sys.stderr)
                    continue

                print(
                    f"  [{domain_key}] Got {len(pairs)} pairs, validating...",
                    file=sys.stderr,
                )

                validated = validate_batch(pairs, validate_binary)

                batch_valid = 0
                batch_invalid = 0
                for v in validated:
                    record = {
                        "english": v["english"],
                        "lojban": v["lojban"],
                        "domain": v["domain"],
                        "valid": v.get("valid", False),
                    }
                    if not v.get("valid"):
                        record["error"] = v.get("error", "unknown")
                        batch_invalid += 1
                    else:
                        batch_valid += 1

                    outf.write(json.dumps(record) + "\n")

                outf.flush()
                needed -= batch_valid
                total_valid += batch_valid
                total_invalid += batch_invalid

                pass_rate = (
                    batch_valid / len(validated) * 100 if validated else 0
                )
                print(
                    f"  [{domain_key}] Round {retries}: "
                    f"{batch_valid} valid, {batch_invalid} invalid "
                    f"({pass_rate:.0f}% pass rate)",
                    file=sys.stderr,
                )

                # Rate limit — be polite to the API.
                time.sleep(1)

            domain_counts[domain_key] = domain_counts.get(domain_key, 0) + (
                target_per_domain - max(needed, 0) - current_count
            )

    # Summary.
    print(f"\n{'='*60}", file=sys.stderr)
    print(f"Generation complete:", file=sys.stderr)
    print(f"  Total valid:   {total_valid}", file=sys.stderr)
    print(f"  Total invalid: {total_invalid}", file=sys.stderr)
    print(f"  API calls:     {total_api_calls}", file=sys.stderr)
    overall_rate = (
        total_valid / (total_valid + total_invalid) * 100
        if (total_valid + total_invalid) > 0
        else 0
    )
    print(f"  Pass rate:     {overall_rate:.1f}%", file=sys.stderr)
    print(f"  Output:        {args.output}", file=sys.stderr)
    print(f"\nPer-domain counts:", file=sys.stderr)
    for dk in DOMAINS:
        c = domain_counts.get(dk, 0)
        print(f"  {dk:12s}: {c}", file=sys.stderr)
    print(f"{'='*60}", file=sys.stderr)


if __name__ == "__main__":
    main()
