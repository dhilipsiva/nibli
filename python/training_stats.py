#!/usr/bin/env python3
"""
training_stats.py — Statistics for Lojban training data.

Reads a JSONL training data file and reports:
  - Total / valid / invalid counts
  - Pairs per domain
  - Gerna pass rate (overall and per-domain)
  - Average sentence length (Lojban tokens)
  - Construct distribution (gadri, connectives, quantifiers, etc.)

Usage:
    python3 python/training_stats.py data/training_raw.jsonl
"""

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path


# ─── Construct detection patterns ─────────────────────────────────

CONSTRUCTS = {
    "lo (veridical)": r"\blo\b",
    "le (description)": r"\ble\b",
    "la (name)": r"\bla\b",
    "ro (universal)": r"\bro\b",
    "su'o (existential)": r"\bsu'o\b",
    "cu (selbri sep)": r"\bcu\b",
    "na (negation)": r"\bna\b",
    "se (conversion)": r"\bse\b",
    "poi (relative)": r"\bpoi\b",
    "noi (incidental)": r"\bnoi\b",
    "nu (event)": r"\bnu\b",
    "du'u (proposition)": r"\bdu'u\b",
    "ka (property)": r"\bka\b",
    ".e (and-sumti)": r"\b\.e\b",
    ".a (or-sumti)": r"\b\.a\b",
    "je (and-selbri)": r"\bje\b",
    "ja (or-selbri)": r"\bja\b",
    "ge...gi (fore-and)": r"\bge\b",
    "ga...gi (fore-or)": r"\bga\b",
    "ganai...gi (fore-if)": r"\bganai\b",
    "pu (past)": r"\bpu\b",
    "ca (present)": r"\bca\b",
    "ba (future)": r"\bba\b",
    "li (number)": r"\bli\b",
    "bilga (obligation)": r"\bbilga\b",
    "curmi (permission)": r"\bcurmi\b",
    "nitcu (necessity)": r"\bnitcu\b",
}


def load_records(path):
    """Load JSONL records from file."""
    records = []
    with open(path, "r") as f:
        for lineno, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                records.append(json.loads(line))
            except json.JSONDecodeError:
                print(f"[WARN] Invalid JSON on line {lineno}", file=sys.stderr)
    return records


def compute_stats(records):
    """Compute statistics from training data records."""
    total = len(records)
    valid = [r for r in records if r.get("valid", False)]
    invalid = [r for r in records if not r.get("valid", False)]

    # Per-domain counts.
    domain_total = Counter(r.get("domain", "unknown") for r in records)
    domain_valid = Counter(r.get("domain", "unknown") for r in valid)
    domain_invalid = Counter(r.get("domain", "unknown") for r in invalid)

    # Sentence lengths (Lojban tokens — whitespace split).
    lojban_lengths = [len(r["lojban"].split()) for r in valid if "lojban" in r]
    english_lengths = [len(r["english"].split()) for r in valid if "english" in r]

    # Construct distribution (valid sentences only).
    construct_counts = Counter()
    for r in valid:
        lojban = r.get("lojban", "")
        for construct_name, pattern in CONSTRUCTS.items():
            if re.search(pattern, lojban):
                construct_counts[construct_name] += 1

    # Error distribution (invalid sentences).
    error_types = Counter()
    for r in invalid:
        err = r.get("error", "unknown")
        # Simplify error messages to categories.
        if "Syntax" in err or "expected" in err:
            error_types["Syntax error"] += 1
        elif "Semantic" in err:
            error_types["Semantic error"] += 1
        elif "Reasoning" in err:
            error_types["Reasoning error"] += 1
        else:
            error_types["Other"] += 1

    return {
        "total": total,
        "valid_count": len(valid),
        "invalid_count": len(invalid),
        "pass_rate": len(valid) / total * 100 if total > 0 else 0,
        "domain_total": dict(domain_total),
        "domain_valid": dict(domain_valid),
        "domain_invalid": dict(domain_invalid),
        "avg_lojban_tokens": sum(lojban_lengths) / len(lojban_lengths) if lojban_lengths else 0,
        "avg_english_tokens": sum(english_lengths) / len(english_lengths) if english_lengths else 0,
        "min_lojban_tokens": min(lojban_lengths) if lojban_lengths else 0,
        "max_lojban_tokens": max(lojban_lengths) if lojban_lengths else 0,
        "construct_counts": dict(construct_counts.most_common()),
        "error_types": dict(error_types.most_common()),
    }


def print_stats(stats):
    """Pretty-print statistics."""
    print("=" * 60)
    print("  Lojban Training Data Statistics")
    print("=" * 60)

    print(f"\n  Total records:    {stats['total']}")
    print(f"  Valid:            {stats['valid_count']}")
    print(f"  Invalid:          {stats['invalid_count']}")
    print(f"  Pass rate:        {stats['pass_rate']:.1f}%")

    print(f"\n  Avg Lojban tokens:  {stats['avg_lojban_tokens']:.1f}")
    print(f"  Avg English tokens: {stats['avg_english_tokens']:.1f}")
    print(f"  Min Lojban tokens:  {stats['min_lojban_tokens']}")
    print(f"  Max Lojban tokens:  {stats['max_lojban_tokens']}")

    # Per-domain breakdown.
    print(f"\n  {'Domain':<20s} {'Total':>6s} {'Valid':>6s} {'Invalid':>7s} {'Rate':>6s}")
    print(f"  {'-'*20} {'-'*6} {'-'*6} {'-'*7} {'-'*6}")
    all_domains = sorted(set(
        list(stats["domain_total"].keys()) +
        list(stats["domain_valid"].keys())
    ))
    for d in all_domains:
        t = stats["domain_total"].get(d, 0)
        v = stats["domain_valid"].get(d, 0)
        inv = stats["domain_invalid"].get(d, 0)
        rate = v / t * 100 if t > 0 else 0
        print(f"  {d:<20s} {t:>6d} {v:>6d} {inv:>7d} {rate:>5.1f}%")

    # Construct distribution.
    if stats["construct_counts"]:
        print(f"\n  Construct Distribution (in valid sentences):")
        print(f"  {'Construct':<25s} {'Count':>6s} {'%':>6s}")
        print(f"  {'-'*25} {'-'*6} {'-'*6}")
        valid_count = stats["valid_count"]
        for construct, count in stats["construct_counts"].items():
            pct = count / valid_count * 100 if valid_count > 0 else 0
            print(f"  {construct:<25s} {count:>6d} {pct:>5.1f}%")

    # Error distribution.
    if stats["error_types"]:
        print(f"\n  Error Types:")
        for etype, count in stats["error_types"].items():
            print(f"    {etype}: {count}")

    print(f"\n{'='*60}")


def export_huggingface(input_path, output_path):
    """Export valid pairs to HuggingFace-compatible JSONL format."""
    records = load_records(input_path)
    valid = [r for r in records if r.get("valid", False)]

    with open(output_path, "w") as f:
        for r in valid:
            hf_record = {
                "english": r["english"],
                "lojban": r["lojban"],
                "domain": r.get("domain", "general"),
            }
            f.write(json.dumps(hf_record) + "\n")

    print(f"Exported {len(valid)} valid pairs to {output_path}")


def main():
    parser = argparse.ArgumentParser(
        description="Statistics for Lojban training data"
    )
    parser.add_argument(
        "input",
        help="Input JSONL training data file",
    )
    parser.add_argument(
        "--export-hf",
        metavar="PATH",
        help="Export valid pairs to HuggingFace-compatible JSONL",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output stats as JSON instead of formatted text",
    )
    args = parser.parse_args()

    if not Path(args.input).exists():
        print(f"[ERROR] File not found: {args.input}", file=sys.stderr)
        sys.exit(1)

    records = load_records(args.input)
    if not records:
        print("[ERROR] No records found in input file", file=sys.stderr)
        sys.exit(1)

    stats = compute_stats(records)

    if args.json:
        print(json.dumps(stats, indent=2))
    else:
        print_stats(stats)

    if args.export_hf:
        export_huggingface(args.input, args.export_hf)


if __name__ == "__main__":
    main()
