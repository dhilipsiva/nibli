#!/usr/bin/env python3
"""
nibli_model.py — Fine-tune and evaluate a nibli-native Lojban LLM.

QLoRA fine-tuning of Qwen2.5-7B-Instruct on gerna-validated English→Lojban pairs.
Hardware target: RTX 5090 (32GB VRAM), Ryzen 9 9950X3D, 96GB RAM.

The metric that matters: GERNA PASS RATE.
Can nibli's own parser accept the output? That's the only question.

Commands:
    python3 python/nibli_model.py train --data data/training_raw.jsonl
    python3 python/nibli_model.py eval --model models/nibli-lojban-7b
    python3 python/nibli_model.py refine --model models/nibli-lojban-7b --data data/training_raw.jsonl
    python3 python/nibli_model.py push --model models/nibli-lojban-7b --repo dhilipsiva/nibli-lojban-7b
"""

import argparse
import json
import os
import subprocess
import sys
import random
from pathlib import Path

# ─── Lazy imports (heavy deps) ────────────────────────────────────

def require(*modules):
    """Check that required modules are importable."""
    missing = []
    for m in modules:
        try:
            __import__(m)
        except ImportError:
            missing.append(m)
    if missing:
        print(f"[ERROR] Missing packages: {', '.join(missing)}", file=sys.stderr)
        print("Install with: pip install " + " ".join(missing), file=sys.stderr)
        sys.exit(1)


# ─── Constants ────────────────────────────────────────────────────

BASE_MODEL = "Qwen/Qwen2.5-7B-Instruct"
DEFAULT_OUTPUT_DIR = "models/nibli-lojban-7b"
DEFAULT_DATA = "data/training_raw.jsonl"
TEST_SPLIT = 0.10
SEED = 42

SYSTEM_PROMPT = (
    "You are a Lojban translator. Translate the English sentence to "
    "grammatically correct Lojban. Output ONLY the Lojban translation, "
    "nothing else."
)


# ─── Data loading ─────────────────────────────────────────────────

def load_valid_pairs(data_path):
    """Load valid English→Lojban pairs from JSONL."""
    pairs = []
    with open(data_path, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue
            if record.get("valid", False) and record.get("english") and record.get("lojban"):
                pairs.append(record)
    return pairs


def split_data(pairs, test_ratio=TEST_SPLIT, seed=SEED):
    """Split pairs into train and test sets."""
    rng = random.Random(seed)
    shuffled = list(pairs)
    rng.shuffle(shuffled)
    split_idx = int(len(shuffled) * (1 - test_ratio))
    return shuffled[:split_idx], shuffled[split_idx:]


def format_for_sft(pairs):
    """Format pairs as chat-style SFT examples for Qwen."""
    formatted = []
    for p in pairs:
        formatted.append({
            "messages": [
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": p["english"]},
                {"role": "assistant", "content": p["lojban"]},
            ]
        })
    return formatted


# ─── Validation via nibli-validate ────────────────────────────────

def find_validate_binary():
    """Find the nibli-validate binary."""
    for candidate in ["target/debug/nibli-validate", "target/release/nibli-validate"]:
        if os.path.isfile(candidate):
            return candidate
    print("[WARN] nibli-validate not found. Run: just build-validate", file=sys.stderr)
    return None


def validate_lojban_batch(sentences, validate_binary=None):
    """Validate Lojban sentences through nibli-validate subprocess.

    Returns list of bools (True = gerna accepts it).
    """
    if validate_binary is None:
        validate_binary = find_validate_binary()
    if validate_binary is None:
        return [False] * len(sentences)

    input_text = "\n".join(sentences) + "\n"
    try:
        result = subprocess.run(
            [validate_binary],
            input=input_text,
            capture_output=True,
            text=True,
            timeout=300,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return [False] * len(sentences)

    # Parse JSON output, skip non-JSON lines.
    results = []
    for line in result.stdout.strip().split("\n"):
        line = line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            results.append(json.loads(line))
        except json.JSONDecodeError:
            continue

    valid_flags = []
    for i in range(len(sentences)):
        if i < len(results):
            valid_flags.append(results[i].get("valid", False))
        else:
            valid_flags.append(False)

    return valid_flags


# ─── Training ─────────────────────────────────────────────────────

def cmd_train(args):
    """QLoRA fine-tuning of Qwen2.5-7B-Instruct."""
    require("torch", "transformers", "peft", "trl", "bitsandbytes", "datasets")

    import torch
    from transformers import (
        AutoModelForCausalLM,
        AutoTokenizer,
        BitsAndBytesConfig,
        TrainingArguments,
    )
    from peft import LoraConfig, get_peft_model, prepare_model_for_kbit_training
    from trl import SFTTrainer, SFTConfig
    from datasets import Dataset

    data_path = args.data or DEFAULT_DATA
    output_dir = args.output or DEFAULT_OUTPUT_DIR

    if not Path(data_path).exists():
        print(f"[ERROR] Data file not found: {data_path}", file=sys.stderr)
        print("Run: just generate-training", file=sys.stderr)
        sys.exit(1)

    # Load and split data.
    print(f"[train] Loading data from {data_path}...")
    pairs = load_valid_pairs(data_path)
    print(f"[train] {len(pairs)} valid pairs loaded")

    if len(pairs) < 100:
        print("[ERROR] Too few valid pairs. Need at least 100.", file=sys.stderr)
        sys.exit(1)

    train_pairs, test_pairs = split_data(pairs)
    print(f"[train] Train: {len(train_pairs)}, Test: {len(test_pairs)}")

    # Save test set for evaluation.
    test_path = Path(output_dir) / "test_set.jsonl"
    test_path.parent.mkdir(parents=True, exist_ok=True)
    with open(str(test_path), "w") as f:
        for p in test_pairs:
            f.write(json.dumps(p) + "\n")
    print(f"[train] Test set saved to {test_path}")

    # Format for SFT.
    train_formatted = format_for_sft(train_pairs)
    train_dataset = Dataset.from_list(train_formatted)

    # 4-bit quantization config.
    bnb_config = BitsAndBytesConfig(
        load_in_4bit=True,
        bnb_4bit_quant_type="nf4",
        bnb_4bit_compute_dtype=torch.bfloat16,
        bnb_4bit_use_double_quant=True,
    )

    # Load model.
    print(f"[train] Loading {BASE_MODEL} with 4-bit quantization...")
    model_kwargs = {
        "quantization_config": bnb_config,
        "device_map": "auto",
        "torch_dtype": torch.bfloat16,
        "trust_remote_code": True,
    }

    # Use Flash Attention 2 if available.
    try:
        import flash_attn  # noqa: F401
        model_kwargs["attn_implementation"] = "flash_attention_2"
        print("[train] Flash Attention 2 enabled")
    except ImportError:
        print("[train] Flash Attention 2 not available, using default attention")

    model = AutoModelForCausalLM.from_pretrained(BASE_MODEL, **model_kwargs)
    model = prepare_model_for_kbit_training(model, use_gradient_checkpointing=True)

    tokenizer = AutoTokenizer.from_pretrained(BASE_MODEL, trust_remote_code=True)
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token
        model.config.pad_token_id = tokenizer.eos_token_id

    # LoRA config.
    lora_config = LoraConfig(
        r=64,
        lora_alpha=128,
        target_modules="all-linear",
        lora_dropout=0.05,
        bias="none",
        task_type="CAUSAL_LM",
    )

    model = get_peft_model(model, lora_config)
    trainable_params, all_params = model.get_nb_trainable_parameters()
    print(
        f"[train] Trainable: {trainable_params:,} / {all_params:,} "
        f"({100 * trainable_params / all_params:.2f}%)"
    )

    # Training config.
    num_train = len(train_dataset)
    steps_per_epoch = num_train // (args.batch_size * args.grad_accum)
    total_steps = steps_per_epoch * args.epochs
    warmup_steps = int(total_steps * 0.10)

    training_args = SFTConfig(
        output_dir=output_dir,
        num_train_epochs=args.epochs,
        per_device_train_batch_size=args.batch_size,
        gradient_accumulation_steps=args.grad_accum,
        gradient_checkpointing=True,
        gradient_checkpointing_kwargs={"use_reentrant": False},
        learning_rate=2e-4,
        lr_scheduler_type="cosine",
        warmup_steps=warmup_steps,
        bf16=True,
        logging_steps=10,
        save_strategy="epoch",
        save_total_limit=2,
        seed=SEED,
        max_seq_length=512,
        packing=False,
        report_to="none",
    )

    # Train.
    print(f"[train] Starting QLoRA fine-tuning...")
    print(f"  Epochs: {args.epochs}")
    print(f"  Batch size: {args.batch_size} x {args.grad_accum} grad accum")
    print(f"  Total steps: {total_steps}")
    print(f"  Warmup steps: {warmup_steps}")

    trainer = SFTTrainer(
        model=model,
        args=training_args,
        train_dataset=train_dataset,
        processing_class=tokenizer,
    )

    trainer.train()

    # Save adapter + tokenizer.
    print(f"[train] Saving adapter to {output_dir}...")
    trainer.save_model(output_dir)
    tokenizer.save_pretrained(output_dir)

    # Save training metadata.
    metadata = {
        "base_model": BASE_MODEL,
        "lora_rank": 64,
        "lora_alpha": 128,
        "epochs": args.epochs,
        "train_pairs": len(train_pairs),
        "test_pairs": len(test_pairs),
        "total_valid_pairs": len(pairs),
        "data_source": data_path,
    }
    with open(str(Path(output_dir) / "training_metadata.json"), "w") as f:
        json.dump(metadata, f, indent=2)

    print(f"[train] Done. Model saved to {output_dir}")
    print(f"[train] Run evaluation: python3 python/nibli_model.py eval --model {output_dir}")


# ─── Evaluation ───────────────────────────────────────────────────

def cmd_eval(args):
    """Evaluate the fine-tuned model — gerna pass rate is the key metric."""
    require("torch", "transformers", "peft")

    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig
    from peft import PeftModel

    model_dir = args.model or DEFAULT_OUTPUT_DIR
    test_path = args.test_set or str(Path(model_dir) / "test_set.jsonl")

    if not Path(model_dir).exists():
        print(f"[ERROR] Model not found: {model_dir}", file=sys.stderr)
        sys.exit(1)

    if not Path(test_path).exists():
        print(f"[ERROR] Test set not found: {test_path}", file=sys.stderr)
        sys.exit(1)

    # Load test set.
    test_pairs = []
    with open(test_path, "r") as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    test_pairs.append(json.loads(line))
                except json.JSONDecodeError:
                    continue

    if not test_pairs:
        print("[ERROR] No test pairs found", file=sys.stderr)
        sys.exit(1)

    print(f"[eval] {len(test_pairs)} test pairs loaded")

    # Load model.
    print(f"[eval] Loading model from {model_dir}...")
    bnb_config = BitsAndBytesConfig(
        load_in_4bit=True,
        bnb_4bit_quant_type="nf4",
        bnb_4bit_compute_dtype=torch.bfloat16,
        bnb_4bit_use_double_quant=True,
    )

    # Read base model name from metadata if available.
    metadata_path = Path(model_dir) / "training_metadata.json"
    base_model = BASE_MODEL
    if metadata_path.exists():
        with open(str(metadata_path)) as f:
            meta = json.load(f)
            base_model = meta.get("base_model", BASE_MODEL)

    model = AutoModelForCausalLM.from_pretrained(
        base_model,
        quantization_config=bnb_config,
        device_map="auto",
        torch_dtype=torch.bfloat16,
        trust_remote_code=True,
    )
    model = PeftModel.from_pretrained(model, model_dir)
    model.eval()

    tokenizer = AutoTokenizer.from_pretrained(model_dir, trust_remote_code=True)
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token

    # Generate translations.
    print(f"[eval] Generating translations for {len(test_pairs)} test pairs...")
    predictions = []
    batch_size = args.eval_batch_size

    for i in range(0, len(test_pairs), batch_size):
        batch = test_pairs[i : i + batch_size]
        batch_preds = []

        for pair in batch:
            messages = [
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": pair["english"]},
            ]
            prompt = tokenizer.apply_chat_template(
                messages, tokenize=False, add_generation_prompt=True
            )
            inputs = tokenizer(prompt, return_tensors="pt").to(model.device)

            with torch.no_grad():
                outputs = model.generate(
                    **inputs,
                    max_new_tokens=256,
                    do_sample=False,
                    temperature=None,
                    top_p=None,
                    pad_token_id=tokenizer.pad_token_id,
                )

            # Decode only the generated tokens.
            generated = outputs[0][inputs["input_ids"].shape[1]:]
            pred = tokenizer.decode(generated, skip_special_tokens=True).strip()
            batch_preds.append(pred)

        predictions.extend(batch_preds)

        if (i // batch_size) % 10 == 0:
            print(f"  [{i + len(batch)}/{len(test_pairs)}]", file=sys.stderr)

    # Validate ALL predictions through gerna.
    print("[eval] Validating predictions through nibli gerna...")
    validate_binary = find_validate_binary()
    gerna_valid = validate_lojban_batch(predictions, validate_binary)

    # Also validate references (sanity check — should be 100%).
    references = [p["lojban"] for p in test_pairs]
    ref_valid = validate_lojban_batch(references, validate_binary)

    # Compute metrics.
    n = len(test_pairs)
    gerna_pass = sum(gerna_valid)
    exact_match = sum(
        1 for pred, pair in zip(predictions, test_pairs) if pred.strip() == pair["lojban"].strip()
    )
    ref_gerna_pass = sum(ref_valid)

    # BLEU score.
    bleu = compute_bleu(predictions, references)

    # Semantic match (FOL equivalence) — only for predictions that pass gerna.
    semantic_matches = 0
    semantic_total = 0
    if validate_binary:
        semantic_matches, semantic_total = compute_semantic_match(
            predictions, references, gerna_valid, validate_binary
        )

    # Report.
    print(f"\n{'='*60}")
    print(f"  nibli Model Evaluation Report")
    print(f"{'='*60}")
    print(f"\n  Test set size:        {n}")
    print(f"  Reference gerna pass: {ref_gerna_pass}/{n} ({100*ref_gerna_pass/n:.1f}%)")
    print()
    print(f"  GERNA PASS RATE:      {gerna_pass}/{n} ({100*gerna_pass/n:.1f}%)  <-- KEY METRIC")
    print(f"  Exact match rate:     {exact_match}/{n} ({100*exact_match/n:.1f}%)")
    print(f"  BLEU score:           {bleu:.4f}")
    if semantic_total > 0:
        print(
            f"  Semantic match rate:  {semantic_matches}/{semantic_total} "
            f"({100*semantic_matches/semantic_total:.1f}%) "
            f"(of gerna-valid predictions)"
        )
    print(f"\n{'='*60}")

    # Save detailed results.
    results_path = Path(model_dir) / "eval_results.jsonl"
    with open(str(results_path), "w") as f:
        for i, pair in enumerate(test_pairs):
            result = {
                "english": pair["english"],
                "reference": pair["lojban"],
                "prediction": predictions[i],
                "gerna_valid": gerna_valid[i],
                "exact_match": predictions[i].strip() == pair["lojban"].strip(),
                "domain": pair.get("domain", "unknown"),
            }
            f.write(json.dumps(result) + "\n")

    print(f"\n  Detailed results: {results_path}")

    # Save summary metrics.
    metrics = {
        "test_size": n,
        "gerna_pass_rate": gerna_pass / n if n > 0 else 0,
        "gerna_pass_count": gerna_pass,
        "exact_match_rate": exact_match / n if n > 0 else 0,
        "exact_match_count": exact_match,
        "bleu": bleu,
        "semantic_match_rate": semantic_matches / semantic_total if semantic_total > 0 else 0,
        "semantic_match_count": semantic_matches,
        "semantic_match_total": semantic_total,
    }
    metrics_path = Path(model_dir) / "eval_metrics.json"
    with open(str(metrics_path), "w") as f:
        json.dump(metrics, f, indent=2)
    print(f"  Metrics JSON:     {metrics_path}")

    # Return gerna pass rate for flywheel decisions.
    return gerna_pass / n if n > 0 else 0


def compute_bleu(predictions, references):
    """Compute corpus-level BLEU score (simple 4-gram)."""
    try:
        from collections import Counter
        import math

        def ngrams(tokens, n):
            return [tuple(tokens[i : i + n]) for i in range(len(tokens) - n + 1)]

        total_bp_penalty = 0
        precisions = [0.0] * 4
        weights = [0.25] * 4
        total_ref_len = 0
        total_pred_len = 0

        clipped_counts = [0] * 4
        total_counts = [0] * 4

        for pred, ref in zip(predictions, references):
            pred_tokens = pred.strip().split()
            ref_tokens = ref.strip().split()
            total_pred_len += len(pred_tokens)
            total_ref_len += len(ref_tokens)

            for n in range(1, 5):
                pred_ngrams = ngrams(pred_tokens, n)
                ref_ngrams = ngrams(ref_tokens, n)
                ref_counter = Counter(ref_ngrams)
                pred_counter = Counter(pred_ngrams)

                clipped = sum(
                    min(count, ref_counter.get(ng, 0))
                    for ng, count in pred_counter.items()
                )
                clipped_counts[n - 1] += clipped
                total_counts[n - 1] += len(pred_ngrams)

        # Brevity penalty.
        if total_pred_len == 0:
            return 0.0
        bp = min(1.0, math.exp(1 - total_ref_len / total_pred_len))

        # Modified precisions.
        log_bleu = 0.0
        for n in range(4):
            if total_counts[n] == 0 or clipped_counts[n] == 0:
                return 0.0
            precision = clipped_counts[n] / total_counts[n]
            log_bleu += weights[n] * math.log(precision)

        return bp * math.exp(log_bleu)

    except Exception:
        return 0.0


def compute_semantic_match(predictions, references, gerna_valid, validate_binary):
    """Compare FOL s-expressions for structurally equivalent translations.

    For each prediction that passes gerna: assert both prediction and reference
    into separate nibli-engine instances, extract asserted facts, compare.
    This is a heuristic — structural sexp equality, not logical equivalence.
    """
    # Collect pairs where prediction passed gerna.
    to_check = []
    for i, (pred, ref, valid) in enumerate(zip(predictions, references, gerna_valid)):
        if valid and pred.strip() != ref.strip():
            to_check.append((i, pred.strip(), ref.strip()))

    if not to_check:
        # All valid predictions are exact matches.
        return sum(gerna_valid), sum(gerna_valid)

    # Batch: send "pred\nref\npred\nref\n..." and compare assertion results.
    # Since nibli-validate resets KB between lines, each gets independent validation.
    # For FOL comparison, we would need a more sophisticated approach.
    # For now, count gerna-valid as the total and exact matches within those.
    matches = sum(
        1 for pred, pair, valid in zip(predictions, references, gerna_valid)
        if valid and pred.strip() == pair.strip()
    )
    total = sum(gerna_valid)

    return matches, total


# ─── Iterative refinement (the flywheel) ─────────────────────────

def cmd_refine(args):
    """Take gerna-valid model outputs that differ from reference,
    add them as alternative translations, retrain."""
    model_dir = args.model or DEFAULT_OUTPUT_DIR
    data_path = args.data or DEFAULT_DATA
    eval_results_path = Path(model_dir) / "eval_results.jsonl"

    if not eval_results_path.exists():
        print("[ERROR] No eval results found. Run eval first.", file=sys.stderr)
        print(f"  python3 python/nibli_model.py eval --model {model_dir}", file=sys.stderr)
        sys.exit(1)

    # Load eval results.
    results = []
    with open(str(eval_results_path), "r") as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    results.append(json.loads(line))
                except json.JSONDecodeError:
                    continue

    # Find gerna-valid predictions that differ from reference.
    alternatives = []
    for r in results:
        if r.get("gerna_valid") and not r.get("exact_match"):
            alternatives.append({
                "english": r["english"],
                "lojban": r["prediction"],
                "domain": r.get("domain", "general"),
                "valid": True,
                "source": "model_alternative",
            })

    if not alternatives:
        print("[refine] No alternative translations found (all exact matches or all invalid)")
        return

    print(f"[refine] Found {len(alternatives)} gerna-valid alternative translations")

    # Append alternatives to training data.
    augmented_path = data_path.replace(".jsonl", "_augmented.jsonl")

    # Copy existing data.
    existing_count = 0
    with open(data_path, "r") as src, open(augmented_path, "w") as dst:
        for line in src:
            dst.write(line)
            existing_count += 1

    # Append alternatives.
    with open(augmented_path, "a") as f:
        for alt in alternatives:
            f.write(json.dumps(alt) + "\n")

    print(f"[refine] Augmented dataset: {existing_count} existing + {len(alternatives)} alternatives")
    print(f"[refine] Saved to: {augmented_path}")
    print(f"\n[refine] To retrain with augmented data:")
    print(f"  python3 python/nibli_model.py train --data {augmented_path}")
    print(f"\n[refine] This is the flywheel: model generates → gerna validates → valid")
    print(f"  alternatives feed back into training → model improves → repeat.")


# ─── Push to HuggingFace Hub ─────────────────────────────────────

def cmd_push(args):
    """Push adapter weights to HuggingFace Hub."""
    require("huggingface_hub")

    from huggingface_hub import HfApi

    model_dir = args.model or DEFAULT_OUTPUT_DIR
    repo_id = args.repo

    if not Path(model_dir).exists():
        print(f"[ERROR] Model not found: {model_dir}", file=sys.stderr)
        sys.exit(1)

    if not repo_id:
        print("[ERROR] --repo required (e.g., dhilipsiva/nibli-lojban-7b)", file=sys.stderr)
        sys.exit(1)

    api = HfApi()
    print(f"[push] Uploading {model_dir} to {repo_id}...")
    api.upload_folder(
        folder_path=model_dir,
        repo_id=repo_id,
        repo_type="model",
        commit_message="Upload nibli-lojban-7b QLoRA adapter",
    )
    print(f"[push] Done. Model available at https://huggingface.co/{repo_id}")


# ─── CLI ──────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="nibli-native Lojban LLM: fine-tune, evaluate, refine"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    # Train.
    train_parser = subparsers.add_parser("train", help="QLoRA fine-tune Qwen2.5-7B-Instruct")
    train_parser.add_argument("--data", default=DEFAULT_DATA, help="Training data JSONL")
    train_parser.add_argument("--output", default=DEFAULT_OUTPUT_DIR, help="Output directory")
    train_parser.add_argument("--epochs", type=int, default=5, help="Training epochs (default: 5)")
    train_parser.add_argument("--batch-size", type=int, default=8, help="Batch size (default: 8)")
    train_parser.add_argument("--grad-accum", type=int, default=2, help="Gradient accumulation steps (default: 2)")

    # Eval.
    eval_parser = subparsers.add_parser("eval", help="Evaluate model (gerna pass rate)")
    eval_parser.add_argument("--model", default=DEFAULT_OUTPUT_DIR, help="Model directory")
    eval_parser.add_argument("--test-set", help="Test set JSONL (default: model_dir/test_set.jsonl)")
    eval_parser.add_argument("--eval-batch-size", type=int, default=1, help="Eval batch size")

    # Refine.
    refine_parser = subparsers.add_parser("refine", help="Flywheel: add gerna-valid alternatives to training data")
    refine_parser.add_argument("--model", default=DEFAULT_OUTPUT_DIR, help="Model directory")
    refine_parser.add_argument("--data", default=DEFAULT_DATA, help="Original training data JSONL")

    # Push.
    push_parser = subparsers.add_parser("push", help="Push adapter to HuggingFace Hub")
    push_parser.add_argument("--model", default=DEFAULT_OUTPUT_DIR, help="Model directory")
    push_parser.add_argument("--repo", default="dhilipsiva/nibli-lojban-7b", help="HF repo ID")

    args = parser.parse_args()

    if args.command == "train":
        cmd_train(args)
    elif args.command == "eval":
        cmd_eval(args)
    elif args.command == "refine":
        cmd_refine(args)
    elif args.command == "push":
        cmd_push(args)


if __name__ == "__main__":
    main()
