#!/usr/bin/env python3
"""Probe production Rust extraction; never mistake translation for a proof.

Run in this directory's pinned Nix shell. All generated files, including
failures, stay under target/self-check-proof. A failed probe is evidence of an
extraction blocker, not a native compiler rejection or a verified theorem.
"""

import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import re
import shutil
import subprocess
import sys
import time
import tomllib


ROOT = Path(__file__).resolve().parents[2]
CONFIG = Path(__file__).with_name("extraction.toml")
OUTPUT = ROOT / "target" / "self-check-proof"
NIBLI_CRATES = (
    "nibli-types", "nibli-lexicon", "nibli-kr", "nibli-semantics",
    "nibli-reason", "nibli-session",
)


@contextmanager
def exclusive_output():
    """Never race another extractor or proof run over generated definitions."""
    OUTPUT.mkdir(parents=True, exist_ok=True)
    with (OUTPUT / "run.lock").open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError("Another extraction/proof run owns the output directory") from error
        yield


def environment(config):
    """Reject ambient/mismatched tools instead of attributing them to our pins."""
    lock = json.loads(CONFIG.with_name("flake.lock").read_text())["nodes"]
    for tool in ("charon", "aeneas"):
        if lock[tool]["locked"]["rev"] != config[f"{tool}_revision"]:
            raise RuntimeError(f"{tool} revision differs between extraction.toml and flake.lock")
        expected = os.environ.get(f"NIBLI_{tool.upper()}_BIN")
        actual = shutil.which(tool)
        if not expected or not actual or os.path.realpath(actual) != os.path.realpath(expected):
            raise RuntimeError(f"Missing pinned {tool}; run in nix develop ./proofs/self-check")
    if CONFIG.with_name("lean-toolchain").read_text().strip() != config["lean_toolchain"]:
        raise RuntimeError("Lean toolchain differs from extraction.toml")
    env = os.environ.copy()
    env["CARGO_TARGET_DIR"] = str(OUTPUT / "cargo")
    # User-supplied Cargo flags could disable checks or alter conditional code.
    for key in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC", "RUSTC_WRAPPER",
                "RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_RUSTFLAGS"):
        if env.get(key):
            raise RuntimeError(f"Unset {key} for the pinned extraction profile")
    return env


def run(command, cwd, log, env, timeout):
    started = time.monotonic()
    with log.open("w") as output:
        try:
            process = subprocess.Popen(
                command,
                cwd=cwd,
                env=env,
                stdout=output,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            code = process.wait(timeout=timeout)
            status = "ok" if code == 0 else "failed"
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            status, code = "timeout", None
        except OSError as error:
            output.write(f"Could not start process: {error}\n")
            status, code = "failed", None
    return {
        "command": command,
        "status": status,
        "exit_code": code,
        "seconds": round(time.monotonic() - started, 3),
        "log": str(log.relative_to(ROOT)),
    }


def source_hashes():
    """Bind reports to local source content, including uncommitted changes."""
    paths = {ROOT / "Cargo.lock", ROOT / "Cargo.toml",
             ROOT / "nibli-verify/spec/nibli_checker.nibli",
             CONFIG.with_name("lean-toolchain")}
    for pattern in ("*.py", "*.lean", "*.toml", "*.nix", "*.lock", "*.json"):
        paths.update(CONFIG.parent.glob(pattern))
    for crate in NIBLI_CRATES:
        paths.add(ROOT / crate / "Cargo.toml")
        paths.update((ROOT / crate / "src").rglob("*.rs"))
        paths.update((ROOT / crate / "src").rglob("*.pest"))
        if (ROOT / crate / "build.rs").exists():
            paths.add(ROOT / crate / "build.rs")
    return {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(paths)
    }


def validate_llbc(path, probe, config):
    """A successful process with missing/opaque roots is not an extraction."""
    artifact = json.loads(path.read_text())
    if artifact["has_errors"]:
        raise ValueError("Charon recorded errors in the LLBC artifact")
    if artifact["charon_version"] != config["charon_version"]:
        raise ValueError("LLBC was emitted by a different Charon version")
    translated = artifact["translated"]
    targets = [t["key"] for t in translated["target_information"]]
    if targets != [config["target"]]:
        raise ValueError("LLBC target differs from the configured target")
    found = set()
    for function in translated["fun_decls"]:
        if function is None:
            continue
        metadata = function["item_meta"]
        name = metadata["name"]
        if all("Ident" in part for part in name):
            rust_path = "::".join(part["Ident"][0] for part in name)
            if rust_path in probe["roots"]:
                if not metadata["started_from"] or "Structured" not in function["body"]:
                    raise ValueError(f"Root has no extracted body: {rust_path}")
                found.add(rust_path)
        first = name[0].get("Ident", [""])[0]
        if first in {crate.replace("-", "_") for crate in NIBLI_CRATES}:
            if function["body"] == "Opaque":
                raise ValueError(f"Opaque Nibli definition in LLBC: {name}")
    missing = set(probe["roots"]) - found
    if missing:
        raise ValueError(f"Missing production roots in LLBC: {sorted(missing)}")


def diagnostics(log):
    text = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", log.read_text(errors="replace"))
    # Keep the first actual failure and its source location, not progress bars
    # or the potentially enormous OCaml backtrace.
    match = re.search(r"\[Error\][^\n]*\n(?:Source:[^\n]*\n)?(?:Compiler source:[^\n]*)?", text)
    return match.group(0).strip() if match else None


def extract(probe, config, env, timeout):
    module = probe.get("lean_module", "Input")
    if not re.fullmatch(r"[A-Z][A-Za-z0-9]*", module):
        raise ValueError("Lean module must be a single capitalized identifier")
    directory = OUTPUT / "probes" / probe["name"]
    # Only remove this probe's generated output. Failed runs cannot reuse stale
    # successful files; no checked-in proof or source is an extraction target.
    if directory.exists():
        shutil.rmtree(directory)
    directory.mkdir(parents=True)
    llbc = directory / ("input.llbc" if module == "Input" else f"{module}.llbc")
    command = [
        "charon", "cargo", "--preset=aeneas", "--error-on-warnings",
        f"--dest-file={llbc}",
    ]
    for root in probe["roots"]:
        command.extend(["--start-from", root])
    # Traverse Nibli dependency bodies too. An opaque semantic compiler would
    # simply move the very property being verified into the trusted base.
    for crate in NIBLI_CRATES:
        command.extend(["--include", crate.replace("-", "_")])
    command.extend(["--", "--lib", "--locked", "--target", config["target"]])
    charon = run(command, ROOT / probe["package"], directory / "charon.log", env, timeout)
    result = {
        "name": probe["name"], "obligation": probe["obligation"],
        "roots": probe["roots"], "charon": charon, "status": "blocked",
    }
    if charon["status"] != "ok" or not llbc.is_file():
        result["reason"] = "Charon did not produce a complete LLBC artifact"
        return result
    try:
        validate_llbc(llbc, probe, config)
    except (ValueError, KeyError, TypeError) as error:
        result["reason"] = f"Incomplete LLBC: {error}"
        return result
    result["llbc_sha256"] = hashlib.sha256(llbc.read_bytes()).hexdigest()
    result["llbc_file"] = str(llbc.relative_to(ROOT))
    result["lean_module"] = module
    # With split files Aeneas names imports after the LLBC file. Distinct
    # modules let component proofs coexist in one Lake project.
    lean = directory / "lean" / module
    lean.mkdir(parents=True)
    aeneas = run(
        ["aeneas", "-backend", "lean", "-abort-on-error", "-warnings-as-errors",
         "-split-files", "-dest", str(lean), str(llbc)],
        ROOT, directory / "aeneas.log", env, timeout,
    )
    result["aeneas"] = aeneas
    if aeneas["status"] != "ok":
        result["reason"] = "Aeneas could not translate the production implementation"
        result["diagnostic"] = diagnostics(directory / "aeneas.log")
        return result
    templates = sorted(str(p.relative_to(ROOT)) for p in lean.rglob("*Template*.lean"))
    if templates:
        result["reason"] = "Unimplemented external definitions require an explicit proof boundary"
        result["templates"] = templates
        return result
    generated = sorted(lean.rglob("*.lean"))
    if not generated:
        result["reason"] = "No Lean definitions were emitted"
        return result
    result["status"] = "translated"
    result["artifacts"] = {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in generated
    }
    return result


def main():
    config = tomllib.loads(CONFIG.read_text())
    probes = {p["name"]: p for p in config["probe"]}
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--probe", action="append", choices=sorted(probes))
    parser.add_argument("--timeout", type=int, default=300,
                        help="Maximum seconds per extraction process (default: 300)")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    try:
        env = environment(config)
        with exclusive_output():
            return extract_selected(config, args.probe, env, args.timeout)
    except RuntimeError as error:
        print(error, file=sys.stderr)
        return 2


def extract_selected(config, selected, env, timeout):
    probes = {p["name"]: p for p in config["probe"]}
    sources = source_hashes()
    results = []
    names = selected or list(probes)
    for name in names:
        print(f"Extracting {name}: {probes[name]['obligation']}", flush=True)
        result = extract(probes[name], config, env, timeout)
        results.append(result)
        report = {
            "schema": 1, "certified": False,
            "notice": "Extraction feasibility only; no equivalence theorem has been proved.",
            "config_sha256": hashlib.sha256(CONFIG.read_bytes()).hexdigest(),
            "aeneas_revision": config["aeneas_revision"],
            "charon_revision": config["charon_revision"],
            "target": config["target"], "probes": results,
            "selected_probes": names,
            "all_probes_selected": set(names) == set(probes),
            "sources": sources,
            "tools": {tool: os.path.realpath(shutil.which(tool))
                      for tool in ("charon", "aeneas")},
        }
        (OUTPUT / "extraction-report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"{name}: {result['status']}" +
              (f" — {result['reason']}" if "reason" in result else " (not proved)"), flush=True)
    if source_hashes() != sources:
        print("Source changed during extraction; discard this report and rerun", file=sys.stderr)
        return 2
    return 0 if all(r["status"] == "translated" for r in results) else 1


if __name__ == "__main__":
    sys.exit(main())
