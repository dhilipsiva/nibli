#!/usr/bin/env python3
"""Fresh production extraction -> independent Nibli finite verdict verification."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time
import tomllib

import extract
import rust_verdicts

DIRECTORY = Path(__file__).resolve().parent
OUTPUT = extract.OUTPUT / "nibli-verdicts"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    result = extract.source_hashes()
    for name in ("flake.nix", "flake.lock"):
        result[name] = digest(extract.ROOT / name)
    for base in (extract.ROOT / "nibli-verify", DIRECTORY / "llbc-json"):
        for path in base.rglob("*"):
            if path.is_file() and "target" not in path.relative_to(base).parts and path.suffix in (".rs", ".toml", ".lock", ".nibli"):
                result[str(path.relative_to(extract.ROOT))] = digest(path)
    return result


def check_saved(report):
    if report.get("status") not in ("verified", "counterexample"):
        raise ValueError("saved run was incomplete")
    if report["sources"] != sources():
        raise ValueError("saved source hashes are stale; rerun the fresh extraction gate")
    paths = {**report["artifacts"], **report["binaries"],
             report["extraction"]["llbc_file"]: report["extraction"]["llbc_sha256"]}
    for mutation in report.get("mutations", {}).values():
        paths.update(mutation["artifacts"])
        paths[mutation["extraction"]["llbc_file"]] = mutation["extraction"]["llbc_sha256"]
    for name, expected in paths.items():
        path = (extract.ROOT / name).resolve()
        if not path.is_relative_to(extract.ROOT) or digest(path) != expected:
            raise ValueError(f"saved artifact changed: {name}")


def rust_digest(hashes):
    rust = {p: h for p, h in hashes.items() if p.endswith(".rs") and p.split('/')[0] in extract.NIBLI_CRATES}
    return hashlib.sha256(json.dumps(rust, sort_keys=True).encode()).hexdigest()


def require_run(command, cwd, log, env, timeout=600):
    result = extract.run(command, cwd, log, env, timeout)
    if result["status"] != "ok":
        raise RuntimeError(f"command {result['status']}: {command[0]}; see {result['log']}")
    return result


def build_tools(env, directory):
    reader_env = env.copy()
    reader_env["RUSTC"] = os.environ["NIBLI_READER_RUSTC"]
    reader_env["CARGO_TARGET_DIR"] = str(extract.OUTPUT / "reader")
    reader = require_run([os.environ["NIBLI_READER_CARGO"], "build", "--locked", "--manifest-path",
                          str(DIRECTORY / "llbc-json/Cargo.toml")], extract.ROOT,
                         directory / "reader-build.log", reader_env)
    native_env = env.copy()
    native_env.pop("CARGO_TARGET_DIR", None)
    runner = require_run(["nix", "develop", "--command", "cargo", "build", "--locked", "--release",
                          "-p", "nibli-verify", "--bin", "nibli-verify-rust"], extract.ROOT,
                         directory / "runner-build.log", native_env)
    return {"reader": reader, "runner": runner}


def check_extraction(result, env, directory):
    if result["status"] != "extracted":
        raise RuntimeError(result.get("reason", "extraction incomplete"))
    llbc = extract.ROOT / result["llbc_file"]
    if digest(llbc) != result["llbc_sha256"]:
        raise ValueError("LLBC digest mismatch")
    # The reader's stdout is JSON, and extract.run records it as its log.
    plain_file = directory / "llbc.json"
    require_run([str(extract.OUTPUT / "reader/debug/nibli-llbc-json"), str(llbc)],
                extract.ROOT, plain_file, env)
    raw = json.loads(plain_file.read_text())
    bundle = rust_verdicts.export(raw)
    bundle_file = directory / "bundle.json"
    bundle_file.write_text(json.dumps(bundle, indent=2) + "\n")
    run = extract.run([str(extract.ROOT / "target/release/nibli-verify-rust"), str(bundle_file),
                       str(directory)], extract.ROOT, directory / "nibli.log", env, 600)
    result_file = directory / "result.json"
    if not result_file.is_file():
        raise RuntimeError(f"Nibli produced no report: {run['status']}")
    checked = json.loads(result_file.read_text())
    code = {"verified": 0, "counterexample": 1, "inconclusive": 2}.get(checked.get("status"))
    if code is None or run["exit_code"] != code:
        raise RuntimeError("Nibli exit status disagrees with its report")
    if digest(llbc) != result["llbc_sha256"]:
        raise ValueError("LLBC changed during verification")
    return raw, checked, run


def fixture_sources(raw):
    crate = rust_verdicts.plain(raw["translated"])
    functions = [f for f in crate["fun_decls"] if f]
    names = ["combine_conjunction", "combine_disjunction", "negate_result", "combine_indeterminate"]
    reasoning = {n: next(f["item_meta"]["source_text"] for f in functions
                         if rust_verdicts.name(f) == f"nibli_reason::reasoning::{n}") for n in names}
    if any(not text for text in reasoning.values()):
        raise ValueError("missing production function source for mutation controls")
    return reasoning


MUTATIONS = {
    "wrong_boolean_branch": ("combine_conjunction", "QueryResult::False", "QueryResult::True"),
    "wrong_resource_precedence": ("combine_indeterminate",
        "(QueryResult::ResourceExceeded(kind), _) => QueryResult::ResourceExceeded(kind)",
        "(QueryResult::ResourceExceeded(_kind), _) => QueryResult::Unknown(UnknownReason::NafDependent)"),
    "wrong_payload": ("combine_indeterminate",
        "(QueryResult::ResourceExceeded(kind), _) => QueryResult::ResourceExceeded(kind)",
        "(QueryResult::ResourceExceeded(_kind), _) => QueryResult::ResourceExceeded(nibli_types::logic::ResourceKind::Depth)"),
    "wrong_negation": ("negate_result", "QueryResult::True => QueryResult::False", "QueryResult::True => QueryResult::True"),
    "reachable_panic": ("combine_conjunction", "QueryResult::False", "panic!()"),
}


def mutations(raw, config, env, directory, outcomes):
    original = fixture_sources(raw)
    for label, mutation in {"baseline": None, **MUTATIONS}.items():
        location = directory / "mutations" / label
        workspace = location / "workspace"
        changed = original.copy()
        if mutation:
            function, old, new = mutation
            if old not in changed[function]:
                raise ValueError(f"mutation anchor changed: {label}")
            changed[function] = changed[function].replace(old, new, 1)
        (workspace / "nibli-reason/src").mkdir(parents=True, exist_ok=True)
        # Reuse the actual production types/methods, whose external-crate LLBC
        # metadata omits source_text. Only the deliberately mutated roots and
        # helper are copied, verbatim from the fresh local extraction.
        type_path = json.dumps(str(extract.ROOT / "nibli-types"))
        (workspace / "nibli-reason/Cargo.toml").write_text(
            '[package]\nname = "nibli-reason"\nversion = "0.0.0"\nedition = "2024"\n'
            + '\n[dependencies]\nnibli-types = { path = ' + type_path + ' }\n')
        (workspace / "Cargo.toml").write_text('[workspace]\nmembers = ["nibli-reason"]\nresolver = "2"\n')
        (workspace / "nibli-reason/src/lib.rs").write_text('#![allow(dead_code)]\nmod reasoning {\nuse nibli_types::logic::{QueryResult, UnknownReason};\n' + "\n".join(changed.values()) + "\n}\n")
        require_run([os.environ["NIBLI_READER_CARGO"], "generate-lockfile", "--offline"], workspace, location / "lock.log", env)
        probe = {"name": label, "package": str((workspace / "nibli-reason").relative_to(extract.ROOT)),
                 "roots": list(rust_verdicts.ROOTS.values()), "obligation": "mutation control"}
        extracted = extract.extract_llbc(probe, config, env, 300, location / "extraction")
        _, checked, run = check_extraction(extracted, env, location)
        failures = [c for c in checked.get("cases", []) if c["status"] == "counterexample"]
        artifacts = {str(p.relative_to(extract.ROOT)): digest(p) for p in
                     (location / "llbc.json", location / "bundle.json", location / "result.json")}
        artifacts.update({str(p.relative_to(extract.ROOT)): digest(p) for p in workspace.rglob("*")
                          if p.is_file() and p.suffix in (".rs", ".toml", ".lock")})
        outcomes[label] = {"status": checked["status"], "counterexamples": len(failures),
                           "example": failures[0]["case"] if failures else None, "run": run,
                           "extraction": extracted, "artifacts": artifacts,
                           "mutation": dict(zip(("function", "old", "new"), mutation)) if mutation else None}
        print(f"Mutation {label}: {checked['status']}", flush=True)
        if checked["status"] != ("counterexample" if mutation else "verified"):
            raise RuntimeError(f"mutation did not yield a concrete counterexample: {label}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mutations", action="store_true", help="also extract and check deliberately faulty Rust copies")
    parser.add_argument("--replay", action="store_true", help="check saved provenance and replay all Nibli observations")
    args = parser.parse_args()
    if args.replay:
        if args.mutations:
            parser.error("--replay and --mutations are separate operations")
        try:
            with extract.exclusive_output():
                saved = json.loads((OUTPUT / "report.json").read_text())
                check_saved(saved)
                run = extract.run([str(extract.ROOT / "target/release/nibli-verify-rust"), "--replay",
                                   str(OUTPUT / "bundle.json"), str(OUTPUT / "result.json")],
                                  extract.ROOT, OUTPUT / "replay.log", os.environ.copy(), 600)
                check_saved(saved)
                code = {"verified": 0, "counterexample": 1}[saved["status"]]
                if run["exit_code"] != code:
                    raise ValueError("replay failed; see replay.log")
            print(f"Replayed Nibli verdict gate: {saved['status']}", flush=True)
            return code
        except (OSError, ValueError, RuntimeError, KeyError, TypeError) as error:
            print(f"inconclusive replay: {error}", file=sys.stderr)
            return 2
    report = {"schema": 1, "status": "inconclusive", "component": "verdict_algebra",
              "self_check_equivalence_verified": False, "lean_used_as_oracle": False}
    started = time.monotonic()
    with extract.exclusive_output():
        OUTPUT.mkdir(parents=True, exist_ok=True)
        report_file = OUTPUT / "report.json"
        report_file.write_text(json.dumps(report, indent=2) + "\n")
        try:
            config = tomllib.loads(extract.CONFIG.read_text())
            env = extract.environment(config, required_tools=("charon",))
            before = sources()
            report["sources"] = before
            report["rust_source_digest"] = rust_digest(before)
            report["tools"] = build_tools(env, OUTPUT)
            report["profile"] = {k: config[k] for k in ("target", "charon_revision", "charon_version")}
            report["binaries"] = {str(p.relative_to(extract.ROOT)): digest(p) for p in
                                  (extract.OUTPUT / "reader/debug/nibli-llbc-json", extract.ROOT / "target/release/nibli-verify-rust")}
            report["reader_compiler"] = os.environ["NIBLI_READER_RUSTC"]
            report["charon_binary"] = os.environ["NIBLI_CHARON_BIN"]
            probe = next(p for p in config["probe"] if p["name"] == "verdicts")
            print("Extracting production Rust verdicts for Nibli", flush=True)
            extracted = extract.extract_llbc(probe, config, env, 300, OUTPUT / "extraction")
            report["extraction"] = extracted
            raw, checked, run = check_extraction(extracted, env, OUTPUT)
            report["nibli"] = {k: checked[k] for k in ("status", "input_values", "expected_executions", "facts", "elapsed_seconds") if k in checked}
            report["run"] = run
            if args.mutations:
                report["mutations"] = {}
                mutations(raw, config, env, OUTPUT, report["mutations"])
            if sources() != before:
                raise ValueError("source changed during verification; rerun on a stable tree")
            report["artifacts"] = {str(p.relative_to(extract.ROOT)): digest(p) for p in
                                   (OUTPUT / "llbc.json", OUTPUT / "bundle.json", OUTPUT / "facts.nibli", OUTPUT / "rules.nibli", OUTPUT / "result.json")}
            report["status"] = checked["status"]
        except (OSError, ValueError, RuntimeError, KeyError, TypeError) as error:
            report["error"] = str(error)
            print(f"inconclusive: {error}", file=sys.stderr)
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        report_file.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Nibli verdict gate: {report['status']}; {report_file.relative_to(extract.ROOT)}", flush=True)
    return {"verified": 0, "counterexample": 1, "inconclusive": 2}[report["status"]]


if __name__ == "__main__":
    sys.exit(main())
