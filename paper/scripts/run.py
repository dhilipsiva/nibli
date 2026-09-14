#!/usr/bin/env python3
"""Reproducible, serial experiments. All subprocesses use argument vectors.

Run inside `nix develop .#paper`. Raw stdout/stderr, explicit preparation
records, partial phases, failed runs, and external cutoffs are retained.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

import workloads as w

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / "paper"
BIN = ROOT / "target/release/nibli-bench-paper"
PROTOCOL = json.loads((PAPER / "protocol.json").read_text())


def dump(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def capture(args):
    p = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if p.returncode:
        raise RuntimeError(f"{args}: {p.returncode}\n{p.stdout}")
    return p.stdout.strip()


def fingerprints():
    paths = capture(["git", "ls-files", "*.rs", "*.wit", "*.pest", "*Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"]).splitlines()
    paths += ["paper/protocol.json", "paper/scripts/workloads.py", "paper/scripts/run.py", "paper/tests/test_adapters.py", "nibli/src/bin/bench_paper.rs"]
    values = {p: digest(ROOT / p) for p in sorted(set(paths)) if not p.startswith(("book/", "fuzz/"))}
    return {"files": values, "sha256": hashlib.sha256(json.dumps(values, sort_keys=True).encode()).hexdigest()}


def tools_present():
    names = ["rustc", "cargo", "just", "vampire", "clingo", "lean", "souffle", "c++", "wasmtime", "wasm-pack", "node", "pdflatex", "latexmk", "time", "timeout", "pdfinfo", "pdftotext"]
    missing = [name for name in names if not shutil.which(name)]
    if missing:
        raise RuntimeError("required tools absent (skips are not evidence): " + ", ".join(missing))
    return {name: shutil.which(name) for name in names}


def metadata():
    paths = tools_present()
    versions = {}
    for name in ["rustc", "cargo", "vampire", "clingo", "lean", "souffle", "c++", "wasmtime", "wasm-pack", "node", "pdflatex", "python3"]:
        p = subprocess.run([name, "--version"], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
        versions[name] = {"returncode": p.returncode, "output": p.stdout.strip()}
    return {"utc": utc(), "baseline": PROTOCOL["engine_baseline"], "git_head": capture(["git", "rev-parse", "HEAD"]),
            "git_status": capture(["git", "status", "--short"]), "fingerprints": fingerprints(),
            "profile": PROTOCOL["profile"], "tool_paths": paths, "versions": versions,
            "uname": platform.uname()._asdict(), "cpu": capture(["lscpu"]),
            "memory": Path("/proc/meminfo").read_text(), "cpu_affinity": sorted(os.sched_getaffinity(0)),
            "binary_sha256": digest(BIN), "environment": {k: os.environ.get(k) for k in ["OMP_NUM_THREADS", "PYTHONHASHSEED", "SOURCE_DATE_EPOCH", "NIBLI_MATERIALIZE", "RUSTFLAGS"]}}


def measured(command, stem, cutoff, env=None, accepted=(0,), stdin=None):
    """GNU time wraps timeout, so cutoffs retain peak RSS and exit 124/137."""
    stem.parent.mkdir(parents=True, exist_ok=True)
    stdout, stderr, usage = (stem.with_suffix(s) for s in (".stdout", ".stderr", ".time"))
    cmd = [shutil.which("time"), "-f", "%M\t%U\t%S\t%x", "-o", str(usage),
           "timeout", "--signal=TERM", "--kill-after=1s", f"{cutoff}s", *map(str, command)]
    started = utc()
    start = time.perf_counter()
    runenv = os.environ.copy()
    runenv.update({"OMP_NUM_THREADS": "1", "RAYON_NUM_THREADS": "1", "NIBLI_QUIET": "1"})
    if env:
        runenv.update(env)
    with stdout.open("wb") as out, stderr.open("wb") as err:
        proc = subprocess.Popen(cmd, cwd=ROOT, stdout=out, stderr=err, env=runenv,
                                stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL, start_new_session=True)
        # GNU timeout enforces the external deadline. Blocking wait avoids
        # Popen.wait(timeout)'s exponential polling delays, which otherwise
        # quantize millisecond baseline runtimes and bias the comparison.
        proc.communicate(input=stdin.encode() if stdin is not None else None)
    elapsed = (time.perf_counter() - start) * 1000
    status = "timeout" if proc.returncode in (124, 137) else "ok" if proc.returncode in accepted else "process_failure"
    rss = cpu_user = cpu_system = None
    if usage.exists():
        for line in usage.read_text().splitlines():
            parts = line.split("\t")
            if len(parts) == 4 and parts[0].isdigit():
                rss, cpu_user, cpu_system = int(parts[0]), float(parts[1]), float(parts[2])
    return {"started_utc": started, "command": list(map(str, command)), "cutoff_seconds": cutoff,
            "status": status, "exit_code": proc.returncode, "wall_ms": elapsed, "peak_rss_kib": rss,
            "cpu_user_s": cpu_user, "cpu_system_s": cpu_system,
            "stdout": str(stdout.relative_to(ROOT)), "stderr": str(stderr.relative_to(ROOT)),
            "usage": str(usage.relative_to(ROOT))}


def prepare(program, req, directory, cache, compile_souffle=True):
    directory.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    dump(directory / "program.json", program)
    dump(directory / "request.json", req)
    (directory / "input.nibli").write_text("\n".join(req["statements"]) + "\n")
    (directory / "queries.nibli").write_text("\n".join(req["queries"]) + "\n")
    (directory / "input.lp").write_text(w.clingo(program))
    source, facts = w.souffle(program)
    (directory / "input.dl").write_text(source)
    for name, rows in facts.items():
        (directory / f"{name}.facts").write_text(rows)
    translation_ms = (time.perf_counter() - start) * 1000
    key = hashlib.sha256(source.encode()).hexdigest()
    executable = cache / key / "program"
    record = {"translation_ms": translation_ms, "souffle_source_sha256": key,
              "binary": str(executable.relative_to(ROOT)), "facts": len(program["facts"])}
    if compile_souffle:
        compilation = executable.parent / "compilation.json"
        if not compilation.exists():
            executable.parent.mkdir(parents=True, exist_ok=True)
            (executable.parent / "input.dl").write_text(source)
            result = measured(["souffle", "-j", "1", "-o", str(executable), str(directory / "input.dl")],
                              executable.parent / "compile", PROTOCOL["preparation_cutoff_seconds"])
            if result["status"] == "ok":
                result["binary_sha256"] = digest(executable)
            dump(compilation, result)
        record["compilation"] = json.loads(compilation.read_text())
    dump(directory / "preparation.json", record)
    return record


def parse_nibli(record, req, program):
    phases = []
    malformed = []
    for line in (ROOT / record["stdout"]).read_text().splitlines():
        if not line.startswith("{"):
            if line.strip():
                malformed.append(line)
            continue
        try:
            phases.append(json.loads(line))
        except json.JSONDecodeError:
            malformed.append(line)
    record["phases"] = phases
    expected_stages = program.get("stage_expected", [program["expected"]])
    outcomes = [x for x in phases if x.get("phase") in ("query", "certificate")]
    record["answers"] = [{"stage": x["stage"], "index": x["index"], "verdict": x["verdict"]} for x in outcomes]
    record["definitive_mismatches"] = []
    record["envelope_failures"] = []
    for x in outcomes:
        expected = expected_stages[x["stage"]][x["index"]]
        if x["verdict"] in ("TRUE", "FALSE") and x["verdict"] != expected:
            record["definitive_mismatches"].append({"stage": x["stage"], "index": x["index"], "expected": expected, "actual": x["verdict"]})
        if x.get("coherent") is False:
            record["envelope_failures"].append(x["coherence_errors"])
    if record["status"] == "ok":
        keys = [(x["stage"], x["index"]) for x in outcomes]
        expected_keys = [(s, i) for s, es in enumerate(expected_stages) for i in range(len(es))]
        if malformed or keys != expected_keys or not phases or phases[-1].get("phase") != "complete":
            record["status"] = "harness_failure"
            record["parse_errors"] = malformed or ["missing/duplicate/reordered phase records"]
    # The envelope stays in raw stdout, exactly as emitted. The summary holds a
    # path and sizes rather than making a second enormous copy of every trace.
    for x in phases:
        x.pop("envelope", None)
        x.pop("ids", None)


def execute(implementation, directory, prep, req, program, stem):
    cutoff = PROTOCOL["cutoff_seconds"]
    if implementation == "nibli":
        command = [BIN, directory / "request.json"]
        if req["updates"]:
            command.append(stem.with_suffix(".redb"))
        record = measured(command, stem, cutoff)
        parse_nibli(record, req, program)
        # Database snapshots are small and retained for update runs; they can be
        # reopened independently with the original driver/toolchain.
    elif implementation == "clingo":
        record = measured(["clingo", "--outf=2", "--models=1", "--parallel-mode=1", directory / "input.lp"], stem, cutoff, accepted=(0, 10, 20, 30))
        if record["status"] == "ok":
            try:
                result = json.loads((ROOT / record["stdout"]).read_text())
                calls = result["Call"]
                witnesses = [witness for call in calls for witness in call.get("Witnesses", [])]
                if result["Result"] != "SATISFIABLE" or len(witnesses) != 1:
                    raise ValueError("expected the unique stable model of a stratified program")
                values = witnesses[0]["Value"]
                if any(not re.fullmatch(r"answer\(\d+\)", v) for v in values):
                    raise ValueError("unexpected clingo output atom")
                present = {int(v[7:-1]) for v in values}
                record["answers"] = [{"stage": 0, "index": i, "verdict": "TRUE" if i in present else "FALSE"} for i in range(len(program["queries"]))]
            except (ValueError, KeyError, IndexError) as error:
                record.update(status="harness_failure", parse_errors=[str(error)])
    else:
        if prep["compilation"]["status"] != "ok":
            return {"status": "preparation_failure", "preparation": prep["compilation"], "answers": []}
        output = stem.with_suffix(".out")
        output.mkdir()
        record = measured([ROOT / prep["binary"], "-j", "1", "-F", directory, "-D", output], stem, cutoff)
        if record["status"] == "ok":
            try:
                present = {int(line) for line in (output / "answer.csv").read_text().splitlines()}
                if not present <= set(range(len(program["queries"]))):
                    raise ValueError("out-of-range answer")
                record["answers"] = [{"stage": 0, "index": i, "verdict": "TRUE" if i in present else "FALSE"} for i in range(len(program["queries"]))]
            except (OSError, ValueError) as error:
                record.update(status="harness_failure", parse_errors=[str(error)])
    if implementation != "nibli":
        record["definitive_mismatches"] = [a for a in record.get("answers", []) if a["verdict"] != program["expected"][a["index"]]]
    return record


def smoke(directory):
    tools_present()
    initial_fingerprints = fingerprints()
    initial_binary = digest(BIN)
    if directory.exists():
        raise RuntimeError("smoke output exists; choose a new --output directory")
    directory.mkdir(parents=True)
    # Hand-derived discriminators: a two-step Horn proof, an absent atom, NAF
    # with and without a blocker, and both policy support paths/unknown sink.
    programs = [
        {"family": "hand_horn", "size": 2, "direction": "both", "seed": 0,
         "facts": [w.atom("dog", "Ada")],
         "rules": [w.rule(w.atom("animal", "$x"), w.atom("dog", "$x")), w.rule(w.atom("alive", "$x"), w.atom("animal", "$x"))],
         "queries": [w.atom("alive", "Ada"), w.atom("alive", "Bea")], "expected": ["TRUE", "FALSE"]},
        {"family": "hand_naf", "size": 3, "direction": "both", "seed": 0,
         "facts": [w.atom("dog", "Ada"), w.atom("dog", "Bea"), w.atom("cat", "Bea")],
         "rules": [w.rule(w.atom("animal", "$x"), w.atom("dog", "$x"), w.atom("cat", "$x", neg=True))],
         "queries": [w.atom("animal", "Ada"), w.atom("animal", "Bea"), w.atom("animal", "Cyd")], "expected": ["TRUE", "FALSE", "FALSE"]},
        w.chain(4, "forward", 11), w.chain(4, "backward", 11), w.policy(100, 11),
    ]
    programs[-1]["queries"] += [w.atom("authorized", "F2", "Release", "S2"), w.atom("warns", "Gate", "F3", "S3")]
    programs[-1]["expected"] += ["TRUE", "TRUE"]
    records = []
    for i, program in enumerate(programs):
        req = w.request(program)
        case = directory / "inputs" / str(i)
        prep = prepare(program, req, case, directory / "compiled")
        for implementation in ("nibli", "clingo", "souffle"):
            r = execute(implementation, case, prep, req, program, directory / "raw" / f"{i}-{implementation}")
            r.update(implementation=implementation, case=program["family"])
            records.append(r)
            print("smoke", program["family"], implementation, r["status"], r.get("answers"), flush=True)
    p = w.updates(100, 11)
    req = w.request(p, mode="updates")
    case = directory / "inputs/updates"
    prep = prepare(p, req, case, directory / "compiled", False)
    records.append(execute("nibli", case, prep, req, p, directory / "raw/updates"))
    passed = all(r["status"] == "ok" and not r.get("definitive_mismatches") and not r.get("envelope_failures")
                 and all(a["verdict"] in ("TRUE", "FALSE") for a in r.get("answers", [])) for r in records)
    passed = passed and initial_fingerprints == fingerprints() and initial_binary == digest(BIN)
    report = {"passed": passed, "utc": utc(), "fingerprints": initial_fingerprints, "binary_sha256": initial_binary, "records": records}
    dump(directory / "smoke.json", report)
    if not passed:
        raise RuntimeError("harness validation failed; preserve this report and fix before freezing")


def freeze(smoke_path):
    path = PAPER / "protocol.freeze.json"
    if path.exists():
        raise RuntimeError("protocol already frozen; never overwrite a recorded freeze")
    result = json.loads(smoke_path.read_text())
    current = fingerprints()
    if not result["passed"] or result["fingerprints"] != current or result["binary_sha256"] != digest(BIN):
        raise RuntimeError("a successful smoke of these exact sources and binary is required")
    dump(path, {"utc": utc(), "protocol": PROTOCOL, "fingerprints": current,
                "binary_sha256": digest(BIN), "smoke": str(smoke_path.relative_to(ROOT)), "smoke_sha256": digest(smoke_path)})
    print("frozen", current["sha256"])


def evaluate(directory):
    frozen = json.loads((PAPER / "protocol.freeze.json").read_text())
    if frozen["fingerprints"] != fingerprints() or frozen["binary_sha256"] != digest(BIN):
        raise RuntimeError("code, protocol, or executable changed after freeze")
    if directory.exists():
        raise RuntimeError("result directory exists; never overwrite an experiment")
    directory.mkdir(parents=True)
    dump(directory / "environment.json", metadata())
    specs = list(w.experiments(PROTOCOL))
    rng = random.Random(PROTOCOL["order_seed"])
    rng.shuffle(specs)
    schedule = []
    for group, p, depth, mat, mode, implementations in specs:
        case_id = f'{group}-{p["family"]}-{p["size"]}-{p["direction"]}-s{p["seed"]}-d{depth}-m{int(mat)}-{mode}'
        for rep in range(-PROTOCOL["warmups_per_seed_case"], PROTOCOL["measured_repetitions"]):
            order = implementations.copy()
            rng.shuffle(order)
            for implementation in order:
                schedule.append({"case_id": case_id, "group": group, "program": p, "depth": depth, "materialization": mat, "mode": mode,
                                 "rep": rep, "warmup": rep < 0, "implementation": implementation})
    dump(directory / "schedule.json", schedule)
    prepared = {}
    # Preparation is explicit and kept out of measured implementation order.
    for group, p, depth, mat, mode, implementations in specs:
        case_id = f'{group}-{p["family"]}-{p["size"]}-{p["direction"]}-s{p["seed"]}-d{depth}-m{int(mat)}-{mode}'
        req = w.request(p, depth, mat, mode)
        prepared[case_id] = prepare(p, req, directory / "inputs" / case_id, directory / "compiled", "souffle" in implementations)
    with (directory / "observations.jsonl").open("x") as observations:
        for index, item in enumerate(schedule):
            p = item["program"]
            req = w.request(p, item["depth"], item["materialization"], item["mode"])
            run_id = f'{index:05d}-{item["case_id"]}-{item["implementation"]}-r{item["rep"]}'
            record = execute(item["implementation"], directory / "inputs" / item["case_id"], prepared[item["case_id"]], req, p, directory / "raw" / run_id)
            record.update({k: v for k, v in item.items() if k != "program"})
            record.update(run_id=run_id, family=p["family"], size=p["size"], direction=p["direction"], seed=p["seed"],
                          fact_count=len(p["facts"]), expected=p.get("stage_expected", [p["expected"]]))
            observations.write(json.dumps(record, sort_keys=True) + "\n")
            observations.flush()
            if index % 10 == 0 or record["status"] != "ok" or record.get("definitive_mismatches"):
                print(f'{index+1}/{len(schedule)} {run_id}: {record["status"]}', flush=True)
    dump(directory / "completed.json", {"utc": utc(), "runs": len(schedule), "fingerprints": fingerprints(),
                                       "observations_sha256": digest(directory / "observations.jsonl")})


def check(directory):
    tools_present()
    directory.mkdir(parents=True, exist_ok=True)
    commands = [
        ["cargo", "fmt", "--all", "--check"],
        ["cargo", "clippy", "--no-deps", "--locked", "--release", "-p", "nibli", "--features", "bench-bins", "--bin", "nibli-bench-paper", "--", "-D", "warnings"],
        ["just", "profile=release", "release-check", "verify-proofs", "verify-soundness", "verify-nibli-kr-seam", "verify-pins", "verify-adjudication", "test-persistence-replay", "test-store"],
        ["cargo", "test", "--locked", "--release", "-p", "nibli-reason", "--lib"],
        ["cargo", "test", "--locked", "--release", "-p", "nibli-engine", "--test", "integration"],
        ["just", "profile=release", "ci-wasm"],
        ["python3", "-m", "unittest", "discover", "-s", "paper/tests", "-v"],
    ]
    records = []
    for i, command in enumerate(commands):
        print("checking", " ".join(command), flush=True)
        result = measured(command, directory / f"check-{i}", 7200, env={"NIBLI_QUIET": "0"})
        log = (ROOT / result["stdout"]).read_text() + (ROOT / result["stderr"]).read_text()
        # The required checks above must actually execute. Do not reinterpret
        # missing-tool branches in the existing recipes as passing evidence.
        result["missing_tool_skip"] = bool(re.search(r"^(?!test ).*(?:\bSKIPPED\b|not found.*skipp|unavailable.*skipp)", log, re.I | re.M))
        records.append(result)
        dump(directory / "checks.json", {"utc": utc(), "fingerprints": fingerprints(), "records": records,
                                         "passed": len(records) == len(commands) and all(x["status"] == "ok" and not x["missing_tool_skip"] for x in records)})
        if result["status"] != "ok" or result["missing_tool_skip"]:
            raise RuntimeError(f"required check failed: {command}; inspect {directory}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("action", choices=["smoke", "freeze", "evaluate", "check", "metadata"])
    parser.add_argument("--output", type=Path)
    parser.add_argument("--smoke", type=Path, default=PAPER / "results/pilot/smoke.json")
    args = parser.parse_args()
    if args.action == "freeze":
        freeze(args.smoke.resolve())
    elif args.action == "metadata":
        print(json.dumps(metadata(), indent=2))
    else:
        default = {"smoke": "pilot", "evaluate": "evaluation", "check": "checks"}[args.action]
        directory = (args.output or PAPER / "results" / default).resolve()
        globals()[args.action](directory)


if __name__ == "__main__":
    main()
