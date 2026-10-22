#!/usr/bin/env python3
"""Regenerate and prove the production verdict algebra, with an axiom audit.

This component gate never certifies the compiler, evaluator, or self-check
equivalence. The unproved obligations remain explicit in coverage.toml.
"""

import hashlib
import json
from pathlib import Path
import re
import sys
import tomllib

import extract


DIRECTORY = Path(__file__).resolve().parent
FOUNDATIONAL_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def audit_axioms(output, expected):
    entries = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))",
        output,
    )
    observed = {}
    for name, axioms, _ in entries:
        if name in observed:
            raise ValueError(f"Duplicate axiom audit entry: {name}")
        observed[name] = sorted(a.strip() for a in axioms.split(",") if a.strip())
        unexpected = set(observed[name]) - FOUNDATIONAL_AXIOMS
        if unexpected:
            raise ValueError(f"Unapproved axioms for {name}: {sorted(unexpected)}")
    if set(observed) != set(expected):
        raise ValueError("Axiom audit did not cover exactly the required theorems")
    return observed


def obligations():
    coverage = tomllib.loads((DIRECTORY / "coverage.toml").read_text())
    for obligation in coverage["obligation"]:
        for path in obligation["sources"] + obligation["tests"]:
            if not (extract.ROOT / path).is_file():
                raise ValueError(f"Missing coverage source: {path}")
    verdicts = next(o for o in coverage["obligation"] if o["id"] == "verdict_algebra")
    expected = verdicts["theorems"]
    declared = re.findall(r"^theorem\s+(\w+)", (DIRECTORY / "Verdicts.lean").read_text(), re.M)
    if not expected or len(expected) != len(set(expected)):
        raise ValueError("The required theorem list is empty or duplicated")
    if {f"NibliSelfCheck.{name}" for name in declared} != set(expected):
        raise ValueError("Verdicts.lean and the required theorem inventory differ")
    return expected


def check_lean_pins(config):
    manifest = json.loads((DIRECTORY / "lake-manifest.json").read_text())
    aeneas = next(p for p in manifest["packages"] if p["name"] == "aeneas")
    if aeneas["rev"] != config["aeneas_revision"] or aeneas["subDir"] != "backends/lean":
        raise ValueError("Lean library and Rust extractor Aeneas pins differ")


def check_artifacts(result):
    for path, expected in result["artifacts"].items():
        if hashlib.sha256((extract.ROOT / path).read_bytes()).hexdigest() != expected:
            raise ValueError(f"Generated definition changed during proof: {path}")
    llbc = extract.OUTPUT / "probes" / "verdicts" / "input.llbc"
    if hashlib.sha256(llbc.read_bytes()).hexdigest() != result["llbc_sha256"]:
        raise ValueError("LLBC changed during proof")


def prove(config, env, report):
    expected = obligations()
    check_lean_pins(config)
    probe = next(p for p in config["probe"] if p["name"] == "verdicts")
    print("Extracting the production verdict functions", flush=True)
    result = extract.extract(probe, config, env, 300)
    report["extraction"] = result
    if result["status"] != "translated":
        raise ValueError(result["reason"])
    for path in [DIRECTORY / "Verdicts.lean"] + [extract.ROOT / p for p in result["artifacts"]]:
        if re.search(r"\b(sorry|admit|axiom|opaque)\b", path.read_text()):
            raise ValueError(f"Unproved or opaque definition in {path}")

    def command(name, argv, timeout=300):
        log = extract.OUTPUT / f"verdicts-{name}.log"
        step = extract.run(argv, DIRECTORY, log, env, timeout)
        report[name] = step
        if step["status"] != "ok":
            raise ValueError(f"{name} failed; see {step['log']}")
        return log.read_text()

    version = command("lean-version", ["lake", "env", "lean", "--version"])
    required = config["lean_toolchain"].split(":v", 1)[1]
    if f"version {required}," not in version or config["target"] not in version:
        raise ValueError("Lean version/target does not match the pinned profile")
    print("Checking the extracted definitions and verdict theorems", flush=True)
    command("build", ["lake", "build"], 1800)
    # Re-elaborate the local proof with warnings fatal even if Lake has an
    # up-to-date cache; an admitted theorem must never count as a passing gate.
    command("proof", ["lake", "env", "lean", "-DwarningAsError=true", "Verdicts.lean"])
    audit = extract.OUTPUT / "VerdictsAudit.lean"
    audit.write_text("import Verdicts\n" + "".join(f"#print axioms {name}\n" for name in expected))
    output = command("audit", ["lake", "env", "lean", "-DwarningAsError=true", str(audit)])
    report["axioms"] = audit_axioms(output, expected)
    report["audit_sha256"] = hashlib.sha256(audit.read_bytes()).hexdigest()
    check_artifacts(result)


def main():
    config = tomllib.loads(extract.CONFIG.read_text())
    try:
        env = extract.environment(config)
        with extract.exclusive_output():
            report_path = extract.OUTPUT / "verdicts-report.json"
            sources = extract.source_hashes()
            report = {
                "schema": 1, "component": "verdict_algebra", "component_verified": False,
                "self_check_equivalence_verified": False,
                "notice": "Production verdict algebra only; full-equivalence obligations remain unproved.",
                "sources": sources,
                "aeneas_revision": config["aeneas_revision"],
                "charon_revision": config["charon_revision"],
                "lean_toolchain": config["lean_toolchain"],
                "target": config["target"],
            }
            # Clear an old success before any command can fail or be interrupted.
            report_path.write_text(json.dumps(report, indent=2) + "\n")
            try:
                prove(config, env, report)
                if extract.source_hashes() != sources:
                    raise ValueError("Source changed during proof; discard this run and rerun")
                report["component_verified"] = True
            except (ValueError, RuntimeError, OSError, KeyError, StopIteration) as error:
                report["error"] = str(error)
            report_path.write_text(json.dumps(report, indent=2) + "\n")
            if not report["component_verified"]:
                print(report["error"], file=sys.stderr)
                return 1
    except (RuntimeError, OSError, ValueError) as error:
        print(error, file=sys.stderr)
        return 2
    print("Verified: production verdict algebra. Full self-check equivalence is NOT proved.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
