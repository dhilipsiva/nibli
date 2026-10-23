#!/usr/bin/env python3
"""Regenerate a production component and audit its implementation proofs.

This component gate never certifies the compiler, evaluator, or self-check
equivalence. The unproved obligations remain explicit in coverage.toml.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import tomllib

import extract
from checker_closure import check_checker_closure


DIRECTORY = Path(__file__).resolve().parent
FOUNDATIONAL_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COMPONENTS = {
    "verdict_algebra": {
        "probe": "verdicts", "module": "Verdicts", "namespace": "NibliSelfCheck",
        "label": "production verdict algebra",
    },
    "scc_stack": {
        "probe": "scc_kernel", "module": "SccCriterion", "namespace": "NibliSelfCheck.Scc",
        "helpers": ["SccGraph", "SccKernelProofs", "SccInvariant", "SccTermination", "SccTraversal"],
        "label": "production indexed SCC traversal and cycle criterion",
    },
    "stratification_scan": {
        "probe": "scc_kernel", "module": "StratificationScan",
        "namespace": "NibliSelfCheck.Stratification",
        "output_prefix": "stratification_scan",
        "label": "production named negative-edge scan",
    },
}


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


def obligations(component_id="verdict_algebra"):
    coverage = tomllib.loads((DIRECTORY / "coverage.toml").read_text())
    for obligation in coverage["obligation"]:
        for path in obligation["sources"] + obligation["tests"]:
            if not (extract.ROOT / path).is_file():
                raise ValueError(f"Missing coverage source: {path}")
    component = COMPONENTS[component_id]
    obligation = next(o for o in coverage["obligation"] if o["id"] == component_id)
    paths = [DIRECTORY / f"{module}.lean" for module in
             component.get("helpers", []) + [component["module"]]]
    return check_theorem_inventory(obligation, paths, component["namespace"])


def check_theorem_inventory(obligation, paths, namespace):
    expected = obligation["theorems"]
    if obligation["theorem_files"] != [str(path.relative_to(extract.ROOT)) for path in paths]:
        raise ValueError("Coverage must name every local theorem file")
    declared = [name for path in paths for name in re.findall(r"^theorem\s+(\w+)", path.read_text(), re.M)]
    if len(declared) != len(set(declared)):
        raise ValueError("Duplicate public theorem names across local files")
    if not expected or len(expected) != len(set(expected)):
        raise ValueError("The required theorem list is empty or duplicated")
    if {f"{namespace}.{name}" for name in declared} != set(expected):
        raise ValueError("Local theorem files and the required theorem inventory differ")
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
    llbc = extract.ROOT / result["llbc_file"]
    if hashlib.sha256(llbc.read_bytes()).hexdigest() != result["llbc_sha256"]:
        raise ValueError("LLBC changed during proof")


def check_proof_sources(paths):
    for path in paths:
        if re.search(r"\b(sorry|admit|axiom|opaque)\b", path.read_text()):
            raise ValueError(f"Unproved or opaque definition in {path}")


def prove(config, env, report, component_id):
    component = COMPONENTS[component_id]
    prefix = component.get("output_prefix", component["probe"])
    expected = obligations(component_id)
    check_lean_pins(config)
    if component_id == "scc_stack":
        check_checker_closure((extract.ROOT / "nibli-verify/spec/nibli_checker.nibli").read_text())
    probe = next(p for p in config["probe"] if p["name"] == component["probe"])
    print(f"Extracting {component['label']}", flush=True)
    result = extract.extract(probe, config, env, 300)
    report["extraction"] = result
    if result["status"] != "translated":
        raise ValueError(result["reason"])
    # Include local helpers, not just the public theorem file. The axiom audit
    # below also follows all transitive dependencies of the required theorems.
    check_proof_sources(
        sorted(DIRECTORY.glob("*.lean")) + [extract.ROOT / p for p in result["artifacts"]]
    )

    def command(name, argv, timeout=300):
        log = extract.OUTPUT / f"{prefix}-{name}.log"
        step = extract.run(argv, DIRECTORY, log, env, timeout)
        report[name] = step
        if step["status"] != "ok":
            raise ValueError(f"{name} failed; see {step['log']}")
        return log.read_text()

    version = command("lean-version", ["lake", "env", "lean", "--version"])
    required = config["lean_toolchain"].split(":v", 1)[1]
    if f"version {required}," not in version or config["target"] not in version:
        raise ValueError("Lean version/target does not match the pinned profile")
    print("Checking the extracted definitions and component theorems", flush=True)
    command("build", ["lake", "build", component["module"]], 1800)
    # Re-elaborate local helpers and the proof with warnings fatal even if Lake
    # has an up-to-date cache; an admitted theorem cannot count as a passing gate.
    for module in component.get("helpers", []):
        command(f"proof-{module}", ["lake", "env", "lean", "-DwarningAsError=true", f"{module}.lean"])
    command("proof", ["lake", "env", "lean", "-DwarningAsError=true", f"{component['module']}.lean"])
    audit = extract.OUTPUT / f"{component['module']}Audit.lean"
    audit.write_text(f"import {component['module']}\n" + "".join(f"#print axioms {name}\n" for name in expected))
    output = command("audit", ["lake", "env", "lean", "-DwarningAsError=true", str(audit)])
    report["axioms"] = audit_axioms(output, expected)
    report["audit_sha256"] = hashlib.sha256(audit.read_bytes()).hexdigest()
    check_artifacts(result)


def main(component_id):
    component = COMPONENTS[component_id]
    prefix = component.get("output_prefix", component["probe"])
    config = tomllib.loads(extract.CONFIG.read_text())
    try:
        env = extract.environment(config)
        with extract.exclusive_output():
            report_path = extract.OUTPUT / f"{prefix}-report.json"
            sources = extract.source_hashes()
            report = {
                "schema": 1, "component": component_id, "component_verified": False,
                "self_check_equivalence_verified": False,
                "notice": f"{component['label']} only; full-equivalence obligations remain unproved.",
                "sources": sources,
                "aeneas_revision": config["aeneas_revision"],
                "charon_revision": config["charon_revision"],
                "lean_toolchain": config["lean_toolchain"],
                "target": config["target"],
            }
            # Clear an old success before any command can fail or be interrupted.
            report_path.write_text(json.dumps(report, indent=2) + "\n")
            try:
                prove(config, env, report, component_id)
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
    print(f"Verified: {component['label']}. Full self-check equivalence is NOT proved.")
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--component", required=True, choices=sorted(COMPONENTS))
    sys.exit(main(parser.parse_args().component))
