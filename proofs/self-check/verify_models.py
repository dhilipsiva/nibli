#!/usr/bin/env python3
"""Audit candidate primitive-library model contracts, without native certification.

The models are not installed into extraction by this command. Successful checks
prove their stated mathematical contracts; they do not verify Rust std internals
or discharge the named stratifier's external-definition boundary.
"""

import hashlib
import json
from pathlib import Path
import sys
import tomllib

import extract
from verify_component import audit_axioms, check_lean_pins, check_proof_sources, check_theorem_inventory


DIRECTORY = Path(__file__).resolve().parent
MODULE = "StdStrings"


def obligations():
    coverage = tomllib.loads((DIRECTORY / "coverage.toml").read_text())
    obligation = next(o for o in coverage["obligation"] if o["id"] == "primitive_strings")
    return check_theorem_inventory(
        obligation, [DIRECTORY / f"{MODULE}.lean"], "NibliSelfCheck.StdStrings",
    )


def initial_report(config, sources):
    return {
        "schema": 1, "model": "primitive_strings", "model_contracts_verified": False,
        "native_implementation_verified": False, "extraction_replacements_installed": False,
        "self_check_equivalence_verified": False,
        "notice": "Candidate string model contracts only; Rust std implementation and extraction bindings remain unverified.",
        "sources": sources, "lean_toolchain": config["lean_toolchain"], "target": config["target"],
        "aeneas_revision": config["aeneas_revision"],
    }


def prove(config, env, report):
    expected = obligations()
    check_lean_pins(config)
    check_proof_sources([DIRECTORY / f"{MODULE}.lean"])

    def command(name, argv, timeout=300):
        log = extract.OUTPUT / f"library-strings-{name}.log"
        result = extract.run(argv, DIRECTORY, log, env, timeout)
        report[name] = result
        if result["status"] != "ok":
            raise ValueError(f"{name} failed; see {result['log']}")
        return log.read_text()

    version = command("lean-version", ["lake", "env", "lean", "--version"])
    required = config["lean_toolchain"].split(":v", 1)[1]
    if f"version {required}," not in version or config["target"] not in version:
        raise ValueError("Lean version/target does not match the pinned profile")
    command("build", ["lake", "build", MODULE], 1800)
    command("proof", ["lake", "env", "lean", "-DwarningAsError=true", f"{MODULE}.lean"])
    audit = extract.OUTPUT / "LibraryStringsAudit.lean"
    audit.write_text(f"import {MODULE}\n" + "".join(f"#print axioms {name}\n" for name in expected))
    output = command("audit", ["lake", "env", "lean", "-DwarningAsError=true", str(audit)])
    report["axioms"] = audit_axioms(output, expected)
    report["audit_sha256"] = hashlib.sha256(audit.read_bytes()).hexdigest()


def main():
    config = tomllib.loads(extract.CONFIG.read_text())
    try:
        env = extract.environment(config)
        with extract.exclusive_output():
            sources = extract.source_hashes()
            report = initial_report(config, sources)
            path = extract.OUTPUT / "library-strings-report.json"
            path.write_text(json.dumps(report, indent=2) + "\n")
            try:
                prove(config, env, report)
                if extract.source_hashes() != sources:
                    raise ValueError("Source changed during model proof; discard this run and rerun")
                report["model_contracts_verified"] = True
            except (ValueError, RuntimeError, OSError, KeyError, StopIteration) as error:
                report["error"] = str(error)
            path.write_text(json.dumps(report, indent=2) + "\n")
            if not report["model_contracts_verified"]:
                print(report["error"], file=sys.stderr)
                return 1
    except (RuntimeError, OSError, ValueError) as error:
        print(error, file=sys.stderr)
        return 2
    print("Verified: candidate string model contracts. Native std, extraction bindings, and full self-check equivalence are NOT proved.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
