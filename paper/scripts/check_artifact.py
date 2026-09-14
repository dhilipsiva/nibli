#!/usr/bin/env python3
"""Validate research sources and retain the small analysis-test transcript.

Reuse a passing report only while its exact source inputs remain unchanged.
This does not rerun the native or WebAssembly suites, or alter observations.
"""
import ast
from pathlib import Path
import sys

from package import validate_claims
from run import PAPER, ROOT, digest, dump, measured


def main():
    sources = sorted([*PAPER.glob("scripts/*.py"), *PAPER.glob("tests/*.py"),
                      PAPER / "research/claims.json", PAPER / "research/sources.json",
                      PAPER / "protocol.freeze.json"])
    hashes = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    for path in sources:
        if path.suffix == ".py":
            ast.parse(path.read_text(), filename=str(path))
    claims = validate_claims()
    directory = PAPER / "results/checks-analysis"
    report_path = directory / "checks.json"
    if report_path.exists():
        import json
        previous = json.loads(report_path.read_text())
        if previous["passed"] and previous["inputs"] == hashes:
            print("Analysis tests: unchanged passing evidence; claim links valid.")
            return
    result = measured([sys.executable, "-m", "unittest", "discover", "-s", "paper/tests", "-v"],
                      directory / "check-0", 60)
    dump(report_path, {"passed": result["status"] == "ok", "inputs": hashes,
                       "claim_register": claims, "test_run": result})
    if result["status"] != "ok":
        raise RuntimeError(f"analysis tests failed: {directory}")
    print("Analysis tests and claim links passed; transcript retained.")


if __name__ == "__main__":
    main()
