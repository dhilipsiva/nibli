#!/usr/bin/env python3
"""Create deterministic source/data archives and rebuild the extracted TeX input.

Run through `just paper-package` inside the paper Nix shell. No upload occurs.
"""
from __future__ import annotations

import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile

from run import fingerprints

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / "paper"
DIST = PAPER / "dist"
EPOCH = 1789344000


def digest(data):
    return hashlib.sha256(data).hexdigest()


def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def read_json(path):
    return json.loads(path.read_text())


def submission_metadata(main_pages):
    numbers = (PAPER / "generated/numbers.tex").read_text()
    macros = dict(re.findall(r"\\newcommand\{\\(\w+)\}\{([^{}]*)\}", numbers))
    macros.update({"True": "TRUE", "False": "FALSE", "Unknown": "UNKNOWN", "Resource": "RESOURCE_EXCEEDED", "Souffle": r"Souffl\'e"})
    abstract = (PAPER / "sections/abstract.tex").read_text()
    def expand(match):
        name = match[1]
        if name not in macros:
            raise RuntimeError(f"abstract metadata cannot expand macro: {name}")
        return macros[name]
    abstract = re.sub(r"\\([A-Za-z]+)(?:\\(?=\s)|\{\})?", expand, abstract)
    abstract = " ".join(abstract.replace("~", " ").split())
    # https://info.arxiv.org/help/prep.html (checked 2026-09-14).
    if not abstract.isascii() or len(abstract) > 1920:
        raise RuntimeError("arXiv abstract must use ASCII and at most 1920 characters")
    return {"title": "Nibli: Auditable Symbolic Reasoning with Bounded Evaluation and Retractable Premises",
            "authors": [{"name": "dhilipsiva", "affiliations": []}], "primary_category": "cs.AI",
            "abstract": abstract, "comments": f"{main_pages} pages of main text, plus references and appendices; reproducible research artifact supplied separately.",
            "submission_status": "not submitted", "license": "not selected; author selects at submission"}


def validate_claims():
    register = read_json(PAPER / "research/claims.json")
    bibliography = (PAPER / "references.bib").read_text()
    keys = set(re.findall(r"@\w+\{([^,]+),", bibliography))
    sources = read_json(PAPER / "research/sources.json")
    verified = {s["bibkey"] for s in sources["sources"]}
    if keys != verified:
        raise RuntimeError(f"bibliography/source register differ: {keys ^ verified}")
    identifiers = set()
    for claim in register["claims"]:
        if claim["id"] in identifiers or not claim["boundary"] or not claim["evidence"]:
            raise RuntimeError(f"incomplete or duplicate claim: {claim['id']}")
        identifiers.add(claim["id"])
        for evidence in claim["evidence"]:
            if evidence["kind"] not in register["evidence_classes"]:
                raise RuntimeError(f"unknown evidence kind: {evidence}")
            if "path" in evidence:
                path = ROOT / evidence["path"]
                if not path.is_file():
                    raise RuntimeError(f"missing claim evidence: {path}")
                if "symbol" in evidence and evidence["symbol"] not in path.read_text():
                    raise RuntimeError(f"missing claim symbol: {evidence}")
            if not set(evidence.get("bibkeys", [])) <= verified:
                raise RuntimeError(f"unverified claim reference: {evidence}")
    return {"claims": len(identifiers), "verified_references": len(verified)}


def archive(path, files, include_manifest=True):
    """files maps safe POSIX member names to paths or in-memory bytes."""
    manifest = {}
    with path.open("wb") as raw:
        with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=EPOCH, compresslevel=6) as compressed:
            with tarfile.open(fileobj=compressed, mode="w|", format=tarfile.PAX_FORMAT) as tar:
                for name, source in sorted(files.items()):
                    if Path(name).is_absolute() or ".." in Path(name).parts:
                        raise RuntimeError(f"unsafe archive member: {name}")
                    data = source if isinstance(source, bytes) else source.read_bytes()
                    info = tarfile.TarInfo(name)
                    info.size, info.mtime, info.mode = len(data), EPOCH, 0o644
                    info.uid = info.gid = 0
                    tar.addfile(info, io.BytesIO(data))
                    manifest[name] = {"sha256": digest(data), "bytes": len(data)}
                if include_manifest:
                    data = json_bytes(manifest)
                    info = tarfile.TarInfo("ARTIFACT-MANIFEST.json")
                    info.size, info.mtime, info.mode = len(data), EPOCH, 0o644
                    tar.addfile(info, io.BytesIO(data))
    return manifest


def verify_research_archive(path, expected):
    """Read the compressed output back and check every payload against its manifest."""
    observed = {}
    embedded = None
    with tarfile.open(path, mode="r|gz") as tar:
        for member in tar:
            if not member.isfile() or member.name in observed:
                raise RuntimeError(f"unexpected research archive member: {member.name}")
            data = tar.extractfile(member).read()
            if member.name == "ARTIFACT-MANIFEST.json":
                if embedded is not None:
                    raise RuntimeError("duplicate research manifest")
                embedded = json.loads(data)
            else:
                observed[member.name] = {"sha256": digest(data), "bytes": len(data)}
    if observed != expected or embedded != expected:
        raise RuntimeError("research archive payload or manifest differs")


def source_files():
    files = {"main.tex": PAPER / "main.tex", "references.bib": PAPER / "references.bib",
             "main.bbl": PAPER / "build/main.bbl"}
    for directory in ("sections", "figures"):
        for path in sorted((PAPER / directory).rglob("*.tex")):
            files[str(path.relative_to(PAPER))] = path
    for path in sorted((PAPER / "generated").glob("*.tex")):
        files[str(path.relative_to(PAPER))] = path
    for name in ("reachability.pdf", "bounds.pdf"):
        files["generated/" + name] = PAPER / "generated" / name
    # Only typesetting inputs belong in the arXiv archive. No unused PNG/CSV,
    # build logs, main PDF, metadata forms, or self-generated manifest.
    return files


def verify_source_archive(path, expected_pdf):
    directory = Path(tempfile.mkdtemp(prefix="arxiv-", dir=PAPER / "build"))
    with tarfile.open(path) as tar:
        tar.extractall(directory, filter="data")
    env = os.environ.copy()
    env.update(SOURCE_DATE_EPOCH=str(EPOCH), FORCE_SOURCE_DATE="1", TZ="UTC")
    # The supplied .bbl is sufficient; do not invoke BibTeX or the analysis
    # scripts. This independently checks that the upload has every TeX input.
    for _ in range(3):
        result = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
                                cwd=directory, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (directory / "package-build.log").write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f"extracted source build failed: {directory}")
    if (directory / "main.pdf").read_bytes() != expected_pdf:
        raise RuntimeError(f"extracted source PDF differs: {directory}")
    log = (directory / "main.log").read_text()
    if re.search(r"undefined references|Citation .* undefined|Reference .* undefined|Overfull \\[hv]box", log):
        raise RuntimeError(f"extracted source layout/reference errors: {directory}")


def research_files():
    # Overlay onto the baseline checkout. Retain final redb snapshots and all
    # raw transcripts; compiled executables are rebuildable and hash-recorded.
    files = {}
    for name in ("Cargo.lock", "flake.nix", "flake.lock", "Justfile", "nibli/Cargo.toml", "nibli/src/bin/bench_paper.rs"):
        files[name] = ROOT / name
    for name in ("README.md", "main.tex", "references.bib", "protocol.json", "protocol.freeze.json", "nibli-paper.pdf", ".gitignore"):
        files["paper/" + name] = PAPER / name
    for name in ("sections", "figures", "scripts", "tests", "research", "generated"):
        for path in sorted((PAPER / name).rglob("*")):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc":
                files[str(path.relative_to(ROOT))] = path
    for name in ("checks", "pilot", "portability", "evaluation"):
        for path in sorted((PAPER / "results" / name).rglob("*")):
            if path.is_file() and not ("compiled" in path.parts and path.name == "program"):
                files[str(path.relative_to(ROOT))] = path
    for directory in sorted((PAPER / "results").iterdir()):
        if not directory.is_dir() or not directory.name.startswith(("pilot-", "checks-")):
            continue
        for path in directory.rglob("*"):
            if path.is_file() and (path.parent == directory or "raw" in path.parts):
                if path.suffix in (".json", ".stdout", ".stderr", ".time"):
                    files[str(path.relative_to(ROOT))] = path
    for name in ("main.bbl", "main.log", "build-report.json", "package-validation.json", "paper.txt"):
        files["paper/build/" + name] = PAPER / "build" / name
    for name in ("submission-metadata.json", "arxiv-manifest.json"):
        files["paper/dist/" + name] = DIST / name
    files["ENGINE-BASELINE.txt"] = b"158e3b0cdeeb09d26ae9e87dd3d5487ab945c2ca\nhttps://github.com/dhilipsiva/nibli\n"
    files["REPRODUCE.md"] = b"""# Reproduce the Nibli paper

This archive is an overlay, not a standalone engine checkout.

1. Clone https://github.com/dhilipsiva/nibli into a new directory.
2. Check out 158e3b0cdeeb09d26ae9e87dd3d5487ab945c2ca.
3. Extract this archive at that checkout root, allowing its named overlay files.
4. Enter `nix develop --extra-experimental-features nix-command
   --extra-experimental-features flakes .#paper`.
5. Read paper/README.md. `just paper-build` regenerates the archived paper;
   the README gives separate output paths for new checks and measurements.

ARTIFACT-MANIFEST.json gives SHA-256 and size for every included file. The
measurement freeze gives source and executable identities for the experiment.
Do not overwrite archived observations or relabel a rebuilt binary as the
original measurement without checking its identity. This package has not been
submitted to arXiv. No private manuscript files are included.
"""
    return files


def main():
    frozen = read_json(PAPER / "protocol.freeze.json")
    if fingerprints() != frozen["fingerprints"]:
        raise RuntimeError("frozen experiment source changed")
    for relative in ("results/checks/checks.json", "results/pilot/smoke.json", "results/portability/portability.json"):
        if not read_json(PAPER / relative)["passed"]:
            raise RuntimeError(f"required evidence failed: {relative}")
    checks = read_json(PAPER / "results/checks/checks.json")
    if checks["fingerprints"] != frozen["fingerprints"]:
        raise RuntimeError("required checks are for different sources")
    completion = read_json(PAPER / "results/evaluation/completed.json")
    if completion["fingerprints"] != frozen["fingerprints"]:
        raise RuntimeError("collection ended on different sources")
    counts = read_json(PAPER / "generated/counts.json")
    if any(counts[k] for k in ("definitive_mismatches", "envelope_failures", "citation_errors", "bounds_changes")):
        raise RuntimeError("unresolved evidence disagreement")
    report = read_json(PAPER / "build/build-report.json")
    pdf = (PAPER / "nibli-paper.pdf").read_bytes()
    if not report["two_clean_builds_identical"] or report["pdf_sha256"] != digest(pdf):
        raise RuntimeError("paper PDF differs from validated build")
    claim_report = validate_claims()
    DIST.mkdir(exist_ok=True)
    source_path = DIST / "nibli-arxiv-source.tar.gz"
    source_manifest = archive(source_path, source_files(), include_manifest=False)
    verify_source_archive(source_path, pdf)
    (DIST / "arxiv-manifest.json").write_bytes(json_bytes(source_manifest))
    metadata = submission_metadata(report["main_text_pages"])
    (DIST / "submission-metadata.json").write_bytes(json_bytes(metadata))
    validation = {"extracted_upload_pdf_identical": True, "pdf_sha256": digest(pdf),
                  "frozen_sources_match": True, "required_checks_passed": True,
                  "main_text_pages": report["main_text_pages"],
                  "abstract_ascii": metadata["abstract"].isascii(),
                  "abstract_characters": len(metadata["abstract"]), **claim_report}
    (PAPER / "build/package-validation.json").write_bytes(json_bytes(validation))
    artifact_path = DIST / "nibli-research-artifact.tar.gz"
    artifact_manifest = archive(artifact_path, research_files())
    verify_research_archive(artifact_path, artifact_manifest)
    summary = {"source_archive": {"file": source_path.name, "sha256": digest(source_path.read_bytes()), "bytes": source_path.stat().st_size, "members": len(source_manifest)},
               "research_archive": {"file": artifact_path.name, "sha256": digest(artifact_path.read_bytes()), "bytes": artifact_path.stat().st_size, "members": len(artifact_manifest)},
               "research_archive_manifest_verified": True, "validation": validation}
    (DIST / "package-report.json").write_bytes(json_bytes(summary))
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
