#!/usr/bin/env python3
"""Build twice in clean directories, verify references and identical PDF bytes."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

PAPER = Path(__file__).resolve().parents[1]


def compile_once(parent):
    directory = Path(tempfile.mkdtemp(prefix="tex-", dir=parent))
    for name in ("main.tex", "references.bib"):
        shutil.copy2(PAPER / name, directory / name)
    for name in ("sections", "figures", "generated"):
        shutil.copytree(PAPER / name, directory / name)
    env = os.environ.copy()
    env.update(SOURCE_DATE_EPOCH="1789344000", FORCE_SOURCE_DATE="1", TZ="UTC")
    result = subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
                             "-file-line-error", "-outdir=.", "main.tex"], cwd=directory, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (directory / "build.log").write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"TeX failed; inspect {directory / 'build.log'}")
    log = (directory / "main.log").read_text()
    if re.search(r"undefined references|Citation .* undefined|Reference .* undefined|Label\(s\) may have changed", log):
        raise RuntimeError(f"unresolved references: {directory}")
    # Document layout problems are visible failures, not hidden build warnings.
    overflow = re.findall(r"Overfull \\[hv]box .*", log)
    if overflow:
        raise RuntimeError(f"overfull boxes in {directory}: {overflow}")
    return directory


def main():
    build = PAPER / "build"
    build.mkdir(exist_ok=True)
    first, second = compile_once(build), compile_once(build)
    pdf = (first / "main.pdf").read_bytes()
    if pdf != (second / "main.pdf").read_bytes():
        raise RuntimeError("PDF bytes differ between clean builds")
    aux = (first / "main.aux").read_text()
    match = re.search(r"\\newlabel\{main-end\}\{\{[^}]*\}\{(\d+)\}", aux)
    if not match:
        raise RuntimeError("main-text end marker missing")
    pages = int(match[1])
    if not 12 <= pages <= 15:
        raise RuntimeError(f"main text has {pages} pages; expected 12--15")
    (PAPER / "nibli-paper.pdf").write_bytes(pdf)
    shutil.copy2(first / "main.bbl", build / "main.bbl")
    shutil.copy2(first / "main.log", build / "main.log")
    subprocess.run(["pdftotext", "-layout", str(PAPER / "nibli-paper.pdf"), str(build / "paper.txt")], check=True)
    text_pages = (build / "paper.txt").read_text().split("\f")
    acknowledgments = [i + 1 for i, page in enumerate(text_pages) if "Acknowledgment of AI assistance" in " ".join(page.split())]
    if acknowledgments != [pages + 1]:
        raise RuntimeError("main-text marker disagrees with the first supporting-material page")
    info = subprocess.check_output(["pdfinfo", str(PAPER / "nibli-paper.pdf")], text=True)
    fonts = subprocess.check_output(["pdffonts", str(PAPER / "nibli-paper.pdf")], text=True)
    report = {"main_text_pages": pages, "pdf_sha256": hashlib.sha256(pdf).hexdigest(),
              "two_clean_builds_identical": True, "undefined_references": False,
              "overfull_boxes": False, "pdfinfo": info, "pdffonts": fonts,
              "supporting_material_starts_on": acknowledgments[0]}
    (build / "build-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    # Retain the successful build directories for diagnostics. They are ignored
    # and never included in either distribution archive.


if __name__ == "__main__":
    main()
