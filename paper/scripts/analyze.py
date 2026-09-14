#!/usr/bin/env python3
"""Derive every quantitative table/plot from completed raw experiment records.

Timeouts are censored observations, never successful 30-second measurements.
CSV exports include the exact plot/table data and every measured sample.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import csv
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / "paper"
RESULTS = PAPER / "results/evaluation"
GENERATED = PAPER / "generated"


def write_csv(path, rows):
    if not rows:
        raise ValueError(f"empty derived data: {path}")
    fields = list(dict.fromkeys(k for row in rows for k in row))
    with path.open("w", newline="") as out:
        writer = csv.DictWriter(out, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def audit_trace(envelope, active):
    """Source-liveness/label check, explicitly NOT a semantic proof checker."""
    checked, errors = 0, []
    for index, step in enumerate(envelope["trace"]["steps"]):
        rule = step["rule"]
        kind = rule["type"]
        if kind not in ("asserted", "derived"):
            continue
        sources = rule.get("sources", [])
        if not sources:
            errors.append(f"step {index}: {kind} lacks source citations")
        for source in sources:
            key, label = ("id", "label") if kind == "asserted" else ("assertion_id", "assertion_label")
            checked += 1
            if source[key] not in active or active[source[key]] != source[label]:
                errors.append(f"step {index}: inactive or mislabeled citation {source[key]}")
    return checked, errors


def audit_raw(record):
    request = json.loads((RESULTS / "inputs" / record["case_id"] / "request.json").read_text())
    active, ids, checked, certificates, errors = {}, [], 0, 0, []
    incomplete_lines = 0
    for line in (ROOT / record["stdout"]).read_text().splitlines():
        if not line.startswith("{"):
            continue
        try:
            phase = json.loads(line)
        except json.JSONDecodeError:
            # An external cutoff can interrupt stdout mid-envelope. Preserve
            # that fact without treating unparseable bytes as a certificate.
            if record["status"] != "timeout":
                raise
            incomplete_lines += 1
            continue
        if phase.get("phase") == "load":
            ids = phase["ids"]
            active = dict(zip(ids, request["statements"], strict=True))
        elif phase.get("phase") == "withdrawal":
            update = request["updates"][phase["stage"] - 1]
            del active[ids[update["index"]]]
        elif phase.get("phase") == "reassertion":
            ids = phase["ids"]
            active[ids[-1]] = request["updates"][phase["stage"] - 1]["text"]
        elif "envelope" in phase:
            n, found = audit_trace(phase["envelope"], active)
            checked += n
            certificates += 1
            errors.extend(found)
    return {"run_id": record["run_id"], "certificates": certificates, "citations": checked,
            "incomplete_json_lines": incomplete_lines, "errors": errors}


def quantiles(values):
    return list(map(float, np.quantile(values, [.25, .5, .75], method="linear"))) if values else [None] * 3


def fmt(x):
    if x is None:
        return "--"
    if x == 0:
        return "0"
    if abs(x) < .01:
        return f"{x:.3g}"
    if abs(x) < 1:
        return f"{x:.3f}"
    return f"{x:.2f}" if x < 10 else f"{x:.1f}" if x < 1000 else f"{x:,.0f}"


def tex_escape(value):
    replacements = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#",
                    "_": r"\_", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}", "^": r"\textasciicircum{}"}
    return "".join(replacements.get(c, c) for c in str(value))


def cell(row, prefix="wall_ms"):
    if row[prefix + "_median"] is None:
        return r"\textit{no completion}"
    return fmt(row[prefix + "_median"]) + " [" + fmt(row[prefix + "_q25"]) + ", " + fmt(row[prefix + "_q75"]) + "]"


def latex_table(filename, columns, rows, header):
    text = [r"\begin{tabular}{" + columns + "}", r"\toprule", " & ".join(header) + r" \\", r"\midrule"]
    text += [" & ".join(map(str, row)) + r" \\" for row in rows]
    text += [r"\bottomrule", r"\end{tabular}"]
    (GENERATED / filename).write_text("\n".join(text) + "\n")


def figure_save(fig, name):
    fig.savefig(GENERATED / f"{name}.pdf", bbox_inches="tight", metadata={"CreationDate": None, "ModDate": None})
    fig.savefig(GENERATED / f"{name}.png", dpi=180, bbox_inches="tight")
    plt.close(fig)


def main():
    global RESULTS, GENERATED
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, default=RESULTS)
    parser.add_argument("--output", type=Path, default=GENERATED)
    args = parser.parse_args()
    RESULTS, GENERATED = args.results.resolve(), args.output.resolve()
    completed = json.loads((RESULTS / "completed.json").read_text())
    raw = RESULTS / "observations.jsonl"
    if hashlib.sha256(raw.read_bytes()).hexdigest() != completed["observations_sha256"]:
        raise RuntimeError("raw observations differ from completion manifest")
    all_records = [json.loads(line) for line in raw.read_text().splitlines()]
    schedule_path = RESULTS / "schedule.json"
    if schedule_path.exists():
        schedule = json.loads(schedule_path.read_text())
    else:
        with gzip.open(RESULTS / "schedule.json.gz", "rt", encoding="utf-8") as source:
            schedule = json.load(source)
    if len(all_records) != len(schedule) or len(all_records) != completed["runs"]:
        raise RuntimeError("incomplete or duplicated run ledger")
    for index, (record, item) in enumerate(zip(all_records, schedule, strict=True)):
        expected_id = f'{index:05d}-{item["case_id"]}-{item["implementation"]}-r{item["rep"]}'
        if record["run_id"] != expected_id or any(record[k] != item[k] for k in
                ("case_id", "group", "depth", "materialization", "mode", "rep", "warmup", "implementation")):
            raise RuntimeError(f"observation does not match scheduled execution: {index}")
    records = [r for r in all_records if not r["warmup"]]
    GENERATED.mkdir(parents=True, exist_ok=True)
    groups = defaultdict(list)
    keys = ["group", "family", "size", "direction", "depth", "materialization", "mode", "implementation"]
    samples, phases = [], []
    for r in records:
        groups[tuple(r[k] for k in keys)].append(r)
        samples.append({k: r.get(k) for k in ["run_id", *keys, "seed", "rep", "status", "wall_ms", "peak_rss_kib", "fact_count"]})
        for phase in r.get("phases", []):
            if "ms" in phase:
                phases.append({"run_id": r["run_id"], "group": r["group"], "size": r["size"], **phase})
    summary = []
    for key, rs in sorted(groups.items()):
        row = dict(zip(keys, key, strict=True))
        row.update(samples=len(rs), completed=sum(r["status"] == "ok" for r in rs),
                   timeouts=sum(r["status"] == "timeout" for r in rs), failures=sum(r["status"] not in ("ok", "timeout") for r in rs),
                   planned_answers=sum(sum(map(len, r["expected"])) for r in rs),
                   definitive_answers=sum(a["verdict"] in ("TRUE", "FALSE") for r in rs for a in r.get("answers", [])),
                   unknown_answers=sum(a["verdict"] == "UNKNOWN" for r in rs for a in r.get("answers", [])),
                   resource_answers=sum(a["verdict"] == "RESOURCE_EXCEEDED" for r in rs for a in r.get("answers", [])),
                   facts_min=min(r["fact_count"] for r in rs), facts_max=max(r["fact_count"] for r in rs))
        row["definitive_coverage"] = row["definitive_answers"] / row["planned_answers"]
        for metric in ("wall_ms", "peak_rss_kib"):
            values = [r[metric] for r in rs if r["status"] == "ok" and r.get(metric) is not None]
            for suffix, value in zip(("q25", "median", "q75"), quantiles(values)):
                row[f"{metric}_{suffix}"] = value
        for phase in ("load", "query", "certificate", "withdrawal", "reassertion", "reopen"):
            values = [sum(p["ms"] for p in r.get("phases", []) if p.get("phase") == phase) for r in rs
                      if r["status"] == "ok" and any(p.get("phase") == phase for p in r.get("phases", []))]
            for suffix, value in zip(("q25", "median", "q75"), quantiles(values)):
                row[f"{phase}_ms_{suffix}"] = value
        for metric in ("bytes", "steps", "validation_ms", "serialization_ms"):
            values = [sum(p.get(metric, 0) for p in r.get("phases", [])) for r in rs
                      if r["status"] == "ok" and any(metric in p for p in r.get("phases", []))]
            for suffix, value in zip(("q25", "median", "q75"), quantiles(values)):
                row[f"{metric}_{suffix}"] = value
        summary.append(row)
    write_csv(GENERATED / "samples.csv", samples)
    write_csv(GENERATED / "phases.csv", phases)
    write_csv(GENERATED / "summary.csv", summary)
    (GENERATED / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    audits = [audit_raw(r) for r in records if r["implementation"] == "nibli" and r["mode"] != "verdict" and "stdout" in r]
    (GENERATED / "citation-audit.json").write_text(json.dumps(audits, indent=2) + "\n")
    comparisons = defaultdict(dict)
    for r in records:
        if r["group"] == "bounds":
            for answer in r.get("answers", []):
                comparisons[(r["family"], r["direction"], r["seed"], r["depth"], r["rep"], answer["index"])][r["materialization"]] = answer["verdict"]
    definitive = {"TRUE", "FALSE"}
    comparable = gains = changes = regressions = 0
    for pair in comparisons.values():
        if False in pair and True in pair:
            if pair[False] in definitive and pair[True] in definitive:
                comparable += 1
                changes += pair[False] != pair[True]
            gains += pair[False] not in definitive and pair[True] in definitive
            regressions += pair[False] in definitive and pair[True] not in definitive
    counts = {"measured_runs": len(records), "warmup_runs": len(all_records) - len(records),
              "timeouts": sum(r["status"] == "timeout" for r in records),
              "failures": sum(r["status"] not in ("ok", "timeout") for r in records),
              "definitive_mismatches": sum(len(r.get("definitive_mismatches", [])) for r in records),
              "envelope_failures": sum(len(r.get("envelope_failures", [])) for r in records),
              "certificates": sum(a["certificates"] for a in audits), "citations": sum(a["citations"] for a in audits),
              "citation_errors": sum(len(a["errors"]) for a in audits),
              "bounds_comparable": comparable, "bounds_gains": gains, "bounds_changes": changes,
              "bounds_regressions": regressions}
    counts["verdicts"] = dict(Counter(a["verdict"] for r in records for a in r.get("answers", [])))
    counts["nibli_timeouts_before_load_completed"] = sum(
        r["implementation"] == "nibli" and r["status"] == "timeout" and
        not any(p.get("phase") == "load" for p in r.get("phases", [])) for r in records)
    counts["incomplete_certificate_json_lines"] = sum(a["incomplete_json_lines"] for a in audits)
    (GENERATED / "counts.json").write_text(json.dumps(counts, indent=2) + "\n")
    def choose(**kwargs):
        return [s for s in summary if all(s[k] == v for k, v in kwargs.items())]
    systems = {"nibli": "Nibli", "clingo": "clingo", "souffle": r"Souffl\'e"}
    table = []
    for s in choose(group="comparison", family="policy"):
        table.append([s["size"], systems[s["implementation"]], cell(s), fmt(s["peak_rss_kib_median"] / 1024) if s["peak_rss_kib_median"] else "--", f'{s["timeouts"]}/{s["samples"]}'])
    latex_table("policy-table.tex", "rlrrr", table, ["Target facts", "System", "Wall ms [Q1, Q3]", "RSS MiB", "Cutoffs"])
    table = []
    for size in (4, 8, 12, 16, 32):
        for direction in ("forward", "backward"):
            cells = []
            for implementation in systems:
                s, = choose(group="comparison", family="chain", size=size, direction=direction, implementation=implementation)
                cells.append(cell(s) + (r"$^{\dagger}$" if s["timeouts"] else ""))
            table.append([size, direction, *cells])
    latex_table("chain-table.tex", "rllrr", table, ["Edges", "Direction", "Nibli ms [Q1, Q3]", "clingo ms", r"Souffl\'e ms"])
    table = []
    for size in (100, 1000, 10000):
        v, = choose(group="evidence", size=size, mode="verdict")
        c, = choose(group="evidence", size=size, mode="certificate")
        cutoffs = f'{v["timeouts"]}/{v["samples"]}; {c["timeouts"]}/{c["samples"]}'
        table.append([size, cell(v, "query_ms"), cell(c, "certificate_ms"), fmt(c["bytes_median"]), cutoffs])
    latex_table("evidence-table.tex", "rllrr", table, ["Target facts", "Verdict ms [Q1,Q3]", "Certificate ms [Q1,Q3]", "JSON bytes", "Cutoffs V; C"])
    table = []
    for s in choose(group="updates"):
        table.append([s["size"], cell(s, "load_ms"), cell(s, "withdrawal_ms"), cell(s, "reopen_ms"), f'{s["completed"]}/{s["samples"]}'])
    latex_table("update-table.tex", "rlllr", table, ["Target facts", "Load ms [Q1,Q3]", "Withdrawals ms", "Reopens ms", "Completed"])
    table = []
    for group in ("comparison", "bounds", "evidence", "updates"):
        for implementation in systems:
            rs = [r for r in records if r["group"] == group and r["implementation"] == implementation]
            if not rs:
                continue
            vc = Counter(a["verdict"] for r in rs for a in r.get("answers", []))
            table.append([group, systems[implementation], len(rs), sum(r["status"] == "timeout" for r in rs),
                          sum(r["status"] not in ("ok", "timeout") for r in rs), vc["TRUE"] + vc["FALSE"], vc["UNKNOWN"], vc["RESOURCE_EXCEEDED"]])
    latex_table("outcomes-table.tex", "llrrrrrr", table, ["Group", "System", "Runs", "Cutoffs", "Failures", "Definite", "U", "R"])
    censored = defaultdict(list)
    for r in records:
        if r["status"] == "timeout":
            last = (r.get("phases") or [{}])[-1].get("phase", "none")
            censored[(r["group"], r["implementation"], r["family"], r["size"], last)].append(r)
    cutoff_rows, table = [], []
    for (group, implementation, family, size, last), rs in sorted(censored.items()):
        rss = quantiles([r["peak_rss_kib"] / 1024 for r in rs if r.get("peak_rss_kib") is not None])
        cutoff_rows.append({"group": group, "implementation": implementation, "family": family, "size": size, "last_completed_phase": last,
                            "cutoffs": len(rs), "rss_mib_q25": rss[0], "rss_mib_median": rss[1], "rss_mib_q75": rss[2]})
        table.append([group, systems[implementation], family, size, last, len(rs), fmt(rss[1])])
    if cutoff_rows:
        write_csv(GENERATED / "cutoffs.csv", cutoff_rows)
    latex_table("cutoff-table.tex", "lllrlrr", table, ["Group", "System", "Family", "Size", "Last phase", "Runs", "RSS MiB"])
    preparations = [json.loads(p.read_text()) for p in sorted((RESULTS / "compiled").glob("*/compilation.json"))]
    prep_rows = [{"source_hash": p.parent.name, **json.loads(p.read_text())} for p in sorted((RESULTS / "compiled").glob("*/compilation.json"))]
    write_csv(GENERATED / "compilation.csv", prep_rows)
    prep_q = quantiles([r["wall_ms"] for r in preparations if r["status"] == "ok"])
    largest = [r for r in records if r["family"] == "policy" and r["size"] == 10000 and r["implementation"] == "nibli"]
    large_cutoffs = sum(r["status"] == "timeout" for r in largest)
    large_loading = sum(r["status"] == "timeout" and not any(p.get("phase") == "load" for p in r.get("phases", [])) for r in largest)
    long_forward = [r for r in records if r["group"] == "comparison" and r["family"] == "chain" and r["size"] >= 12 and r["direction"] == "forward" and r["implementation"] == "nibli"]
    long_backward = [r for r in records if r["group"] == "comparison" and r["family"] == "chain" and r["size"] >= 12 and r["direction"] == "backward" and r["implementation"] == "nibli"]
    forward_cutoffs = sum(r["status"] == "timeout" for r in long_forward)
    backward_completed = sum(r["status"] == "ok" for r in long_backward)
    medium_verdict, = choose(group="evidence", size=1000, mode="verdict")
    medium_cert, = choose(group="evidence", size=1000, mode="certificate")
    findings = (r"The largest policy cases expose an ingestion limit in this workflow. Of " + str(len(largest)) +
                r" measured Nibli runs at the 10,000-fact target across the comparison and evidence groups, " + str(large_cutoffs) +
                r" reach the external cutoff; " + str(large_loading) +
                r" do so before loading completes. These runs provide no completed query or certificate timing. "
                r"The result concerns the recorded sequence of public API calls, including admission and state publication. "
                r"It does not isolate parser throughput or prove that every bulk-ingestion strategy has the same limit." + "\n\n" +
                r"The recursive asymmetry is also substantial: forward queries on chains of 12, 16, and 32 edges reach the cutoff in " +
                str(forward_cutoffs) + " of " + str(len(long_forward)) + r" measured runs, while " + str(backward_completed) + " of " +
                str(len(long_backward)) + r" reverse-query runs complete. Dataset size alone therefore gives a poor account of the cost: "
                r"the requested direction and evaluation path matter. A higher depth bound is not a time budget, "
                r"and an eligible finite relation does not imply that the engine will eagerly complete it before attempting a positive query." + "\n\n")
    if medium_verdict["query_ms_median"] is not None and medium_cert["certificate_ms_median"] is not None:
        ratio = medium_cert["certificate_ms_median"] / medium_verdict["query_ms_median"]
        findings += (r"At the 1,000-fact target, the ratio of median certificate time to median verdict-only query time is " + fmt(ratio) +
                     r". This is a ratio of two fresh-session medians, not a paired speedup estimate. "
                     r"The median separately measured JSON serialization time is " + fmt(medium_cert["serialization_ms_median"]) +
                     r"~ms. The distinction between evidence-producing reasoning and serialization is consequential: "
                     r"the former requests a trace through an execution path that retains backward derivation work. "
                     r"The comparison does not attribute every part of that difference to one internal optimization." + "\n")
    (GENERATED / "findings.tex").write_text("% Generated from measured observations; never hand-edit numbers.\n" + findings)
    plt.rcParams.update({"font.size": 12, "pdf.fonttype": 42, "axes.spines.top": False, "axes.spines.right": False})
    fig, axes = plt.subplots(1, 2, figsize=(9, 3.0), sharey=True)
    colors = {"nibli": "#202020", "clingo": "#0072B2", "souffle": "#D55E00"}
    for ax, direction in zip(axes, ("forward", "backward")):
        for impl in systems:
            rs = sorted(choose(group="comparison", family="chain", direction=direction, implementation=impl), key=lambda x: x["size"])
            valid = [r for r in rs if r["wall_ms_median"] is not None]
            ax.plot([r["size"] for r in valid], [r["wall_ms_median"] for r in valid], "o-", color=colors[impl], label={"nibli": "Nibli", "clingo": "clingo", "souffle": "Soufflé"}[impl])
            ax.fill_between([r["size"] for r in valid], [r["wall_ms_q25"] for r in valid], [r["wall_ms_q75"] for r in valid], color=colors[impl], alpha=.15)
            for r in rs:
                if r["timeouts"]:
                    ax.scatter(r["size"], 30000, marker="^", color=colors[impl], s=45)
        ax.axhline(30000, linestyle=":", color=".5", linewidth=.8)
        ax.set_title(direction.capitalize())
        ax.set_xlabel("Chain edges")
        ax.set_xticks([4, 8, 12, 16, 32])
        ax.set_yscale("log")
    axes[0].set_ylabel("Workload time (ms)")
    axes[1].legend(frameon=False, loc="lower right")
    fig.tight_layout()
    figure_save(fig, "reachability")
    fig, axes = plt.subplots(1, 3, figsize=(9, 2.6), sharey=True)
    for ax, (family, direction) in zip(axes, [("policy", "both"), ("chain", "forward"), ("chain", "backward")]):
        for mat, style in ((False, "s--"), (True, "o-")):
            rs = sorted(choose(group="bounds", family=family, direction=direction, materialization=mat), key=lambda x: x["depth"])
            ax.plot([r["depth"] for r in rs], [100 * r["definitive_coverage"] for r in rs], style, color=".15" if mat else ".55", label="On" if mat else "Off")
        ax.set_title("Policy, target 100" if family == "policy" else f"8 edges, {direction}")
        ax.set_xlabel("Depth bound")
        ax.set_xticks([2, 5, 10, 20])
        ax.set_ylim(-4, 104)
    axes[0].set_ylabel("Definitive coverage (%)")
    axes[-1].legend(frameon=False)
    fig.tight_layout()
    figure_save(fig, "bounds")
    environment = json.loads((RESULTS / "environment.json").read_text())
    cpu_model = re.search(r"^Model name:\s*(.+)$", environment["cpu"], re.M)[1]
    memory_kib = int(re.search(r"^MemTotal:\s*(\d+)", environment["memory"], re.M)[1])
    macros = {"MeasuredRuns": counts["measured_runs"], "WarmupRuns": counts["warmup_runs"], "TimeoutRuns": counts["timeouts"],
              "FailedRuns": counts["failures"], "DefinitiveMismatches": counts["definitive_mismatches"],
              "CertificateCount": counts["certificates"], "CitationCount": counts["citations"], "CitationErrors": counts["citation_errors"],
              "BoundsComparable": comparable, "BoundsGains": gains, "BoundsChanges": changes, "BoundsRegressions": regressions,
              "CompilationMedianMs": fmt(prep_q[1]), "CompilationQOneMs": fmt(prep_q[0]), "CompilationQThreeMs": fmt(prep_q[2]),
              "CompiledPrograms": len(preparations), "ArtifactRevision": environment["fingerprints"]["sha256"][:16],
              "EngineRevision": environment["git_head"][:12],
              "CpuModel": tex_escape(cpu_model), "VisibleCpus": len(environment["cpu_affinity"]),
              "VisibleMemoryGiB": f"{memory_kib / 1024**2:.1f}",
              "LoadingCutoffs": counts["nibli_timeouts_before_load_completed"]}
    macros["CertificateMedianRatio"] = fmt(medium_cert["certificate_ms_median"] / medium_verdict["query_ms_median"])
    port = PAPER / "results/portability/portability.json"
    if port.exists():
        pr = json.loads(port.read_text())
        protocol = json.loads((PAPER / "protocol.freeze.json").read_text())["protocol"]
        expected_port = {(case, seed, rep, runtime)
                         for case in ("policy", "chain-forward", "chain-backward", "support", "witness", "tense")
                         for seed in protocol["seeds"]
                         for rep in range(-protocol["warmups_per_seed_case"], protocol["measured_repetitions"])
                         for runtime in ("native", "wasmtime", "node")}
        observed_port = {(r["case"], r["seed"], r["rep"], r["runtime"]) for r in pr["records"]}
        if not pr["passed"] or observed_port != expected_port or len(pr["records"]) != len(expected_port):
            raise RuntimeError("portability matrix is incomplete, duplicated, or failed")
        measured_port = [r for r in pr["records"] if not r["warmup"]]
        macros["PortableComparisons"] = len(measured_port)
        macros["PortableAnswers"] = sum(len(r["answers"]) for r in measured_port)
        macros["PortableFailures"] = sum(not r["passed"] for r in measured_port)
    else:
        raise RuntimeError("required portability evidence is absent")
    (GENERATED / "numbers.tex").write_text("% Generated by scripts/analyze.py; never hand-edit.\n" + "\n".join("\\newcommand{\\" + name + "}{" + str(value) + "}" for name, value in macros.items()) + "\n")
    print(json.dumps(counts, indent=2))
    if counts["definitive_mismatches"] or counts["envelope_failures"] or counts["citation_errors"] or changes:
        raise RuntimeError("evidence disagreement: retain records; no clean-result claim is permitted")


if __name__ == "__main__":
    main()
