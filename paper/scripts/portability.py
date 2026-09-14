#!/usr/bin/env python3
"""Behavior, not timing, across native, the WASI component, and Node/V8.

Adequate-budget comparisons are separate from the fuel-trap/recovery smoke in
paper-check. Database reopening is tested on native and Wasmtime only.
"""
import json
import random
from pathlib import Path
import re
import sys

import workloads as w
from run import ROOT, PAPER, BIN, PROTOCOL, dump, digest, measured


def normalize(value):
    if isinstance(value, str):
        return value.upper()
    name = next(iter(value))
    return {"ResourceExceeded": "RESOURCE_EXCEEDED", "Unknown": "UNKNOWN"}[name]


def main():
    output = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else PAPER / "results/portability"
    if output.exists():
        raise RuntimeError("portability output already exists")
    output.mkdir(parents=True)
    artifacts = [BIN, ROOT / "target/release/nibli-host", ROOT / "target/wasm32-wasip2/release/nibli.wasm",
                 PAPER / "build/node/nibli_wasm.js", PAPER / "build/node/nibli_wasm_bg.wasm"]
    for path in artifacts:
        if not path.is_file():
            raise RuntimeError(f"required artifact absent: {path}")
    dump(output / "artifacts.json", {str(p.relative_to(ROOT)): digest(p) for p in artifacts + [Path(__file__), PAPER / "scripts/portability.cjs"]})
    records = []
    rng = random.Random(PROTOCOL["order_seed"])
    for seed in PROTOCOL["seeds"]:
        policy = w.policy(100, seed)
        cases = [("policy", w.request(policy, mode="certificate"), [policy["expected"]]),
                 ("chain-forward", w.request(w.chain(4, "forward", seed), mode="certificate"), [["TRUE"]]),
                 ("chain-backward", w.request(w.chain(4, "backward", seed), mode="certificate"), [["FALSE"]])]
        name = f"N{seed}"
        cases += [("support", {"statements": ["all $x: dog($x) -> animal($x).", "all $x: cat($x) -> animal($x).", f"dog({name}).", f"cat({name})."],
                              "queries": [f"animal({name})."], "depth": 10, "materialization": True, "mode": "updates",
                              "updates": [{"op": "retract", "index": 2}, {"op": "retract", "index": 3}, {"op": "assert", "text": f"dog({name})."}]},
                   [["TRUE"], ["TRUE"], ["FALSE"], ["TRUE"]]),
                  ("witness", {"statements": [f"bite(some dog, {name})."], "queries": [f"bite(some dog, {name}).", 'dog("sk_0").'],
                              "depth": 10, "materialization": True, "mode": "certificate", "updates": []}, [["TRUE", "FALSE"]]),
                  ("tense", {"statements": [f"past dog({name})."], "queries": [f"past dog({name}).", f"dog({name})."],
                            "depth": 10, "materialization": True, "mode": "certificate", "updates": []}, [["TRUE", "FALSE"]])]
        for label, request, expected in cases:
            case = output / f"{label}-s{seed}"
            case.mkdir()
            dump(case / "request.json", request)
            dump(case / "expected.json", expected)
            script = [":fuel 50000000000", f':depth {request["depth"]}', *request["statements"]]
            script += [":certify " + q for q in request["queries"]]
            for op in request["updates"]:
                script.append(f':retract {op["index"]}' if op["op"] == "retract" else op["text"])
                script += [":certify " + q for q in request["queries"]]
            script += [":quit"]
            (case / "input.nibli").write_text("\n".join(script) + "\n")
            # Stable IDs follow accepted singleton assertions (0..n-1); the
            # native and JS paths also check the IDs returned by their APIs.
            commands = {
                "native": [BIN, case / "request.json"] + ([case / "state.redb"] if request["updates"] else []),
                "wasmtime": [ROOT / "target/release/nibli-host"],
                "node": ["node", PAPER / "scripts/portability.cjs", PAPER / "build/node/nibli_wasm.js", case / "request.json"],
            }
            flat = [x for stage in expected for x in stage]
            for rep in range(-1, PROTOCOL["measured_repetitions"]):
                order = list(commands)
                rng.shuffle(order)
                for runtime in order:
                    command = commands[runtime].copy()
                    if runtime == "native" and request["updates"]:
                        command[-1] = case / f"state-r{rep}.redb"
                    env = {"NIBLI_WASM_PATH": str(artifacts[2]), "NIBLI_FUEL": "50000000000", "NIBLI_MEMORY_MB": "512", "NIBLI_MATERIALIZE": "1", "NIBLI_STRICT": "0", "NIBLI_EXISTENTIAL_IMPORT": "0"}
                    result = measured(command, case / f"{runtime}-r{rep}", 30, env=env, stdin="\n".join(script) + "\n" if runtime == "wasmtime" else None)
                    envelopes = []
                    for line in (ROOT / result["stdout"]).read_text().splitlines():
                        if not line.startswith("{"):
                            continue
                        obj = json.loads(line)
                        if "envelope" in obj:
                            envelopes.append(obj["envelope"])
                        elif "schema" in obj:
                            envelopes.append(obj)
                    actual = [normalize(e["result"]) for e in envelopes]
                    result.update(runtime=runtime, case=label, seed=seed, rep=rep, warmup=rep < 0, answers=actual, expected=flat,
                                  profiles_match=all(e["profile"]["max_chain_depth"] == 10 and e["profile"]["materialization"] is True for e in envelopes),
                                  passed=result["status"] == "ok" and actual == flat and all(e["schema"] == 2 for e in envelopes))
                    records.append(result)
                    print(label, seed, runtime, rep, result["passed"], actual, flush=True)
                    dump(output / "portability.json", {"passed": all(r["passed"] and r["profiles_match"] for r in records), "records": records})
    if not all(r["passed"] and r["profiles_match"] for r in records):
        raise RuntimeError("portability mismatch; retain all transcripts")


if __name__ == "__main__":
    main()
