"""Engine-neutral finite programs and three independent surface renderers.

Variables begin with '$'; constants are opaque ASCII capitalized identifiers.
No translator parses another engine's generated text. No numeric/equality,
existential-head, modal, or trusted-compute operation is in this comparison.
"""
from __future__ import annotations

import copy
import json
import random
import re


def atom(name, *args, neg=False):
    return {"name": name, "args": list(args), "neg": neg}


def rule(head, *body):
    return {"head": head, "body": list(body)}


def validate(program):
    arities = {}
    for a in program["facts"] + program["queries"] + [
        a for r in program["rules"] for a in [r["head"], *r["body"]]
    ]:
        if not re.fullmatch(r"[a-z][a-z_]*", a["name"]):
            raise ValueError("unsupported predicate spelling")
        n = arities.setdefault(a["name"], len(a["args"]))
        if n != len(a["args"]):
            raise ValueError("inconsistent arity")
        for term in a["args"]:
            if not re.fullmatch(r"\$[a-z]+|[A-Z][A-Za-z0-9]*", term):
                raise ValueError("unsupported term")
    for a in program["facts"] + program["queries"]:
        if a["neg"] or any(x.startswith("$") for x in a["args"]):
            raise ValueError("facts and queries must be positive and ground")
    for r in program["rules"]:
        positive = {x for a in r["body"] if not a["neg"] for x in a["args"] if x.startswith("$")}
        used = {x for a in [r["head"], *r["body"]] for x in a["args"] if x.startswith("$")}
        if r["head"]["neg"] or not used <= positive:
            raise ValueError("unsafe or non-Horn rule")
    return arities


def kr_atom(a):
    return ("~" if a["neg"] else "") + a["name"] + "(" + ", ".join(a["args"]) + ")"


def nibli(program):
    validate(program)
    lines = []
    for r in program["rules"]:
        variables = sorted({x for a in [r["head"], *r["body"]] for x in a["args"] if x.startswith("$")})
        lines.append("all " + ", ".join(variables) + ": " + " & ".join(map(kr_atom, r["body"])) + " -> " + kr_atom(r["head"]) + ".")
    return lines + [kr_atom(a) + "." for a in program["facts"]]


def clingo(program):
    validate(program)

    def term(x):
        return x[1:].upper() if x.startswith("$") else json.dumps(x)

    def lit(a):
        return ("not " if a["neg"] else "") + a["name"] + "(" + ",".join(map(term, a["args"])) + ")"

    lines = [lit(a) + "." for a in program["facts"]]
    lines += [lit(r["head"]) + " :- " + ", ".join(map(lit, r["body"])) + "." for r in program["rules"]]
    lines += [f"answer({i}) :- {lit(a)}." for i, a in enumerate(program["queries"])]
    return "\n".join(lines + ["#show answer/1."]) + "\n"


def souffle(program):
    arities = validate(program)

    def term(x):
        return x[1:].upper() if x.startswith("$") else json.dumps(x)

    def lit(a):
        return ("!" if a["neg"] else "") + "p_" + a["name"] + "(" + ",".join(map(term, a["args"])) + ")"

    lines = [f".decl p_{name}(" + ",".join(f"a{i}:symbol" for i in range(n)) + ")" for name, n in sorted(arities.items())]
    # Facts stay external to the generated executable. Compilation therefore
    # cannot constant-fold the measured dataset into an answer.
    edb = sorted({a["name"] for a in program["facts"]})
    lines += [f".input p_{name}" for name in edb]
    lines += [lit(r["head"]) + " :- " + ", ".join(map(lit, r["body"])) + "." for r in program["rules"]]
    lines += [".decl answer(i:number)", ".output answer"]
    lines += [f"answer({i}) :- {lit(a)}." for i, a in enumerate(program["queries"])]
    facts = {name: "" for name in edb}
    for a in program["facts"]:
        facts[a["name"]] += "\t".join(a["args"]) + "\n"
    return "\n".join(lines) + "\n", {"p_" + name: rows for name, rows in facts.items()}


def chain(edges, direction, seed):
    labels = [f"N{i}" for i in range(edges + 1)]
    random.Random(seed).shuffle(labels)
    facts = [atom("earlier", a, b) for a, b in zip(labels, labels[1:])]
    random.Random(seed + 1).shuffle(facts)
    query = atom("earlier", labels[0], labels[-1]) if direction == "forward" else atom("earlier", labels[-1], labels[0])
    return {"family": "chain", "size": edges, "direction": direction, "seed": seed,
            "facts": facts, "rules": [rule(atom("earlier", "$a", "$c"), atom("earlier", "$a", "$b"), atom("earlier", "$b", "$c"))],
            "queries": [query], "expected": ["TRUE" if direction == "forward" else "FALSE"]}


def policy(target, seed):
    rng = random.Random(seed)
    flows = max(4, target * 4 // 11)
    facts = []
    for i in range(flows):
        f, s = f"F{i}", f"S{i}"
        facts.append(atom("carries", f, "Data", s, "Origin", "Route"))
        if i != 3:  # An unclassified sink is deliberately not cleared.
            facts.append(atom("dangerous", s, "Data", "Exploit"))
        sanitized, waived = rng.random() < .5, rng.random() < .25
        if i in (0, 1, 2, 3):
            sanitized, waived = {0: (True, True), 1: (False, False), 2: (False, True), 3: (False, False)}[i]
        if sanitized:
            facts.append(atom("prevents", "Sanitizer", f))
        if waived:
            facts.append(atom("permits", "Review", f, "Waiver"))
    rng.shuffle(facts)
    carried = atom("carries", "$f", "$d", "$s", "$o", "$r")
    dangerous = atom("dangerous", "$s", "$d", "Exploit")
    authorized = atom("authorized", "$f", "Release", "$s")
    rules = [
        rule(authorized, carried, dangerous, atom("prevents", "Sanitizer", "$f")),
        rule(authorized, carried, dangerous, atom("permits", "Review", "$f", "Waiver")),
        rule(atom("warns", "Gate", "$f", "$s"), carried, atom("authorized", "$f", "Release", "$s", neg=True)),
    ]
    return {"family": "policy", "size": target, "direction": "both", "seed": seed,
            "facts": facts, "rules": rules,
            "queries": [atom("warns", "Gate", "F0", "S0"), atom("warns", "Gate", "F1", "S1")],
            "expected": ["FALSE", "TRUE"]}


def updates(target, seed):
    p = policy(target, seed)
    sole = atom("prevents", "Sanitizer", "F1")
    p["facts"].append(sole)
    p["queries"] = [atom("authorized", "F0", "Release", "S0"), atom("warns", "Gate", "F0", "S0"),
                    atom("authorized", "F1", "Release", "S1"), atom("warns", "Gate", "F1", "S1")]
    nr = len(p["rules"])
    def ix(a):
        return nr + p["facts"].index(a)
    sanitizer = atom("prevents", "Sanitizer", "F0")
    p["updates"] = [{"op": "retract", "index": ix(sanitizer)},
                    {"op": "retract", "index": ix(atom("permits", "Review", "F0", "Waiver"))},
                    {"op": "assert", "text": kr_atom(sanitizer) + "."},
                    {"op": "reopen"}, {"op": "retract", "index": ix(sole)},
                    {"op": "assert", "text": kr_atom(sole) + "."}, {"op": "reopen"}]
    tf = ["TRUE", "FALSE", "TRUE", "FALSE"]
    p["stage_expected"] = [tf, tf, ["FALSE", "TRUE", "TRUE", "FALSE"], tf, tf,
                           ["TRUE", "FALSE", "FALSE", "TRUE"], tf, tf]
    p["expected"] = tf
    return p


def request(program, depth=10, materialization=True, mode="verdict"):
    return {"statements": nibli(program), "queries": [kr_atom(a) + "." for a in program["queries"]],
            "depth": depth, "materialization": materialization, "mode": mode,
            "updates": copy.deepcopy(program.get("updates", []))}


def experiments(protocol):
    for seed in protocol["seeds"]:
        for size in protocol["policy_sizes"]:
            yield "comparison", policy(size, seed), 10, True, "verdict", ["nibli", "clingo", "souffle"]
        for size in protocol["chain_edges"]:
            for direction in ("forward", "backward"):
                yield "comparison", chain(size, direction, seed), 10, True, "verdict", ["nibli", "clingo", "souffle"]
        for depth in protocol["depths"]:
            for mat in (False, True):
                for program in [policy(100, seed), chain(8, "forward", seed), chain(8, "backward", seed)]:
                    yield "bounds", program, depth, mat, "verdict", ["nibli"]
        for size in protocol["policy_sizes"]:
            for mode in ("verdict", "certificate"):
                yield "evidence", policy(size, seed), 10, True, mode, ["nibli"]
        for size in protocol["update_sizes"]:
            yield "updates", updates(size, seed), 10, True, "updates", ["nibli"]
