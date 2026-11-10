"""Structural LLBC -> finite Nibli facts. No Rust execution or contract decisions.

The pinned typed reader resolves Charon's sharing codec first. This normalizer
substitutes local bindings and inlines acyclic calls, retaining EVERY branch as
a guarded path. Only Nibli evaluates those guards and expressions. Unsupported
operations terminate a path at an explicit barrier, never at a fabricated return.
The normalizer and Charon remain part of the disclosed trusted computing base.
"""

from dataclasses import dataclass, replace
import itertools
import json

ROOTS = {
    "and": "nibli_reason::reasoning::combine_conjunction",
    "or": "nibli_reason::reasoning::combine_disjunction",
    "not": "nibli_reason::reasoning::negate_result",
}
TYPES = {name: f"nibli_types::logic::{name}" for name in
         ("QueryResult", "UnknownReason", "ResourceKind")}
MAX_PATHS = 4096
MAX_EXPRESSIONS = 20000


class Unsupported(ValueError):
    pass


def plain(value):
    if isinstance(value, dict):
        if set(value) == {"Untagged"}:
            return plain(value["Untagged"])
        if set(value) in ({"Deduplicated"}, {"Value"}) and not isinstance(value.get("Value"), dict):
            raise ValueError("expected non-deduplicated output from the typed LLBC reader")
        return {key: plain(item) for key, item in value.items()}
    if isinstance(value, list):
        return [plain(item) for item in value]
    return value


def name(declaration):
    parts = declaration["item_meta"]["name"]
    # Roots/types have plain paths. Impl segments on helper functions are kept
    # in the source metadata; helpers are resolved by declaration id, not names.
    return "::".join(p["Ident"][0] for p in parts if "Ident" in p)


@dataclass
class State:
    env: dict
    guards: tuple = ()
    outcome: str = "running"
    value: object = None
    location: object = None


class Exporter:
    def __init__(self, raw):
        if raw["charon_version"] != "0.1.293" or raw["has_errors"]:
            raise ValueError("wrong Charon version or incomplete extraction")
        self.crate = plain(raw["translated"])
        self.functions = self.index(self.crate["fun_decls"])
        self.types = self.index(self.crate["type_decls"])
        self.type_names = {i: name(t) for i, t in self.types.items()}
        self.facts = set()
        self.expressions = {}
        self.guards = {}
        self.locations = {}
        self.cases = []
        self.paths = []
        self.root = None
        self.domains = {}
        self.values = {"bool:true", "bool:false"}
        self.serial = 0

    @staticmethod
    def index(items):
        result = {}
        for item in items:
            if item is not None:
                key = item["def_id"]
                if key in result:
                    raise ValueError("duplicate declaration id")
                result[key] = item
        return result

    def fact(self, relation, *arguments):
        self.facts.add((relation, tuple(map(str, arguments))))

    def fresh(self, prefix):
        self.serial += 1
        return f"{prefix}:{self.serial}"

    def expr(self, operation, *arguments):
        key = (self.root, operation, *arguments)
        if key not in self.expressions:
            if len(self.expressions) >= MAX_EXPRESSIONS:
                raise ValueError("structural expression limit exceeded")
            ident = self.fresh("e")
            self.expressions[key] = ident
            self.fact(operation, ident, self.root, *arguments)
        return ("node", self.expressions[key])

    @staticmethod
    def node(symbol):
        if symbol[0] != "node":
            raise Unsupported("aggregate/reference used as a scalar")
        return symbol[1]

    def literal(self, value):
        self.values.add(value)
        return self.expr("rv_literal", value)

    def guard(self, conditions):
        if not conditions:
            return "g0"
        if len(conditions) == 1:
            expr, wanted = conditions[0]
            key = ("test", expr, wanted)
            relation, args = "rv_guard_test", (expr, wanted)
        else:
            middle = len(conditions) // 2
            left, right = self.guard(conditions[:middle]), self.guard(conditions[middle:])
            key = ("join", left, right)
            relation, args = "rv_guard_join", (left, right)
        if key not in self.guards:
            self.guards[key] = self.fresh("g")
            self.fact(relation, self.guards[key], *args)
        return self.guards[key]

    def adt_id(self, ty):
        ref = ty.get("Adt", {})
        if ref.get("builtin") or ref.get("id") not in self.types:
            raise Unsupported("expected a declared enum")
        if any(ref.get("generics", {}).get(k) for k in ("types", "const_generics", "trait_refs")):
            raise Unsupported("generic enum")
        return ref["id"]

    def variant(self, reference, variant):
        ident = reference["id"]
        if self.type_names.get(ident) not in TYPES.values():
            raise Unsupported("enum outside the finite verdict profile")
        variants = self.types[ident]["kind"]["Enum"]
        item = next((v for v in variants if v["id"] == variant), None)
        if item is None:
            raise ValueError("missing enum variant")
        return self.type_names[ident].split("::")[-1] + "::" + item["name"]

    def domain(self, ident, active=()):
        if ident in self.domains:
            return self.domains[ident]
        if ident in active or self.type_names.get(ident) not in TYPES.values():
            raise Unsupported("recursive or unsupported input type")
        decl = self.types[ident]
        if "Enum" not in decl["kind"]:
            raise Unsupported("non-enum input")
        values = []
        for variant in decl["kind"]["Enum"]:
            tag = self.variant({"id": ident}, variant["id"])
            self.values.add(tag)
            fields = variant["fields"]
            if len(fields) > 1:
                raise Unsupported("multi-field verdict enum")
            payloads = self.domain(self.adt_id(fields[0]["ty"]), (*active, ident)) if fields else [None]
            for payload in payloads:
                value = tag if payload is None else f"{tag}({payload})"
                values.append(value)
                self.values.add(value)
                self.fact("rv_enum", value, tag)
                self.fact("rv_type", value, self.type_names[ident].split("::")[-1])
                if payload is not None:
                    self.fact("rv_field_value", value, tag, payload)
                    self.fact("rv_construct", tag, payload, value)
        if not values or len(values) != len(set(values)):
            raise ValueError("empty or duplicate enum domain")
        self.domains[ident] = values
        return values

    def place(self, place, env):
        kind = place["kind"]
        if "Local" in kind:
            if kind["Local"] not in env:
                raise Unsupported("read of unavailable local")
            return env[kind["Local"]]
        if "Projection" in kind:
            base, projection = kind["Projection"]
            symbol = self.place(base, env)
            if projection == "Deref" and symbol[0] == "ref":
                return symbol[1]
            if isinstance(projection, dict) and "Field" in projection:
                variant, field = projection["Field"]
                if symbol[0] == "tuple" and variant is None:
                    return symbol[1][field]
                if variant is not None and field == 0:
                    tag = self.variant(base["ty"]["Adt"], variant)
                    return self.expr("rv_payload_expr", self.node(symbol), tag)
        raise Unsupported("unsupported place projection")

    def constant(self, constant):
        kind, _ty = constant
        if "Bool" in kind:
            return self.literal("bool:true" if kind["Bool"] else "bool:false")
        if "Discriminant" in kind:
            return self.literal(self.variant(*kind["Discriminant"]))
        raise Unsupported("non-verdict constant")

    def operand(self, operand, env):
        if "Const" in operand:
            return self.constant(operand["Const"])
        for mode in ("Copy", "Move"):
            if mode in operand:
                return self.place(operand[mode], env)
        raise Unsupported("unknown operand")

    def rvalue(self, value, env):
        if "Use" in value:
            return self.operand(value["Use"][0], env)
        if "Ref" in value and value["Ref"]["kind"] == "Shared":
            return ("ref", self.place(value["Ref"]["place"], env))
        if "Discriminant" in value:
            return self.expr("rv_tag_expr", self.node(self.place(value["Discriminant"], env)))
        if "Aggregate" in value:
            aggregate, operands = value["Aggregate"]
            if "Adt" not in aggregate:
                raise Unsupported("non-enum/tuple aggregate")
            ref, variant, active = aggregate["Adt"]
            fields = tuple(self.operand(v, env) for v in operands)
            if ref["builtin"] == "Tuple" and variant is None and active is None:
                return ("tuple", fields)
            if active is not None:
                raise Unsupported("union construction")
            tag = self.variant(ref, variant)
            if not fields:
                return self.literal(tag)
            if len(fields) == 1:
                return self.expr("rv_construct_expr", tag, self.node(fields[0]))
        if "BinaryOp" in value:
            op, left, right = value["BinaryOp"]
            if op in ("Eq", "Ne"):
                result = self.expr("rv_equal_expr", self.node(self.operand(left, env)), self.node(self.operand(right, env)))
                return result if op == "Eq" else self.expr("rv_not_expr", self.node(result))
        if "UnaryOp" in value and value["UnaryOp"][0] == "Not":
            return self.expr("rv_not_expr", self.node(self.operand(value["UnaryOp"][1], env)))
        raise Unsupported("unsupported rvalue: " + next(iter(value)))

    def assign(self, env, dest, value):
        if set(dest["kind"]) != {"Local"}:
            raise Unsupported("write through a projection/reference")
        result = env.copy()
        result[dest["kind"]["Local"]] = value
        return result

    def function(self, fid, arguments, guards, stack):
        if fid in stack or len(stack) > 32:
            raise Unsupported("recursive/deep call graph")
        function = self.functions.get(fid)
        if function is None or function["signature"]["is_unsafe"]:
            raise Unsupported("missing/unsafe callee")
        if any(function["generics"][k] for k in ("types", "const_generics", "trait_clauses")):
            raise Unsupported("generic callee")
        body = function["body"]
        if not isinstance(body, dict) or "Structured" not in body:
            raise Unsupported("opaque or unstructured callee")
        body = body["Structured"]
        if body["locals"]["arg_count"] != len(arguments):
            raise ValueError("callee argument count mismatch")
        initial = State(dict(enumerate(arguments, 1)), guards)
        result = self.block(body["body"], [initial], (*stack, fid))
        return [replace(s, outcome="blocked", value="missing return") if s.outcome == "running" else s for s in result]

    def block(self, block, states, stack):
        for statement in block["statements"]:
            next_states = []
            for state in states:
                if state.outcome != "running":
                    next_states.append(state)
                    continue
                location = {"function": name(self.functions[stack[-1]]), "statement": statement["id"], "span": statement["span"]}
                file_id = statement["span"].get("data", {}).get("file_id")
                location["file"] = next((f["name"] for f in self.crate.get("files", []) if f and f["id"] == file_id), None)
                state = replace(state, location=location)
                try:
                    next_states.extend(self.statement(statement["kind"], state, stack))
                except (Unsupported, KeyError, IndexError) as error:
                    next_states.append(replace(state, outcome="blocked", value=str(error)))
            if len(next_states) > MAX_PATHS:
                raise ValueError("structural path limit exceeded")
            states = next_states
        return states

    def statement(self, kind, state, stack):
        if kind == "Nop" or isinstance(kind, dict) and "Borrowck" in kind:
            return [state]
        if isinstance(kind, dict) and ("StorageLive" in kind or "StorageDead" in kind):
            env = state.env.copy()
            env.pop(next(iter(kind.values())), None)
            return [replace(state, env=env)]
        if kind == "Return":
            return [replace(state, outcome="return", value=self.node(state.env[0]))]
        if kind in ("UnwindResume", "UnwindTerminate", "UndefinedBehavior"):
            return [replace(state, outcome="panic", value=kind)]
        if not isinstance(kind, dict):
            raise Unsupported(str(kind))
        if "Panic" in kind:
            return [replace(state, outcome="panic", value="panic")]
        if "Assign" in kind:
            dest, value = kind["Assign"]
            return [replace(state, env=self.assign(state.env, dest, self.rvalue(value, state.env)))]
        if "Call" in kind:
            call = kind["Call"]["call"]
            if call["safety"] != "Inherit":
                raise Unsupported("nonstandard call safety")
            target = call["func"].get("Regular", {}).get("kind", {}).get("Fun")
            args = [self.operand(arg, state.env) for arg in call["args"]]
            outcomes = self.function(target, args, state.guards, stack)
            return [replace(state, guards=s.guards, env=self.assign(state.env, call["dest"], ("node", s.value)))
                    if s.outcome == "return" else s for s in outcomes]
        if "Switch" in kind:
            switch = kind["Switch"]
            data = switch["data"]
            scrutinee = data["scrutinee"]
            if "Value" in scrutinee:
                expr = self.operand(scrutinee["Value"], state.env)
            else:
                expr = self.expr("rv_tag_expr", self.node(self.place(scrutinee["Discriminant"], state.env)))
            outcomes, tests = [], []
            for constant, branch in data["branches"]:
                test = self.node(self.expr("rv_equal_expr", self.node(expr), self.node(self.constant(constant))))
                tests.append((test, "bool:false"))
                selected = replace(state, guards=(*state.guards, (test, "bool:true")))
                outcomes.extend(self.block(switch["branches"][branch], [selected], stack))
            fallback = replace(state, guards=(*state.guards, *tests))
            if data["fallback"] is not None:
                outcomes.extend(self.block(switch["branches"][data["fallback"]], [fallback], stack))
            else:
                # Even an allegedly exhaustive Rust switch gets a checked
                # residual barrier; missing coverage cannot silently disappear.
                outcomes.append(replace(fallback, outcome="blocked", value="uncovered switch"))
            return outcomes
        raise Unsupported("unsupported statement: " + next(iter(kind)))

    def export(self):
        qr = [i for i, n in self.type_names.items() if n == TYPES["QueryResult"]]
        if len(qr) != 1:
            raise ValueError("missing/ambiguous QueryResult type")
        domain = self.domain(qr[0])
        variants = self.types[qr[0]]["kind"]["Enum"]
        if {v["name"] for v in variants} != {"True", "False", "Unknown", "ResourceExceeded"}:
            raise Unsupported("QueryResult constructors need contract review")
        self.fact("rv_guard_start", "g0")
        for root, rust_name in ROOTS.items():
            self.root = root
            matches = [i for i, f in self.functions.items() if name(f) == rust_name]
            if len(matches) != 1:
                raise ValueError("missing/ambiguous production root: " + rust_name)
            signature = self.functions[matches[0]]["signature"]
            arity = 1 if root == "not" else 2
            if len(signature["inputs"]) != arity or any(self.adt_id(t) != qr[0] for t in [*signature["inputs"], signature["output"]]):
                raise Unsupported("production root signature changed")
            args = [self.expr("rv_argument", str(i)) for i in range(arity)]
            for inputs in itertools.product(domain, repeat=arity):
                case = f"{root}:{len(self.cases)}"
                self.cases.append({"id": case, "root": root, "inputs": list(inputs)})
                self.fact("rv_case", case, root)
                for i, value in enumerate(inputs):
                    self.fact("rv_input", case, str(i), value)
            for outcome in self.function(matches[0], args, (), ()):
                guard = self.guard(outcome.guards)
                path = self.fresh("p")
                relation = {"return": "rv_path", "blocked": "rv_barrier", "panic": "rv_trap"}[outcome.outcome]
                self.fact(relation, path, root, guard, outcome.value)
                self.locations[path] = outcome.location
                self.paths.append({"id": path, "root": root, "kind": outcome.outcome, "detail": outcome.value})
        for left, right in itertools.permutations(sorted(self.values), 2):
            self.fact("rv_distinct", left, right)
        return {"schema": 1, "domain": domain, "cases": self.cases, "paths": self.paths,
                "locations": self.locations,
                "facts": [{"relation": relation, "arguments": list(args)} for relation, args in sorted(self.facts)]}


def export(raw):
    return Exporter(raw).export()


if __name__ == "__main__":
    import sys
    with open(sys.argv[1]) as stream:
        print(json.dumps(export(json.load(stream)), indent=2))
