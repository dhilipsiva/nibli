"""Fail-closed structural export controls; production Rust is checked by the gate."""
import copy
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import rust_verdicts as rv
import verify_nibli_verdicts as gate


def reference(ident):
    return {"id": ident, "builtin": None, "generics": {}}


def metadata(name):
    return {"name": [{"Ident": [part, 0]} for part in name.split("::")]}


def statement(kind, ident=0):
    return {"kind": kind, "id": ident, "span": {"test_line": ident}}


def place(ident):
    return {"kind": {"Local": ident}, "ty": {"Adt": reference(0)}}


def program():
    types = []
    for ident, name, variants in [
        (0, "QueryResult", [("True", None), ("False", None), ("Unknown", 1), ("ResourceExceeded", 2)]),
        (1, "UnknownReason", [(n, None) for n in ("CycleCut", "IncompleteKnowledge", "NafDependent", "BackendUnavailable", "NonFinite")]),
        (2, "ResourceKind", [(n, None) for n in ("Depth", "Fuel", "Memory")]),
    ]:
        types.append({"def_id": ident, "item_meta": metadata(rv.TYPES[name]), "kind": {"Enum": [
            {"id": i, "name": n, "fields": [] if field is None else [{"ty": {"Adt": reference(field)}}]}
            for i, (n, field) in enumerate(variants)]}})
    functions = []
    for ident, (root, name) in enumerate(rv.ROOTS.items()):
        arity = 1 if root == "not" else 2
        functions.append({"def_id": ident, "item_meta": metadata(name),
            "signature": {"is_unsafe": False, "inputs": [{"Adt": reference(0)}] * arity, "output": {"Adt": reference(0)}},
            "generics": {"types": [], "const_generics": [], "trait_clauses": []},
            "body": {"Structured": {"locals": {"arg_count": arity}, "body": {"statements": [
                statement({"Assign": [place(0), {"Aggregate": [{"Adt": [reference(0), 0, None]}, []]}]}),
                statement("Return", 1)]}}}})
    return {"charon_version": "0.1.293", "has_errors": False,
            "translated": {"fun_decls": functions, "type_decls": types}}


class RustExportTests(unittest.TestCase):
    def test_every_input_is_derived_from_types(self):
        bundle = rv.export(program())
        n = len(bundle["domain"])
        self.assertEqual(len(bundle["cases"]), 2 * n * n + n)
        self.assertFalse(any(f["relation"] in ("rv_eval", "rv_return", "rv_expected", "rv_case_ok") for f in bundle["facts"]))

    def test_new_payload_value_expands_coverage(self):
        original = rv.export(program())
        changed = program()
        changed["translated"]["type_decls"][1]["kind"]["Enum"].append({"id": 5, "name": "NewReason", "fields": []})
        result = rv.export(changed)
        self.assertEqual(len(result["domain"]), len(original["domain"]) + 1)
        n = len(result["domain"])
        self.assertEqual(len(result["cases"]), 2 * n * n + n)

    def test_new_top_level_variant_requires_contract_review(self):
        changed = program()
        changed["translated"]["type_decls"][0]["kind"]["Enum"].append({"id": 4, "name": "Other", "fields": []})
        with self.assertRaisesRegex(rv.Unsupported, "contract review"):
            rv.export(changed)

    def test_branches_are_preserved_without_native_evaluation(self):
        changed = program()
        body = changed["translated"]["fun_decls"][0]["body"]["Structured"]["body"]
        old = copy.deepcopy(body)
        body["statements"] = [statement({"Switch": {"data": {
            "scrutinee": {"Value": {"Const": [{"Bool": True}, {"Scalar": "Bool"}]}},
            "branches": [[[ {"Bool": True}, {"Scalar": "Bool"}], 0]], "fallback": 1},
            "branches": [old, {"statements": [statement({"Loop": {"statements": []}})]}]}})]
        exported = rv.export(changed)
        self.assertTrue(any(p["kind"] == "blocked" and "Loop" in p["detail"] for p in exported["paths"]))
        self.assertTrue(any(p["kind"] == "return" and p["root"] == "and" for p in exported["paths"]))

    def test_recursion_is_an_explicit_barrier(self):
        changed = program()
        body = changed["translated"]["fun_decls"][0]["body"]["Structured"]["body"]
        body["statements"].insert(0, statement({"Call": {"call": {
            "safety": "Inherit", "func": {"Regular": {"kind": {"Fun": 0}}},
            "args": [{"Move": place(1)}, {"Move": place(2)}], "dest": place(0)}}}))
        bundle = rv.export(changed)
        self.assertTrue(any(p["kind"] == "blocked" and "recursive" in p["detail"] for p in bundle["paths"]))

    def test_invalid_extraction_and_missing_roots_fail(self):
        for key, value in [("has_errors", True), ("charon_version", "0.0")]:
            changed = program(); changed[key] = value
            with self.assertRaises(ValueError): rv.export(changed)
        changed = program(); changed["translated"]["fun_decls"].pop()
        with self.assertRaisesRegex(ValueError, "production root"): rv.export(changed)

    def test_reader_sharing_codec_must_be_resolved(self):
        with self.assertRaisesRegex(ValueError, "typed LLBC reader"):
            rv.plain({"Deduplicated": 7})

    def test_rust_digest_ignores_proof_files_but_binds_code(self):
        original = {"nibli-reason/src/reasoning.rs": "a", "proofs/self-check/Verdicts.lean": "b"}
        self.assertEqual(gate.rust_digest(original), gate.rust_digest({**original, "proofs/self-check/Verdicts.lean": "c"}))
        self.assertNotEqual(gate.rust_digest(original), gate.rust_digest({**original, "nibli-reason/src/reasoning.rs": "c"}))

    def test_replay_rejects_stale_sources_and_changed_artifacts(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            artifact = root / "input.llbc"
            artifact.write_text("original")
            report = {"status": "verified", "sources": {"source": "original"},
                      "artifacts": {}, "binaries": {}, "extraction": {
                          "llbc_file": "input.llbc", "llbc_sha256": gate.digest(artifact)}}
            with patch.object(gate.extract, "ROOT", root), patch.object(gate, "sources", return_value=report["sources"]):
                gate.check_saved(report)
                artifact.write_text("changed")
                with self.assertRaisesRegex(ValueError, "artifact changed"):
                    gate.check_saved(report)
            with patch.object(gate, "sources", return_value={"source": "changed"}):
                with self.assertRaisesRegex(ValueError, "stale"):
                    gate.check_saved(report)

    def test_missing_tool_clears_a_previous_success(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            report = output / "report.json"
            report.write_text('{"status":"verified"}')
            with patch.object(gate, "OUTPUT", output), \
                 patch.object(gate.extract, "ROOT", output.parent), \
                 patch.object(gate.extract, "exclusive_output", contextlib.nullcontext), \
                 patch.object(gate.extract, "environment", side_effect=RuntimeError("missing pinned tool")), \
                 patch("sys.argv", ["verify_nibli_verdicts.py"]), \
                 contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(gate.main(), 2)
            saved = json.loads(report.read_text())
            self.assertEqual(saved["status"], "inconclusive")
            self.assertIn("missing pinned tool", saved["error"])


if __name__ == "__main__":
    unittest.main()
