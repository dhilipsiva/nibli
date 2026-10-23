"""The proof gate must reject missing evidence and additional assumptions."""

import hashlib
import unittest
from pathlib import Path
import tempfile
from unittest.mock import patch

import extract
from verify_verdicts import audit_axioms, check_artifacts, obligations
from verify_component import check_proof_sources


class AxiomAuditTests(unittest.TestCase):
    def test_missing_theorem_output_fails(self):
        with self.assertRaisesRegex(ValueError, "exactly the required"):
            audit_axioms("", ["NibliSelfCheck.conjunction_total"])

    def test_admitted_theorem_fails(self):
        with self.assertRaisesRegex(ValueError, "Unapproved axioms"):
            audit_axioms("'theorem' depends on axioms: [propext, sorryAx]", ["theorem"])

    def test_assumed_native_equivalence_fails(self):
        with self.assertRaisesRegex(ValueError, "Unapproved axioms"):
            audit_axioms("'theorem' depends on axioms: [Nibli.compiler_correct]", ["theorem"])

    def test_duplicate_or_unexpected_theorem_fails(self):
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            audit_axioms("'a' does not depend on any axioms\n" * 2, ["a"])
        with self.assertRaisesRegex(ValueError, "exactly the required"):
            audit_axioms("'wrong' does not depend on any axioms", ["expected"])

    def test_foundations_and_closed_proofs_are_allowed(self):
        observed = audit_axioms(
            "'a' depends on axioms: [propext,\n Quot.sound]\n"
            "'b' does not depend on any axioms\n", ["a", "b"],
        )
        self.assertEqual(observed, {"a": ["Quot.sound", "propext"], "b": []})

    def test_coverage_references_live_source_and_all_component_theorems(self):
        self.assertTrue(obligations())
        self.assertTrue(obligations("scc_stack"))

    def test_unproved_local_helper_fails_even_with_an_empty_public_proof(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Public.lean").write_text("import Helper\n")
            (root / "Helper.lean").write_text("theorem helper : False := by sorry\n")
            with self.assertRaisesRegex(ValueError, "Unproved.*Helper.lean"):
                check_proof_sources(sorted(root.glob("*.lean")))

    def test_changed_generated_definition_cannot_certify_the_original_rust(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Funs.lean").write_text("modified after extraction")
            with patch.object(extract, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "changed during proof"):
                    check_artifacts({"artifacts": {"Funs.lean": "original digest"}})

    def test_named_component_llbc_is_checked_for_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "SccKernel.llbc"
            path.write_text("changed input")
            with patch.object(extract, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "LLBC changed"):
                    check_artifacts({
                        "artifacts": {}, "llbc_file": "SccKernel.llbc",
                        "llbc_sha256": hashlib.sha256(b"original input").hexdigest(),
                    })


if __name__ == "__main__":
    unittest.main()
