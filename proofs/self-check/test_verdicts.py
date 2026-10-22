"""The proof gate must reject missing evidence and additional assumptions."""

import unittest
from pathlib import Path
import tempfile
from unittest.mock import patch

import extract
from verify_verdicts import audit_axioms, check_artifacts, obligations


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

    def test_changed_generated_definition_cannot_certify_the_original_rust(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Funs.lean").write_text("modified after extraction")
            with patch.object(extract, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "changed during proof"):
                    check_artifacts({"artifacts": {"Funs.lean": "original digest"}})


if __name__ == "__main__":
    unittest.main()
