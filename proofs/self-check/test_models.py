"""Library model audits are explicit about their non-native proof boundary."""

from contextlib import redirect_stderr
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import extract
import verify_models


class ModelAuditTests(unittest.TestCase):
    def test_all_public_model_contracts_are_inventoried(self):
        for model in verify_models.MODELS:
            self.assertTrue(verify_models.obligations(model))

    def test_model_success_never_claims_native_certification(self):
        for model in verify_models.MODELS:
            report = verify_models.initial_report({
                "lean_toolchain": "test", "target": "test", "aeneas_revision": "test",
            }, {}, model)
            report["model_contracts_verified"] = True
            self.assertEqual(report["scope"], "model_contracts_only")
            for key in ("native_implementation_verified", "extraction_bindings_verified",
                        "self_check_equivalence_verified"):
                self.assertIs(report[key], False)

    def test_failed_first_model_clears_later_selected_successes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "library-maps-report.json"
            path.write_text('{"model_contracts_verified":true}')
            with patch.object(extract, "OUTPUT", root), \
                    patch.object(extract, "environment", return_value={}), \
                    patch.object(extract, "source_hashes", return_value={}), \
                    patch.object(verify_models, "prove", side_effect=ValueError("proof failed")), \
                    redirect_stderr(io.StringIO()):
                self.assertEqual(verify_models.main(["strings", "maps"]), 1)
            self.assertIs(json.loads(path.read_text())["model_contracts_verified"], False)

    def test_unlisted_model_contract_cannot_escape_the_audit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "StdStrings.lean").write_text(
                "theorem listed : True := by trivial\ntheorem unlisted : True := by trivial\n"
            )
            (root / "coverage.toml").write_text('''
[[obligation]]
id = "primitive_strings"
theorem_files = ["StdStrings.lean"]
theorems = ["NibliSelfCheck.StdStrings.listed"]
''')
            with patch.object(verify_models, "DIRECTORY", root), patch.object(extract, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "inventory differ"):
                    verify_models.obligations()


if __name__ == "__main__":
    unittest.main()
