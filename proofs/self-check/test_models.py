"""Library model audits are explicit about their non-native proof boundary."""

from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import extract
import verify_models


class ModelAuditTests(unittest.TestCase):
    def test_all_public_string_contracts_are_inventoried(self):
        self.assertTrue(verify_models.obligations())

    def test_model_success_never_claims_native_certification(self):
        report = verify_models.initial_report({
            "lean_toolchain": "test", "target": "test", "aeneas_revision": "test",
        }, {})
        report["model_contracts_verified"] = True
        for key in ("native_implementation_verified", "extraction_replacements_installed",
                    "self_check_equivalence_verified"):
            self.assertIs(report[key], False)

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
