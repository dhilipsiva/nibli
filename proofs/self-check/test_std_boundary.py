"""External models require exact reviewed identities, signatures and scopes."""

import json
from pathlib import Path
import re
import tempfile
import unittest

import std_boundary


class LibraryBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads((std_boundary.DIRECTORY / "std_boundary_signatures.json").read_text())
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        module, roots = std_boundary.PROBES["stratification"]
        self.probe = {"name": "stratification", "lean_module": module, "roots": roots}
        for kind in ("Types", "Funs"):
            text = self.manifest["headers"][kind].replace("__INPUT__", module) + "\n"
            for declaration in self.manifest[kind].values():
                text += f'\n/-- Reviewed declaration. -/\n@[{declaration["rust_kind"]} "{declaration["rust_pattern"]}"]\n{declaration["signature"]}\n'
            (self.root / f"{kind}External_Template.lean").write_text(text)

    def test_complete_reviewed_profile_installs_without_holes(self):
        result = std_boundary.install(self.root, std_boundary.PROFILE, self.probe)
        self.assertIs(result["native_std_implementation_verified"], False)
        self.assertFalse(list(self.root.glob("*Template*")))
        for kind, bodies in (("Types", std_boundary.TYPE_BODIES), ("Funs", std_boundary.FUN_BODIES)):
            self.assertEqual(set(self.manifest[kind]), set(bodies))
            text = (self.root / f"{kind}External.lean").read_text()
            self.assertNotRegex(text, r"\b(?:axiom|sorry|admit|opaque)\b")
            self.assertEqual(len(re.findall(r"^def ", text, re.M)), len(bodies))
            for declaration in self.manifest[kind].values():
                self.assertTrue(declaration["rust_pattern"].startswith(("core::", "alloc::", "std::")))

    def assert_refused_without_replacement(self):
        with self.assertRaises(ValueError):
            std_boundary.install(self.root, std_boundary.PROFILE, self.probe)
        self.assertFalse((self.root / "TypesExternal.lean").exists())
        self.assertFalse((self.root / "FunsExternal.lean").exists())

    def test_changed_function_signature_preserves_both_templates(self):
        path = self.root / "FunsExternal_Template.lean"
        path.write_text(path.read_text().replace("String → String → Result Bool", "String → String → Result Usize"))
        self.assert_refused_without_replacement()
        self.assertTrue((self.root / "TypesExternal_Template.lean").exists())

    def test_extra_header_declaration_is_rejected(self):
        path = self.root / "FunsExternal_Template.lean"
        path.write_text(path.read_text().replace("public import Aeneas\n",
            "public import Aeneas\ndef nibli_reason.extra : Bool := true\n", 1))
        self.assert_refused_without_replacement()

    def test_extra_declaration_between_reviewed_items_is_rejected(self):
        path = self.root / "FunsExternal_Template.lean"
        text = path.read_text()
        marker = "/-- Reviewed declaration. -/"
        second = text.index(marker, text.index(marker) + len(marker))
        path.write_text(text[:second] + text[second:].replace(marker,
            marker + "\ndef nibli_reason.extra : Bool := true\n", 1))
        self.assert_refused_without_replacement()

    def test_changed_rust_identity_cannot_reuse_a_lean_name(self):
        path = self.root / "FunsExternal_Template.lean"
        path.write_text(path.read_text().replace('"core::borrow::', '"nibli_reason::borrow::', 1))
        self.assert_refused_without_replacement()

    def test_additional_native_function_cannot_be_modeled(self):
        path = self.root / "FunsExternal_Template.lean"
        path.write_text(path.read_text() + '\n/-- Additional declaration. -/\n@[rust_fun "nibli_reason::compiler"]\naxiom compiler : Bool\n')
        self.assert_refused_without_replacement()

    def test_unrecognized_or_duplicate_template_is_rejected(self):
        extra = self.root / "nested"
        extra.mkdir()
        (extra / "TypesExternal_Template.lean").write_text("extra")
        self.assert_refused_without_replacement()

    def test_other_probe_roots_and_modules_are_rejected(self):
        for changed in (
            {**self.probe, "name": "evaluation"},
            {**self.probe, "roots": ["nibli_reason::compiler"]},
            {**self.probe, "lean_module": "Input"},
        ):
            with self.assertRaisesRegex(ValueError, "not approved"):
                std_boundary.install(self.root, std_boundary.PROFILE, changed)

    def test_unknown_profile_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "Unknown"):
            std_boundary.install(self.root, "permissive", self.probe)

    def test_unannotated_or_duplicate_declaration_is_rejected(self):
        for source in (
            "axiom missing : Type",
            '@[rust_type "std::A"]\naxiom A : Type\n/-- Again. -/\n@[rust_type "std::A"]\naxiom A : Type',
        ):
            with self.assertRaises(ValueError):
                std_boundary.declarations(source)


if __name__ == "__main__":
    unittest.main()
