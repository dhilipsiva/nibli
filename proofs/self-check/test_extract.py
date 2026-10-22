"""Failure-mode tests for the extraction boundary, not simulated proof results."""

import os
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import extract


class ExtractionTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.output = self.root / "target"
        self.probe = {"name": "sample", "package": "nibli-types",
                      "roots": ["nibli_types::real_function"], "obligation": "sample"}
        self.config = {"target": "x86_64-unknown-linux-gnu", "charon_version": "fixture"}
        self.addCleanup(patch.stopall)
        patch.object(extract, "ROOT", self.root).start()
        patch.object(extract, "OUTPUT", self.output).start()

    def write_llbc(self, directory):
        artifact = {
            "has_errors": False, "charon_version": "fixture",
            "translated": {
                "target_information": [{"key": self.config["target"]}],
                "fun_decls": [{
                    "item_meta": {"name": [{"Ident": [part, 0]} for part in
                                             self.probe["roots"][0].split("::")],
                                  "started_from": True},
                    "body": {"Structured": {}},
                }],
            },
        }
        path = directory / "input.llbc"
        path.write_text(json.dumps(artifact))
        return path, artifact

    def test_zero_exit_without_llbc_is_not_a_success(self):
        with patch.object(extract, "run", return_value={"status": "ok"}):
            result = extract.extract(self.probe, self.config, {}, 1)
        self.assertEqual(result["status"], "blocked")
        self.assertNotIn("aeneas", result)

    def test_failed_extraction_discards_previous_artifacts(self):
        directory = self.output / "probes" / "sample"
        directory.mkdir(parents=True)
        (directory / "input.llbc").write_text("stale")
        with patch.object(extract, "run", return_value={"status": "failed"}):
            result = extract.extract(self.probe, self.config, {}, 1)
        self.assertEqual(result["status"], "blocked")
        self.assertFalse((directory / "input.llbc").exists())

    def test_unimplemented_external_is_not_a_success(self):
        def fake_run(command, cwd, log, env, timeout):
            directory = self.output / "probes" / "sample"
            if command[0] == "charon":
                self.write_llbc(directory)
            else:
                (directory / "lean" / "Input" / "FunsExternal_Template.lean").write_text("axiom stub : True")
            return {"status": "ok"}

        with patch.object(extract, "run", side_effect=fake_run):
            result = extract.extract(self.probe, self.config, {}, 1)
        self.assertEqual(result["status"], "blocked")
        self.assertTrue(result["templates"])

    def test_empty_translation_is_not_a_success(self):
        def fake_run(command, cwd, log, env, timeout):
            if command[0] == "charon":
                self.write_llbc(self.output / "probes" / "sample")
            return {"status": "ok"}

        with patch.object(extract, "run", side_effect=fake_run):
            result = extract.extract(self.probe, self.config, {}, 1)
        self.assertEqual(result["status"], "blocked")

    def test_missing_production_root_is_not_a_success(self):
        path, artifact = self.write_llbc(self.root)
        artifact["translated"]["fun_decls"] = []
        path.write_text(json.dumps(artifact))
        with self.assertRaisesRegex(ValueError, "Missing production roots"):
            extract.validate_llbc(path, self.probe, self.config)

    def test_opaque_nibli_dependency_is_not_a_success(self):
        path, artifact = self.write_llbc(self.root)
        artifact["translated"]["fun_decls"].append({
            "item_meta": {"name": [{"Ident": ["nibli_types", 0]},
                                   {"Ident": ["dependency", 0]}]},
            "body": "Opaque",
        })
        path.write_text(json.dumps(artifact))
        with self.assertRaisesRegex(ValueError, "Opaque Nibli definition"):
            extract.validate_llbc(path, self.probe, self.config)

    def test_error_artifact_is_not_a_success(self):
        path, artifact = self.write_llbc(self.root)
        artifact["has_errors"] = True
        path.write_text(json.dumps(artifact))
        with self.assertRaisesRegex(ValueError, "recorded errors"):
            extract.validate_llbc(path, self.probe, self.config)

    def test_wrong_target_is_not_a_success(self):
        path, artifact = self.write_llbc(self.root)
        artifact["translated"]["target_information"] = [{"key": "wasm32-unknown-unknown"}]
        path.write_text(json.dumps(artifact))
        with self.assertRaisesRegex(ValueError, "target differs"):
            extract.validate_llbc(path, self.probe, self.config)

    def test_competing_run_cannot_replace_proof_inputs(self):
        with extract.exclusive_output():
            with self.assertRaisesRegex(RuntimeError, "Another extraction"):
                with extract.exclusive_output():
                    self.fail("An overlapping run acquired the lock")

    def test_timeout_is_an_operational_failure(self):
        result = extract.run(
            [sys.executable, "-c", "import time; time.sleep(10)"],
            self.root, self.root / "timeout.log", os.environ.copy(), 0.05,
        )
        self.assertEqual(result["status"], "timeout")
        self.assertIsNone(result["exit_code"])


if __name__ == "__main__":
    unittest.main()
