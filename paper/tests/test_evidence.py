import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import analyze
from analyze import audit_trace


class SourceAudit(unittest.TestCase):
    def test_live_source_and_withdrawn_or_mislabeled_source(self):
        envelope = {"trace": {"steps": [{"rule": {"type": "asserted", "sources": [{"id": 3, "label": "dog(Ada)."}]}}]}}
        self.assertEqual(audit_trace(envelope, {3: "dog(Ada)."}), (1, []))
        self.assertTrue(audit_trace(envelope, {})[1])
        self.assertTrue(audit_trace(envelope, {3: "cat(Ada)."})[1])
        missing = copy.deepcopy(envelope)
        missing["trace"]["steps"][0]["rule"]["sources"] = []
        self.assertTrue(audit_trace(missing, {3: "dog(Ada)."})[1])

    def test_cutoff_preserves_complete_envelope_before_partial_json(self):
        envelope = {"trace": {"steps": [{"rule": {"type": "asserted", "sources": [{"id": 3, "label": "dog(Ada)."}]}}]}}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inputs = root / "inputs/case"
            inputs.mkdir(parents=True)
            (inputs / "request.json").write_text(json.dumps({"statements": ["dog(Ada)."], "updates": []}))
            (root / "raw.stdout").write_text(json.dumps({"phase": "load", "ids": [3]}) + "\n" +
                                           json.dumps({"phase": "certificate", "envelope": envelope}) + "\n" + '{"phase": "certificate", "envelope":')
            record = {"case_id": "case", "run_id": "run", "stdout": "raw.stdout", "status": "timeout"}
            with patch.multiple(analyze, ROOT=root, RESULTS=root):
                result = analyze.audit_raw(record)
                self.assertEqual(result["certificates"], 1)
                self.assertEqual(result["citations"], 1)
                self.assertEqual(result["incomplete_json_lines"], 1)
                self.assertEqual(result["errors"], [])
                record["status"] = "ok"
                with self.assertRaises(json.JSONDecodeError):
                    analyze.audit_raw(record)


if __name__ == "__main__":
    unittest.main()
