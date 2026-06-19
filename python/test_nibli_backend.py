#!/usr/bin/env python3
"""Tests for the Nibli Python compute backend."""

import json
import socket
import subprocess
import sys
import threading
import time
import unittest
from pathlib import Path

BACKEND_SCRIPT = Path(__file__).parent / "nibli_backend.py"
HOST = "127.0.0.1"
PORT = 15555  # Use non-default port to avoid conflicts


def send_request(request, host=HOST, port=PORT):
    """Send a JSON Lines request and return the parsed response."""
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.settimeout(5)
    sock.connect((host, port))
    try:
        payload = json.dumps(request) + "\n"
        sock.sendall(payload.encode("utf-8"))
        data = b""
        while b"\n" not in data:
            chunk = sock.recv(4096)
            if not chunk:
                break
            data += chunk
        return json.loads(data.decode("utf-8").strip())
    finally:
        sock.close()


class TestNibliBackend(unittest.TestCase):
    proc = None

    @classmethod
    def setUpClass(cls):
        """Start the backend server as a subprocess."""
        cls.proc = subprocess.Popen(
            [sys.executable, str(BACKEND_SCRIPT), "--port", str(PORT)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        # Wait for server to be ready
        for _ in range(50):
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.settimeout(1)
                sock.connect((HOST, PORT))
                sock.close()
                break
            except (ConnectionRefusedError, OSError):
                time.sleep(0.1)
        else:
            raise RuntimeError("Backend server did not start in time")

    @classmethod
    def tearDownClass(cls):
        """Stop the backend server."""
        if cls.proc:
            cls.proc.terminate()
            cls.proc.wait(timeout=5)

    def test_pilji_true(self):
        resp = send_request({"relation": "pilji", "args": [
            {"type": "number", "value": 6.0},
            {"type": "number", "value": 2.0},
            {"type": "number", "value": 3.0},
        ]})
        self.assertTrue(resp["result"])

    def test_pilji_false(self):
        resp = send_request({"relation": "pilji", "args": [
            {"type": "number", "value": 7.0},
            {"type": "number", "value": 2.0},
            {"type": "number", "value": 3.0},
        ]})
        self.assertFalse(resp["result"])

    def test_sumji(self):
        resp = send_request({"relation": "sumji", "args": [
            {"type": "number", "value": 5.0},
            {"type": "number", "value": 2.0},
            {"type": "number", "value": 3.0},
        ]})
        self.assertTrue(resp["result"])

    def test_sumji_float_tolerance(self):
        # 0.1 + 0.2 = 0.30000000000000004 in IEEE-754, but math.isclose answers
        # TRUE for 0.3. This is the canonical tolerant semantics the Rust engine
        # and host now share. A genuinely-wrong claim stays FALSE.
        resp = send_request({"relation": "sumji", "args": [
            {"type": "number", "value": 0.3},
            {"type": "number", "value": 0.1},
            {"type": "number", "value": 0.2},
        ]})
        self.assertTrue(resp["result"])
        resp = send_request({"relation": "sumji", "args": [
            {"type": "number", "value": 0.4},
            {"type": "number", "value": 0.1},
            {"type": "number", "value": 0.2},
        ]})
        self.assertFalse(resp["result"])

    def test_dilcu(self):
        resp = send_request({"relation": "dilcu", "args": [
            {"type": "number", "value": 4.0},
            {"type": "number", "value": 12.0},
            {"type": "number", "value": 3.0},
        ]})
        self.assertTrue(resp["result"])

    def test_dilcu_by_zero(self):
        resp = send_request({"relation": "dilcu", "args": [
            {"type": "number", "value": 0.0},
            {"type": "number", "value": 5.0},
            {"type": "number", "value": 0.0},
        ]})
        self.assertFalse(resp["result"])

    def test_tenfa(self):
        resp = send_request({"relation": "tenfa", "args": [
            {"type": "number", "value": 8.0},
            {"type": "number", "value": 2.0},
            {"type": "number", "value": 3.0},
        ]})
        self.assertTrue(resp["result"])

    def test_tenfa_false(self):
        resp = send_request({"relation": "tenfa", "args": [
            {"type": "number", "value": 9.0},
            {"type": "number", "value": 2.0},
            {"type": "number", "value": 3.0},
        ]})
        self.assertFalse(resp["result"])

    def test_dugri(self):
        # log_2(8) = 3
        resp = send_request({"relation": "dugri", "args": [
            {"type": "number", "value": 3.0},
            {"type": "number", "value": 8.0},
            {"type": "number", "value": 2.0},
        ]})
        self.assertTrue(resp["result"])

    def test_unknown_relation(self):
        resp = send_request({"relation": "foobar", "args": [
            {"type": "number", "value": 1.0},
            {"type": "number", "value": 2.0},
            {"type": "number", "value": 3.0},
        ]})
        self.assertIn("error", resp)
        self.assertIn("Unknown relation", resp["error"])

    def test_too_few_args(self):
        resp = send_request({"relation": "pilji", "args": [
            {"type": "number", "value": 6.0},
        ]})
        self.assertIn("error", resp)

    def test_multiple_requests_same_connection(self):
        """Verify persistent connections work (multiple requests on one TCP socket)."""
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(5)
        sock.connect((HOST, PORT))
        try:
            reader = sock.makefile("r", encoding="utf-8")
            writer = sock.makefile("w", encoding="utf-8")

            # Request 1
            writer.write(json.dumps({"relation": "sumji", "args": [
                {"type": "number", "value": 10.0},
                {"type": "number", "value": 7.0},
                {"type": "number", "value": 3.0},
            ]}) + "\n")
            writer.flush()
            resp1 = json.loads(reader.readline())
            self.assertTrue(resp1["result"])

            # Request 2
            writer.write(json.dumps({"relation": "pilji", "args": [
                {"type": "number", "value": 12.0},
                {"type": "number", "value": 3.0},
                {"type": "number", "value": 4.0},
            ]}) + "\n")
            writer.flush()
            resp2 = json.loads(reader.readline())
            self.assertTrue(resp2["result"])
        finally:
            sock.close()

    def test_large_exponent_survives_connection(self):
        """A huge-exponent tenfa raises OverflowError inside the handler; it must
        return an error response and the connection must keep working."""
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(5)
        sock.connect((HOST, PORT))
        try:
            reader = sock.makefile("r", encoding="utf-8")
            writer = sock.makefile("w", encoding="utf-8")

            # 10 ** 1000 overflows float exponentiation → OverflowError.
            writer.write(json.dumps({"relation": "tenfa", "args": [
                {"type": "number", "value": 1.0},
                {"type": "number", "value": 10.0},
                {"type": "number", "value": 1000.0},
            ]}) + "\n")
            writer.flush()
            resp1 = json.loads(reader.readline())
            self.assertIn("error", resp1)

            # The same connection must still serve a follow-up valid request.
            writer.write(json.dumps({"relation": "sumji", "args": [
                {"type": "number", "value": 5.0},
                {"type": "number", "value": 2.0},
                {"type": "number", "value": 3.0},
            ]}) + "\n")
            writer.flush()
            resp2 = json.loads(reader.readline())
            self.assertTrue(resp2["result"])
        finally:
            sock.close()

    def test_non_dict_json_returns_error(self):
        """Valid JSON that is not an object must return an error, not crash the
        connection (it would AttributeError on `.get`)."""
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(5)
        sock.connect((HOST, PORT))
        try:
            reader = sock.makefile("r", encoding="utf-8")
            writer = sock.makefile("w", encoding="utf-8")

            for raw in ("123", "[1, 2, 3]", "null"):
                writer.write(raw + "\n")
                writer.flush()
                resp = json.loads(reader.readline())
                self.assertIn("error", resp)

            # Connection still serves a valid request afterward.
            writer.write(json.dumps({"relation": "pilji", "args": [
                {"type": "number", "value": 6.0},
                {"type": "number", "value": 2.0},
                {"type": "number", "value": 3.0},
            ]}) + "\n")
            writer.flush()
            resp = json.loads(reader.readline())
            self.assertTrue(resp["result"])
        finally:
            sock.close()

    def test_bounded_pool_concurrency(self):
        """~40 concurrent single-request connections (> the default 32 workers)
        must all complete correctly — the bounded pool cycles workers as
        connections close, so no deadlock and no dropped requests."""
        results = {}
        errors = []

        def worker(i):
            try:
                resp = send_request({"relation": "pilji", "args": [
                    {"type": "number", "value": 6.0},
                    {"type": "number", "value": 2.0},
                    {"type": "number", "value": 3.0},
                ]})
                results[i] = resp.get("result")
            except Exception as e:
                errors.append((i, str(e)))

        threads = [threading.Thread(target=worker, args=(i,)) for i in range(40)]
        for t in threads:
            t.start()
        for t in threads:
            t.join(timeout=10)

        self.assertEqual(errors, [], f"no connection should error: {errors}")
        self.assertEqual(len(results), 40, "all 40 requests completed")
        self.assertTrue(all(results.values()), "all pilji(6,2,3) results are True")


if __name__ == "__main__":
    unittest.main()
