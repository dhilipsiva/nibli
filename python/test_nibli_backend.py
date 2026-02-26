#!/usr/bin/env python3
"""Tests for the Nibli Python compute backend."""

import json
import socket
import subprocess
import sys
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


if __name__ == "__main__":
    unittest.main()
