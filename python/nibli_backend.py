#!/usr/bin/env python3
"""
Nibli Compute Backend — Python Reference Server

A TCP server speaking JSON Lines protocol. Receives compute requests from
the Nibli runner and returns evaluation results.

Protocol (JSON Lines — one JSON object per line):

  Request:  {"relation":"tenfa","args":[{"type":"number","value":8.0},{"type":"number","value":2.0},{"type":"number","value":3.0}]}
  Response: {"result":true}
  Error:    {"error":"Unknown relation: foobar"}

Usage:
  python3 python/nibli_backend.py                  # default 127.0.0.1:5555
  python3 python/nibli_backend.py --port 9000      # custom port
  python3 python/nibli_backend.py --host 0.0.0.0   # listen on all interfaces

Extend by adding entries to the HANDLERS dict.
"""

import argparse
import json
import math
import socket
import sys
import threading


# ── Argument extraction helpers ──


def get_number(arg):
    """Extract a numeric value from a compute arg dict. Returns None if not a number."""
    if arg.get("type") == "number":
        return arg.get("value")
    return None


def get_string(arg):
    """Extract a string value from a compute arg dict (variable/constant/description)."""
    if arg.get("type") in ("variable", "constant", "description"):
        return arg.get("value")
    return None


# ── Built-in compute handlers ──
# Each handler receives `args` (list of arg dicts) and returns a bool.
# Raise ValueError for bad inputs.


def handle_pilji(args):
    """Multiplication: x1 = x2 * x3"""
    x1, x2, x3 = get_number(args[0]), get_number(args[1]), get_number(args[2])
    if None in (x1, x2, x3):
        raise ValueError("pilji requires 3 numeric arguments")
    return math.isclose(x1, x2 * x3)


def handle_sumji(args):
    """Addition: x1 = x2 + x3"""
    x1, x2, x3 = get_number(args[0]), get_number(args[1]), get_number(args[2])
    if None in (x1, x2, x3):
        raise ValueError("sumji requires 3 numeric arguments")
    return math.isclose(x1, x2 + x3)


def handle_dilcu(args):
    """Division: x1 = x2 / x3"""
    x1, x2, x3 = get_number(args[0]), get_number(args[1]), get_number(args[2])
    if None in (x1, x2, x3):
        raise ValueError("dilcu requires 3 numeric arguments")
    if x3 == 0:
        return False
    return math.isclose(x1, x2 / x3)


def handle_tenfa(args):
    """Exponentiation: x1 = x2 ** x3"""
    x1, x2, x3 = get_number(args[0]), get_number(args[1]), get_number(args[2])
    if None in (x1, x2, x3):
        raise ValueError("tenfa requires 3 numeric arguments")
    return math.isclose(x1, x2**x3)


def handle_dugri(args):
    """Logarithm: x1 = log_x3(x2), i.e. x3^x1 = x2"""
    x1, x2, x3 = get_number(args[0]), get_number(args[1]), get_number(args[2])
    if None in (x1, x2, x3):
        raise ValueError("dugri requires 3 numeric arguments")
    if x3 <= 0 or x3 == 1 or x2 <= 0:
        return False
    return math.isclose(x1, math.log(x2, x3))


# ── Handler registry ──

HANDLERS = {
    "pilji": handle_pilji,
    "sumji": handle_sumji,
    "dilcu": handle_dilcu,
    "tenfa": handle_tenfa,
    "dugri": handle_dugri,
}


# ── Connection handler ──


def handle_connection(conn, addr):
    """Handle a single client connection (one JSON line per request)."""
    print(f"[+] Connection from {addr}")
    try:
        reader = conn.makefile("r", encoding="utf-8")
        writer = conn.makefile("w", encoding="utf-8")

        for line in reader:
            line = line.strip()
            if not line:
                continue

            try:
                request = json.loads(line)
            except json.JSONDecodeError as e:
                response = {"error": f"Invalid JSON: {e}"}
                writer.write(json.dumps(response) + "\n")
                writer.flush()
                continue

            relation = request.get("relation", "")
            args = request.get("args", [])

            handler = HANDLERS.get(relation)
            if handler is None:
                response = {"error": f"Unknown relation: {relation}"}
            else:
                try:
                    if len(args) < 3:
                        response = {
                            "error": f"{relation} requires at least 3 arguments, got {len(args)}"
                        }
                    else:
                        result = handler(args)
                        response = {"result": result}
                except (ValueError, TypeError, ZeroDivisionError) as e:
                    response = {"error": str(e)}

            writer.write(json.dumps(response) + "\n")
            writer.flush()

    except (ConnectionResetError, BrokenPipeError):
        pass
    finally:
        print(f"[-] Disconnected {addr}")
        conn.close()


# ── Server ──


def serve(host, port):
    """Start the TCP server."""
    server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server.bind((host, port))
    server.listen(5)

    print(f"Nibli Compute Backend listening on {host}:{port}")
    print(f"Registered handlers: {', '.join(sorted(HANDLERS.keys()))}")
    print("Ctrl+C to stop\n")

    try:
        while True:
            conn, addr = server.accept()
            t = threading.Thread(target=handle_connection, args=(conn, addr), daemon=True)
            t.start()
    except KeyboardInterrupt:
        print("\nShutting down.")
    finally:
        server.close()


def main():
    parser = argparse.ArgumentParser(description="Nibli Compute Backend — Python Reference Server")
    parser.add_argument("--host", default="127.0.0.1", help="Bind address (default: 127.0.0.1)")
    parser.add_argument("--port", type=int, default=5555, help="Listen port (default: 5555)")
    args = parser.parse_args()

    serve(args.host, args.port)


if __name__ == "__main__":
    main()
