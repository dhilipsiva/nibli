#!/usr/bin/env python3
"""
Nibli Compute Backend — Python Reference Server

A TCP server speaking JSON Lines protocol. Receives compute requests from
the Nibli runner and returns evaluation results.

Protocol (JSON Lines — one JSON object per line):

  Request:  {"relation":"exponential","args":[{"type":"number","value":8.0},{"type":"number","value":2.0},{"type":"number","value":3.0}]}
  Response: {"result":true}
  Error:    {"error":"Unknown relation: foobar"}

Usage:
  python3 python/nibli_backend.py                  # default 127.0.0.1:5555
  python3 python/nibli_backend.py --port 9000      # custom port
  python3 python/nibli_backend.py --host 0.0.0.0   # listen on all interfaces

Extend by adding entries to the HANDLERS dict.
"""

import argparse
import concurrent.futures
import json
import math
import os
import socket
import sys


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


def handle_product(args):
    """Multiplication: x1 = x2 * x3"""
    x1, x2, x3 = get_number(args[0]), get_number(args[1]), get_number(args[2])
    if None in (x1, x2, x3):
        raise ValueError("product requires 3 numeric arguments")
    return math.isclose(x1, x2 * x3)


def handle_sum(args):
    """Addition: x1 = x2 + x3"""
    x1, x2, x3 = get_number(args[0]), get_number(args[1]), get_number(args[2])
    if None in (x1, x2, x3):
        raise ValueError("sum requires 3 numeric arguments")
    return math.isclose(x1, x2 + x3)


def handle_quotient(args):
    """Division: x1 = x2 / x3"""
    x1, x2, x3 = get_number(args[0]), get_number(args[1]), get_number(args[2])
    if None in (x1, x2, x3):
        raise ValueError("quotient requires 3 numeric arguments")
    if x3 == 0:
        return False
    return math.isclose(x1, x2 / x3)


def handle_exponential(args):
    """Exponentiation: x1 = x2 ** x3"""
    x1, x2, x3 = get_number(args[0]), get_number(args[1]), get_number(args[2])
    if None in (x1, x2, x3):
        raise ValueError("exponential requires 3 numeric arguments")
    return math.isclose(x1, x2**x3)


def handle_logarithm(args):
    """Logarithm: x1 = log_x3(x2), i.e. x3^x1 = x2"""
    x1, x2, x3 = get_number(args[0]), get_number(args[1]), get_number(args[2])
    if None in (x1, x2, x3):
        raise ValueError("logarithm requires 3 numeric arguments")
    if x3 <= 0 or x3 == 1 or x2 <= 0:
        return False
    return math.isclose(x1, math.log(x2, x3))


# ── Handler registry ──

HANDLERS = {
    "product": handle_product,
    "sum": handle_sum,
    "quotient": handle_quotient,
    "exponential": handle_exponential,
    "logarithm": handle_logarithm,
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

            # Valid JSON that is not an object (e.g. `123`, `[1,2,3]`, `null`)
            # would AttributeError on `.get` below and kill the connection.
            if not isinstance(request, dict):
                writer.write(json.dumps({"error": "Request must be a JSON object"}) + "\n")
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
                except Exception as e:
                    # Catch-all per request: any handler error (a bad value, or
                    # an OverflowError from a huge-exponent exponential) becomes an
                    # error response — one bad request must never kill the
                    # connection thread (or, with the pool, leak a worker).
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

    # Bounded worker pool: a per-connection unbounded thread spawn lets a single
    # client exhaust the host's threads. Excess connections queue instead.
    max_workers = int(os.environ.get("NIBLI_BACKEND_WORKERS", "32"))
    executor = concurrent.futures.ThreadPoolExecutor(max_workers=max_workers)

    print(f"Nibli Compute Backend listening on {host}:{port}")
    print(f"Registered handlers: {', '.join(sorted(HANDLERS.keys()))}")
    print(f"Max concurrent connections: {max_workers}")
    print("Ctrl+C to stop\n")

    try:
        while True:
            conn, addr = server.accept()
            executor.submit(handle_connection, conn, addr)
    except KeyboardInterrupt:
        print("\nShutting down.")
    finally:
        executor.shutdown(wait=False)
        server.close()


def main():
    parser = argparse.ArgumentParser(description="Nibli Compute Backend — Python Reference Server")
    parser.add_argument("--host", default="127.0.0.1", help="Bind address (default: 127.0.0.1)")
    parser.add_argument("--port", type=int, default=5555, help="Listen port (default: 5555)")
    args = parser.parse_args()

    serve(args.host, args.port)


if __name__ == "__main__":
    main()
