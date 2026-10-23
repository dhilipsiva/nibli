#!/usr/bin/env python3
"""Compatibility entry point for the production verdict-algebra proof gate."""

import sys

from verify_component import audit_axioms, check_artifacts, obligations, main


if __name__ == "__main__":
    sys.exit(main("verdict_algebra"))
