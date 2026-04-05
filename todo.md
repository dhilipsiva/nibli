# Nibli — Reasoning Engine Backlog

Ordered by dependency, correctness impact, then user value.

## PENDING:

1. remove any unsafe codes. Always use 100% safe rust
2. Do a code scan to ensure things are DRY
3. Remove any unnecessary abstractions
4. Ensure that the code never panics (If it cannot be avoided, atleast ensure that it panices with enough data to debug)
