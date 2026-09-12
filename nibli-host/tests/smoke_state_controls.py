"""Run real host processes against one durable KB; fail closed on any mismatch."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile


binary, component = map(str, map(Path.resolve, map(Path, sys.argv[1:3])))


def run(script, database=None, *, depth=None, succeeds=True):
    env = os.environ.copy()
    for name in (
        "NIBLI_DB_PATH", "NIBLI_MAX_CHAIN_DEPTH", "NIBLI_COMPUTE_ADDR",
    ):
        env.pop(name, None)
    env.update(
        NIBLI_WASM_PATH=component, NIBLI_QUIET="0", NIBLI_STRICT="0",
        NIBLI_EXISTENTIAL_IMPORT="0", NIBLI_MATERIALIZE="1",
        NIBLI_FUEL="50000000000", NIBLI_MEMORY_MB="512",
    )
    if database:
        env["NIBLI_DB_PATH"] = str(database)
    if depth is not None:
        env["NIBLI_MAX_CHAIN_DEPTH"] = depth
    result = subprocess.run(
        [binary], input=script, text=True, capture_output=True, env=env, timeout=180,
    )
    output = result.stdout + result.stderr
    assert (result.returncode == 0) == succeeds, output
    return output


with tempfile.TemporaryDirectory(prefix="nibli-host-controls-") as directory:
    database = Path(directory) / "retained.redb"
    first = run(
        "dog(Adam).\ndog(Bob).\n:retract 0\n:retract 1\n:facts --all\n:depth 17\n",
        database,
    )
    assert "#0 [withdrawn]: dog(Adam)." in first, first
    assert "#1 [withdrawn]: dog(Bob)." in first, first
    second = run(":facts\n:facts --all\n:depth\ndog(Carol).\n:facts --all\n", database)
    assert "[Facts] Knowledge base is empty." in second, second
    assert "#0 [withdrawn]: dog(Adam)." in second, second
    assert "#1 [withdrawn]: dog(Bob)." in second, second
    assert "[Fact #2] Asserted." in second, second
    assert "#2 [active]: dog(Carol)." in second, second
    assert "[Depth] Maximum chain depth: 10" in second, second
    third = run(":depth\n:reset\n:depth\n:facts --all\n", database, depth="23")
    assert third.count("[Depth] Maximum chain depth: 23") == 2, third
    assert "[Facts] 0 retained assertion record(s):" in third, third
    assert "[Facts] 0 retained assertion record(s):" in run(":facts --all\n", database)

    atomic = run("dog(Adam). greater(20, 15).\n:facts --all\n? dog(Adam).\n", database)
    assert "[Facts] 0 retained assertion record(s):" in atomic, atomic
    assert "[Query] FALSE" in atomic, atomic
    assert "[Fact #" not in atomic, atomic

for invalid in ("0", "-1", "+1", "1.5", "4294967296", "invalid"):
    output = run(":quit\n", depth=invalid, succeeds=False)
    assert "NIBLI_MAX_CHAIN_DEPTH:" in output, output

opacity = run(
    "person(Adam).\n"
    "entitled(every person, event { eats(some cat) }).\n"
    "? entitled(Adam, event { eats(some cat) }).\n"
    "? cat(some cat).\n"
    "? eats(some cat).\n"
    "? cat(exactly 0 cat).\n"
    "?? cat($c).\n"
    "cat(Bela).\n"
    "? cat(some cat).\n"
    "? eats(some cat).\n"
)
assert [line for line in opacity.splitlines() if line.startswith("[Query] ")] == [
    "[Query] TRUE", "[Query] FALSE", "[Query] FALSE",
    "[Query] TRUE", "[Query] TRUE", "[Query] FALSE",
], opacity
assert "[Find] No witnesses found." in opacity, opacity

print("PASS: retained records survive processes, IDs never reuse, depth/reset/config, assertion atomicity and quoted-body opacity agree")
