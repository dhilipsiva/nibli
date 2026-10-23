"""Conservative source-drift check for the manually stated Horn criterion.

This is not a Nibli parser or an evaluator refinement proof. Every non-comment
line mentioning a modeled predicate must match the reviewed source, including
its derived-only lock and the consumer that reports the violation. Changes to
this small fragment require reviewing SccCriterion.lean's inductive relations.
"""

import re


MENTIONS_CRITERION = re.compile(r"\b(?:dep_edge|dep_path|neg_dep_path|unstratifiable_cycle)\b")
REVIEWED = '''
derived_only("dep_edge").
derived_only("dep_path").
derived_only("neg_dep_path").
derived_only("unstratifiable_cycle").
all $a, $b: pos_dep($a, $b) -> dep_edge($a, $b).
all $a, $b: neg_dep($a, $b) -> dep_edge($a, $b).
all $a, $b: dep_edge($a, $b) -> dep_path($a, $b).
all $a, $b, $c: dep_path($a, $b) & dep_edge($b, $c) -> dep_path($a, $c).
all $a, $b: neg_dep($a, $b) -> neg_dep_path($a, $b).
all $a, $b, $c: dep_path($a, $b) & neg_dep($b, $c) -> neg_dep_path($a, $c).
all $a, $b, $c: neg_dep_path($a, $b) & dep_edge($b, $c) -> neg_dep_path($a, $c).
all $p: neg_dep_path($p, $p) -> unstratifiable_cycle($p).
all $p, $version, $n: ast_program($p, $version) & unstratifiable_cycle($n) -> native_violation($p, $n, "stratification").
'''.strip().splitlines()


def check_checker_closure(text):
    observed = [
        " ".join(line.split()) for line in text.splitlines()
        if not line.lstrip().startswith("#") and MENTIONS_CRITERION.search(line)
    ]
    if observed != REVIEWED:
        raise ValueError("Checker closure clauses changed; review the Horn criterion model")
