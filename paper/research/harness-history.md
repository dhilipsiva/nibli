# Harness validation before protocol freeze

These corrections were made to research tooling before the successful pilot
and frozen collection. None changed engine algorithms or interfaces. These
preflight attempts are not counted as measured runs or verification passes.

1. The initial Soufflé hand case used `cat` as a relation name, colliding with
   a built-in. The adapter now prefixes every relation with `p_`. A translation
   test pins this behavior and the hand-derived negation cases pass all engines.
2. Waiting with `Popen.wait(timeout=...)` introduced polling delays that biased
   millisecond whole-process timings. The final wrapper uses blocking
   `communicate()` and an independent GNU `timeout` process for the deadline.
3. Clippy initially followed dependencies and reported existing warnings
   outside the private benchmark. The final check uses the repository's
   `--no-deps` convention and treats warnings in the new binary as errors.
4. A missing-tool detector initially matched the word `skipped` inside passing
   test names. It now excludes `test ...` result lines and uses word boundaries
   for actual skip messages. Required tool presence is checked before the suite.
5. The measurement wrapper's quiet environment suppressed a host transcript
   expected by a smoke test. Verification now explicitly runs with
   `NIBLI_QUIET=0`; benchmark runs retain `NIBLI_QUIET=1`.

The final `results/pilot/smoke.json` and `results/checks/checks.json` retain
successful source fingerprints and logs. Earlier attempt reports and logs are
included under their original preflight directory names in the research archive
for diagnosis; generated executables and duplicate input preparations from
those attempts are not needed to reproduce the frozen experiment.

The first official large-policy cutoffs occurred before the `load` phase
completed. They are retained as incomplete loading observations, not evidence
that generating a certificate itself exceeded the cutoff. No workload was
removed or resized in response.
