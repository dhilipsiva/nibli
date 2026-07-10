# Vendored: Predilex (thesaurus of predicates)

- **Source:** https://github.com/Ntsekees/Predilex
- **Pinned commit:** `3dab1796fd15370e9a40bb25c9854f529e05a737`
- **Retrieved:** 2026-07-10
- **License:** CC0 1.0 Universal (public-domain dedication; upstream
  `LICENSE.md`). No attribution required — this file is a courtesy provenance
  record. A stanza also lives in the repo-root `NOTICE`.
- **Vendored files:**
  - `Lojban.csv` — VERBATIM upstream `conlangs/Lojban.csv` (1 header +
    459 data rows, 14 columns). Maps Lojban lemmas to language-neutral
    sememes, with Supertype frames and optional slot-permutation tokens.
  - `predilex-arity.csv` — a PROJECTION of upstream `predilex.csv` (repo
    root, ~10k sememes) down to the `id,arity` columns (9,995 data rows).
    NOT verbatim — regenerate with the command below.
- **Consumed by:** `nibli-verify/src/predilex.rs` (`include_str!`), which
  feeds the `verify-dict` gate (`nibli-verify/tests/predilex_differential.rs`,
  `just verify-dict`, part of `ci`).

## Refresh (re-pin)

Both files MUST come from the SAME commit — sememe ids drift across upstream
commits. From the repo root, with `$SHA` set to the new pin:

```bash
curl -sfL https://raw.githubusercontent.com/Ntsekees/Predilex/$SHA/conlangs/Lojban.csv \
  -o nibli-verify/vendor/predilex/Lojban.csv
curl -sfL https://raw.githubusercontent.com/Ntsekees/Predilex/$SHA/predilex.csv \
  -o /tmp/predilex-master.csv
/usr/bin/python3 - <<'EOF'
import csv
with open('/tmp/predilex-master.csv', newline='', encoding='utf-8') as f:
    rows = list(csv.reader(f))
data = rows[2:]  # the master file has TWO header rows (short + long names)
arities = {r[0]: r[3] for r in data if len(r) >= 4 and r[0]}
with open('nibli-verify/vendor/predilex/predilex-arity.csv', 'w', newline='',
          encoding='utf-8') as f:
    w = csv.writer(f, lineterminator='\n')
    w.writerow(['id', 'arity'])
    for k in sorted(arities):
        w.writerow([k, arities[k]])
EOF
```

Then update the pinned commit here + in `NOTICE`, and re-run
`just verify-dict` against a FULL dictionary build (`just fetch-dict`) — a
re-pin can shift the gate's tallies, floors, and the `KNOWN_UNDERCOUNTS`
allowlist (its still-undercounting invariant will flag stale entries).

Do not edit `Lojban.csv` (verbatim upstream). `predilex-arity.csv` is
generated — regenerate, never hand-edit.
