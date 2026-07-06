# Vendored: ilmentufa camxes (standard grammar)

- **Source:** https://github.com/lojban/ilmentufa
- **Pinned commit:** `778ea138f7d150121ca722db7536ce3b123943ac`
- **Vendored files:**
  - `camxes.js` — the STANDARD-grammar parser (PEG.js 0.8.0 output). Exposes a
    browser global `camxes` (`camxes.parse(text)` → tree, or throws
    `camxes.SyntaxError` with flat `.message`/`.line`/`.column`).
  - `camxes_preproc.js` — the preprocessor. Exposes a browser global function
    `camxes_preprocessing(text)`. `run_camxes.js` always runs this before parse,
    so we do too.
  - `camxes_shim.js` — hand-written (this repo). Defines `window.camxes_validate`.
  - `LICENSE` — MIT (ilmentufa; camxes.js © Masato Hagiwara). See repo `NOTICE`.
- **Variant:** standard only — NOT `camxes-beta` / `-cbm` / `-ckt` / `-exp` / `-morpho`.
- **Same pin as** the flake's `ilmentufa` input (`NIBLI_CAMXES_DIR`) that
  `nibli-verify`'s `verify-parser` gate drives via node — one grammar source of truth.
- **Refresh:** re-copy from `$NIBLI_CAMXES_DIR/{camxes.js,camxes_preproc.js,LICENSE}`
  inside the Nix dev shell if the flake pin changes.

Do not edit `camxes.js` / `camxes_preproc.js` — they are generated/upstream. Only
`camxes_shim.js` is ours.
