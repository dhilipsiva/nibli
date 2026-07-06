// camxes_shim.js — a stable, synchronous bridge from Rust (js-sys) to the vendored
// ilmentufa standard-grammar parser. Loaded AFTER camxes.js (exposes global
// `camxes`) and camxes_preproc.js (exposes global function `camxes_preprocessing`).
//
// Exposes `window.camxes_validate(text)` returning a plain object:
//   { ok: true }
//   { ok: false, message, line, column }
// nibli-fanva's `gates::official_gate` reads this. The globals are resolved at
// CALL time, so <script> load order does not matter.
(function () {
  window.camxes_validate = function (text) {
    try {
      // Mirror run_camxes.js: preprocess, then parse. camxes.parse throws
      // camxes.SyntaxError (flat .message/.line/.column) on a grammar rejection.
      var pre = (typeof camxes_preprocessing === "function")
        ? camxes_preprocessing(text)
        : text;
      camxes.parse(pre);
      return { ok: true };
    } catch (e) {
      // Only a genuine grammar rejection counts as invalid; anything else
      // (a loader/engine bug) is re-thrown so the Rust side degrades gracefully
      // to the local gerna+smuni gates rather than falsely rejecting.
      if (!e || e.name !== "SyntaxError") throw e;
      var loc = (e.location && e.location.start) ? e.location.start : e;
      return {
        ok: false,
        message: (e.message != null) ? String(e.message) : String(e),
        line: loc.line || 0,
        column: loc.column || 0,
      };
    }
  };
})();
