//! Doc-fence gate: every statement inside a ```nibli-kr fence — in the mdBook
//! tutorial docs AND in the repo-root specs — must compile through the SHIPPED
//! front-end, the same `NibliEngine::assert_text` path as the REPL's `:load`
//! and `nibli-validate`.
//!
//! Why here and not in the `docs` CI job: that job is Nix + `mdbook build`
//! with no Rust toolchain at all (~2 min), and the standing deferral ("keep
//! the docs job free of a full cargo build") protects exactly that lightness.
//! `just ci` already compiles the workspace, so this rides along for free.
//!
//! Why `nibli-verify`: it is `publish = false` (so reaching outside the
//! package dir has no packaging consequence), it already depends on
//! nibli-engine, and `ci` already builds it for `verify-nibli-kr-seam`.
//!
//! SCOPE — the boundary is COMPILABLE EXAMPLE vs. METASYNTAX, carried by the
//! info string, NOT tutorial vs. specification. The root specs were out of
//! scope at first on the theory that a spec is "red by construction"; the
//! failures turned out to be exactly two categories, both of them MISLABELS:
//! notation (`pred(term, term, …)`) and NIBLI_KR §14's `pred` declarations,
//! which are an explicit v2 feature and a compile error today. Tagging either
//! ```nibli-kr claims it compiles. Both now live in ```text fences, and every
//! remaining ```nibli-kr fence in the spec is checked like any other.

use std::fs;
use std::path::{Path, PathBuf};

use nibli_engine::NibliEngine;

/// The two scan roots, resolved from the manifest dir so the test is
/// CWD-independent.
const MDBOOK_SRC: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../mdbook/src");
const REPO_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/..");

const FENCE_LANG: &str = "nibli-kr";

/// Coverage floors, PER ROOT. A path typo or a broken scanner must fail LOUDLY
/// rather than pass by checking nothing (the discipline `nibli-ui`'s
/// `shipped_examples_compile` floor established), and one floor spanning both
/// roots would let a collapse in either hide behind the other's count. Set
/// just under today's 22/6 (mdBook) and 32/1 (root) so ordinary doc edits
/// never touch this file.
const MIN_MDBOOK_STATEMENTS: usize = 20;
const MIN_MDBOOK_FILES: usize = 5;
const MIN_ROOT_STATEMENTS: usize = 25;
const MIN_ROOT_FILES: usize = 1;

struct Stmt {
    file: String,
    line: usize,
    /// Fence ordinal within the file — statements in one fence share a KB.
    fence: usize,
    text: String,
}

/// `(fence_char, run_length, remainder)` when `t` opens with 3+ ` or ~.
fn fence_run(t: &str) -> Option<(char, usize, &str)> {
    let ch = t.chars().next()?;
    if ch != '`' && ch != '~' {
        return None;
    }
    let n = t.chars().take_while(|&c| c == ch).count();
    // ` and ~ are one byte each, so the char count is also the byte offset.
    if n < 3 { None } else { Some((ch, n, &t[n..])) }
}

/// CommonMark-shaped fence scan.
///
/// State carries the opening fence's CHARACTER and RUN LENGTH, so (a) a fence
/// carrying an info string never closes a block, and (b) a longer outer fence
/// may legally contain a shorter inner one. A plain `^```(\w*)$` regex once
/// inverted fence state on the hyphenated `nibli-kr` tag in the book's
/// verify_book.py; this construction cannot make that mistake.
fn extract(rel: &str, src: &str) -> Vec<Stmt> {
    let mut out = Vec::new();
    let mut open: Option<(char, usize, bool)> = None;
    let mut fence_no = 0usize;

    for (i, raw) in src.lines().enumerate() {
        let t = raw.trim_start();
        let indent = raw.len() - t.len();

        match open {
            Some((ch, len, is_kr)) => {
                if let Some((fch, flen, rest)) = fence_run(t)
                    && fch == ch
                    && flen >= len
                    && rest.trim().is_empty()
                {
                    open = None;
                    continue;
                }
                if !is_kr {
                    continue;
                }
                let s = raw.trim();
                // Blank lines and whole-line `#` comments are corpus
                // convention, not statements (the same skip the .nibli
                // corpora and nibli-ui's guard use). A TRAILING `#` comment
                // stays attached — it is legal KR and must compile.
                if s.is_empty() || s.starts_with('#') {
                    continue;
                }
                out.push(Stmt {
                    file: rel.to_string(),
                    line: i + 1,
                    fence: fence_no,
                    text: s.to_string(),
                });
            }
            None => {
                // 4+ spaces of indent is an indented code block, not a fence.
                if indent > 3 {
                    continue;
                }
                if let Some((fch, flen, rest)) = fence_run(t) {
                    let lang = rest
                        .trim()
                        .split_whitespace()
                        .next()
                        .unwrap_or("")
                        .to_ascii_lowercase();
                    if lang == FENCE_LANG {
                        fence_no += 1;
                    }
                    open = Some((fch, flen, lang == FENCE_LANG));
                }
            }
        }
    }

    assert!(
        open.is_none(),
        "{rel}: unterminated code fence — everything after it is swallowed, \
         so any ```{FENCE_LANG} fence below it is silently unchecked"
    );
    out
}

fn markdown_files(dir: &Path, recurse: bool, out: &mut Vec<PathBuf>) {
    let rd = fs::read_dir(dir).unwrap_or_else(|e| {
        panic!(
            "cannot read {}: {e} — did the scan root move?",
            dir.display()
        )
    });
    let mut paths: Vec<PathBuf> = rd.map(|e| e.unwrap().path()).collect();
    paths.sort(); // deterministic report order
    for p in paths {
        if p.is_dir() {
            if recurse {
                markdown_files(&p, recurse, out);
            }
        } else if p.extension().is_some_and(|e| e == "md") {
            out.push(p);
        }
    }
}

/// Collect every ```nibli-kr statement under one scan root.
///
/// Returns `(statements, files_that_had_at_least_one_fence)`.
///
/// `recurse` is a CORRECTNESS constraint at the repo root, not a speed knob:
/// descending from there would reach `book/` — the private Orange AVA
/// manuscript, which the docs may never import — and `mdbook/book/`, the
/// generated HTML. Keep the root walk flat.
fn scan(root: &str, prefix: &str, recurse: bool) -> (Vec<Stmt>, usize) {
    let root = Path::new(root);
    let mut files = Vec::new();
    markdown_files(root, recurse, &mut files);

    let mut statements = Vec::new();
    let mut files_with_fences = 0usize;
    for path in &files {
        let rel = format!("{prefix}{}", path.strip_prefix(root).unwrap().display());
        let stmts = extract(&rel, &fs::read_to_string(path).unwrap());
        if !stmts.is_empty() {
            files_with_fences += 1;
        }
        statements.extend(stmts);
    }
    (statements, files_with_fences)
}

#[test]
fn kr_doc_fences_compile() {
    // mdBook recurses (a book is a tree); the repo root does NOT — see `scan`.
    let (mdbook_stmts, mdbook_files) = scan(MDBOOK_SRC, "mdbook/src/", true);
    let (root_stmts, root_files) = scan(REPO_ROOT, "", false);

    let (mdbook_n, root_n) = (mdbook_stmts.len(), root_stmts.len());
    let mut statements = mdbook_stmts;
    statements.extend(root_stmts);

    // One KB per FENCE: a fence is what a reader pastes into `:load`, so its
    // lines are asserted CUMULATIVELY (this also catches a pair of lines that
    // are individually fine but jointly unstratifiable). reset() between
    // fences keeps every failure attributable to one fence.
    let engine = NibliEngine::new();
    let mut current: Option<(String, usize)> = None;
    let mut failures: Vec<String> = Vec::new();

    for st in &statements {
        let key = (st.file.clone(), st.fence);
        if current.as_ref() != Some(&key) {
            engine
                .reset()
                .expect("reset between independent doc fences");
            current = Some(key);
        }
        if let Err(e) = engine.assert_text(&st.text) {
            failures.push(format!(
                "  {}:{}\n      {}\n      -> {e}",
                st.file, st.line, st.text
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "{} statement(s) in ```{FENCE_LANG} fences do not compile:\n\n{}\n\n\
         Every line in a ```{FENCE_LANG} fence must be ONE complete statement \
         that compiles through the shipped front-end. `:load` and \
         nibli-validate are both line-oriented, so a statement wrapped across \
         lines is a doc bug even when the joined text would parse. Prose \
         examples, REPL transcripts, output, and pseudo-syntax belong in a \
         ```text fence.",
        failures.len(),
        failures.join("\n"),
    );

    assert!(
        mdbook_n >= MIN_MDBOOK_STATEMENTS && mdbook_files >= MIN_MDBOOK_FILES,
        "doc-fence coverage collapsed under mdbook/src: {mdbook_n} statement(s) \
         across {mdbook_files} file(s) (floor {MIN_MDBOOK_STATEMENTS}/\
         {MIN_MDBOOK_FILES}) — the scanner or the path is broken, not the docs",
    );
    assert!(
        root_n >= MIN_ROOT_STATEMENTS && root_files >= MIN_ROOT_FILES,
        "doc-fence coverage collapsed at the repo root: {root_n} statement(s) \
         across {root_files} file(s) (floor {MIN_ROOT_STATEMENTS}/\
         {MIN_ROOT_FILES}) — the scanner or the path is broken, not the docs",
    );
}
