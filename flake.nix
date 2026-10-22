{
  description = "nibli - Zero-Hallucination Symbolic Reasoning Engine (dev environment)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };

        # An exact stable release with WASI targets (wasip2 used by cargo-component), equal to
        # `rust-version` in Cargo.toml. wasmtime 49 needs rustc 1.96 or later, and from 1.97 the
        # wasm32-wasip2 standard library imports wasi:clocks/monotonic-clock even for a bare
        # println!, which `just smoke-component-imports` refuses (the component's documented
        # surface has no clock): 1.96 is the release that satisfies both. Moving past it means
        # deciding that surface again. Pinned, so updating rust-overlay never moves it silently.
        rustToolchain = pkgs.rust-bin.stable."1.96.1".default.override {
          extensions = [ "rust-src" "rust-analyzer" "clippy" "rustfmt" ];
          targets = [ "wasm32-wasip1" "wasm32-wasip2" "wasm32-unknown-unknown" ];
        };

        # Pinned nightly for cargo-fuzz (libFuzzer needs nightly sanitizer-coverage
        # flags). NOT on PATH by default — stable stays the shell toolchain; the
        # fuzz recipes prefix PATH with NIBLI_NIGHTLY_BIN for their invocation only.
        # Date must predate the locked rust-overlay revision.
        nightlyFuzzToolchain = pkgs.rust-bin.nightly."2026-03-15".default;
      in
      {
        # Minimal shell for the RELEASE workflow's artifact + publish jobs
        # (`nix develop .#release`). Deliberately NOT the default shell: that
        # one carries vampire/clingo/lean4/dioxus-cli/cargo-fuzz/maturin, which
        # on aarch64-darwin risk source builds or unavailability — and
        # release.yml starts with a COLD Magic Nix Cache (the cache is
        # per-workflow), so closure size matters far more there than in ci.yml.
        # Reuses the same `rustToolchain` binding as the default shell, so every
        # released binary comes from the flake-pinned rustc on all three targets.
        # python3 is here because the release-* recipes follow release-check's
        # `python3 + tomllib` idiom.
        devShells.release = pkgs.mkShell {
          buildInputs = [ rustToolchain pkgs.just pkgs.python3 ];
        };
        devShells.lucy = pkgs.mkShell {
          nativeBuildInputs = [ rustToolchain pkgs.just pkgs.pkg-config ]
            ++ pkgs.lib.optionals pkgs.stdenv.isLinux [ pkgs.xvfb-run pkgs.xdotool pkgs.dbus ];
          buildInputs = [ pkgs.gtk4 ];
        };

        # Research artifact: inherit the engine verification environment and its
        # locked toolchain; add compiled Datalog, plotting, and PDF production.
        devShells.paper = pkgs.mkShell {
          inputsFrom = [ self.devShells.${system}.default ];
          buildInputs = with pkgs; [
            souffle
            wasm-pack
            time
            poppler-utils
            (python3.withPackages (p: [ p.matplotlib p.numpy p.pandas ]))
            (texlive.combine {
              inherit (texlive) scheme-small latexmk collection-latexrecommended
                collection-latexextra collection-fontsrecommended pgf;
            })
          ];
          SOURCE_DATE_EPOCH = "1789344000";
          PYTHONHASHSEED = "0";
          MPLBACKEND = "Agg";
          OMP_NUM_THREADS = "1";
        };

        devShells.default = pkgs.mkShell {

          buildInputs = with pkgs; [
            # Core Compiler
            rustToolchain
            just
            # Supply-chain gate (deny.toml): `cargo deny check advisories bans licenses sources`
            cargo-deny

            # WASI Component Model Tooling
            wasm-tools          # Low-level WASM/WIT manipulation
            cargo-component     # Builds Rust crates as WASI components
            wit-bindgen         # Generates bindings from .wit files
            wasmtime            # Executes the compiled WASI components
            wac-cli

            # Helix Editor Ecosystem
            taplo               # TOML Language Server
            marksman            # Markdown Language Server
            lldb                # Debugger

            # Compute Backend (Python reference server)
            python3

            # Differential-testing oracle: classical FOL prover for nibli-verify
            # (Track A soundness gate — checks the Horn/NAF-free fragment against
            # an external prover). Driven as a subprocess on TPTP FOF problems.
            vampire

            # Differential-testing oracle #2 (Track A, phase 2): ASP/Datalog solver
            # for nibli-verify's stratified negation-as-failure + closed-world
            # fragment — the semantics gap the classical prover can't cover, where
            # clingo's perfect/stable-model semantics matches nibli's. Driven as a
            # subprocess on clingo `.lp` programs (`nibli-verify --asp`).
            clingo

            # Proof assistant for the mechanized soundness proofs (Track B). The
            # `proofs/` Lean files are checked by `lean` in `just verify-proofs`.
            lean4

            # Node.js runs the wasm-pack test legs (verify-wasm-node; wasm-bindgen
            # tests under node), and wasm-pack drives them; without it the V8 leg
            # of the three-way determinism check cannot run in CI.
            nodejs
            wasm-pack

            # libFuzzer harness driver for the three fuzz targets (`just fuzz-ci`);
            # runs against the pinned nightly via NIBLI_NIGHTLY_BIN.
            cargo-fuzz

            # Mutation-testing driver for the soundness paths (`just mutants`);
            # scope + test invocation live in mutants.toml at the repo root.
            cargo-mutants

            # Native build dependencies
            pkg-config
            openssl

            # Dioxus web (dx CLI for dev server)
            dioxus-cli

            # wasm-opt for `dx build --release` (`just build-ui`): dx runs it as the
            # release optimization pass, and fails the build if it's missing.
            binaryen

            # Code-derived docs site (`just docs` / `just docs-serve` → mdbook/)
            mdbook
            # Mermaid preprocessor for the developer-guide crate map; `just docs`
            # runs `mdbook-mermaid install` so the JS assets stay ungenerated in git
            mdbook-mermaid

            # PyO3 extension for nibli-auth (`just build-auth-py`)
            maturin
          ];

          # The pinned nightly toolchain's bin dir for cargo-fuzz (see above).
          NIBLI_NIGHTLY_BIN = "${nightlyFuzzToolchain}/bin";

          shellHook = ''
            if [ -e "$HOME/.cargo/bin/cargo-component" ]; then
              echo "warning: ~/.cargo/bin/cargo-component shadows the Nix-provided one. Remove it." >&2
            fi
            rustc --version
            python3 --version
            echo "Target 'wasm32-wasip2' is active."
            export CARGO_INSTALL_ROOT="$PWD/.cargo-local"
            echo "=================================================="
            echo " nibli - Zero-Hallucination Reasoning Engine (dev) "
            echo "=================================================="
          '';
        };
      }
    );
}
