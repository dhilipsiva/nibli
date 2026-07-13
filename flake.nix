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

        # Latest stable Rust with WASI targets (wasip2 used by cargo-component)
        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
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
        devShells.default = pkgs.mkShell {

          buildInputs = with pkgs; [
            # Core Compiler
            rustToolchain
            just

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
            # tests under node).
            nodejs

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
