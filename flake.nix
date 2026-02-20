{
  description = "Lojban Neuro-Symbolic Engine Development Environment";

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

        # Inject the absolute latest stable compiler, forcing the WASI Preview 2 target
        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "rust-analyzer" ];
          targets = [ "wasm32-wasip1" "wasm32-wasip2" "wasm32-unknown-unknown" ];
        };
      in
      {
        devShells.default = pkgs.mkShell {

          buildInputs = with pkgs; [
            # Core Compiler
            rustToolchain
            just

            # WASI Preview 2 / Component Model Tooling
            wasm-tools          # Low-level WASM/WIT manipulation
            cargo-component     # Builds Rust crates as WASI components
            wit-bindgen         # Generates bindings from .wit files
            wasmtime            # Executes the compiled WASI components
            wac-cli

            # Helix Editor Ecosystem
            taplo               # TOML Language Server
            marksman            # Markdown Language Server
            lldb                # Debugger

            # Native build dependencies
            pkg-config
            openssl
          ];
          shellHook = ''
            echo "=================================================="
            echo " Lojban NeSy Engine - Nix Dev Environment Loaded  "
            echo "=================================================="
            rustc --version
            echo "Target 'wasm32-wasip2' is active."
          '';
        };
      }
    );
}
