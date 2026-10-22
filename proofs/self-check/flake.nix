{
  description = "Pinned Rust extraction environment for Nibli self-check verification";

  inputs.aeneas.url = "github:AeneasVerif/aeneas/fdebf20d78e8007bb92fc17068f17fc2e6cfbbbf";
  inputs.nixpkgs.follows = "aeneas/charon/nixpkgs";

  outputs = { self, aeneas, nixpkgs, ... }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      extraction = aeneas.packages.${system};
    in {
      packages.${system} = {
        inherit (extraction) aeneas charon;
        default = extraction.aeneas;
      };
      devShells.${system}.default = pkgs.mkShell {
        packages = [ extraction.aeneas extraction.charon pkgs.elan pkgs.python3 pkgs.just pkgs.git ];
        NIBLI_AENEAS_SOURCE = aeneas.outPath;
        NIBLI_CHARON_SOURCE = aeneas.inputs.charon.outPath;
        NIBLI_AENEAS_BIN = "${extraction.aeneas}/bin/aeneas";
        NIBLI_CHARON_BIN = "${extraction.charon}/bin/charon";
      };
    };
}
