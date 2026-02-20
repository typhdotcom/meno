{
  description = "Meno – Lean 4 math project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            elan
            git
            curl
          ];

          shellHook = ''
            export ELAN_HOME="''${ELAN_HOME:-$HOME/.elan}"
          '';
        };
      });
}
