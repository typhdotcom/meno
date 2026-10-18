{ inputs, ... }:
{
  perSystem =
    { pkgs, system, ... }:
    {
      devShells.default = pkgs.mkShell {
        # elan manages the Lean toolchain named in lean-toolchain; curl and
        # git are what it reaches for when fetching one.
        packages = [
          pkgs.curl
          pkgs.uv
          pkgs.nushell
          inputs.typh-perkeep.packages.${system}.default
          pkgs.elan
          pkgs.git
        ];

        shellHook = ''
          export PERKEEP_STATE="''${XDG_STATE_HOME:-$HOME/.local/state}/perkeep-math"
          export CAMLI_CONFIG_DIR="$PERKEEP_STATE/config"
          export PK_SERVER=http://localhost:3180
          export ELAN_HOME="''${ELAN_HOME:-$HOME/.elan}"
        '';
      };
    };
}
