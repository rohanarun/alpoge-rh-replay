{
  description = "Independent replay of Alpöge's RH release — flake-managed Lean 4.33.1 + mathlib";

  inputs = {
    nixpkgs.url = "git+file:///mnt/data1/git/github.com/NixOS/nixpkgs.git";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs = { self, nixpkgs, lean4-nix }:
    let
      system = "x86_64-linux";
      rawPkgs = import nixpkgs { inherit system; };
      pkgs = import nixpkgs { inherit system; overlays = [
        (lean4-nix.readToolchainFile ./lean-toolchain)
      ]; };
    in
    {
      packages.${system}.default = pkgs.lean.lean-all;

      devShells.${system}.default = pkgs.mkShell {
        buildInputs = [ pkgs.lean.lean-all ];

        shellHook = ''
          export PATH="${pkgs.lean.lean-all}/bin:$PATH"
        '';
      };

      checks.${system}."lean-version" = pkgs.runCommand "verify-lean-version" { } ''
        ${pkgs.lean.lean-all}/bin/lean --version
      '';

      checks.${system}."lake-build" = pkgs.runCommand "verify-lake-build" { } ''
        export PATH="${pkgs.lean.lean-all}/bin:$PATH"
        cd /mnt/data1/time-2026/11-november/20/alpoge-rh-replay
        ${pkgs.lean.lean-all}/bin/lake --version
      '';
    };
}