{
  # The toolchain Wiz's tests need besides Lean: GMP (the C and LLVM backends), LLVM's
  # `llc`, Boehm GC (the self-hosted backend's runtime), a C compiler, and elan (which
  # installs the Lean version in `lean-toolchain`). CI runs every step in this shell
  # (`nix develop`); locally, `nix develop` gives the same environment as
  # /workspace/wiz-env.sh.
  description = "Wiz: development and CI environment";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in {
      devShells = forAll (pkgs: {
        default = pkgs.mkShell {
          packages = [ pkgs.elan pkgs.gmp pkgs.boehmgc pkgs.llvm pkgs.python3 pkgs.git ];
          # The tests and `wiz build` read the toolchain from these variables (see
          # Wiz/Compiler/Build.lean and selfhostCompileRun in Tests/Elab.lean). When they
          # become flags and a toolchain record, this is the one place to change.
          shellHook = ''
            export WIZ_CFLAGS="-I${pkgs.gmp.dev}/include"
            export WIZ_LDFLAGS="-L${pkgs.gmp}/lib -Wl,-rpath,${pkgs.gmp}/lib"
            export WIZ_LLC="${pkgs.llvm}/bin/llc"
            export WIZ_GC_CFLAGS="-I${pkgs.boehmgc.dev}/include"
            export WIZ_GC_LDFLAGS="-L${pkgs.boehmgc}/lib -Wl,-rpath,${pkgs.boehmgc}/lib -lgc -lpthread"
          '';
        };
      });
    };
}
