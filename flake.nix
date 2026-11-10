{
  # The toolchain Wiz's tests need besides Lean: GMP (the C and LLVM backends), LLVM's
  # `llc`, Boehm GC (the self-hosted backend's runtime), a C compiler, and elan (which
  # installs the Lean version in `lean-toolchain`). CI runs every step in this shell
  # (`nix develop`); locally, `nix develop` gives the same environment as
  # /workspace/wiz-env.sh, and writes grail.local.wiz for grail.
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
          # `wiz` and `grail` take the toolchain as flags (stage 23a); grail and the test
          # driver read this machine's paths from the uncommitted grail.local.wiz written
          # here (when run from the repository root). Nothing reads the environment.
          shellHook = ''
            WIZ_CFLAGS="-I${pkgs.gmp.dev}/include"
            WIZ_LDFLAGS="-L${pkgs.gmp}/lib -Wl,-rpath,${pkgs.gmp}/lib"
            WIZ_LLC="${pkgs.llvm}/bin/llc"
            WIZ_GC_CFLAGS="-I${pkgs.boehmgc.dev}/include"
            WIZ_GC_LDFLAGS="-L${pkgs.boehmgc}/lib -Wl,-rpath,${pkgs.boehmgc}/lib -lgc -lpthread"
            if [ -f grail.wiz ]; then
              local_wiz=$(printf '%s\n' \
                '-- This machine'"'"'s toolchain, written by the nix dev shell (flake.nix); not committed.' \
                'import Grail' \
                'def settings : Settings := Settings.empty' \
                "  |> Settings.set \"cflags\" \"$WIZ_CFLAGS\"" \
                "  |> Settings.set \"ldflags\" \"$WIZ_LDFLAGS\"" \
                "  |> Settings.set \"llc\" \"$WIZ_LLC\"" \
                "  |> Settings.set \"gc-cflags\" \"$WIZ_GC_CFLAGS\"" \
                "  |> Settings.set \"gc-ldflags\" \"$WIZ_GC_LDFLAGS\"")
              [ "$(cat grail.local.wiz 2>/dev/null)" = "$local_wiz" ] || printf '%s\n' "$local_wiz" > grail.local.wiz
            fi
          '';
        };
      });
    };
}
