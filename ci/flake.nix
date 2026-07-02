{
  inputs = {
    gen.url = "github:sini/gen";
    gen-prelude.url = "github:sini/gen-prelude";
    gen-types.url = "github:sini/gen-types";
    # nixpkgs is the CI runner's dependency (nix-unit harness, treefmt) and supplies the `lib` the
    # test modules use — including the evalModules-equivalence ORACLE's reference side (spec §3).
    # The library itself (../lib) is nixpkgs-lib-free (ci/tests/purity.nix enforces this).
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };

  outputs =
    inputs@{
      gen,
      gen-prelude,
      gen-types,
      ...
    }:
    let
      genTypes = gen-types.lib;
      genMerge = import ../lib {
        prelude = gen-prelude.lib;
        types = genTypes;
      };
    in
    gen.lib.mkCi {
      inherit inputs;
      name = "gen-merge";
      testModules = ./tests;
      specialArgs = {
        inherit genMerge genTypes;
      };
    };
}
