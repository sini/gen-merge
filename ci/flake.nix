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
      # Compat mode (ci/tests/compat-nixpkgs-types.nix): the SAME byte-mode engine with nixpkgs
      # `lib.types` injected as the leaf `types` instead of gen-types. nixpkgs enters as a VALUE here
      # (never a `lib/` dep — purity.nix); `../lib` stays nixpkgs-free. This is the supported escape
      # hatch for migration / a custom nixpkgs `mkOptionType`.
      nixpkgsLib = import "${inputs.nixpkgs}/lib";
      genMergeCompat = import ../lib {
        prelude = gen-prelude.lib;
        types = nixpkgsLib.types;
      };
      # Internal core seam (lib/modules.nix) — exposes `classifyModule` + the collection predicates that
      # are NOT on the public `lib/default.nix` surface (the lint-predicate export precedent: additive to
      # core, public surface unchanged). The classify suite unit-asserts `classifyModule` directly through
      # this test-only handle; the shipped API (`pureModule`, `evalModuleTree`) is exercised via `genMerge`.
      genMergeCore = import ../lib/modules.nix {
        prelude = gen-prelude.lib;
        priority = import ../lib/priority.nix { prelude = gen-prelude.lib; };
      };
    in
    gen.lib.mkCi {
      inherit inputs;
      name = "gen-merge";
      testModules = ./tests;
      specialArgs = {
        inherit
          genMerge
          genTypes
          genMergeCompat
          nixpkgsLib
          genMergeCore
          ;
      };
    };
}
