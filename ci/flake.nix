{
  inputs = {
    gen-harness.url = "github:sini/gen-harness";
    gen-prelude.url = "github:sini/gen-prelude";
    gen-types.url = "github:sini/gen-types";
    # nixpkgs is the CI runner's dependency (nix-unit harness, treefmt) and supplies the `lib` the
    # test modules use — including the evalModules-equivalence ORACLE's reference side (spec §3).
    # The library itself (../lib) is nixpkgs-lib-free (ci/tests/purity.nix enforces this).
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };

  outputs =
    inputs@{
      gen-harness,
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
      genLinkset = import ../lib/linkset.nix { prelude = gen-prelude.lib; };
      genMergeCore = import ../lib/modules.nix {
        prelude = gen-prelude.lib;
        priority = import ../lib/priority.nix { prelude = gen-prelude.lib; };
      };
      # The protocol boundary (lib/interface.nix) and the type VOCABULARY, on the internal seam. The
      # boundary is reached through the core rather than re-imported, so the suite reads the same
      # binding the library does; the vocabulary is imported directly for `mkType`, the gen record
      # WITHOUT its foreign expression, which is the operand every C-2 reading is taken on.
      inherit (genMergeCore) interface;
      genMergeVocab = import ../lib/types.nix {
        prelude = gen-prelude.lib;
        core = genMergeCore;
      };
      # A gen-merge instance over a CALLER-SUPPLIED leaf vocabulary. The `types` parameter is this
      # library's UNCONTROLLED input — `lib/default.nix` names a foreign vocabulary as supported — and
      # the namespace assembly has to be total over it. This is the only way a suite can reach the
      # PUBLISH path's refusal at all: `genMerge` above is built over the shipped roster, and a roster
      # that behaves cannot exercise a refusal.
      genMergeWith =
        types:
        import ../lib {
          prelude = gen-prelude.lib;
          inherit types;
        };
    in
    gen-harness.lib.mkCi {
      inherit inputs;
      name = "gen-merge";
      # `testModules` is the whole of `flake.tests`, and `flake.tests` is the whole of what the
      # batch asserter behind `checks.default` quantifies over. Cells that assert an ERROR cannot
      # live there — the asserter forces `expr` unconditionally, so a throwing `expr` crashes the
      # gate rather than failing a cell. They are therefore outside this tree by construction, on
      # their own output: `./tests-error.nix`, read by `nix-unit --flake ./ci#testsError`.
      testModules = ./tests;
      specialArgs = {
        inherit
          genMerge
          genTypes
          genMergeCompat
          nixpkgsLib
          genMergeCore
          genLinkset
          genMergeVocab
          genMergeWith
          interface
          ;
      };
      extraModules = [ ./tests-error.nix ];
    };
}
