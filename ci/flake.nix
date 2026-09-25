{
  inputs = {
    gen-harness.url = "github:sini/gen-harness";
    gen-prelude.url = "github:sini/gen-prelude";
    gen-types.url = "github:sini/gen-types";
    # The comparison MACHINERY (ci/tests/differential.nix). It enters on the TEST plane and not on
    # the library's, which is the same placement `nixpkgs` gets below and for the same reason: an
    # instrument the engine is measured by must not become a node in the engine's own lock. It is
    # dependency-free — its whole surface is written in `builtins` — so pinning it adds exactly one
    # node here and nothing to `../flake.nix`.
    gen-differential.url = "github:sini/gen-differential";
    # The incremental plane (ADR-0008 item 2) — see `../flake.nix`'s own comment. Pinned again here
    # because the CI flake does not follow the library flake's inputs (same precedent as
    # gen-prelude/gen-types above, each pinned independently at both layers).
    gen-memo.url = "github:sini/gen-memo";
    # The ONE universal graph evaluator (ADR-0006) — see `../flake.nix`'s own comment. Pinned again
    # here for the reason gen-prelude/gen-types/gen-memo are: the CI flake does not follow the
    # library flake's inputs, and a `../lib` constructed BY PATH reaches no flake output, so every
    # construction below has to supply `scope` itself.
    gen-scope.url = "github:sini/gen-scope";
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
      gen-differential,
      gen-memo,
      gen-scope,
      ...
    }:
    let
      # ★ ONE BINDING FOR THE SUBSTRATE, and here that is load-bearing rather than tidy. The standalone
      # -entry cell compares the ROOT `default.nix`'s applied surface against the flake's `lib` output,
      # and that comparison is only a reading of the SHIM if both sides are built over the same
      # substrate. Two separate `gen-prelude.lib` expressions would let the cell pass while comparing
      # two different builds, which is the shape of a tautology rather than a test.
      #
      # It also cannot come from the harness: `genPrelude` there is a VENDORED single function
      # (`hasInfix`), deliberately not the library, and a suite needing more supplies its own from
      # gen-prelude at its own root — which this is.
      prelude = gen-prelude.lib;
      genTypes = gen-types.lib;
      # The gen-types FLAKE itself, for the one cell asserting that passing it where its `lib` belongs
      # refuses by name (tests-error.nix, `linkset-vocabulary`).
      genTypesFlake = gen-types;
      # ADR-0008 item 2 — the ONE incremental plane. Bound once, same substrate precedent as
      # `prelude` above: every `../lib` instance this file builds shares this one `genMemo`.
      genMemo = gen-memo.lib;
      # ADR-0006 — the ONE universal graph evaluator, bound once for the same reason as `prelude`
      # and `genMemo`: every `../lib` instance this file builds drives its module-tree knot on THIS
      # value, so "one instance" is a property of this binding rather than of a convention.
      genScope = gen-scope.lib;
      genMerge = import ../lib {
        inherit prelude;
        types = genTypes;
        memo = genMemo;
        scope = genScope;
      };
      # Compat mode (ci/tests/compat-nixpkgs-types.nix): the SAME byte-mode engine with nixpkgs
      # `lib.types` injected as the leaf `types` instead of gen-types. nixpkgs enters as a VALUE here
      # (never a `lib/` dep — purity.nix); `../lib` stays nixpkgs-free. This is the supported escape
      # hatch for migration / a custom nixpkgs `mkOptionType`.
      nixpkgsLib = import "${inputs.nixpkgs}/lib";
      genMergeCompat = import ../lib {
        inherit prelude;
        types = nixpkgsLib.types;
        memo = genMemo;
        scope = genScope;
      };
      # Internal core seam (lib/modules.nix) — exposes `classifyModule` + the collection predicates that
      # are NOT on the public `lib/default.nix` surface (the lint-predicate export precedent: additive to
      # core, public surface unchanged). The classify suite unit-asserts `classifyModule` directly through
      # this test-only handle; the shipped API (`pureModule`, `evalModuleTree`) is exercised via `genMerge`.
      genLinkset = import ../lib/linkset.nix { inherit prelude; };
      genMergeCore = import ../lib/modules.nix {
        inherit prelude;
        priority = import ../lib/priority.nix { inherit prelude; };
        memo = genMemo;
        scope = genScope;
      };
      # The protocol boundary (lib/interface.nix) and the type VOCABULARY, on the internal seam. The
      # boundary is reached through the core rather than re-imported, so the suite reads the same
      # binding the library does; the vocabulary is imported directly for `mkType`, the gen record
      # WITHOUT its foreign expression, which is the operand every C-2 reading is taken on.
      inherit (genMergeCore) interface;
      genMergeVocab = import ../lib/types.nix {
        inherit prelude;
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
          inherit prelude types;
          memo = genMemo;
          scope = genScope;
        };
      # A gen-merge instance over a CALLER-SUPPLIED incremental plane (spec §3 O1 — the seam test):
      # `memo` is the other uncontrolled input `lib/default.nix` names, so a suite substituting an
      # adversarial `warmDecision` (always-dirty / always-clean) reaches gen-merge's SPLICE gate
      # through the same `../lib` entry point every other instance here uses, rather than a private
      # bypass that only exercises the substitution and not the seam.
      genMergeWithMemo =
        memo:
        import ../lib {
          inherit prelude memo;
          types = genTypes;
          scope = genScope;
        };
      # A gen-merge instance over a CALLER-SUPPLIED evaluator. `scope` is the third uncontrolled
      # input `lib/default.nix` names, and this is the only way a suite can reach its DOOR at all:
      # `genMerge` above is built over the real gen-scope, and an evaluator that answers cannot
      # exercise a refusal. Same `../lib` entry point as every other instance here, never a private
      # bypass that would exercise the door's reason function without exercising the door.
      genMergeWithScope =
        scope:
        import ../lib {
          inherit prelude scope;
          types = genTypes;
          memo = genMemo;
        };
      # The comparison machinery, bound once so the differential suite and any later consumer read
      # the same instrument. `lib` (nixpkgs, harness-supplied) is the REFERENCE side there, exactly
      # as it is for the equivalence oracle — the two instruments assert over one reference by
      # construction rather than by two files agreeing about which nixpkgs they meant.
      differential = gen-differential.lib;
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
          prelude
          genMergeCompat
          nixpkgsLib
          genMergeCore
          genLinkset
          genMergeVocab
          genMergeWith
          genMergeWithMemo
          genMergeWithScope
          genMemo
          genTypesFlake
          genScope
          interface
          differential
          ;
      };
      extraModules = [
        ./tests-error.nix
        # The per-process cells: verdicts that are PROCESS EXITS (uncatchable aborts), one
        # fixture per evaluator process. Exposed as `apps.<system>.tests-process` and run by
        # `ci --tests-process` under the column's evaluator, never as a sandboxed check.
        ./tests-process.nix
      ];
    };
}
