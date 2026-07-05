# evalModules-equivalence oracle (design spec §3) — the C1 acceptance gate.
#
# gen-merge `.config` == `lib.evalModules` `.config` (value-equality on the data spine +
# import-equivalence on a deferred leaf). nixpkgs `lib` enters ONLY here, on the oracle's REFERENCE
# side; the library (../lib) is nixpkgs-lib-free (purity.nix). Fixtures are parameterized by
# { mkOption, types, mkMerge, mkIf, mkForce, mkDefault } so both engines run the SAME source.
{ lib, genMerge, ... }:
let
  gm = genMerge;
  gmP = {
    inherit (gm)
      mkOption
      mkMerge
      mkIf
      mkForce
      mkDefault
      ;
    inherit (gm) types;
  };
  npP = {
    inherit (lib)
      mkOption
      mkMerge
      mkIf
      mkForce
      mkDefault
      ;
    inherit (lib) types;
  };

  # The parity corpus — shared with the portable-subset lint (lint.nix asserts it accepts every one).
  # Single source of truth (`_fixtures/corpus.nix`), so the lint's accept-set IS this oracle's set.
  fixtures = import ./_fixtures/corpus.nix;

  stripModule = c: builtins.removeAttrs c [ "_module" ];
  gmConfigOf = fx: (gm.evalModuleTree { modules = fx gmP; }).config;
  npConfigOf = fx: stripModule (lib.evalModules { modules = fx npP; }).config;
  byteIdentical = fx: gmConfigOf fx == npConfigOf fx;

  # deferred leaf: materialize both through nixpkgs, compare configs (pure — plain class content)
  deferredFixture = P: [
    {
      options.c = P.mkOption {
        type = P.types.deferredModule;
        default = { };
      };
    }
    {
      c = {
        x = 11;
        y = 22;
      };
    }
  ];
  materialize =
    mod:
    stripModule
      (lib.evalModules {
        modules = [
          mod
          {
            options.x = lib.mkOption { type = lib.types.int; };
            options.y = lib.mkOption { type = lib.types.int; };
          }
        ];
      }).config;

  oracleTests = lib.mapAttrs' (name: fx: {
    name = "test-${name}-byte-identical";
    value = {
      expr = byteIdentical fx;
      expected = true;
    };
  }) fixtures;
in
{
  flake.tests.oracle = oracleTests // {
    test-deferred-import-equivalent = {
      expr =
        materialize (gm.evalModuleTree { modules = deferredFixture gmP; }).config.c
        == materialize (lib.evalModules { modules = deferredFixture npP; }).config.c;
      expected = true;
    };

    # TEETH: the oracle must be able to FAIL. A non-byte-mode engine that concatenated lists in
    # FORWARD module order would produce [a b c]; nixpkgs produces [c a b]. Assert the oracle
    # discriminates that difference (else "byte-identical" is vacuous).
    test-oracle-has-teeth-list-order = {
      expr =
        [
          "a"
          "b"
          "c"
        ] == (npConfigOf (fixtures.listof-reverse)).xs;
      expected = false;
    };
    # TEETH: a wrong priority winner (dropping mkForce) would diverge; confirm the winner is force.
    test-oracle-has-teeth-priority = {
      expr =
        (npConfigOf (fixtures.typed-and-priority)).a == "forced"
        && (gmConfigOf (fixtures.typed-and-priority)).a == "forced";
      expected = true;
    };
    # TEETH: nullOr(null) must be null, not dropped/`{}`; either must pick the RIGHT branch. Confirm
    # both engines agree on the discriminating values (so the byte-identical assertion has content).
    test-oracle-has-teeth-combinators = {
      expr =
        let
          n = npConfigOf (fixtures.nullor-combinator);
          e = npConfigOf (fixtures.either-combinator);
        in
        n.unset == null && n.set == "v" && e.s == "left" && e.i == 7;
      expected = true;
    };

    # AC#3 — a leaf-vs-group collision at the SAME path (one module declares `a.b` as a leaf option,
    # another declares `a.b.c`, making `a.b` a group) must THROW in BOTH engines (nixpkgs refuses to
    # make an option the parent of sub-options; byte-mode must not silently `//`-merge).
    test-nested-leaf-vs-group-collision-both-throw = {
      expr =
        let
          fx = P: [
            { options.a.b = P.mkOption { type = P.types.int; }; }
            { options.a.b.c = P.mkOption { type = P.types.int; }; }
            { config.a.b.c = 1; }
          ];
        in
        (builtins.tryEval (builtins.deepSeq (gmConfigOf fx) null)).success == false
        && (builtins.tryEval (builtins.deepSeq (npConfigOf fx) null)).success == false;
      expected = true;
    };

    # AC#4 — an undeclared nested key (`config.a.b.z` with no `options.a.b.z`, and no freeformType)
    # must THROW in BOTH engines: the orphan/undeclared-key check applies PER GROUP LEVEL, not only
    # at the root. A naive recursion that silently drops it would diverge from nixpkgs.
    test-nested-undeclared-key-both-throw = {
      expr =
        let
          fx = P: [
            {
              options.a.b.c = P.mkOption {
                type = P.types.int;
                default = 1;
              };
            }
            { config.a.b.z = 9; }
          ];
        in
        (builtins.tryEval (builtins.deepSeq (gmConfigOf fx) null)).success == false
        && (builtins.tryEval (builtins.deepSeq (npConfigOf fx) null)).success == false;
      expected = true;
    };
  };
}
