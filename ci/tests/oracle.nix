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

  fixtures = {
    typed-and-priority = P: [
      {
        options.a = P.mkOption {
          type = P.types.str;
          default = "da";
        };
      }
      {
        options.b = P.mkOption {
          type = P.types.int;
          default = 0;
        };
      }
      {
        a = P.mkForce "forced";
        b = 7;
      }
      { a = P.mkDefault "weak"; }
    ];
    freeform = P: [
      {
        freeformType = P.types.lazyAttrsOf P.types.str;
        options.known = P.mkOption {
          type = P.types.str;
          default = "k";
        };
      }
      {
        known = "K";
        extra1 = "e1";
      }
      { extra2 = "e2"; }
    ];
    submodule-name-selfref = P: [
      {
        options.entries = P.mkOption {
          default = { };
          type = P.types.attrsOf (
            P.types.submodule (
              { name, config, ... }:
              {
                config._module.args.self = config;
                options.n = P.mkOption {
                  type = P.types.str;
                  default = name;
                };
                options.label = P.mkOption {
                  type = P.types.str;
                  default = "L-" + config.n;
                };
              }
            )
          );
        };
      }
      {
        entries.foo = { };
        entries.bar = {
          n = "custom";
        };
      }
    ];
    listof-reverse = P: [
      {
        options.xs = P.mkOption {
          type = P.types.listOf P.types.str;
          default = [ ];
        };
      }
      {
        xs = [
          "a"
          "b"
        ];
      }
      { xs = [ "c" ]; }
    ];
    nested-submodule = P: [
      {
        options.outer = P.mkOption {
          default = { };
          type = P.types.submodule {
            options.inner = P.mkOption {
              default = { };
              type = P.types.submodule {
                options.v = P.mkOption {
                  type = P.types.int;
                  default = 1;
                };
              };
            };
          };
        };
      }
      { outer.inner.v = 42; }
    ];
    mkif-mkmerge = P: [
      {
        options.a = P.mkOption {
          type = P.types.str;
          default = "d";
        };
      }
      {
        config = P.mkMerge [
          (P.mkIf false { a = "no"; })
          (P.mkIf true { a = "yes"; })
        ];
      }
    ];
    # merge-aware combinators — byte-identical to nixpkgs `lib.types.{nullOr,either,oneOf}`.
    nullor-combinator = P: [
      {
        options.unset = P.mkOption {
          type = P.types.nullOr P.types.str;
          default = null;
        };
        options.set = P.mkOption {
          type = P.types.nullOr P.types.str;
          default = null;
        };
        options.nested = P.mkOption {
          type = P.types.nullOr (P.types.listOf P.types.int);
          default = null;
        };
      }
      {
        set = "v";
        nested = [
          1
          2
        ];
      }
    ];
    either-combinator = P: [
      {
        options.s = P.mkOption { type = P.types.either P.types.str P.types.int; };
        options.i = P.mkOption { type = P.types.either P.types.str P.types.int; };
      }
      {
        s = "left";
        i = 7;
      }
    ];
    oneof-combinator = P: [
      {
        options.v = P.mkOption {
          type = P.types.oneOf [
            P.types.str
            P.types.int
            P.types.bool
          ];
        };
      }
      { v = true; }
    ];
    # nested/structured option-declaration paths — `options.a.b.c = mkOption {…}` must build a
    # nested option TREE (nixpkgs `lib.evalModules` auto-nests), so `config.a.b.c` resolves and a
    # SECOND module's `options.a.b.d` merges by RECURSING beside the first (not `//`-clobbering `b`).
    # This is the prerequisite for composing den-shaped configs (`options.den.schema/hosts/classes`).
    nested-options = P: [
      {
        options.a.b.c = P.mkOption {
          type = P.types.int;
          default = 1;
        };
      }
      { config.a.b.c = 7; }
      {
        options.a.b.d = P.mkOption {
          type = P.types.str;
          default = "x";
        };
      }
    ];
    # the real gen-aspects `aspectSubmodule` shape: keyed collection of submodules, each with a
    # self-referential `config._module.args.aspect = config`, structural options (name / includes as
    # listOf), AND a freeform of nested string keys — the integrated C2 surface, byte-identical.
    aspect-shaped = P: [
      {
        options.aspects = P.mkOption {
          default = { };
          type = P.types.attrsOf (
            P.types.submodule (
              {
                name,
                config,
                aspect,
                ...
              }:
              {
                config._module.args.aspect = config;
                freeformType = P.types.lazyAttrsOf P.types.str;
                options.name = P.mkOption {
                  type = P.types.str;
                  default = name;
                };
                options.includes = P.mkOption {
                  type = P.types.listOf P.types.str;
                  default = [ ];
                };
                # reads the self-ref module ARG `aspect` (= config), proving the fixpoint binding
                options.selfName = P.mkOption {
                  type = P.types.str;
                  default = aspect.name;
                };
              }
            )
          );
        };
      }
      {
        aspects.web = {
          includes = [ "base" ];
          extra = "x";
        };
        aspects.db.includes = [
          "base"
          "pg"
        ];
      }
    ];
  };

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
