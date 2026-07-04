# Compat-mode suite — nixpkgs `lib.types` on the byte-mode engine (the supported escape hatch).
#
# gen-merge's `(loc, defs)` dispatch (`mergeDefs` calls `type.merge loc defs` when a `.merge` exists;
# a nixpkgs type carries no `.verify`, so gen-merge's post-merge verify is skipped) is exactly the
# contract a nixpkgs `mkOptionType` satisfies — and nixpkgs' property tags (`_type =
# "override"/"merge"/"if"`, with the same `priority`/`content`/`contents`/`condition` fields) are
# byte-compatible with gen-merge's priority pass (lib/priority.nix). So `import ../lib` with
# `types = nixpkgsLib.types` yields a `genMergeCompat` engine that runs UNMODIFIED nixpkgs types.
#
# nixpkgs enters here as an INJECTED VALUE (specialArgs), never a `lib/` dependency (purity.nix); the
# one-way boundary is deliberate — nixpkgs types plug INTO the engine (they carry `.merge`), but
# gen-types checkers do NOT run inside `lib.evalModules` (they carry no `.merge`). This suite pins the
# seam: nixpkgs leaves + property constructors + structural types through `genMergeCompat`, byte-equal
# to `nixpkgsLib.evalModules` AND (where the shape is engine-agnostic) to the gen-types-typed engine,
# plus the throw-teeth that fire through a nixpkgs type's OWN merge/check path.
{
  genMerge,
  genMergeCompat,
  nixpkgsLib,
  ...
}:
let
  npLib = nixpkgsLib;
  npT = npLib.types;
  gmT = genMerge.types;

  # Constructor-parameter records (mirrors oracle.nix's `P`-parameterization): the SAME fixture
  # source runs under nixpkgs constructors (`npP`) and gen-native constructors (`gmP`). `enumT`
  # abstracts the one signature divergence — nixpkgs `enum elems` vs gen-types `enum name elems`.
  npP = {
    inherit (npLib)
      mkOption
      mkMerge
      mkIf
      mkForce
      mkDefault
      ;
    types = npT;
    enumT = npT.enum;
  };
  gmP = {
    inherit (genMerge)
      mkOption
      mkMerge
      mkIf
      mkForce
      mkDefault
      ;
    types = gmT;
    enumT = gmT.enum "e";
  };

  stripModule = c: builtins.removeAttrs c [ "_module" ];
  compatCfg = mods: stripModule (genMergeCompat.evalModuleTree { modules = mods; }).config;
  npCfg = mods: stripModule (npLib.evalModules { modules = mods; }).config;
  gmCfg = mods: stripModule (genMerge.evalModuleTree { modules = mods; }).config;

  # (a) leaf shim — nixpkgs leaf types (str/int/enum/listOf/nullOr) driven through the compat engine.
  leafFixture = P: [
    {
      options.s = P.mkOption {
        type = P.types.str;
        default = "d";
      };
      options.n = P.mkOption {
        type = P.types.int;
        default = 0;
      };
      options.e = P.mkOption {
        type = P.enumT [
          "a"
          "b"
          "c"
        ];
        default = "a";
      };
      options.xs = P.mkOption {
        type = P.types.listOf P.types.str;
        default = [ ];
      };
      options.maybe = P.mkOption {
        type = P.types.nullOr P.types.str;
        default = null;
      };
    }
    {
      s = "v";
      n = 7;
      e = "b";
      xs = [
        "x"
        "y"
      ];
      maybe = "set";
    }
    { xs = [ "z" ]; }
  ];

  # (b) property constructors — nixpkgs mkForce/mkDefault/mkIf/mkMerge discharging through the pass.
  propFixture = P: [
    {
      options.a = P.mkOption {
        type = P.types.str;
        default = "da";
      };
      options.b = P.mkOption {
        type = P.types.int;
        default = 0;
      };
    }
    { a = P.mkForce "forced"; }
    { a = P.mkDefault "weak"; }
    {
      config = P.mkMerge [
        (P.mkIf false { b = 1; })
        (P.mkIf true { b = 9; })
      ];
    }
  ];

  # (c) structural boundary — nixpkgs `attrsOf (submodule …)`, byte-equal to `lib.evalModules`. The
  # nixpkgs `submodule.merge` runs a full `lib.evalModules` per instance INSIDE gen-merge's dispatch.
  structFixture = P: [
    {
      options.hosts = P.mkOption {
        default = { };
        type = P.types.attrsOf (
          P.types.submodule (
            { name, config, ... }:
            {
              options.hostname = P.mkOption {
                type = P.types.str;
                default = name;
              };
              options.port = P.mkOption {
                type = P.types.int;
                default = 22;
              };
              options.label = P.mkOption {
                type = P.types.str;
                default = "h-" + config.hostname;
              };
            }
          )
        );
      };
    }
    {
      hosts.web.port = 80;
      hosts.db.hostname = "database";
    }
  ];

  # (d) mixed direction — gen-merge's OWN structural `attrsOf` wrapping a nixpkgs leaf `elemType`
  # (`npT.str`), byte-equal to nixpkgs `attrsOf str`. The gen-merge strategy dispatches the nixpkgs
  # leaf's `.merge` (`mergeEqualOption`); the nixpkgs leaf's `.check` is not run (no `.verify`) —
  # identical OUTPUT on a valid value.
  mixedMods = [
    {
      options.tags = genMergeCompat.mkOption {
        default = { };
        type = genMergeCompat.attrsOf npT.str;
      };
    }
    { tags.a = "x"; }
    { tags.b = "y"; }
  ];
  npMixedMods = [
    {
      options.tags = npLib.mkOption {
        default = { };
        type = npT.attrsOf npT.str;
      };
    }
    { tags.a = "x"; }
    { tags.b = "y"; }
  ];

  # (e) throw-teeth — a bad element in a nixpkgs `listOf int` must THROW through nixpkgs' OWN
  # merge/check path (`listOf.merge` → `mergeDefinitions` runs `int.check`), not silently pass.
  badListMods = [
    {
      options.xs = npLib.mkOption {
        type = npT.listOf npT.int;
        default = [ ];
      };
    }
    {
      xs = [
        1
        2
        "not-an-int"
      ];
    }
  ];
  goodListMods = [
    {
      options.xs = npLib.mkOption {
        type = npT.listOf npT.int;
        default = [ ];
      };
    }
    {
      xs = [
        1
        2
        3
      ];
    }
  ];
in
{
  flake.tests.compat = {
    # (a) leaf shim: compat == nixpkgs == gen-native (three-way byte-identity on the leaf surface).
    test-leaf-shim-compat-eq-nixpkgs = {
      expr = compatCfg (leafFixture npP) == npCfg (leafFixture npP);
      expected = true;
    };
    test-leaf-shim-compat-eq-gen-native = {
      expr = compatCfg (leafFixture npP) == gmCfg (leafFixture gmP);
      expected = true;
    };
    # discriminating values — proves the equality above is not vacuous.
    test-leaf-shim-values = {
      expr = compatCfg (leafFixture npP);
      expected = {
        s = "v";
        n = 7;
        e = "b";
        xs = [
          "z"
          "x"
          "y"
        ];
        maybe = "set";
      };
    };

    # (b) property constructors: nixpkgs mkForce/mkDefault/mkIf/mkMerge discharge identically.
    test-property-constructors-compat-eq-nixpkgs = {
      expr = compatCfg (propFixture npP) == npCfg (propFixture npP);
      expected = true;
    };
    test-property-constructors-compat-eq-gen-native = {
      expr = compatCfg (propFixture npP) == gmCfg (propFixture gmP);
      expected = true;
    };
    test-property-constructors-winners = {
      expr = compatCfg (propFixture npP);
      expected = {
        a = "forced";
        b = 9;
      };
    };

    # (c) structural boundary: nixpkgs attrsOf(submodule) byte-equal to lib.evalModules.
    test-structural-compat-eq-nixpkgs = {
      expr = compatCfg (structFixture npP) == npCfg (structFixture npP);
      expected = true;
    };
    test-structural-values = {
      expr = compatCfg (structFixture npP);
      expected = {
        hosts = {
          web = {
            hostname = "web";
            port = 80;
            label = "h-web";
          };
          db = {
            hostname = "database";
            port = 22;
            label = "h-database";
          };
        };
      };
    };

    # (d) mixed direction: gen-merge structural attrsOf over a nixpkgs leaf, byte-equal to nixpkgs.
    test-mixed-direction-compat-eq-nixpkgs = {
      expr = compatCfg mixedMods == npCfg npMixedMods;
      expected = true;
    };
    test-mixed-direction-values = {
      expr = compatCfg mixedMods;
      expected = {
        tags = {
          a = "x";
          b = "y";
        };
      };
    };

    # (e) throw-teeth: the bad element THROWS through the nixpkgs type's own check path…
    test-throw-teeth-bad-element-throws = {
      expr = (builtins.tryEval (builtins.deepSeq (compatCfg badListMods) null)).success;
      expected = false;
    };
    # …and the same shape with valid ints does NOT throw and byte-matches nixpkgs (teeth non-vacuous).
    test-throw-teeth-good-control = {
      expr = compatCfg goodListMods == npCfg goodListMods;
      expected = true;
    };
  };
}
