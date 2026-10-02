# `_module.<x>` — THE VALUES (den-hoag-lnleu). nixpkgs declares four `_module` options; this engine
# reads `args` and `freeformType`, takes `check` and `specialArgs` at `evalModuleTree`'s door, and
# meets every other sub-key in the realizer as an ordinary config path (`moduleDefOf`). Its refusals
# are `ci/tests-error.nix`'s `refusal-messages` group; here, what a `freeformType` absorbs, what a
# declared `options._module.<x>` merges, that warm agrees with cold, and the controls that read the
# same before and after. Each expected value is nixpkgs' on the same input.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption;
  t = gm.types;

  decl = {
    options.x = mkOption { default = "dflt"; };
  };
  ff = t.lazyAttrsOf t.raw;
  reader =
    f:
    { config, ... }:
    {
      options.r = mkOption { };
      config.r = f config;
    };
  readPkgs =
    { pkgs, ... }:
    {
      options.r = mkOption { };
      config.r = pkgs;
    };
  cfgOf = modules: (evalModuleTree { inherit modules; }).config;
  # A child at `n.k`, reading its `name`, under an `apply` that rewrites it.
  readName =
    { name, ... }:
    {
      options.v = mkOption { default = name; };
    };
  renameApply.options._module.args = mkOption { apply = a: a // { name = "Q"; }; };
  childTree = modules: (evalModuleTree { inherit modules; }).type;
  nestedName =
    child:
    (cfgOf [
      {
        options.n = mkOption {
          type = t.attrsOf child;
          default = { };
        };
        config.n.k = { };
      }
    ]).n.k.v;
  names = modules: builtins.attrNames (cfgOf modules);

  # V7, V8: a base evaluation, the same set plus one edited module warm from it, and the cold control.
  warmCold =
    base: edit:
    let
      prev = evalModuleTree { modules = base; };
      warm = evalModuleTree {
        modules = base ++ [ edit ];
        warmFrom = prev;
        editedModules = [ edit ];
      };
      cold = evalModuleTree { modules = base ++ [ edit ]; };
    in
    {
      warm = warm.config.r;
      cold = cold.config.r;
      mode = warm.warmDecision.mode;
    };
in
{
  flake.tests.module-key = {
    # A `freeformType` absorbs `_module.bogus` as it absorbs any undeclared key, and a module reads
    # it back; the returned `config` stays `_module`-free.
    test-a-freeformtype-absorbs-a-module-unknown-key = {
      expr =
        let
          c = cfgOf [
            decl
            {
              config._module.bogus = 1;
              config._module.freeformType = ff;
            }
            (reader (c: c._module.bogus or "ABSENT"))
          ];
        in
        {
          inherit (c) r;
          names = builtins.attrNames c;
        };
      expected = {
        r = 1;
        names = [
          "r"
          "x"
        ];
      };
    };
    # `freeformType` under a property is pushed down, as `args` is.
    test-a-freeformtype-under-mkif-absorbs = {
      expr = names [
        decl
        { y = 1; }
        { config._module = gm.mkIf true { freeformType = ff; }; }
      ];
      expected = [
        "x"
        "y"
      ];
    };
    # A declared `options._module.foo` merges as a declared option, readable by a module, and never
    # leaks into the returned `config`.
    test-a-declared-module-sub-option-merges = {
      expr =
        (cfgOf [
          decl
          {
            options._module.foo = mkOption { };
            config._module.foo = 1;
          }
          (reader (c: c._module.foo or "ABSENT"))
        ]).r;
      expected = 1;
    };
    test-a-declared-module-sub-option-stays-out-of-the-returned-config = {
      expr = names [
        decl
        {
          options._module.foo = mkOption { };
          config._module.foo = 1;
        }
      ];
      expected = [ "x" ];
    };
    # Warm agrees with cold: an edited module adding an absorbed `_module.bogus` refuses the
    # freeform-layer reuse, and a declared `_module` leaf never splices from prev's `_module`-free
    # `config`.
    test-warm-agrees-with-cold-on-an-absorbed-module-key = {
      expr = warmCold [
        decl
        { config._module.freeformType = ff; }
        (reader (c: c._module.bogus or "ABSENT"))
      ] { config._module.bogus = 1; };
      expected = {
        warm = 1;
        cold = 1;
        mode = "warm";
      };
    };
    test-warm-agrees-with-cold-on-a-declared-module-sub-option = {
      expr = warmCold [
        decl
        {
          options._module.foo = mkOption { };
          config._module.foo = 1;
        }
        (reader (c: c._module.foo or "ABSENT"))
      ] { config.x = "edited"; };
      expected = {
        warm = 1;
        cold = 1;
        mode = "warm";
      };
    };
    # An unknown `_module.<x>` is no lint finding: both engines refuse it under `check` and absorb it
    # under a `freeformType`. Live control, same instrument: an `mkAfter` definition is one.
    test-a-module-unknown-key-is-not-a-lint-finding = {
      expr =
        let
          lint =
            m:
            gm.lint {
              modules = [
                decl
                m
              ];
            };
        in
        {
          bogus = lint { config._module.bogus = 1; };
          control = builtins.length (lint {
            config.x = gm.mkAfter "a";
          });
        };
      expected = {
        bogus = [ ];
        control = 1;
      };
    };

    # CONTROLS: what reads the same before and after.
    test-control-module-args-read = {
      expr =
        (cfgOf [
          decl
          { config._module.args.pkgs = "P"; }
          readPkgs
        ]).r;
      expected = "P";
    };
    test-control-module-args-under-mkif-read = {
      expr =
        (cfgOf [
          decl
          { config._module = gm.mkIf true { args.pkgs = "P"; }; }
          readPkgs
        ]).r;
      expected = "P";
    };
    test-control-freeformtype-absorbs = {
      expr = names [
        decl
        { y = 1; }
        { config._module.freeformType = ff; }
      ];
      expected = [
        "x"
        "y"
      ];
    };
    test-control-caller-check-false-lists-an-undeclared-key = {
      expr =
        map (u: u.path)
          (evalModuleTree {
            check = false;
            modules = [
              decl
              { y = 1; }
            ];
          }).undeclared;
      expected = [ [ "y" ] ];
    };
    test-control-empty-module-attrset = {
      expr = names [
        decl
        { config._module = { }; }
      ];
      expected = [ "x" ];
    };
    test-control-plain-module = {
      expr = names [ decl ];
      expected = [ "x" ];
    };
    # A `submodule`-typed `options._module` takes every `_module.<x>` the engine does not own, as
    # nixpkgs' submodule does once its own `_module` options are merged into it; `args` is still the
    # engine's, so both reads give nixpkgs' `[ 2 "P" ]`.
    test-a-submodule-typed-module-option-takes-the-rest = {
      expr =
        (cfgOf [
          decl
          {
            options._module = mkOption {
              type = t.submodule { options.foo = mkOption { default = 1; }; };
              default = { };
            };
            config._module.foo = 2;
            config._module.args.pkgs = "P";
          }
          (
            { config, pkgs, ... }:
            {
              options.r = mkOption { };
              config.r = [
                config._module.foo
                pkgs
              ];
            }
          )
        ]).r;
      expected = [
        2
        "P"
      ];
    };
    test-a-submodule-typed-module-option-reads-its-default = {
      expr =
        (cfgOf [
          decl
          {
            options._module = mkOption {
              type = t.submodule { options.foo = mkOption { default = 1; }; };
              default = { };
            };
          }
          (reader (c: c._module.foo))
        ]).r;
      expected = 1;
    };
    # An engine-owned `_module.<k>` re-declared where nixpkgs' `mergeOptionDecls` accepts it: its own
    # type with an `example` changes nothing, and an `apply` maps the merged value, as nixpkgs' does.
    test-an-owned-key-redeclared-with-its-own-type-changes-nothing = {
      expr =
        (cfgOf [
          decl
          {
            options._module.args = mkOption {
              type = t.lazyAttrsOf t.raw;
              example = { };
            };
            config._module.args.pkgs = "P";
          }
          readPkgs
        ]).r;
      expected = "P";
    };
    test-an-owned-key-redeclared-with-an-apply-maps-the-merged-set = {
      expr =
        (cfgOf [
          decl
          {
            options._module.args = mkOption { apply = a: a // { pkgs = "Q"; }; };
            config._module.args.pkgs = "P";
          }
          readPkgs
        ]).r;
      expected = "Q";
    };
    test-a-freeformtype-redeclared-with-an-apply-absorbs = {
      expr = names [
        decl
        { options._module.freeformType = mkOption { apply = _: ff; }; }
        { y = 1; }
      ];
      expected = [
        "x"
        "y"
      ];
    };
    # An `apply` on `args` declared inside a `submodule`-typed `_module` leaf maps the merged set, as
    # nixpkgs' does once it merges its own `_module` options into the leaf.
    test-an-owned-key-apply-inside-a-submodule-leaf-maps-the-merged-set = {
      expr =
        (cfgOf [
          decl
          {
            options._module = mkOption {
              type = t.submodule {
                options.foo = mkOption { default = 1; };
                options.args = mkOption { apply = a: a // { pkgs = "Q"; }; };
              };
              default = { };
            };
            config._module.foo = 2;
            config._module.args.pkgs = "P";
          }
          (
            { config, pkgs, ... }:
            {
              options.r = mkOption { };
              config.r = [
                config._module.foo
                pkgs
              ];
            }
          )
        ]).r;
      expected = [
        2
        "Q"
      ];
    };
    # Two modules' `apply`s on one owned key keep the later, as every redeclaration in this engine
    # right-biases a doubled field (ADR-0029's ordered fold). nixpkgs refuses the pair.
    test-two-applies-on-an-owned-key-keep-the-later = {
      expr =
        (cfgOf [
          decl
          { options._module.args = mkOption { apply = a: a // { pkgs = "Q1"; }; }; }
          {
            options._module.args = mkOption { apply = a: a // { pkgs = "Q2"; }; };
            config._module.args.pkgs = "P";
          }
          readPkgs
        ]).r;
      expected = "Q2";
    };
    # A nixpkgs `submodule` leaf is judged by nixpkgs with the engine's own declarations taking part,
    # and an untyped `apply` there merges with them, so it maps the merged set as nixpkgs' does.
    test-an-owned-key-apply-inside-a-nixpkgs-submodule-leaf-maps-the-merged-set = {
      expr =
        (cfgOf [
          decl
          {
            options._module = mkOption {
              type = nixpkgsLib.types.submodule {
                options.foo = nixpkgsLib.mkOption { default = 1; };
                options.args = nixpkgsLib.mkOption { apply = a: a // { pkgs = "Q"; }; };
              };
              default = { };
            };
            config._module.foo = 2;
            config._module.args.pkgs = "P";
          }
          (
            { config, pkgs, ... }:
            {
              options.r = mkOption { };
              config.r = [
                config._module.foo
                pkgs
              ];
            }
          )
        ]).r;
      expected = [
        2
        "Q"
      ];
    };
    # In a nested child, the set an `apply` on `_module.args` maps holds the position's `name`, and the
    # `name` its modules receive is the applied one, as in nixpkgs' `submoduleWith`: for the
    # tree-as-a-type and for `types.submodule` alike. The control reads the position without one.
    test-an-owned-key-apply-maps-a-nested-tree-child-name = {
      expr = nestedName (childTree [
        readName
        renameApply
      ]);
      expected = "Q";
    };
    test-an-owned-key-apply-maps-a-submodule-child-name = {
      expr = nestedName (
        t.submodule {
          imports = [
            readName
            renameApply
          ];
        }
      );
      expected = "Q";
    };
    test-a-nested-child-name-without-an-apply-is-the-position = {
      expr = nestedName (childTree [ readName ]);
      expected = "k";
    };
  };
}
