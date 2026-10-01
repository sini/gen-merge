# `_module.<x>` — THE VALUES (den-hoag-lnleu). nixpkgs declares four `_module` options; this engine
# reads `args` and `freeformType`, takes `check` and `specialArgs` at `evalModuleTree`'s door, and
# meets every other sub-key in the realizer as an ordinary config path (`moduleDefOf`). Its refusals
# are `ci/tests-error.nix`'s `refusal-messages` group; here, what a `freeformType` absorbs, what a
# declared `options._module.<x>` merges, that warm agrees with cold, and the controls that read the
# same before and after. Each expected value is nixpkgs' on the same input.
{ genMerge, ... }:
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
  };
}
