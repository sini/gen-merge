# FUNCTOR MODULES ARE APPLIED BY THEIR PUBLISHED FORMALS (den-hoag-genmerge-functor-module-application-u6lf8).
#
# A nixpkgs `setFunctionArgs`-shaped module (`{ __functor; __functionArgs; }`) is a function module
# to nixpkgs' `lib.evalModules`, which reads its formals with the functor-aware `lib.functionArgs`
# and sources each from `specialArgs` then `_module.args`. `callM` and `callD` answer it the same
# way, so a wrapped `{ myArg, ... }:` module whose `myArg` is a `_module.args` value evaluates
# rather than aborting `called without required argument`. Each parity cell states the gen-merge
# answer beside the live nixpkgs answer on the same module value.
#
# RED, evaluated at gen-merge dd18d6b (builtin readers, a functor unwrapped and applied to the base
# set): the module-application cells abort `called without required argument 'myArg'`, the
# declaration-stratum cell likewise, the lint cell reads `[ ]`, and the published-formals cell
# reads "flavour-not-passed". The pureModule and config-only cells are green on both sides.
#
# Two functor DEFINITIONS take the default law's function arm, as nixpkgs' `lib.isFunction` reads
# them (den-hoag-1ypox). RED at gen-merge 37cd511 (the builtin `isFunction` at both sites): the
# two-functor and setFunctionArgs cells read "set", the check-only cell reads
# `{ functor = true; lambda = false; }`, and the lambda-beside-a-functor cell aborts
# `conflicting definitions`.
{ genMerge, nixpkgsLib, ... }:
let
  inherit (genMerge) evalModuleTree mkOption mergeDefaultOption;
  np = nixpkgsLib;
  functor = {
    __functor = _: args: args;
    __functionArgs = {
      host = false;
    };
  };
  lam = x: x;
  # A nixpkgs `setFunctionArgs`-shaped module that names a `_module.args` formal.
  functorModule = {
    __functor = _: args: { config.out = args.flavour or "flavour-not-passed"; };
    __functionArgs = {
      flavour = false;
    };
  };
  tree =
    mods:
    (evalModuleTree { } (
      [
        { options.out = mkOption { }; }
        { config._module.args.flavour = "flavour-passed"; }
      ]
      ++ mods
    )).config.out;

  # nixpkgs `lib.setFunctionArgs f (functionArgs f)`, the wrapper a lowering puts around a module
  wrap = f: np.setFunctionArgs (args: f args) (builtins.functionArgs f);
  argsMod = {
    config._module.args.myArg = "from-module-args";
  };
  onArg = { myArg, ... }: { config.x = myArg; };
  onConfig = { config, ... }: { config.x = "config-only"; };
  gmX =
    mods:
    (evalModuleTree { } ([ { options.x = mkOption { type = genMerge.types.str; }; } ] ++ mods))
    .config.x;
  npX =
    mods:
    (np.evalModules { modules = [ { options.x = np.mkOption { type = np.types.str; }; } ] ++ mods; })
    .config.x;
  both = mods: {
    gm = gmX mods;
    np = npX mods;
  };
  declaring = { myArg, ... }: { options.y = mkOption { default = "declared"; }; };
  # Two definitions of one default-merged position, by kind: a `setFunctionArgs` wrapper is a
  # function to nixpkgs' `lib.isFunction`, so the law takes its function arm (den-hoag-1ypox).
  one = x: [ x ];
  two = x: [ (x + 1) ];
  defsOf =
    vs:
    map (v: {
      file = "/t/d.nix";
      value = v;
    }) vs;
  sfaPair = defsOf [
    (np.setFunctionArgs one { })
    (np.setFunctionArgs two { })
  ];
  mixPair = defsOf [
    one
    (np.setFunctionArgs two { })
  ];
  sharedFunctor = np.setFunctionArgs one { };
  checkOnly =
    vs:
    builtins.tryEval
      (evalModuleTree { } (
        [
          {
            options.x = mkOption {
              type = genMerge.mkOptionType {
                name = "t";
                check = _: true;
              };
            };
          }
        ]
        ++ map (v: { x = v; }) vs
      )).config.x;
in
{
  flake.tests.functor-readers = {
    test-two-functor-defs-merge-as-functions = {
      expr = builtins.typeOf (
        mergeDefaultOption
          [ "x" ]
          [
            {
              file = "a";
              value = functor;
            }
            {
              file = "b";
              value = functor;
            }
          ]
      );
      expected = "lambda";
    };
    test-setfunctionargs-defs-take-the-function-arm-nixpkgs-takes = {
      expr = {
        gm = builtins.typeOf (mergeDefaultOption [ "x" ] sfaPair);
        np = builtins.typeOf (np.mergeDefaultOption [ "x" ] sfaPair);
        applied = mergeDefaultOption [ "x" ] sfaPair 1;
      };
      expected = {
        gm = "lambda";
        np = "lambda";
        applied = [
          1
          2
        ];
      };
    };
    test-a-lambda-beside-a-functor-merges-as-functions = {
      expr = mergeDefaultOption [ "x" ] mixPair 1;
      expected = [
        1
        2
      ];
    };
    test-control-a-functor-beside-an-attrset-merges-as-attrsets = {
      expr = {
        gm = builtins.attrNames (
          mergeDefaultOption [ "x" ] (defsOf [
            sharedFunctor
            { b = 2; }
          ])
        );
        np = builtins.attrNames (
          np.mergeDefaultOption [ "x" ] (defsOf [
            sharedFunctor
            { b = 2; }
          ])
        );
      };
      expected = {
        gm = [
          "__functionArgs"
          "__functor"
          "b"
        ];
        np = [
          "__functionArgs"
          "__functor"
          "b"
        ];
      };
    };
    test-check-only-type-refuses-one-functor-defined-twice-as-it-refuses-a-lambda = {
      expr = {
        functor =
          (checkOnly [
            sharedFunctor
            sharedFunctor
          ]).success;
        lambda =
          (checkOnly [
            one
            one
          ]).success;
      };
      expected = {
        functor = false;
        lambda = false;
      };
    };
    test-control-two-lambda-defs-merge-as-functions = {
      expr = builtins.typeOf (
        mergeDefaultOption
          [ "x" ]
          [
            {
              file = "a";
              value = lam;
            }
            {
              file = "b";
              value = lam;
            }
          ]
      );
      expected = "lambda";
    };
    test-functor-module-is-applied-by-its-published-formals = {
      expr = tree [ functorModule ];
      expected = "flavour-passed";
    };
    test-control-lambda-module-reads-its-formal = {
      expr = tree [ ({ flavour, ... }: { config.out = flavour; }) ];
      expected = "flavour-passed";
    };
    test-a-wrapped-module-args-formal-matches-nixpkgs = {
      expr = both [
        argsMod
        (wrap onArg)
      ];
      expected = {
        gm = "from-module-args";
        np = "from-module-args";
      };
    };
    test-control-the-unwrapped-module-args-formal-matches-nixpkgs = {
      expr = both [
        argsMod
        onArg
      ];
      expected = {
        gm = "from-module-args";
        np = "from-module-args";
      };
    };
    test-control-a-wrapped-config-formal-matches-nixpkgs = {
      expr = both [ (wrap onConfig) ];
      expected = {
        gm = "config-only";
        np = "config-only";
      };
    };
    test-control-a-pure-module-wrapper-reads-its-lambda-formals = {
      expr = gmX [
        argsMod
        (genMerge.pureModule onArg)
      ];
      expected = "from-module-args";
    };
    test-the-declaration-stratum-applies-a-wrapped-module-by-its-formals = {
      expr = (genMerge.declaredOptions { } [ (wrap declaring) ]).y.default;
      expected = "declared";
    };
    test-lint-reads-a-wrapped-module-options-formal = {
      expr = map (f: f.kind) (genMerge.lint [ (wrap ({ options, ... }: { })) ]);
      expected = [ "options-introspection" ];
    };
  };
}
