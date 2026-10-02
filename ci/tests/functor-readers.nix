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
# The value-merge readers are NOT this unit's: two functor DEFINITIONS still merge as attrsets in
# `mergeDefaultOption`, where nixpkgs merges them as functions. That cell is pinned below as the
# residue it is, beside its lambda control, and den-hoag-1ypox carries it.
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
    (evalModuleTree {
      modules = [
        { options.out = mkOption { }; }
        { config._module.args.flavour = "flavour-passed"; }
      ]
      ++ mods;
    }).config.out;

  # nixpkgs `lib.setFunctionArgs f (functionArgs f)`, the wrapper a lowering puts around a module
  wrap = f: np.setFunctionArgs (args: f args) (builtins.functionArgs f);
  argsMod = {
    config._module.args.myArg = "from-module-args";
  };
  onArg = { myArg, ... }: { config.x = myArg; };
  onConfig = { config, ... }: { config.x = "config-only"; };
  gmX =
    mods:
    (evalModuleTree { modules = [ { options.x = mkOption { type = genMerge.types.str; }; } ] ++ mods; })
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
in
{
  flake.tests.functor-readers = {
    test-two-functor-defs-merge-as-attrsets = {
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
      expected = "set";
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
      expr = (genMerge.declaredOptions { modules = [ (wrap declaring) ]; }).y.default;
      expected = "declared";
    };
    test-lint-reads-a-wrapped-module-options-formal = {
      expr = map (f: f.kind) (genMerge.lint { modules = [ (wrap ({ options, ... }: { })) ]; });
      expected = [ "options-introspection" ];
    };
  };
}
