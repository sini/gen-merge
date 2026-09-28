# THE READERS STAY THE BUILTINS (den-hoag-7gp66 P2 L0, K1 of the door-fold gate).
#
# gen-prelude's `isFunction`/`functionArgs` became nixpkgs' functor-aware readers (P2-OQ15 arm (i)).
# gen-merge binds the builtins instead, so a functor keeps the meaning it had here: an attrset. Two
# of the sites whose answer would move are pinned below on a functor, each beside a lambda control
# whose answer is the same under either reader. Adopting nixpkgs' functor-aware parity (a functor
# module applied by its published formals, functor defs merged as functions) is gen-merge's own P2
# unit's change, and it flips these cells deliberately.
{ genMerge, ... }:
let
  inherit (genMerge) evalModuleTree mkOption mergeDefaultOption;
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
    test-functor-module-is-unwrapped-not-read-by-formals = {
      expr = tree [ functorModule ];
      expected = "flavour-not-passed";
    };
    test-control-lambda-module-reads-its-formal = {
      expr = tree [ ({ flavour, ... }: { config.out = flavour; }) ];
      expected = "flavour-passed";
    };
  };
}
