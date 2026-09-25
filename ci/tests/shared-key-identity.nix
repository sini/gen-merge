# ONE ANSWER PER INPUT ACROSS NIX, DETERMINATE AND LIX at a check-only `mkOptionType`'s shared-key
# `==` (lib/modules.nix `sharedKeyDiffers`, and `callM`'s binding of a `baseArgs` formal).
#
# `==`'s identity short-circuit (the Nix manual's "Value identity optimization") compares value
# SLOTS on upstream Nix and Determinate and object identity on Lix. So one function, or one value
# holding an attribute that throws when forced, compares equal on all three only when both sides are
# the SAME slot. The fold compares each definer's own slot, and `callM` binds a `specialArgs` formal to
# `baseArgs`' own attribute, so the cells that keep one slot are kept on every evaluator (cells 1, 2,
# 6, 7). Where the definitions hold the value in DIFFERENT slots the evaluators split, and the split is
# stated (README "Known byte-mode boundaries"): cells 5 and 8 pin each evaluator's answer to that
# evaluator's own `==` observed on the same shape, so they hold ×3 and red on any evaluator whose fold
# stops answering as its `==` does. The refusing arms (distinct closures) are on the error plane,
# ci/tests-error.nix `mkoptiontype-default-merge`.
#
# RED, evaluated: cells 1, 6 and 7 at gen-merge ef21648 (the named refusal on Nix and Determinate);
# cell 2 there (the foreign throw on Nix and Determinate); cells 6 and 7 again with only the
# `sharedKeyDiffers` edit (no `callM` edit). Cells 5 and 8 with a fold that calls every shared function
# equal (false on Nix and Determinate) and with one that refuses every function (false on Lix).
{ genMerge, ... }:
let
  gm = genMerge;
  ty = gm.mkOptionType {
    name = "thread";
    check = _: true;
  };
  decl = {
    options.heddle = gm.mkOption { type = ty; };
  };
  heddleOf =
    args: modules: (gm.evalModuleTree (args // { modules = [ decl ] ++ modules; })).config.heddle;
  # two files, each defining `heddle = <a> / <b>`
  pair =
    a: b:
    heddleOf { } [
      {
        _file = "/demo/warp.nix";
        config.heddle = a;
      }
      {
        _file = "/demo/weft.nix";
        config.heddle = b;
      }
    ];
  f = x: x + 1;
  # a value one of whose attributes throws when forced: the shape of a nixpkgs package set, whose
  # deep `==` reaches an alias that throws
  big = {
    ok = 1;
    bad = throw "shared-key-identity: forced the throwing attribute";
  };
  # a function module reading formal `fa` (or `bigArg`) into `heddle.a`
  modFa = file: { fa, ... }: {
    _file = file;
    config.heddle = {
      a = fa;
    };
  };
  modBig = file: { bigArg, ... }: {
    _file = file;
    config.heddle = {
      a = bigArg;
    };
  };
  keptKeys = v: builtins.attrNames v;
  accepted = v: (builtins.tryEval (builtins.typeOf v)).success;
  # the observers: each evaluator's own `==` on the input's shape, with no gen-merge in it
  lb = {
    id = x: x;
  };
  # `callM`'s shape for a `_module.args` formal: a formal bound to a thunk a `mapAttrs` made per
  # application, written into an attribute literal
  applyLikeCallM = s: ({ id, ... }: { a = id; }) (builtins.mapAttrs (n: _: s.${n}) s);
in
{
  flake.tests.shared-key-identity = {
    # 1. One bound function written at each site: one slot, kept ×3.
    test-a-function-bound-once-at-a-shared-key-is-kept = {
      expr = keptKeys (pair { a = f; } { a = f; });
      expected = [ "a" ];
    };
    # 2. One bound value with a throwing attribute: one slot, so `==` never descends into it. Kept ×3.
    test-one-value-with-a-throwing-attribute-bound-once-is-kept = {
      expr = keptKeys (pair { a = big; } { a = big; });
      expected = [ "a" ];
    };
    # 5. The stated split, user-made copies: a selection written at each site is a fresh slot per site.
    # Nix and Determinate refuse, Lix keeps; each answers as its own `==` on `{ a = s.id; }` twice.
    test-a-function-reached-by-selection-answers-as-the-evaluator-s-own-identity = {
      expr = accepted (pair { a = lb.id; } { a = lb.id; }) == ({ a = lb.id; } == { a = lb.id; });
      expected = true;
    };
    # 6. A `specialArgs` formal binds to `baseArgs`' own slot, so two modules reading it agree ×3.
    test-a-function-passed-as-a-special-arg-is-kept = {
      expr = keptKeys (
        heddleOf { specialArgs.fa = f; } [
          (modFa "/demo/warp.nix")
          (modFa "/demo/weft.nix")
        ]
      );
      expected = [ "a" ];
    };
    # 7. The same for a value with a throwing attribute (the nixpkgs `pkgs` stand-in).
    test-a-value-with-a-throwing-attribute-passed-as-a-special-arg-is-kept = {
      expr = keptKeys (
        heddleOf { specialArgs.bigArg = big; } [
          (modBig "/demo/warp.nix")
          (modBig "/demo/weft.nix")
        ]
      );
      expected = [ "a" ];
    };
    # 8. THE CHOSEN RESIDUE. A `_module.args` formal is copied per module application, so each module
    # holds its own slot: Nix and Determinate refuse, Lix keeps, each as its own `==` on `callM`'s
    # shape. One shared cell per argument name per evaluation removes the split on all three; that
    # costs thunks the hub perf-bench's kindMatch bounds do not admit, so it is not paid here. This
    # cell pins the residue as chosen: a landing that removes the split reds it on Nix and
    # Determinate, by design, and replaces it with a cell like 6.
    test-a-function-passed-through-module-args-answers-as-the-evaluator-s-own-identity = {
      expr =
        accepted (
          heddleOf { } [
            { config._module.args.fa = f; }
            (modFa "/demo/warp.nix")
            (modFa "/demo/weft.nix")
          ]
        ) == (applyLikeCallM lb == applyLikeCallM lb);
      expected = true;
    };
  };
}
