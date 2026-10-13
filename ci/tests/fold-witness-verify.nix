# A record stating `verify` is judged by its `verify` on the merged value, whatever its fold's witness says
# (den-hoag-u5jwx): its published `check` is the verify's one-definition projection, so the per-fold sites
# owe it nothing beside the verify. The shape is gen-schema's `refined` over a container: the base's
# identity fields removed, a `verify` stated, completed through `mkOptionType`. The refinement holds of the
# merged value only, so a split across two definitions is served, where owing the per-definition `check`
# refused each definition by the base's name. The refusal and its reason: `tests-error.nix`
# `fold-rewrite-check`.
{
  genMerge,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  try = e: (builtins.tryEval (builtins.deepSeq e e)).value;
  verifyCopy =
    base: verify:
    gm.mkOptionType (
      builtins.removeAttrs base [
        "functor"
        "typeMerge"
        "__mint"
        "__okAt"
        "__payload"
        "__sealed"
        "__typeSelf"
      ]
      // {
        inherit verify;
      }
    );
  read =
    ty: defs:
    try
      (gm.evalModuleTree { } (
        [ { options.o = gm.mkOption { type = ty; }; } ] ++ map (d: { o = d; }) defs
      )).config.o;
in
{
  flake.tests.fold-witness-verify = {
    test-a-verify-copy-of-attrs-serves-a-merged-value-refinement-split-across-definitions = {
      expr = read (verifyCopy (t.attrsOf t.int) (v: if v ? a && v ? b then null else "needs a and b")) [
        { a = 1; }
        { b = 2; }
      ];
      expected = {
        a = 1;
        b = 2;
      };
    };
    test-a-verify-copy-of-list-serves-a-merged-value-refinement-split-across-definitions = {
      expr =
        read (verifyCopy (t.listOf t.int) (v: if builtins.length v >= 2 then null else "needs two"))
          [
            [ 1 ]
            [ 2 ]
          ];
      expected = [
        2
        1
      ];
    };
  };
}
