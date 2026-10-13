# A container is told by what it CARRIES, never by its name alone (den-hoag-i3kma, ADR-0025 item 1,
# ADR-0039). The key walk and the fold look `nullOr` through to its `carries.element` and key an
# `attrsOf` by its `carries.element`; a record NAMED `nullOr` or `attrsOf` that carries no element
# reads as any foreign record does. Two shapes reach that: a stock nixpkgs constructor whose functor
# is renamed, which re-homing does not recognise (`interface.homedAt`), so it keeps nixpkgs' `name`
# and states no `carries`; and a `//` copy of gen's own `attrsOf` whose `carries` states no element.
# Reading `carries.element` off either was an uncatchable `attribute … missing`.
#
# Each cell's expected value is nixpkgs' twin (every gen constructor its nixpkgs counterpart) in
# nixpkgs' `lib.evalModules`, computed in the same run. The site each cell discharges is named in a
# comment by the predicate that reads it; every cell beside the stock control was an abort before.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  nt = nixpkgsLib.types;
  try = e: (builtins.tryEval (builtins.deepSeq e e)).value;
  subOpts = mkOption: int: {
    key = "name-tested-carriage-sub";
    options.a = mkOption {
      type = int;
      default = 0;
    };
    options.b = mkOption {
      type = int;
      default = 0;
    };
  };
  sub = t.submodule (subOpts gm.mkOption t.int);
  ntSub = nt.submodule (subOpts nixpkgsLib.mkOption nt.int);
  renamed =
    ty:
    ty
    // {
      functor = ty.functor // {
        name = "renamed";
      };
    };
  # `x`'s value under gen's engine, and under nixpkgs' engine over the twin.
  gen =
    ty: v:
    try
      (gm.evalModuleTree { } [
        { options.x = gm.mkOption { type = ty; }; }
        { x = v; }
      ]).config.x;
  twin =
    ty: v:
    try
      (nixpkgsLib.evalModules {
        modules = [
          { options.x = nixpkgsLib.mkOption { type = ty; }; }
          { x = v; }
        ];
      }).config.x;
  # `try` answers `false` for a refusal, so the twin is held to serving: two refusals are not a pass.
  cell =
    mk: v:
    let
      ref = twin (mk ntSub nt) v;
    in
    {
      expr = {
        value = gen (mk sub t) v;
        twinServes = builtins.isAttrs ref;
      };
      expected = {
        value = ref;
        twinServes = true;
      };
    };
  one = {
    k = {
      a = 1;
    };
  };
  two = {
    k = {
      j = {
        a = 1;
      };
    };
  };
in
{
  flake.tests.name-tested-carriage = {
    # The stock control: re-homing recognises nixpkgs' `nullOr`, which then carries its element.
    test-a-stock-nullor-union-member-serves-the-twin = cell (
      s: _: nt.attrsOf (nt.either (nt.nullOr s) nt.str)
    ) one;
    # `modules.containerMemberAt` and `modules.containerAt`: a union member renamed is a container
    # as any foreign split is, not looked through.
    test-a-renamed-nullor-union-member-serves-the-twin = cell (
      s: _: nt.attrsOf (nt.either (renamed (nt.nullOr s)) nt.str)
    ) one;
    # `modules.keyedOverMemberAt`: gen's `attrsOf` over a renamed `nullOr` element.
    test-an-attrs-over-a-renamed-nullor-serves-the-twin = cell (
      s: k: nt.attrsOf (k.attrsOf (renamed (nt.nullOr s)))
    ) two;
    # `modules.keyWalk` under an over-approximating container, and `modules.unionKeys` at a union
    # member: each read the element where `containerAt` did not make the record a container.
    test-a-lazy-attrs-over-a-renamed-nullor-serves-the-twin = cell (
      s: k: k.lazyAttrsOf (renamed (nt.nullOr s))
    ) one;
    test-a-lazy-attrs-over-a-renamed-nullor-union-member-serves-the-twin = cell (
      s: k: k.lazyAttrsOf (nt.either (renamed (nt.nullOr s)) nt.str)
    ) one;
    # `modules.keyedOverAt`: an `attrsOf` copy whose `carries` states no element.
    test-an-attrs-copy-carrying-no-element-serves-the-twin = cell (
      s: k: nt.attrsOf (k.attrsOf s // { carries.alternatives = [ s ]; })
    ) two;
    # `interface.mayFoldNested`: the same copy as gen's own `attrsOf`'s element.
    test-an-attrs-copy-carrying-no-element-under-gen-attrs-serves-the-twin = cell (
      s: k: k.attrsOf (k.attrsOf s // { carries.alternatives = [ s ]; })
    ) two;
  };
}
