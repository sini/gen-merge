# A hand-made `carries` is read for what it states, and a read with an answer of the record's own
# serves it (den-hoag-l4bv5, ADR-0025 item 1, ADR-0039). `carries` states by role what a type
# carries, and its constructor writes it beside `recarry`, `substructure` and the fold; a `//` over
# a constructed type (or a descriptor's own) can state another role, none, or no set at all. A
# container's step that states `forward` but carries no element does not forward: its own
# substructure, which its fold reads, is its answer (`interface.forwardStep`). An over-approximating
# container is one only where it carries an element (`modules.keyedOverAt`). Each cell beside the
# control was an uncatchable `attribute … missing` before.
#
# Each cell's expected value is nixpkgs' twin (every gen constructor its nixpkgs counterpart) in
# nixpkgs' `lib.evalModules`, computed in the same run. The reads a refusal answers are pinned by
# message in `../tests-error.nix`, `hand-made-carriage`.
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
    key = "hand-made-carriage-sub";
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
  noElem = ty: ty // { carries.alternatives = [ sub ]; };
  # `x`'s value under gen's engine, and under nixpkgs' engine, over the same type.
  gen =
    ty: v:
    try
      (gm.evalModuleTree { } [
        { options.x = gm.mkOption { type = ty; }; }
        { x = v; }
      ]).config.x;
  np =
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
    engine: ty: twin: v:
    let
      ref = np twin v;
    in
    {
      expr = {
        value = engine ty v;
        twinServes = builtins.isAttrs ref || builtins.isList ref;
      };
      expected = {
        value = ref;
        twinServes = true;
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
  flake.tests.hand-made-carriage = {
    # The control: the copy unforged.
    test-a-gen-attrs-over-a-gen-attrs-serves-the-twin-in-nixpkgs = cell np (t.attrsOf (
      t.attrsOf sub
    )) (nt.attrsOf (nt.attrsOf ntSub)) two;
    # `interface.forwardStep`: the copy states `forward` and carries no element, under a gen
    # container in nixpkgs' engine.
    test-an-attrs-copy-carrying-no-element-under-gen-attrs-serves-the-twin-in-nixpkgs =
      cell np (t.attrsOf (noElem (t.attrsOf sub))) (nt.attrsOf (nt.attrsOf ntSub))
        two;
    test-an-attrs-copy-carrying-no-element-under-gen-list-serves-the-twin-in-nixpkgs =
      cell np (t.listOf (noElem (t.attrsOf sub))) (nt.listOf (nt.attrsOf ntSub))
        [ two.k ];
    # The same, a copy stating no `carries` at all, through the `defineType` door.
    test-an-attrs-copy-stating-no-carries-through-define-type-serves-the-twin-in-nixpkgs = cell np (
      t.attrsOf
        (t.defineType (removeAttrs (t.attrsOf sub) [ "carries" ]))
    ) (nt.attrsOf (nt.attrsOf ntSub)) two;
    # `modules.keyedOverAt`: a `lazyAttrsOf` copy carrying no element is not keyed over-approximately,
    # so the key walk never reads the element it does not carry (`modules.keyWalk`).
    test-a-lazy-attrs-copy-carrying-no-element-under-gen-attrs-serves-the-twin = cell gen (t.attrsOf (
      noElem (t.lazyAttrsOf sub)
    )) (nt.attrsOf (nt.lazyAttrsOf ntSub)) two;
  };
}
