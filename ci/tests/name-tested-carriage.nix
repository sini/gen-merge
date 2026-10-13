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
  # `b` with `x`'s fold: gen's `split` and `mergeDefs` and nixpkgs' `merge`, as far as `x` states them.
  foldOf =
    b: x:
    b
    // builtins.intersectAttrs {
      split = null;
      mergeDefs = null;
      merge = null;
    } x;
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
        twinServes = builtins.isAttrs ref || builtins.isList ref;
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

    # THE MARK OVER-APPROXIMATES THE WALK (`interface.mayFoldNested`, `interface.mayBeContainer`). A `//`
    # copy of gen's `nullOr` whose `carries` states no element is a container the walk keys where it is
    # read (`modules.containerAt`): it states no element to look through. An exact container marks its
    # element by the mark, and the fold reads the walk's node only where the mark is set
    # (`modules.unionNodeAt`); so a mark that excludes such a copy by its name lets the walk mint a node
    # the fold never reads. The seven through `attrs-of-attrs` were an uncatchable `attribute 'config'
    # missing` at c3b4d83 for that reason; the last two pin arms a narrower repair breaks.
    test-a-nullor-copy-carrying-no-element-under-gen-attrs-serves-the-twin = cell (
      s: k: k.attrsOf (k.nullOr s // { carries.alternatives = [ s ]; })
    ) one;
    test-a-nullor-copy-carrying-no-element-under-gen-list-serves-the-twin = cell (
      s: k: k.listOf (k.nullOr s // { carries.alternatives = [ s ]; })
    ) [ one.k ];
    test-a-nullor-copy-carrying-an-unknown-role-under-nixpkgs-attrs-serves-the-twin = cell (
      s: k: nt.attrsOf (k.nullOr s // { carries.foo = s; })
    ) one;
    test-a-nullor-copy-carrying-no-element-through-the-mkoptiontype-door-serves-the-twin = cell (
      s: k:
      k.attrsOf (
        (if k ? defineType then gm.mkOptionType else (x: x)) (
          k.nullOr s // { carries.alternatives = [ s ]; }
        )
      )
    ) one;
    test-a-nullor-copy-over-a-union-carrying-no-element-under-gen-attrs-serves-the-twin = cell (
      s: k: k.attrsOf (k.nullOr (k.either s k.str) // { carries.alternatives = [ s ]; })
    ) one;
    # Below a step under an over-approximating container, and an exact container over an exact one.
    test-a-nullor-copy-carrying-no-element-under-lazy-attrs-of-attrs-serves-the-twin = cell (
      s: k: k.lazyAttrsOf (k.attrsOf (k.nullOr s // { carries.alternatives = [ s ]; }))
    ) two;
    test-a-nullor-copy-carrying-no-element-under-attrs-of-attrs-serves-the-twin = cell (
      s: k: k.attrsOf (k.attrsOf (k.nullOr s // { carries.alternatives = [ s ]; }))
    ) two;
    # `modules.containerMemberAt`: a union member stating no element makes the union a container, keyed
    # where read (its `choose`); a walk that looks such a member through keys nothing below it.
    test-a-nullor-copy-carrying-no-element-as-a-union-member-serves-the-twin = cell (
      s: k: nt.either (k.nullOr s // { carries.alternatives = [ s ]; }) nt.int
    ) one.k;
    # gen's `nullOr` renamed (`// { name }`) is a container node under an over-approximating container.
    test-a-renamed-gen-nullor-under-lazy-attrs-serves-the-twin = cell (
      s: k: k.lazyAttrsOf (k.nullOr s // { name = "renamedNullOr"; })
    ) one;
    # Neither a name nor a stated step decides it: gen's `attrsOf` renamed `nullOr` is a container (it was refused
    # by name at c3b4d83, nixpkgs serves it), and gen's `attrsOf` stating `substructure.forward = null` is a
    # container still.
    test-an-attrs-renamed-nullor-under-lazy-attrs-serves-the-twin = cell (
      s: k: k.lazyAttrsOf (k.attrsOf s // { name = "nullOr"; })
    ) two;
    test-an-attrs-stating-no-step-under-lazy-attrs-serves-the-twin = cell (
      s: k:
      k.lazyAttrsOf (
        k.attrsOf s
        // {
          substructure = (k.attrsOf s).substructure or { } // {
            forward = null;
          };
        }
      )
    ) two;
    # `modules.keyedOverAt` reads the constructor that BUILT the record, never its `name`: gen's `listOf` renamed
    # `attrsOf` or `lazyAttrsOf` keys its indices as a list does, and gen's `attrsOf` renamed `nullOr` is a
    # container at a union member. Each was an uncatchable abort at 6bacad6 (`expected a set but found a list`,
    # `'builtins.head' called on an empty list`), where nixpkgs serves.
    test-a-list-renamed-attrs-under-gen-attrs-serves-the-twin = cell (
      s: k: k.attrsOf (k.listOf s // { name = "attrsOf"; })
    ) { k = [ { a = 1; } ]; };
    test-a-list-renamed-lazy-attrs-under-gen-attrs-serves-the-twin = cell (
      s: k: k.attrsOf (k.listOf s // { name = "lazyAttrsOf"; })
    ) { k = [ { a = 1; } ]; };
    test-a-list-renamed-lazy-attrs-under-gen-list-serves-the-twin = cell (
      s: k: k.listOf (k.listOf s // { name = "lazyAttrsOf"; })
    ) [ [ { a = 1; } ] ];
    test-an-attrs-renamed-nullor-as-a-union-member-serves-the-twin = cell (
      s: k: nt.either (k.attrsOf s // { name = "nullOr"; }) nt.int
    ) one;
    # Container status is read off the FOLD (`mergeDefs.container`), which a `//` copy carries with the fold it
    # takes: gen's `nullOr` whose fold is rewritten to `attrsOf`'s or `lazyAttrsOf`'s (`split`, `mergeDefs`,
    # nixpkgs' `merge`), keeping its own name, is the container its fold is. At 6bacad6 the first aborted
    # (`'builtins.head' called on an empty list`) and the second was refused, where nixpkgs serves; the third,
    # renamed as its fold, served at 6bacad6 and aborted under a reading of the payload's constructor.
    test-a-nullor-with-attrs-fold-as-a-union-member-serves-the-twin =
      cell (s: k: nt.either (foldOf (k.nullOr s) (k.attrsOf s)) nt.int)
        {
          j = {
            a = 1;
          };
        };
    test-a-nullor-with-lazy-attrs-fold-as-a-union-member-serves-the-twin =
      cell (s: k: nt.either (foldOf (k.nullOr s) (k.lazyAttrsOf s)) nt.int)
        {
          j = {
            a = 1;
          };
        };
    # ADR-0039 (b′)'s VALUE oracle (den-hoag-u5jwx): a copy whose fold is rewritten, given a value its own `check`
    # admits, serves its fold's value, the value the fold's own constructor gives. nixpkgs refuses this cell (its
    # rebuild declares the base's options under the copy's merge), so the law, not the twin, is the reference.
    test-an-attrs-with-a-nullor-fold-serves-the-nullor-value = {
      expr = gen (foldOf (t.attrsOf sub) (t.nullOr sub)) { a = 1; };
      expected = {
        a = 1;
        b = 0;
      };
    };
    # A derivation keeps its base's fold as its own: the fold's witness is re-tied to the record the door completes.
    test-a-derivation-of-gen-attrs-serves-its-value = {
      expr = gen (gm.deriveType { } "name-tested-carriage" (t.attrsOf sub)) { j.a = 1; };
      expected = {
        j = {
          a = 1;
          b = 0;
        };
      };
    };
    test-a-nullor-with-attrs-fold-and-name-as-a-union-member-serves-the-twin =
      cell (s: k: nt.either (foldOf (k.nullOr s) (k.attrsOf s) // { name = "attrsOf"; }) nt.int)
        {
          j = {
            a = 1;
          };
        };
  };
}
