# den-hoag-q6d1z: the foreign chain below a node, under merges that reshape what each key holds
# (`uniq (lazyAttrsOf (R …))`, the stock `lazyAttrsOf`'s merge overridden). Each cell is a type
# `t`, a definition `m` of option `s`, and a read `r` of the merged `s`. Read by
# `nesting-keys-foreign-chain-reshaped` in both planes: a served cell where nixpkgs serves the
# same value, a refusal or base's own failure where it does not.
{ gm, nixpkgsLib }:
let
  t = gm.types;
  np = nixpkgsLib.types;
  inherit (gm) mkIf;
  sub = t.submodule {
    options.a = gm.mkOption {
      type = t.int;
      default = 0;
    };
  };
  el = t.attrsOf sub;
  reshapeOf =
    g: a:
    a
    // {
      merge = loc: defs: g (a.merge loc defs);
      substSubModules =
        m:
        let
          r = a.substSubModules m;
        in
        r // { merge = loc: defs: g (r.merge loc defs); };
    };
  stock = r: r;
  swap =
    r:
    r
    // {
      foo = r.bar;
      bar = r.foo;
    };
  # a three-cycle: the tree read at foo is bar's, and bar holds baz's
  rot =
    r:
    r
    // {
      foo = r.bar;
      bar = r.baz;
      baz = r.foo;
    };
  dup = r: r // { bar = r.foo; };
  # foo keeps its own tree and gains bar's `j` under a new key
  graft =
    r:
    r
    // {
      foo = r.foo // {
        g = r.bar.j;
      };
    };
  # bar's tree is served at two keys, foo and baz; bar holds foo's
  fan =
    r:
    r
    // {
      foo = r.bar;
      bar = r.foo;
      baz = r.bar;
    };
  deeper = r: { wrap = r; };
  rmJ = builtins.mapAttrs (_: v: removeAttrs v [ "j" ]);
  filtKey = nixpkgsLib.filterAttrs (n: _: n != "bar");
  # merges that read an element's VALUE: in the capture fold the element is a site record
  filtVal = nixpkgsLib.filterAttrs (_: v: v.j.k.a == 1);
  filtValOr = nixpkgsLib.filterAttrs (_: v: (v.j.k.a or 0) == 1);
  mapVal = builtins.mapAttrs (_: v: if v.j.k.a == 1 then v else { });
  mapValOr = builtins.mapAttrs (_: v: if (v.j.k.a or 0) == 1 then v else { });
  mapValL = builtins.mapAttrs (_: l: if (builtins.head l).k.a == 1 then l else [ ]);
  mapValN = builtins.mapAttrs (_: v: if v.k.a == 1 then v else null);
  # the value keeps its own trees, the capture fold (whose site records lack `k`) swaps them
  valSwap = r: if r.foo.j ? k then r else swap r;
  # a leaf read decides the placement: the element read to decide (baz, foo) and the one placed at
  # the key read are each refused where the capture holds another there
  valOrSwap = r: if (r.foo.j.k.a or 0) == 1 then r else swap r;
  valOrBaz = r: if (r.baz.j.k.a or 0) == 3 then r else swap r;
  valOrRot = r: if (r.foo.j.k.a or 0) == 1 then r else rot r;
  # the same decisions on a chain whose node holds a list (an eager walk, `unique` above it): the element
  # read to decide is refused at its own position, which the capture gave another key's element
  valHasL = r: if (builtins.head r.foo) ? k then r else swap r;
  valOrL = r: if ((builtins.head r.foo).k.a or 0) == 1 then r else swap r;
  valOrLj = r: if ((builtins.head r.foo).j.k.a or 0) == 1 then r else swap r;
  valOrLL = r: if ((at (at r.foo 0) 0).k.a or 0) == 1 then r else swap r;
  toList = builtins.attrValues;
  addConst = r: r // { extra.j.k.a = 9; };
  inDup =
    r:
    r
    // {
      foo = r.foo // {
        j2 = r.foo.j;
      };
    };
  catL = r: r // { foo = r.foo ++ r.bar; };
  filtL = builtins.mapAttrs (_: builtins.filter (e: (e.k.a or 0) == 1));
  revL = builtins.mapAttrs (_: nixpkgsLib.reverseList);
  dropFirst = builtins.mapAttrs (_: builtins.tail);
  swapInner =
    r:
    r
    // {
      foo = [
        (builtins.elemAt r.foo 1)
        (builtins.elemAt r.foo 0)
      ];
    };

  O = g: np.uniq (reshapeOf g (np.lazyAttrsOf (np.attrsOf el)));
  Ol = g: np.uniq (reshapeOf g (np.lazyAttrsOf (np.lazyAttrsOf el)));
  # a node over a node: the move at the outer lazy step, the eager record two steps down
  O3 = g: np.uniq (reshapeOf g (np.lazyAttrsOf (np.lazyAttrsOf (np.attrsOf el))));
  # fozin's one-step level
  O1 =
    g:
    np.uniq (
      reshapeOf g (
        np.attrsWith {
          elemType = el;
          lazy = true;
          placeholder = "p";
        }
      )
    );
  # an eagerly keyed record over a lazy step, below the node
  O4 = g: np.uniq (reshapeOf g (np.lazyAttrsOf (np.attrsOf (np.lazyAttrsOf el))));
  O5 = g: np.uniq (reshapeOf g (np.lazyAttrsOf (np.listOf (np.lazyAttrsOf el))));
  O5s = g: np.uniq (reshapeOf g (np.lazyAttrsOf (np.listOf el)));
  O6 = g: np.uniq (reshapeOf g (np.lazyAttrsOf (np.nullOr (np.lazyAttrsOf el))));
  # the element directly under the node's key: the key's value IS the element
  O6s = g: np.uniq (reshapeOf g (np.lazyAttrsOf (np.nullOr el)));
  # four lazy steps over a strict record; a strict record over a strict record
  O7 = g: np.uniq (reshapeOf g (np.lazyAttrsOf (np.lazyAttrsOf (np.lazyAttrsOf (np.attrsOf el)))));
  O8 = g: np.uniq (reshapeOf g (np.lazyAttrsOf (np.attrsOf (np.attrsOf el))));
  O9 = g: np.uniq (reshapeOf g (np.lazyAttrsOf (np.listOf (np.listOf el))));

  two = {
    s.foo.j.k.a = 1;
    s.bar.j.k.a = 2;
  };
  three = {
    s.foo.j.k.a = 1;
    s.bar.j.k.a = 2;
    s.baz.j.k.a = 3;
  };
  three3 = {
    s.foo.j.j.k.a = 1;
    s.bar.j.j.k.a = 2;
  };
  four = {
    s.foo.j.j.j.k.a = 1;
    s.bar.j.j.j.k.a = 2;
  };
  three8 = {
    s.foo.j.i.k.a = 1;
    s.bar.j.i.k.a = 2;
  };
  two4 = {
    s.foo.j.x.k.a = 1;
    s.bar.j.x.k.a = 2;
  };
  twoL = {
    s.foo = [ { k.a = 1; } ];
    s.bar = [
      { k.a = 2; }
      { k.a = 3; }
    ];
  };
  twoN = {
    s.foo.k.a = 1;
    s.bar.k.a = 2;
  };
  twoNm = {
    s.foo.k.a = 1;
    s.bar.m.a = 2;
  };
  mixL = {
    s.foo = [
      [ { k.a = 1; } ]
      [
        { k.a = 2; }
        { k.a = 3; }
      ]
    ];
    s.bar = [ [ { k.a = 4; } ] ];
  };
  # a definition of bar that reads foo's tree
  kd =
    { config, ... }:
    {
      s.foo.j.k.a = 1;
      s.bar = if config.s.foo.j.k.a == 1 then { j.k.a = 2; } else { };
    };
  # the read tree's own definition is conditional on the read tree (den-hoag-i4j0n)
  selfFoo =
    { config, ... }:
    {
      s.foo = mkIf (config.s.foo.j.k.a == 2) { j.k.a = 1; };
      s.bar.j.k.a = 2;
    };
  selfFoo1 =
    { config, ... }:
    {
      s.foo = mkIf (config.s.foo.k.a == 2) { k.a = 1; };
      s.bar.k.a = 2;
    };
  selfBarDup =
    { config, ... }:
    {
      s.foo.j.k.a = 1;
      s.bar = mkIf (config.s.bar.j.k.a == 1) { j.k.a = 2; };
    };
  # an inner sibling one lazy step below, `mkIf` on the read tree (the stated shortfall)
  mk3 =
    { config, ... }:
    {
      s.foo.j.x.k.a = 1;
      s.foo.j.y = mkIf (config.s.foo.j.x.k.a == 1) { k.a = 5; };
    };
  mkL =
    { config, ... }:
    {
      s.foo = [
        {
          x.k.a = 1;
          y = mkIf ((builtins.elemAt config.s.foo 0).x.k.a == 1) { k.a = 5; };
        }
      ];
    };
  mkLb =
    { config, ... }:
    {
      s.foo = [
        {
          k.a = 1;
          y = mkIf ((builtins.elemAt config.s.foo 0).k.a == 1) { a = 5; };
        }
      ];
      s.bar = [ { k.a = 2; } ];
    };
  mkN =
    { config, ... }:
    {
      s.foo.x.k.a = 1;
      s.foo.y = mkIf (config.s.foo.x.k.a == 1) { k.a = 5; };
    };
  names = builtins.attrNames;
  at = builtins.elemAt;
  twoLj = {
    s.foo = [ { j.k.a = 1; } ];
    s.bar = [ { j.k.a = 2; } ];
  };
in
{
  # read cell `c`: its type mounted at option `s`, its definitions, its read of the merged `s`
  readOf =
    c:
    c.r
      (gm.evalModuleTree { } [
        { options.s = gm.mkOption { type = c.t; }; }
        c.m
      ]).config.s;
  cells = {
    # swaps, rotations and fan-in at a node over a strict record
    swapBar = {
      t = O swap;
      m = two;
      r = s: s.bar.j.k.a;
    };
    swapAll = {
      t = O swap;
      m = two;
      r = s: s;
    };
    swapFooJNames = {
      t = O swap;
      m = two;
      r = s: names s.foo.j;
    };
    swapONamesM = {
      t = O swap;
      m = {
        s.foo.j.k.a = 1;
        s.bar.j.m.a = 2;
      };
      r = s: names s.foo.j;
    };
    swapTopNames = {
      t = O swap;
      m = two;
      r = names;
    };
    rotFoo = {
      t = O rot;
      m = three;
      r = s: s.foo.j.k.a;
    };
    rotBaz = {
      t = O rot;
      m = three;
      r = s: s.baz.j.k.a;
    };
    fanBar = {
      t = O fan;
      m = three;
      r = s: s.bar.j.k.a;
    };
    deeperRead = {
      t = O deeper;
      m = two;
      r = s: s.wrap.foo.j.k.a;
    };
    # where the moved tree holds its own: a duplicate, a graft
    dupFoo = {
      t = O dup;
      m = two;
      r = s: s.foo.j.k.a;
    };
    dupKd = {
      t = O dup;
      m = kd;
      r = s: s.foo.j.k.a;
    };
    dupSelf = {
      t = O dup;
      m = selfBarDup;
      r = s: s.bar.j.k.a;
    };
    graftJ = {
      t = O graft;
      m = two;
      r = s: s.foo.j.k.a;
    };
    graftBar = {
      t = O graft;
      m = two;
      r = s: s.bar.j.k.a;
    };
    stockAll = {
      t = O stock;
      m = three;
      r = s: s;
    };
    kdStock = {
      t = O stock;
      m = kd;
      r = s: s.bar.j.k.a;
    };
    # one key deeper: the record below the outer node is itself a level
    swap3Foo = {
      t = O3 swap;
      m = three3;
      r = s: s.foo.j.j.k.a;
    };
    swap3Bar = {
      t = O3 swap;
      m = three3;
      r = s: s.bar.j.j.k.a;
    };
    swap3FooJNames = {
      t = O3 swap;
      m = three3;
      r = s: names s.foo.j;
    };
    deep7Swap = {
      t = O7 swap;
      m = four;
      r = s: s.foo.j.j.j.k.a;
    };
    deep7SwapNames = {
      t = O7 swap;
      m = four;
      r = s: names s.foo.j.j;
    };
    deep7Stock = {
      t = O7 stock;
      m = four;
      r = s: s.foo.j.j.j.k.a;
    };
    deep8Swap = {
      t = O8 swap;
      m = three8;
      r = s: s.foo.j.i.k.a;
    };
    deep8SwapNames = {
      t = O8 swap;
      m = three8;
      r = s: names s.foo.j;
    };
    deep8SwapNames2 = {
      t = O8 swap;
      m = three8;
      r = s: names s.foo.j.i;
    };
    deep8Stock = {
      t = O8 stock;
      m = three8;
      r = s: s.foo.j.i.k.a;
    };
    # a lazy record below the node, and fozin's one-step level (`keyedWhereRead`)
    swapFooLazy = {
      t = Ol swap;
      m = two;
      r = s: s.foo.j.k.a;
    };
    oneSwapFoo = {
      t = O1 swap;
      m = twoN;
      r = s: s.foo.k.a;
    };
    oneSwapFooNames = {
      t = O1 swap;
      m = twoN;
      r = s: names s.foo;
    };
    # a strict record over a lazy step, a list and a nullOr over a lazy step
    strictLazySwap = {
      t = O4 swap;
      m = two4;
      r = s: s.foo.j.x.k.a;
    };
    strictLazyMkTop = {
      t = O4 stock;
      m = mk3;
      r = names;
    };
    strictLazyMk = {
      t = O4 stock;
      m = mk3;
      r = s: s.foo.j.x.k.a;
    };
    strictLazyMkY = {
      t = O4 stock;
      m = mk3;
      r = s: s.foo.j.y.k.a;
    };
    listLazyMkX = {
      t = O5 stock;
      m = mkL;
      r = s: (at s.foo 0).x.k.a;
    };
    nullLazyMkX = {
      t = O6 stock;
      m = mkN;
      r = s: s.foo.x.k.a;
    };
    swapSelf = {
      t = O swap;
      m = selfFoo;
      r = s: s.foo.j.k.a;
    };
    oneSwapSelf = {
      t = O1 swap;
      m = selfFoo1;
      r = s: s.foo.k.a;
    };
    # the element is the key's own value (`nullOr` directly over it)
    swapNNames = {
      t = O6s swap;
      m = twoN;
      r = s: names s.foo;
    };
    swapNLeaf = {
      t = O6s swap;
      m = twoN;
      r = s: s.foo.k.a;
    };
    twoNm = {
      t = O6s swap;
      m = twoNm;
      r = s: names s.foo;
    };
    twoNmHas = {
      t = O6s swap;
      m = twoNm;
      r = s: s.foo ? m;
    };
    twoNmNull = {
      t = O6s swap;
      m = twoNm;
      r = s: s.foo == null;
    };
    twoNmTop = {
      t = O6s swap;
      m = twoNm;
      r = names;
    };
    fanNNames = {
      t = O6s fan;
      m = {
        s.foo.k.a = 1;
        s.bar.k.a = 2;
        s.baz.k.a = 3;
      };
      r = s: names s.baz;
    };
    stockNNames = {
      t = O6s stock;
      m = twoN;
      r = s: names s.foo;
    };
    dupNNames = {
      t = O6s dup;
      m = twoN;
      r = s: names s.bar;
    };
    # merges that drop or add keys, or reshape the record
    rmJNames = {
      t = O rmJ;
      m = {
        s.foo.j.k.a = 1;
        s.foo.j2.k.a = 3;
        s.bar.j.k.a = 2;
      };
      r = s: names s.foo;
    };
    rmJLeaf = {
      t = O rmJ;
      m = {
        s.foo.j.k.a = 1;
        s.foo.j2.k.a = 3;
        s.bar.j.k.a = 2;
      };
      r = s: s.foo.j2.k.a;
    };
    filtKeyLeaf = {
      t = O filtKey;
      m = two;
      r = s: s.foo.j.k.a;
    };
    filtKeyTop = {
      t = O filtKey;
      m = two;
      r = names;
    };
    toListLen = {
      t = O toList;
      m = two;
      r = builtins.length;
    };
    toListLeaf = {
      t = O toList;
      m = two;
      r = s: (at s 0).j.k.a;
    };
    addConstLeaf = {
      t = O addConst;
      m = two;
      r = s: s.extra.j.k.a;
    };
    addConstFoo = {
      t = O addConst;
      m = two;
      r = s: s.foo.j.k.a;
    };
    inDupLeaf = {
      t = O inDup;
      m = two;
      r = s: s.foo.j2.k.a;
    };
    inDupNames = {
      t = O inDup;
      m = two;
      r = s: names s.foo;
    };
    # merges that read an element's value (not parametric in their elements)
    filtValTop = {
      t = O filtVal;
      m = two;
      r = names;
    };
    filtValNames = {
      t = O filtVal;
      m = two;
      r = s: names s.foo;
    };
    filtValLeaf = {
      t = O filtVal;
      m = two;
      r = s: s.foo.j.k.a;
    };
    filtValOrTop = {
      t = O filtValOr;
      m = two;
      r = names;
    };
    filtValOrNames = {
      t = O filtValOr;
      m = two;
      r = s: names s.foo;
    };
    filtValOrLeaf = {
      t = O filtValOr;
      m = two;
      r = s: s.foo.j.k.a;
    };
    mapValTop = {
      t = O mapVal;
      m = two;
      r = names;
    };
    mapValNames = {
      t = O mapVal;
      m = two;
      r = s: names s.foo;
    };
    mapValHas = {
      t = O mapVal;
      m = two;
      r = s: s.foo ? j;
    };
    mapValLeaf = {
      t = O mapVal;
      m = two;
      r = s: s.foo.j.k.a;
    };
    mapValOrNames = {
      t = O mapValOr;
      m = two;
      r = s: names s.foo;
    };
    mapValOrLeaf = {
      t = O mapValOr;
      m = two;
      r = s: s.foo.j.k.a;
    };
    mapValLLen = {
      t = O5s mapValL;
      m = twoL;
      r = s: builtins.length s.foo;
    };
    mapValLBarLen = {
      t = O5s mapValL;
      m = twoL;
      r = s: builtins.length s.bar;
    };
    mapValL0 = {
      t = O5s mapValL;
      m = twoL;
      r = s: (at s.foo 0).k.a;
    };
    mapValNNull = {
      t = O6s mapValN;
      m = twoN;
      r = s: s.bar == null;
    };
    mapValNNames = {
      t = O6s mapValN;
      m = twoN;
      r = s: names s.foo;
    };
    mapValNLeaf = {
      t = O6s mapValN;
      m = twoN;
      r = s: s.foo.k.a;
    };
    valSwapNames = {
      t = O valSwap;
      m = two;
      r = s: names s.foo;
    };
    valSwapJNames = {
      t = O valSwap;
      m = two;
      r = s: names s.foo.j;
    };
    valSwapLeaf = {
      t = O valSwap;
      m = two;
      r = s: s.foo.j.k.a;
    };
    valSwapBar = {
      t = O valSwap;
      m = two;
      r = s: s.bar.j.k.a;
    };
    valOrSwapLeaf = {
      t = O valOrSwap;
      m = two;
      r = s: s.foo.j.k.a;
    };
    valOrSwapBar = {
      t = O valOrSwap;
      m = two;
      r = s: s.bar.j.k.a;
    };
    valOrBazBar = {
      t = O valOrBaz;
      m = three;
      r = s: s.bar.j.k.a;
    };
    valOrBazFoo = {
      t = O valOrBaz;
      m = three;
      r = s: s.foo.j.k.a;
    };
    valOrRotBar = {
      t = O valOrRot;
      m = three;
      r = s: s.bar.j.k.a;
    };
    valHasLBar = {
      t = O5s valHasL;
      m = twoL;
      r = s: (at s.bar 0).k.a;
    };
    valHasLFoo = {
      t = O5s valHasL;
      m = twoL;
      r = s: (at s.foo 0).k.a;
    };
    valOrLBar = {
      t = O5s valOrL;
      m = twoL;
      r = s: (at s.bar 0).k.a;
    };
    valOrLFoo = {
      t = O5s valOrL;
      m = twoL;
      r = s: (at s.foo 0).k.a;
    };
    valOrLjBar = {
      t = O5 valOrLj;
      m = twoLj;
      r = s: (at s.bar 0).j.k.a;
    };
    valOrLjFoo = {
      t = O5 valOrLj;
      m = twoLj;
      r = s: (at s.foo 0).j.k.a;
    };
    valOrLLBar = {
      t = O9 valOrLL;
      m = mixL;
      r = s: (at (at s.bar 0) 0).k.a;
    };
    valOrLLFoo = {
      t = O9 valOrLL;
      m = mixL;
      r = s: (at (at s.foo 0) 0).k.a;
    };
    # list records
    catLLen = {
      t = O5s catL;
      m = twoL;
      r = s: builtins.length s.foo;
    };
    catL0 = {
      t = O5s catL;
      m = twoL;
      r = s: (at s.foo 0).k.a;
    };
    catL1 = {
      t = O5s catL;
      m = twoL;
      r = s: (at s.foo 1).k.a;
    };
    filtLLen = {
      t = O5s filtL;
      m = twoL;
      r = s: builtins.length s.foo;
    };
    filtL0 = {
      t = O5s filtL;
      m = twoL;
      r = s: (at s.foo 0).k.a;
    };
    filtLBarLen = {
      t = O5s filtL;
      m = twoL;
      r = s: builtins.length s.bar;
    };
    revLBar0 = {
      t = O5s revL;
      m = twoL;
      r = s: (at s.bar 0).k.a;
    };
    swapLLen = {
      t = O5s swap;
      m = twoL;
      r = s: builtins.length s.foo;
    };
    swapL0 = {
      t = O5s swap;
      m = twoL;
      r = s: (at s.foo 0).k.a;
    };
    swapLNames = {
      t = O5s swap;
      m = twoL;
      r = s: names (at s.foo 0);
    };
    swapLNamesM = {
      t = O5s swap;
      m = {
        s.foo = [ { k.a = 1; } ];
        s.bar = [ { m.a = 2; } ];
      };
      r = s: names (at s.foo 0);
    };
    stockLmkLen = {
      t = O5s stock;
      m = mkLb;
      r = s: builtins.length s.foo;
    };
    stockLmkX = {
      t = O5s stock;
      m = mkLb;
      r = s: (at s.foo 0).k.a;
    };
    mixLen = {
      t = O9 stock;
      m = mixL;
      r = s: map builtins.length s.foo;
    };
    mix11 = {
      t = O9 stock;
      m = mixL;
      r = s: (at (at s.foo 1) 1).k.a;
    };
    mixDropLen = {
      t = O9 dropFirst;
      m = mixL;
      r = s: map builtins.length s.foo;
    };
    mixDrop01 = {
      t = O9 dropFirst;
      m = mixL;
      r = s: (at (at s.foo 0) 1).k.a;
    };
    mixSwapLen = {
      t = O9 swapInner;
      m = mixL;
      r = s: map builtins.length s.foo;
    };
    mixSwap01 = {
      t = O9 swapInner;
      m = mixL;
      r = s: (at (at s.foo 0) 1).k.a;
    };
  };
}
