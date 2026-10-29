# A door's return for a caller's FOREIGN record, closed under its rebuilds (`interface.rebuildClosed.imported`,
# den-hoag-d61ws). The published `mkOptionType` and `deriveType` return gen's record for a foreign one (re-homed,
# completed or derived), carrying the record's check; nixpkgs re-derives a declared type through that record's
# rebuilds, `substSubModules` at the fixup and the later declaration's `typeMerge` at a redeclaration, and through gen's
# own `substructure.rebuild` where a gen container holds it. Each cell reads nixpkgs' `lib.evalModules`.
#  - the CHECK cells: a definition the record's check rejects is refused, one it admits is served with the all-nixpkgs
#    `addCheck` twin's value;
#  - the WIDENING cells: the check is owed relative to the record's own parameters at a join that widens them; over a
#    container, membership in those parameters is judged at every depth, so a value with an element outside them is
#    served with the twin's value, and one inside them that the check rejects is refused;
#  - the VERIFY cells: a `verify` the caller states is never read on a definition alone by the closure, so two
#    definitions each failing it and merging to a value it admits are served at a redeclaration, and a verify reading a
#    member only the merged value has never runs on a definition (an uncatchable abort);
#  - the ELEMENT cells: a door outside a nixpkgs container whose element is a gen submodule copy stating `verify` keeps
#    the element's `verify` its own rebuild carries;
#  - the UNION cells (ADR-0039 (b′)): the door's return as a member of an overlapping nixpkgs union declared twice. The
#    stated merge law is nixpkgs' own v2 `either` / `oneOf` rule: the first member whose merge states no `headError`
#    over the definitions. A value oracle (the return admits: its merge; its check rejects: the other member's) and a
#    check oracle (both reject: refused). nixpkgs' twin serves the return's base merge there, its `addCheck` dropped at
#    the redeclaration, so these values are served beyond nixpkgs, under this law;
#  - the OVERRIDE-JOIN cells: a v2 ad-hoc override whose functor rebuilds it, judged at the join nixpkgs asks for: a
#    join that is the override again is refused as the twin refuses it, and a coherent join is served with the twin's
#    value, the override's check owed inside the parameters its v2 merge was built at;
#  - the OWN-PARAMETERS cells: a NON-v2 record whose functor rebuilds itself at its own payload is the record whose
#    check is the debt, so its own parameters are judged by gen's constructor for its functor name at its payload
#    (nixpkgs names a constructor by its functor name): a value inside them its check rejects is refused by name, in
#    every engine and order, and one outside them is served with the twin's value, whatever record the partner's
#    functor returns away from its own payload.
# Red: every check cell with `imported` reverted to `t: r: r`; the `elemG` cells with `substructure` left out; the
# widening cells with the join's check taken whole; the container widening cells outside the parameters with
# membership read by the base's `check` alone; the verify and element cells with the closure built from the
# door's return instead of the caller's record (P11); the override-join refusals with `close` owing `oc` on every
# join, or with the base's membership read by its `check`; the door-column refusals with a refused join rebuilt over its
# met roles (`relationMergeWithin`), and the door-column check oracle with an override's stock read by its own `check`
# (`metWith`); the override-join values with the check owed on every value; the own-parameters refusals with the
# stock's membership read by its own `check` (`metWith`) and the base's by its own merge (`rebuildClosed.own`), each
# site partitioning them; the own-parameters values with the check owed on every value at both sites.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins)
    all
    concatMap
    elemAt
    isAttrs
    isInt
    isList
    length
    listToAttrs
    ;
  run =
    ts: dv:
    let
      c =
        (nl.evalModules {
          modules = map (t: { options.x = nl.mkOption { type = t; }; }) ts ++ map (v: { x = v; }) dv;
        }).config;
      o = builtins.tryEval (builtins.deepSeq c.x c.x);
    in
    if o.success then o.value else "REFUSED";
  subOf = mk: int: {
    key = "drc-sub-${if mk == nl.mkOption then "np" else "gen"}";
    options.a = mk {
      type = int;
      default = 0;
    };
    options.b = mk {
      type = int;
      default = 0;
    };
  };
  gSub = gt.submodule (subOf gm.mkOption gt.int);
  npSub = np.submodule (subOf nl.mkOption np.int);
  pSub = v: !(isAttrs v) || !(isInt (v.a or null)) || v.a != 2;
  pList = v: !(isList v) || all (x: !(isInt x) || x < 10) v;
  # one shape per rebuild nixpkgs calls: a module-set container (the fixup's `substSubModules`), a leaf container (the
  # later declaration's `typeMerge`); `twin` is the all-nixpkgs record the value oracle reads
  shapes = {
    nullOrG = {
      t = np.nullOr gSub;
      twin = np.nullOr npSub;
      p = pSub;
      ok.a = 1;
      bad.a = 2;
    };
    nullOrNp = {
      t = np.nullOr npSub;
      twin = np.nullOr npSub;
      p = pSub;
      ok.a = 1;
      bad.a = 2;
    };
    listOf = {
      t = np.listOf np.int;
      twin = np.listOf np.int;
      p = pList;
      ok = [ 1 ];
      bad = [ 20 ];
    };
  };
  # an ad-hoc `// { check }` over a v2 leaf container is the v2-incoherent ad-hoc class, refused by name in gen's
  # engine and unchanged here (ADR-0039), so the `check` copy is read over the module-set shapes only
  copies = {
    addCheck = p: t: np.addCheck t p;
    check = p: t: t // { check = v: t.check v && p v; };
  };
  poss = {
    root = {
      mk = t: t;
      w = v: v;
    };
    elemNp = {
      mk = np.attrsOf;
      w = v: { k = v; };
    };
    elemG = {
      mk = gt.attrsOf;
      w = v: { k = v; };
    };
  };
  arrs = {
    A = plain: x: [ x ];
    TL = plain: x: [
      plain
      x
    ];
    LL = plain: x: [
      x
      x
    ];
  };
  doors = {
    mkOptionType = gm.mkOptionType;
    deriveType = gm.deriveType { } "drc";
  };
  points = [
    [
      "mkOptionType"
      "nullOrG"
      "root"
      "A"
    ]
    [
      "mkOptionType"
      "nullOrG"
      "elemNp"
      "A"
    ]
    [
      "mkOptionType"
      "nullOrG"
      "elemG"
      "A"
    ]
    [
      "mkOptionType"
      "nullOrG"
      "root"
      "TL"
    ]
    [
      "mkOptionType"
      "nullOrG"
      "root"
      "LL"
    ]
    [
      "mkOptionType"
      "nullOrNp"
      "root"
      "A"
    ]
    [
      "mkOptionType"
      "nullOrNp"
      "elemG"
      "A"
    ]
    [
      "mkOptionType"
      "listOf"
      "root"
      "TL"
    ]
    [
      "mkOptionType"
      "listOf"
      "root"
      "LL"
    ]
    [
      "mkOptionType"
      "listOf"
      "elemNp"
      "LL"
    ]
    [
      "deriveType"
      "nullOrG"
      "root"
      "A"
    ]
    [
      "deriveType"
      "nullOrG"
      "elemG"
      "LL"
    ]
  ];
  cell =
    c: pt:
    let
      d = builtins.elemAt pt 0;
      S = shapes.${builtins.elemAt pt 1};
      P = poss.${builtins.elemAt pt 2};
      a = builtins.elemAt pt 3;
      ts = arrs.${a} (P.mk S.t) (P.mk (doors.${d} (copies.${c} S.p S.t)));
    in
    {
      name = "test-${d}-${c}-${builtins.concatStringsSep "-" (builtins.tail pt)}";
      value = {
        expr = {
          rejected = run ts [ (P.w S.bad) ];
          admitted = run ts [ (P.w S.ok) ];
        };
        expected = {
          rejected = "REFUSED";
          admitted = run [ (P.mk (np.addCheck S.twin S.p)) ] [ (P.w S.ok) ];
        };
      };
    };
  checkCells = concatMap (
    c: map (cell c) (builtins.filter (pt: !(c == "check" && builtins.elemAt pt 1 == "listOf")) points)
  ) (builtins.attrNames copies);
  # a join that WIDENS the record's parameters (enum extension stays a union, ADR-0039): X = mkOptionType (enum [ a b ]),
  # with or without a check rejecting "b", declared after Y = enum [ b c ]; "c" is outside X's base and served
  widened = c: {
    name = "test-mkOptionType-${c}-a-widening-join-owes-the-check-relative-to-its-own-parameters";
    value =
      let
        X = gm.mkOptionType (
          if c == "none" then
            np.enum [
              "a"
              "b"
            ]
          else
            np.addCheck (np.enum [
              "a"
              "b"
            ]) (v: v != "b")
        );
        Y = np.enum [
          "b"
          "c"
        ];
      in
      {
        expr = map (v: run [ Y X ] [ v ]) [
          "a"
          "b"
          "c"
        ];
        expected = [
          "a"
          (if c == "none" then "b" else "REFUSED")
          "c"
        ];
      };
  };
  # the same join over a container: X = mkOptionType (C (enum [ a b ])) with a check admitting at most one element,
  # declared after Y = C (enum [ b c ]). A value whose elements are all in X's parameters is X's to judge; one with an
  # element "c" is not, at any depth, and is served with the all-nixpkgs `addCheck` twin's value
  widenedIn = c: k: v: {
    name = "test-mkOptionType-${c}-${k}-a-widening-join-judges-membership-at-every-depth-${v}";
    value =
      let
        C = {
          attrsOf = np.attrsOf;
          lazyAttrsOf = np.lazyAttrsOf;
          listOf = np.listOf;
        };
        vals = {
          inB2 = {
            k = "a";
            j = "b";
          };
          outB2 = {
            k = "a";
            j = "c";
          };
          outB2c = {
            k = "c";
            j = "c";
          };
        };
        w = x: if k == "listOf" then builtins.attrValues x else x;
        p = x: length (if isList x then x else builtins.attrNames x) <= 1;
        B = C.${k} (
          np.enum [
            "a"
            "b"
          ]
        );
        Y = C.${k} (
          np.enum [
            "b"
            "c"
          ]
        );
      in
      {
        expr =
          run
            [
              Y
              (gm.mkOptionType (copies.${c} p B))
            ]
            [ (w vals.${v}) ];
        expected = if v == "inB2" then "REFUSED" else run [ Y (np.addCheck B p) ] [ (w vals.${v}) ];
      };
  };
  # a `verify` stated by the caller, through `mkOptionType`, declared after its plain twin and twice: split definitions
  # each failing it merge to a value it admits, served with the twin's merge. `mem` reads members only the merged value
  # holds, so a per-definition read aborts. (Declared alone, and a lone failing definition at a redeclaration, are the
  # `verify` copy's own carriage, not this closure's.)
  vfs = {
    lenTwo = {
      t = np.listOf np.int;
      vf = v: if length v >= 2 then null else "need two";
      split = [
        [ 1 ]
        [ 2 ]
      ];
      merged = [
        2
        1
      ];
    };
    mem = {
      t = np.attrsOf np.int;
      vf = v: if v.a == 1 && v.b == 1 then null else "need a and b";
      split = [
        { a = 1; }
        { b = 1; }
      ];
      merged = {
        a = 1;
        b = 1;
      };
    };
  };
  verified = n: a: {
    name = "test-mkOptionType-verify-${n}-${a}-reads-the-merged-value";
    value =
      let
        V = vfs.${n};
        X = gm.mkOptionType (V.t // { verify = V.vf; });
        ts = arrs.${a} V.t X;
      in
      {
        expr = run ts V.split;
        expected = V.merged;
      };
  };
  # the door outside a nixpkgs container whose element is a gen submodule copy stating `verify`: the element's verify,
  # carried by the return's own rebuild, stays enforced under the closure
  element = d: k: {
    name = "test-${d}-${k}-of-a-verify-copy-keeps-the-elements-verify";
    value =
      let
        E = gSub // {
          verify = v: if pSub v then null else "a must not be 2";
        };
        C =
          {
            attrsOf = {
              m = np.attrsOf;
              w = v: { k = v; };
            };
            listOf = {
              m = np.listOf;
              w = v: [ v ];
            };
          }
          .${k};
        X = doors.${d} (C.m E);
      in
      {
        expr = {
          bad = run [ X ] [ (C.w { a = 2; }) ];
          ok = run [ X ] [ (C.w { a = 1; }) ];
        };
        expected = {
          bad = "REFUSED";
          ok = run [ (C.m npSub) ] [ (C.w { a = 1; }) ];
        };
      };
  };
  union = c: u: a: {
    name = "test-mkOptionType-${c}-in-${u}-${a}-takes-the-first-member-stating-no-headError";
    value =
      let
        X = gm.mkOptionType (copies.${c} (v: !(isAttrs v) || (v.a or 0) != 20) npSub);
        Y = np.attrsOf np.int;
        U =
          x:
          {
            either = np.either x Y;
            oneOf = np.oneOf [
              x
              Y
            ];
          }
          .${u};
        ts = arrs.${a} (U npSub) (U X);
      in
      {
        expr = {
          admitted = run ts [ { a = 1; } ];
          rejected = run ts [ { a = 20; } ];
          neither = run ts [ { a = "s"; } ];
        };
        expected = {
          admitted = {
            a = 1;
            b = 0;
          };
          rejected.a = 20;
          neither = "REFUSED";
        };
      };
  };
  # a nixpkgs v2 record with an ad-hoc `check` whose functor rebuilds the override, through `mkOptionType`: the join
  # nixpkgs asks the door for is decided on the join itself. A join that is the override again is refused by name, as
  # the all-nixpkgs twin's coherence guard refuses it; a coherent join is served with the twin's value, and owes the
  # check on the values the override's v2 merge admits (`xaa`, `xnull`), which the twin serves only by dropping it.
  # `npg` reads nixpkgs' engine over gen's export, `door` gen's engine; TL is the gen container first, LL the door twice.
  short = v: isList v && length v < 2;
  ea = np.enum [ "a" ];
  isA = p: (p.elemType.functor.payload.values or null) == [ "a" ];
  # `c`'s record over `elem` with check `p`, its functor returning the override at the payloads `at` holds and `c`'s
  # coherent record at any other
  overAt =
    c: p: at: elem:
    np.mkOptionType {
      inherit ((c elem)) name merge;
      check = p;
      functor = (c elem).functor // {
        type = q: if at q then overAt c p at q.elemType else c q.elemType;
      };
      nestedTypes.elemType = elem;
    };
  listInt = {
    np = np.listOf np.int;
    gt = gt.listOf np.int;
  };
  listB = {
    np = np.listOf (np.enum [ "b" ]);
    gt = gt.listOf (np.enum [ "b" ]);
  };
  overrides = {
    shortList = {
      p = np.mkOptionType {
        name = "listOf";
        check = short;
        inherit (listInt.np) merge;
        functor = {
          name = "listOf";
          wrapped = null;
          payload.elemType = np.int;
          type = _: overrides.shortList.p;
          binOp =
            a: b:
            let
              m = a.elemType.typeMerge b.elemType.functor;
            in
            if m == null then null else { elemType = m; };
        };
        nestedTypes.elemType = np.int;
      };
      beside = listInt;
    };
    lazyList = {
      p = np.mkOptionType {
        name = "listOf";
        check = isList;
        inherit (listInt.np) merge;
        functor = {
          name = "listOf";
          wrapped = null;
          payload = {
            elemType = np.int;
            lazy = true;
          };
          type = _: overrides.lazyList.p;
          binOp =
            a: b:
            let
              m = a.elemType.typeMerge b.elemType.functor;
            in
            if m == null then
              null
            else
              {
                elemType = m;
                inherit (a) lazy;
              };
        };
        nestedTypes.elemType = np.int;
      };
      beside = listInt;
    };
    shortOver = {
      p = listInt.np // {
        check = short;
      };
      beside = listInt;
    };
    hzP = {
      p = overAt np.listOf short isA ea;
      beside = listB;
    };
    hzQ = {
      p = overAt np.listOf (v: isList v && all (x: x == "a") v && length v < 2) isA ea;
      beside = listB;
    };
    hzR = {
      p = overAt np.listOf short (q: !(isA q)) ea;
      beside = listB;
    };
    hzN = {
      p = overAt np.nullOr (v: v != null) isA ea;
      beside = {
        np = np.nullOr (np.enum [ "b" ]);
        gt = gt.nullOr (np.enum [ "b" ]);
      };
    };
  };
  joinVals = {
    ok = [ 2 ];
    long = [
      2
      3
    ];
    a = [ "a" ];
    b = [ "b" ];
    ab = [
      "a"
      "b"
    ];
    xaa = [
      "a"
      "a"
    ];
    xnull = null;
  };
  runGen =
    ts: dv:
    let
      c =
        (gm.evalModuleTree { } (
          map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ map (v: { x = v; }) dv
        )).config;
      o = builtins.tryEval (builtins.deepSeq c.x c.x);
    in
    if o.success then o.value else "REFUSED";
  # `expect` is "REFUSED", or "twin": the all-nixpkgs twin's value in the same order
  overrideJoin =
    expect: pn: engine: a: vn:
    let
      h = overrides.${pn};
      D = gm.mkOptionType h.p;
      arr = {
        TL = s: P: [
          s
          P
        ];
        LT = s: P: [
          P
          s
        ];
        LL = _: P: [
          P
          P
        ];
      };
    in
    {
      name = "test-mkOptionType-override-join-${pn}-${engine}-${a}-${vn}";
      value = {
        expr = (if engine == "door" then runGen else run) (arr.${a} h.beside.gt D) [ joinVals.${vn} ];
        expected = if expect == "twin" then run (arr.${a} h.beside.np h.p) [ joinVals.${vn} ] else expect;
      };
    };
  overrideJoins =
    map (pt: overrideJoin "REFUSED" pt.p pt.e pt.a pt.v) [
      # the check oracle: inside the override's own parameters, rejected by its check
      {
        p = "shortList";
        e = "npg";
        a = "TL";
        v = "long";
      }
      {
        p = "shortList";
        e = "npg";
        a = "LL";
        v = "long";
      }
      {
        p = "hzP";
        e = "npg";
        a = "TL";
        v = "xaa";
      }
      {
        p = "hzP";
        e = "door";
        a = "TL";
        v = "xaa";
      }
      {
        p = "hzN";
        e = "npg";
        a = "TL";
        v = "xnull";
      }
      # the join is the override again, which the twin refuses
      {
        p = "shortList";
        e = "npg";
        a = "TL";
        v = "ok";
      }
      {
        p = "shortList";
        e = "npg";
        a = "LL";
        v = "ok";
      }
      {
        p = "shortList";
        e = "door";
        a = "TL";
        v = "ok";
      }
      {
        p = "shortList";
        e = "door";
        a = "LL";
        v = "ok";
      }
      {
        p = "lazyList";
        e = "npg";
        a = "TL";
        v = "ok";
      }
      {
        p = "lazyList";
        e = "npg";
        a = "LL";
        v = "ok";
      }
      {
        p = "lazyList";
        e = "door";
        a = "LL";
        v = "ok";
      }
      {
        p = "hzR";
        e = "npg";
        a = "TL";
        v = "a";
      }
      {
        p = "hzR";
        e = "door";
        a = "TL";
        v = "a";
      }
      {
        p = "hzP";
        e = "door";
        a = "LL";
        v = "a";
      }
    ]
    # regression pins: gen's engine refuses these through the override's own carriage, the join decision aside
    ++ map (pt: overrideJoin "REFUSED" pt.p "door" pt.a pt.v) [
      {
        p = "lazyList";
        a = "TL";
        v = "ok";
      }
      {
        p = "shortList";
        a = "TL";
        v = "long";
      }
      {
        p = "shortList";
        a = "LL";
        v = "long";
      }
    ]
    # a coherent join, served with the twin's value: a value outside the override's own parameters is not its check's
    # to judge (the widening law), and a join the override's functor does not rebuild is not refused for its partner
    ++ map (pt: overrideJoin "twin" pt.p pt.e pt.a pt.v) (
      concatMap
        (e: [
          {
            p = "hzP";
            inherit e;
            a = "TL";
            v = "a";
          }
          {
            p = "hzP";
            inherit e;
            a = "TL";
            v = "b";
          }
          {
            p = "hzP";
            inherit e;
            a = "TL";
            v = "ab";
          }
          {
            p = "shortList";
            inherit e;
            a = "LT";
            v = "ok";
          }
        ])
        [
          "npg"
          "door"
        ]
      ++ [
        {
          p = "hzQ";
          e = "npg";
          a = "TL";
          v = "b";
        }
        {
          p = "shortOver";
          e = "npg";
          a = "TL";
          v = "ok";
        }
      ]
    );
  # a NON-v2 record (plain merge) over `c (enum ["a"])` with check `p`, whose functor returns itself at its own payload
  # and `other`'s record at any other: rebuilt by its own functor, it is the record whose check is the debt, so its own
  # parameters are judged by gen's constructor for its functor name at its payload, and a value inside them its check
  # rejects is refused by name where the all-nixpkgs twin serves it. A value outside them is served with the twin's value
  legacyAt =
    c: p: merge: other: elem:
    np.mkOptionType {
      inherit ((c elem)) name;
      check = p;
      inherit merge;
      functor = (c elem).functor // {
        type = q: if isA q then legacyAt c p merge other q.elemType else other q.elemType;
      };
      nestedTypes.elemType = elem;
    };
  plain = _: defs: concatMap (d: d.value) defs;
  shortA = v: isAttrs v && length (builtins.attrNames v) < 2;
  lax =
    elem:
    np.mkOptionType {
      name = "listOf";
      check = isList;
      merge = plain;
      functor = (np.listOf elem).functor // {
        type = q: lax q.elemType;
      };
      nestedTypes.elemType = elem;
    };
  # the lax record in nixpkgs' v2 protocol, its `isList` check marked coherent (it is: `headError` is `isList`)
  laxV =
    elem:
    np.mkOptionType {
      name = "listOf";
      check = {
        __functor = _: isList;
        isV2MergeCoherent = true;
      };
      merge = {
        __functor =
          self: loc: defs:
          (self.v2 { inherit loc defs; }).value;
        v2 =
          { loc, defs }:
          {
            headError = if all (d: isList d.value) defs then null else { message = "not a list"; };
            value = plain loc defs;
            valueMeta = { };
          };
      };
      functor = (np.listOf elem).functor // {
        type = q: laxV q.elemType;
      };
      nestedTypes.elemType = elem;
    };
  gLcAt = legacyAt np.listOf short plain gLcAt;
  stocksOf = c: {
    np = {
      T = c.np (np.enum [ "b" ]);
      U = c.np (np.enum [ "c" ]);
    };
    gt = {
      T = c.gt (np.enum [ "b" ]);
      U = c.gt (np.enum [ "c" ]);
    };
  };
  L = {
    np = np.listOf;
    gt = gt.listOf;
  };
  N = {
    np = np.nullOr;
    gt = gt.nullOr;
  };
  A = {
    np = np.attrsOf;
    gt = gt.attrsOf;
  };
  # an author record named `either`, nixpkgs' member-wise relation, itself at its own members and nixpkgs' `either`
  # elsewhere; beside nixpkgs' `either` stocks in every column
  eitherAt =
    l: r:
    np.mkOptionType rec {
      name = "either";
      check = v: v == "a";
      merge = nl.mergeEqualOption;
      functor = (np.either l r).functor // {
        type =
          a: b:
          if
            (a.functor.payload.values or null) == [ "a" ] && (b.functor.payload.values or null) == [ "x" ]
          then
            eitherAt a b
          else
            np.either a b;
      };
      typeMerge =
        f':
        let
          mt1 = l.typeMerge (builtins.head f'.payload.elemType).functor;
          mt2 = r.typeMerge (builtins.elemAt f'.payload.elemType 1).functor;
        in
        if f'.name == "either" && mt1 != null && mt2 != null then functor.type mt1 mt2 else null;
      nestedTypes.left = l;
      nestedTypes.right = r;
    };
  owns = {
    gL = {
      p = legacyAt np.listOf short plain np.listOf ea;
      beside = stocksOf L;
    };
    gLN = {
      p = legacyAt np.nullOr (v: v != null) (_: defs: (builtins.head defs).value) np.nullOr ea;
      beside = stocksOf N;
    };
    gLA = {
      p = legacyAt np.attrsOf shortA (
        _: defs: builtins.foldl' (a: d: a // d.value) { } defs
      ) np.attrsOf ea;
      beside = stocksOf A;
    };
    gLc = {
      p = gLcAt ea;
      beside = stocksOf L;
    };
    gLg = {
      p = legacyAt np.listOf short plain gt.listOf ea;
      beside = stocksOf L;
    };
    gLw = {
      p = legacyAt np.listOf short plain lax ea;
      beside = stocksOf L;
    };
    gLv = {
      p = legacyAt np.listOf short plain laxV ea;
      beside = stocksOf L;
    };
    # the lax record completed by gen's door; its twin is the raw lax record, whose semantics the completion keeps
    gLd = {
      p = legacyAt np.listOf short plain (elem: gm.mkOptionType (lax elem)) ea;
      twin = legacyAt np.listOf short plain lax ea;
      beside = stocksOf L;
    };
    gE = {
      p = eitherAt (np.enum [ "a" ]) (np.enum [ "x" ]);
      beside = rec {
        np = {
          T = nl.types.either (nl.types.enum [ "b" ]) (nl.types.enum [ "y" ]);
          U = nl.types.either (nl.types.enum [ "c" ]) (nl.types.enum [ "z" ]);
        };
        gt = np;
      };
    };
  };
  ownVals = joinVals // {
    bb = [
      "b"
      "b"
    ];
    xaaA = {
      k = "a";
      j = "a";
    };
    x = "x";
  };
  # `cell`: "<partner> <engine> <order> <value>", the order a word over T, U (the stocks) and P (the partner); engines
  # `npg` (nixpkgs' fold over the door's return), `door` (gen's), `raw` (gen's, the record undoored), and `npg2` / `door2`
  # through the second door (`types.mkOptionType`). `expect` is "REFUSED", "twin" or "control" (a twin cell the
  # partner's own check admits, which never reaches the judge)
  ownJoin =
    expect: cell:
    let
      w = builtins.filter builtins.isString (builtins.split " " cell);
      pn = elemAt w 0;
      engine = elemAt w 1;
      order = elemAt w 2;
      h = owns.${pn};
      at =
        S: P:
        builtins.genList (
          i:
          let
            l = builtins.substring i 1 order;
          in
          if l == "P" then P else S.${l}
        ) (builtins.stringLength order);
      D =
        {
          npg = gm.mkOptionType h.p;
          door = gm.mkOptionType h.p;
          raw = h.p;
          npg2 = gt.mkOptionType h.p;
          door2 = gt.mkOptionType h.p;
        }
        .${engine};
      v = ownVals.${elemAt w 3};
    in
    {
      name = "test-mkOptionType-own-parameters-${pn}-${engine}-${order}-${elemAt w 3}${
        if expect == "control" then "-control" else ""
      }";
      value = {
        expr = (if engine == "npg" || engine == "npg2" then run else runGen) (at h.beside.gt D) [ v ];
        expected = if expect == "REFUSED" then expect else run (at h.beside.np (h.twin or h.p)) [ v ];
      };
    };
  ownParameters =
    map (ownJoin "REFUSED") [
      "gL npg TP xaa"
      "gL npg PT xaa"
      "gL door TP xaa"
      "gL door PT xaa"
      "gL raw TP xaa"
      "gL raw PT xaa"
      "gLN npg TP xnull"
      "gLN npg PT xnull"
      "gLN door TP xnull"
      "gLN door PT xnull"
      "gLN raw TP xnull"
      "gLN raw PT xnull"
      "gLA npg TP xaaA"
      "gLA npg PT xaaA"
      "gLA raw TP xaaA"
      "gLA raw PT xaaA"
      "gLc door PT xaa"
      "gLg npg TP xaa"
      # N >= 3
      "gL door TPU xaa"
      "gL npg UTPP xaa"
      "gLN door UPT xnull"
      "gLA npg TPUP xaaA"
      "gLN raw TPU xnull"
      # a functor returning a lax record away from its own payload: non-v2, v2 coherence-marked, gen-completed
      "gLw door TP xaa"
      "gLw npg PT xaa"
      "gLw npg TP xaa"
      "gLv door TP xaa"
      "gLv npg TP xaa"
      "gLd door TP xaa"
      "gLd npg TP xaa"
      # the alternatives role
      "gE door TP x"
      "gE npg TP x"
      # the second door
      "gL door2 TP xaa"
      "gL door2 PT xaa"
      "gL npg2 TP xaa"
      "gL npg2 PT xaa"
    ]
    # outside the partner's own parameters: no lax join stands in for its domain
    ++ map (ownJoin "twin") (
      concatMap
        (o: [
          "gLv ${o} ab"
          "gLv ${o} bb"
        ])
        [
          "npg TP"
          "npg PT"
          "npg TPU"
          "npg PTU"
          "npg UPT"
          "npg TPUP"
          "npg PTPU"
          "door TP"
        ]
      ++ [ "gLv door TPUP bb" ]
      ++
        concatMap
          (
            pn:
            concatMap
              (o: [
                "${pn} ${o} ab"
                "${pn} ${o} bb"
              ])
              [
                "door TP"
                "npg PT"
                "npg PTU"
                "npg UPT"
              ]
          )
          [
            "gLw"
            "gLd"
          ]
      ++
        concatMap
          (o: [
            "gL ${o} ab"
            "gL ${o} bb"
          ])
          [
            "npg TP"
            "npg PT"
            "door TP"
            "door PT"
          ]
    )
    ++ map (ownJoin "control") (
      concatMap
        (o: [
          "gL ${o} a"
          "gL ${o} b"
        ])
        [
          "npg TP"
          "npg PT"
          "door TP"
          "door PT"
        ]
    );
in
{
  flake.tests.door-return-closed = listToAttrs (
    checkCells
    ++ overrideJoins
    ++ ownParameters
    ++ map widened [
      "none"
      "addCheck"
    ]
    ++ concatMap (
      c:
      concatMap
        (
          k:
          map (widenedIn c k) [
            "inB2"
            "outB2"
            "outB2c"
          ]
        )
        [
          "attrsOf"
          "lazyAttrsOf"
          "listOf"
        ]
    ) (builtins.attrNames copies)
    ++ concatMap (
      n:
      map (verified n) [
        "TL"
        "LL"
      ]
    ) (builtins.attrNames vfs)
    ++ concatMap (
      d:
      map (element d) [
        "attrsOf"
        "listOf"
      ]
    ) (builtins.attrNames doors)
    ++ concatMap (
      c:
      concatMap
        (
          u:
          map (union c u) [
            "TL"
            "LL"
          ]
        )
        [
          "either"
          "oneOf"
        ]
    ) (builtins.attrNames copies)
  );
}
