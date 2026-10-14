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
#    the redeclaration, so these values are served beyond nixpkgs, under this law.
# Red: every check cell with `imported` reverted to `t: r: r`; the `elemG` cells with `substructure` left out; the
# widening cells with the join's check taken whole; the container widening cells outside the parameters with
# membership read by the base's `check` alone; the verify and element cells with the closure built from the
# door's return instead of the caller's record (P11).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins)
    all
    concatMap
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
in
{
  flake.tests.door-return-closed = listToAttrs (
    checkCells
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
