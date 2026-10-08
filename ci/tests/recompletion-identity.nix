# RE-COMPLETING A COMPLETED RECORD KEEPS THE WITNESSES IT ARRIVED WITH (den-hoag-59gnz). The two doors
# that re-complete a caller's record, the published `types.defineType` and `mkOptionType`, never re-tie
# the check witness over a check they did not derive (C1), and the published `defineType` keeps the
# stale stamp of a copy whose distinguishing content changed (C2), so the copy is read as the raw copy
# is: its own check enforced alone and beside its twin, its identity refused by name. A copy departing
# only at fields a door does not read keeps its completion's identity (C3). At a module set, the
# redeclaration step carries a dropped witnessed rewrite's check (C4), so an ad-hoc override of a gen
# submodule is enforced beside its twin (owner-ruled 2026-10-08, arm (b)).
#
# `p` rejects the `bad` value and admits the `ok` one; the base admits both. A cell reads the served
# value, or "REFUSED" for a catchable refusal.
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  np = nixpkgsLib.types;
  inherit (builtins) deepSeq tryEval;
  try =
    v:
    let
      r = tryEval (deepSeq v v);
    in
    if r.success then r.value else "REFUSED";
  ev =
    tys: val:
    try
      (gm.evalModuleTree { } (
        map (ty: { options.x = gm.mkOption { type = ty; }; }) tys ++ [ { x = val; } ]
      )).config.x;
  # the nixpkgs engine mounting a type, which reads the foreign protocol's derived fields
  mount =
    ty: val:
    try
      (nixpkgsLib.evalModules {
        modules = [
          { options.x = nixpkgsLib.mkOption { type = ty; }; }
          { x = val; }
        ];
      }).config.x;
  # `idOf` against the plain type's: "=" | "!=" | "REFUSED"
  id =
    base: x:
    let
      r = tryEval (genTypes.idOf x);
    in
    if !r.success then
      "REFUSED"
    else if r.value == genTypes.idOf base then
      "="
    else
      "!=";
  # one door's re-completion of `x`: alone, and beside its plain twin in both orders
  row = base: x: bad: ok: {
    id = id base x;
    alone = ev [ x ] bad;
    twinFirstBad = ev [ base x ] bad;
    twinLastBad = ev [ x base ] bad;
    twinFirstOk = ev [ base x ] ok;
    twinLastOk = ev [ x base ] ok;
  };
  enforced = bad: ok: {
    id = "REFUSED";
    alone = "REFUSED";
    twinFirstBad = "REFUSED";
    twinLastBad = "REFUSED";
    twinFirstOk = ok;
    twinLastOk = ok;
  };

  int = gt.int;
  pInt = v: v != 1;
  intAdd = np.addCheck int pInt;
  intOvr = int // {
    check = v: int.check v && pInt v;
  };
  enum = gt.enum "e" [
    "a"
    "b"
  ];
  pEnum = v: v != "a";
  enumAdd = np.addCheck enum pEnum;
  enumVer = enum // {
    verify = v: if pEnum v then null else "rejected by p";
  };
  S = gt.submodule { options.a = gm.mkOption { type = gt.int; }; };
  pS = v: v.a != 1;
  sOvr = S // {
    check = v: S.check v && pS v;
  };
  sAdd = np.addCheck S pS;
  sBoth = sOvr // {
    verify = v: if pS v then (S.verify or (_: null)) v else "rejected by p";
  };
  doors = {
    raw = x: x;
    inherit (gt) defineType;
    inherit (gm) mkOptionType;
  };
  # a module-set row: alone, beside the plain submodule both orders, and twice
  subRow = x: {
    aloneOk = ev [ x ] { a = 2; };
    aloneBad = ev [ x ] { a = 1; };
    twinFirstOk = ev [ S x ] { a = 2; };
    twinLastOk = ev [ x S ] { a = 2; };
    twinFirstBad = ev [ S x ] { a = 1; };
    twinLastBad = ev [ x S ] { a = 1; };
    twiceOk = ev [ x x ] { a = 2; };
    twiceBad = ev [ x x ] { a = 1; };
  };
  subEnforced = {
    aloneOk.a = 2;
    aloneBad = "REFUSED";
    twinFirstOk.a = 2;
    twinLastOk.a = 2;
    twinFirstBad = "REFUSED";
    twinLastBad = "REFUSED";
    twiceOk.a = 2;
    twiceBad = "REFUSED";
  };
  attrsInt = gt.attrsOf gt.int;
  overridesMerge =
    t:
    t
    // {
      merge = _: _: { forced = 1; };
    };
in
{
  flake.tests.recompletion-identity = {
    # C1: a check-modified copy re-completed through either door is enforced alone and beside its twin,
    # and its identity is refused by name, as the raw copy's is.
    test-a-check-modified-copy-is-enforced-through-each-door = {
      expr = {
        addDefine = row int (gt.defineType intAdd) 1 2;
        ovrDefine = row int (gt.defineType intOvr) 1 2;
        addImport = row int (gm.mkOptionType intAdd) 1 2;
        ovrImport = row int (gm.mkOptionType intOvr) 1 2;
        raw = row int intAdd 1 2;
      };
      expected = {
        addDefine = enforced 1 2;
        ovrDefine = enforced 1 2;
        addImport = enforced 1 2;
        ovrImport = enforced 1 2;
        raw = enforced 1 2;
      };
    };
    # C1 one level up: a composite over a re-completed copy does not take the plain composite's
    # identity, and the element's check is enforced beside the plain container.
    test-a-composite-over-a-recompleted-copy-is-not-the-plain-composite = {
      expr = {
        listId = id (gt.listOf int) (gt.listOf (gt.defineType intAdd));
        nullOrId = id (gt.nullOr int) (gt.nullOr (gt.defineType intAdd));
        listBesidePlainBad =
          ev
            [
              (gt.listOf int)
              (gt.listOf (gt.defineType intAdd))
            ]
            [ 1 ];
        listBesidePlainOk =
          ev
            [
              (gt.listOf (gt.mkOptionType intAdd))
              (gt.listOf int)
            ]
            [ 2 ];
      };
      expected = {
        listId = "REFUSED";
        nullOrId = "REFUSED";
        listBesidePlainBad = "REFUSED";
        listBesidePlainOk = [ 2 ];
      };
    };
    # C2: the published `defineType` keeps a verify-only copy's stale stamp, so its identity is refused,
    # and beside its twin the value the copy admits is served, as it is raw.
    test-a-verify-only-copy-keeps-its-stale-stamp = {
      expr = {
        id = id enum (gt.defineType enumVer);
        twinFirstOk = ev [
          enum
          (gt.defineType enumVer)
        ] "b";
        twinLastOk = ev [
          (gt.defineType enumVer)
          enum
        ] "b";
        rawId = id enum enumVer;
      };
      expected = {
        id = "REFUSED";
        twinFirstOk = "b";
        twinLastOk = "b";
        rawId = "REFUSED";
      };
    };
    # C3: a copy departing only at fields a door does not read keeps its completion's identity there.
    # `defineType` re-derives the description and every caller field; the import door reads neither a
    # caller field nor the description. A check-rewriting copy keeps its mark at the import door, so
    # beside its twin the value both admit is served.
    test-a-metadata-only-copy-keeps-its-completions-identity = {
      expr = {
        tagDefine = id int (gt.defineType (int // { myTag = 1; }));
        descDefine = id int (gt.defineType (int // { description = "a described copy"; }));
        tagImport = id int (gm.mkOptionType (int // { myTag = 1; }));
        descImport = id int (gm.mkOptionType (int // { description = "a described copy"; }));
        enumAddImportOk = [
          (ev [
            enum
            (gm.mkOptionType enumAdd)
          ] "b")
          (ev [
            (gm.mkOptionType enumAdd)
            enum
          ] "b")
        ];
      };
      expected = {
        tagDefine = "=";
        descDefine = "=";
        tagImport = "=";
        descImport = "=";
        enumAddImportOk = [
          "b"
          "b"
        ];
      };
    };
    # C3 on the row path (gate G-1): a record completed under a row is returned as it is, so every field
    # it publishes survives the door, and a copy overriding one (`merge`, which nixpkgs' engine reads)
    # does not keep its base's identity. Mounted in nixpkgs, the override is re-derived away.
    test-a-row-completed-copy-overriding-a-published-field-is-not-its-base = {
      expr = {
        id = id attrsInt (gt.defineType (overridesMerge attrsInt));
        mounted = mount (gt.defineType (overridesMerge attrsInt)) { k = 1; };
        noRowMounted = mount (gt.defineType (overridesMerge int)) 1;
      };
      expected = {
        id = "REFUSED";
        mounted.k = 1;
        noRowMounted = 1;
      };
    };
    # THE STATED INCOHERENCE, pinned (spec OQ-T1): a renamed copy keeps its identity at both doors,
    # while the relation keys on the name and refuses it beside the plain type.
    test-a-renamed-copy-is-one-type-by-identity-and-two-by-its-relation = {
      expr = {
        defineId = id int (gt.defineType (int // { name = "port"; }));
        importId = id int (gm.mkOptionType (int // { name = "port"; }));
        typeEq = genTypes.typeEq int (gt.defineType (int // { name = "port"; }));
        listBeside =
          ev
            [
              (gt.listOf int)
              (gt.listOf (gt.defineType (int // { name = "port"; })))
            ]
            [ 1 ];
      };
      expected = {
        defineId = "=";
        importId = "=";
        typeEq = true;
        listBeside = "REFUSED";
      };
    };
    # THE STATED EXCLUSION, pinned (spec §2.5 F3): a foreign record states no check witness, so a
    # wrapper over a nixpkgs type re-completed through `defineType` is not seen as a rewrite.
    test-a-foreign-wrapper-through-defineType-is-outside-the-class = {
      expr = ev [ (gt.defineType (np.addCheck np.int pInt)) ] 1;
      expected = 1;
    };
    # C4 and the owner ruling (b): at a module set, a witnessed rewrite of a gen submodule (the ad-hoc
    # `// { check }` override, nixpkgs' `addCheck`, which over a non-v2 type is that override, and the
    # override with a `verify`) is enforced alone, twice and beside the plain submodule in both orders,
    # raw and through each door.
    test-a-module-set-override-is-enforced-beside-its-twin = {
      expr = builtins.mapAttrs (
        _: door:
        builtins.mapAttrs (_: x: subRow (door x)) {
          ovr = sOvr;
          add = sAdd;
          both = sBoth;
        }
      ) doors;
      expected = builtins.mapAttrs (_: _: {
        ovr = subEnforced;
        add = subEnforced;
        # the `both` form refuses its `ok` value declared alone, raw and through each door alike (its
        # `verify` reads the submodule's definition as the plain submodule's does not); pre-existing
        both = subEnforced // {
          aloneOk = "REFUSED";
        };
      }) doors;
    };
    # C4 beyond the bare position: element positions, three declarations, and the freeform plane, which
    # the declaration list's fixup does not run on.
    test-the-module-set-carriage-reaches-every-plane = {
      expr = {
        listOf = [
          (ev
            [
              (gt.listOf S)
              (gt.listOf sOvr)
            ]
            [ { a = 2; } ]
          )
          (ev
            [
              (gt.listOf sOvr)
              (gt.listOf S)
            ]
            [ { a = 1; } ]
          )
        ];
        three = [
          (ev [
            S
            sAdd
            S
          ] { a = 2; })
          (ev [
            S
            sAdd
            S
          ] { a = 1; })
        ];
        freeform =
          let
            r =
              v:
              try
                (gm.evalModuleTree { } [
                  { freeformType = gt.lazyAttrsOf S; }
                  { freeformType = gt.lazyAttrsOf sOvr; }
                  { q = v; }
                ]).config.q;
          in
          [
            (r { a = 2; })
            (r { a = 1; })
          ];
      };
      expected = {
        listOf = [
          [ { a = 2; } ]
          "REFUSED"
        ];
        three = [
          { a = 2; }
          "REFUSED"
        ];
        freeform = [
          { a = 2; }
          "REFUSED"
        ];
      };
    };
  };
}
