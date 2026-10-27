# gen-merge: a type returned by the `mkOptionType` door (either door, `gm.mkOptionType` and `types.mkOptionType`)
# states its relation (`retainedRelation`) beside gen's role (`carries`), and at the element and embedding pairs it
# is joined in that relation where gen cannot read it whole and the door return's own relation answers the pair with
# no ad-hoc override. Each row is read by gen's engine and, over the SAME declared types, by nixpkgs'
# `lib.evalModules`, which reads the gen records through their exported protocol. RED (the row `"REFUSED"`) where
# the pair guards read `? carries` alone and take the door return for a gen partner, so the embedding-row join and
# THE MEET are skipped and the pair answers "a partner that states no element type of its own". A door return
# whose element check rejects the value is refused by the meet where nixpkgs drops the check; those are pinned by
# name on the error plane (`tests-error.nix`, `door-partner`). The OVERRIDE cells read the payload-dependent
# partners against nixpkgs' twin (`twin`): RED (served) where the door return's own join is not asked, or is walked
# along its element alone (an override under `either`) or past an option-shaped role (`attrTag`); RED (refused)
# where a door return gen reads whole is re-routed to the stated relation.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  nl = nixpkgsLib;
  gt = gm.types;
  np = nl.types;
  door = gm.mkOptionType;
  tdoor = gt.mkOptionType;
  json =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x (builtins.toJSON x));
    in
    if r.success then r.value else "REFUSED";
  gen =
    ts: v:
    json
      (gm.evalModuleTree { } (map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ [ { x = v; } ]))
      .config.x;
  npe =
    ts: v:
    json
      (nl.evalModules {
        modules = map (t: { options.x = nl.mkOption { type = t; }; }) ts ++ [ { x = v; } ];
      }).config.x;
  sub = np.submodule { options.a = nl.mkOption { type = np.int; }; };
  p = v: !(builtins.isAttrs v) || (v.a or 0) != 1;
  aI = gt.attrsOf np.int;
  phId = np.attrsWith {
    elemType = np.int;
    placeholder = "id";
  };
  # a raw `attrsWith`-named partner whose payload states a parameter no embedding row has
  rawExtraAttrs = np.mkOptionType {
    name = "attrsOf";
    check = builtins.isAttrs;
    merge = (np.attrsOf np.int).merge;
    functor = {
      name = "attrsWith";
      wrapped = null;
      payload = {
        elemType = np.int;
        lazy = false;
        placeholder = "name";
        extra = 1;
      };
      type = _: rawExtraAttrs;
      binOp =
        a: b:
        let
          m = a.elemType.typeMerge b.elemType.functor;
        in
        if m == null then null else a // { elemType = m; };
    };
    nestedTypes.elemType = np.int;
  };
  # a module value is compared by the configuration it evaluates to: a static module declares `a`, the definition
  # sets it
  staticA = np.deferredModuleWith {
    staticModules = [ { options.a = nl.mkOption { default = 1; }; } ];
  };
  configOf =
    m:
    let
      r = builtins.tryEval (builtins.deepSeq m m);
    in
    if r.success then json (nl.evalModules { modules = [ r.value ]; }).config else "REFUSED";
  genV =
    ts: v:
    (gm.evalModuleTree { } (map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ [ { x = v; } ]))
    .config.x;
  npV =
    ts: v:
    (nl.evalModules {
      modules = map (t: { options.x = nl.mkOption { type = t; }; }) ts ++ [ { x = v; } ];
    }).config.x;
  # each row: the declared types in order, and the value
  rows = {
    aoInt-TL = [
      [
        aI
        (door aI)
      ]
      { k = 2; }
    ];
    aoInt-LT = [
      [
        (door aI)
        aI
      ]
      { k = 2; }
    ];
    aoStr-TL = [
      [
        (gt.attrsOf np.str)
        (door (gt.attrsOf np.str))
      ]
      { k = "s"; }
    ];
    aoStr-LT = [
      [
        (door (gt.attrsOf np.str))
        (gt.attrsOf np.str)
      ]
      { k = "s"; }
    ];
    aoSub-TL = [
      [
        (gt.attrsOf sub)
        (door (gt.attrsOf sub))
      ]
      { k.a = 2; }
    ];
    aoSub-LT = [
      [
        (door (gt.attrsOf sub))
        (gt.attrsOf sub)
      ]
      { k.a = 2; }
    ];
    aoAo-TL = [
      [
        (gt.attrsOf aI)
        (door (gt.attrsOf aI))
      ]
      { k.j = 2; }
    ];
    aoAo-LT = [
      [
        (door (gt.attrsOf aI))
        (gt.attrsOf aI)
      ]
      { k.j = 2; }
    ];
    aoLo-TL = [
      [
        (gt.attrsOf (gt.listOf np.int))
        (door (gt.attrsOf (gt.listOf np.int)))
      ]
      { k = [ 2 ]; }
    ];
    aoLo-LT = [
      [
        (door (gt.attrsOf (gt.listOf np.int)))
        (gt.attrsOf (gt.listOf np.int))
      ]
      { k = [ 2 ]; }
    ];
    laoInt-TL = [
      [
        (gt.lazyAttrsOf np.int)
        (door (gt.lazyAttrsOf np.int))
      ]
      { k = 2; }
    ];
    laoInt-LT = [
      [
        (door (gt.lazyAttrsOf np.int))
        (gt.lazyAttrsOf np.int)
      ]
      { k = 2; }
    ];
    r5-TL = [
      [
        (gt.attrsOf sub)
        (door (gt.attrsOf (np.addCheck sub p)))
      ]
      { k.a = 2; }
    ];
    r5-LT = [
      [
        (door (gt.attrsOf (np.addCheck sub p)))
        (gt.attrsOf sub)
      ]
      { k.a = 2; }
    ];
    dm-TL = [
      [
        gt.deferredModule
        (door gt.deferredModule)
      ]
      { }
    ];
    dm-LT = [
      [
        (door gt.deferredModule)
        gt.deferredModule
      ]
      { }
    ];
    dmThree-TL = [
      [
        gt.deferredModule
        (door gt.deferredModule)
      ]
      { }
    ];
    dmThree-LT = [
      [
        (door gt.deferredModule)
        gt.deferredModule
      ]
      { }
    ];
    dmNpDoor-TL = [
      [
        gt.deferredModule
        (door np.deferredModule)
      ]
      { }
    ];
    aoDoorNp-TL = [
      [
        aI
        (door (np.attrsOf np.int))
      ]
      { k = 2; }
    ];
    aoDoorNp-LT = [
      [
        (door (np.attrsOf np.int))
        aI
      ]
      { k = 2; }
    ];
    laoDoorNp-TL = [
      [
        (gt.lazyAttrsOf np.int)
        (door (np.lazyAttrsOf np.int))
      ]
      { k = 2; }
    ];
    phId-door-TL = [
      [
        aI
        (door phId)
      ]
      { k = 2; }
    ];
    phId-door-LT = [
      [
        (door phId)
        aI
      ]
      { k = 2; }
    ];
    rawExtraDoor-TL = [
      [
        aI
        (door rawExtraAttrs)
      ]
      { k = 2; }
    ];
    tdAoInt-TL = [
      [
        aI
        (tdoor aI)
      ]
      { k = 2; }
    ];
    tdAoInt-LT = [
      [
        (tdoor aI)
        aI
      ]
      { k = 2; }
    ];
    tdLaoSub-TL = [
      [
        (gt.lazyAttrsOf sub)
        (tdoor (gt.lazyAttrsOf (np.addCheck sub p)))
      ]
      { k.a = 2; }
    ];
    tdDm-TL = [
      [
        gt.deferredModule
        (tdoor gt.deferredModule)
      ]
      { }
    ];
    tdPhId-TL = [
      [
        aI
        (tdoor phId)
      ]
      { k = 2; }
    ];
    # one level down, at any depth, and the door over its own output
    inLo-TL = [
      [
        (gt.listOf aI)
        (gt.listOf (door aI))
      ]
      [ { k = 2; } ]
    ];
    inLo-LT = [
      [
        (gt.listOf (door aI))
        (gt.listOf aI)
      ]
      [ { k = 2; } ]
    ];
    inAo-TL = [
      [
        (gt.attrsOf aI)
        (gt.attrsOf (door aI))
      ]
      { j.k = 2; }
    ];
    inAo-LT = [
      [
        (gt.attrsOf (door aI))
        (gt.attrsOf aI)
      ]
      { j.k = 2; }
    ];
    inNo-TL = [
      [
        (gt.nullOr (gt.lazyAttrsOf np.int))
        (gt.nullOr (door (gt.lazyAttrsOf np.int)))
      ]
      { k = 2; }
    ];
    inEi-TL = [
      [
        (gt.either np.str aI)
        (gt.either np.str (door aI))
      ]
      { k = 2; }
    ];
    in2Ao-TL = [
      [
        (gt.attrsOf (gt.attrsOf aI))
        (gt.attrsOf (gt.attrsOf (door aI)))
      ]
      { i.j.k = 2; }
    ];
    in2Ao-LT = [
      [
        (gt.attrsOf (gt.attrsOf (door aI)))
        (gt.attrsOf (gt.attrsOf aI))
      ]
      { i.j.k = 2; }
    ];
    in2Lo-TL = [
      [
        (gt.listOf (gt.listOf aI))
        (gt.listOf (gt.listOf (door aI)))
      ]
      [ [ { k = 2; } ] ]
    ];
    dd-TL = [
      [
        aI
        (door (door aI))
      ]
      { k = 2; }
    ];
  };
  # served at the base and at the fix alike: the carrying types whose payload is the role's key alone, the leaves,
  # and the door over nixpkgs' other combinators
  three = f: bare: v: {
    "${f}-TL" = [
      [
        bare
        (door bare)
      ]
      v
    ];
    "${f}-LT" = [
      [
        (door bare)
        bare
      ]
      v
    ];
    "${f}-LL" = [
      [
        (door bare)
        (door bare)
      ]
      v
    ];
  };
  controls =
    three "loInt" (gt.listOf np.int) [ 2 ]
    // three "noInt" (gt.nullOr np.int) 2
    // three "eiInt" (gt.either np.int np.str) 2
    // three "enumA" (gt.enum "e" [ "a" ]) "a"
    // three "leafInt" gt.int 2
    // three "leafStr" gt.str "s"
    // three "leafString" gt.string "s"
    // three "leafPath" gt.path "/x"
    // three "leafPathLike" gt.pathLike "/x"
    // three "leafNumber" gt.number 2
    // three "subInt" (gt.submodule { options.a = gm.mkOption { type = gt.int; }; }) { a = 2; }
    // {
      eiNpDoor-TL = [
        [
          (gt.either np.int np.str)
          (door (np.either np.int np.str))
        ]
        2
      ];
      eiNpDoor-LT = [
        [
          (door (np.either np.int np.str))
          (gt.either np.int np.str)
        ]
        2
      ];
      loNpDoor-TL = [
        [
          (gt.listOf np.int)
          (door (np.listOf np.int))
        ]
        [ 2 ]
      ];
      loNpDoor-LT = [
        [
          (door (np.listOf np.int))
          (gt.listOf np.int)
        ]
        [ 2 ]
      ];
      noNpDoor-TL = [
        [
          (gt.nullOr np.int)
          (door (np.nullOr np.int))
        ]
        2
      ];
      subNpDoor-TL = [
        [
          (gt.submodule { options.a = gm.mkOption { type = gt.int; }; })
          (door (np.submodule { options.a = nl.mkOption { type = np.int; }; }))
        ]
        { a = 2; }
      ];
      pathNpDoor-TL = [
        [
          gt.path
          (door np.path)
        ]
        "/x"
      ];
    };
  # the payload-dependent partners (`door-return-closed.nix`'s override family), each with gen's container `G` it is
  # declared beside, nixpkgs' twin `T` of that container, and the values read
  short = v: builtins.isList v && builtins.length v < 2;
  short1 = v: builtins.isAttrs v && builtins.length (builtins.attrNames v) < 2;
  shortList = np.mkOptionType {
    name = "listOf";
    check = short;
    inherit (np.listOf np.int) merge;
    functor = {
      name = "listOf";
      wrapped = null;
      payload.elemType = np.int;
      type = _: shortList;
      binOp =
        a: b:
        let
          m = a.elemType.typeMerge b.elemType.functor;
        in
        if m == null then null else { elemType = m; };
    };
    nestedTypes.elemType = np.int;
  };
  isA = q: (q.elemType.functor.payload.values or null) == [ "a" ];
  # an ad-hoc override whose functor returns the override at the payloads `at` holds and the coherent constructor at
  # any other: over `listOf` / `nullOr`, and over `attrsWith` (the embedding path)
  overAt =
    c: check: at: elem:
    np.mkOptionType {
      inherit (c elem) name merge;
      inherit check;
      functor = (c elem).functor // {
        type = q: if at q then overAt c check at q.elemType else c q.elemType;
      };
      nestedTypes.elemType = elem;
    };
  overAtA =
    check: at: elem:
    np.mkOptionType {
      inherit (np.attrsOf elem) name merge;
      inherit check;
      functor = (np.attrsOf elem).functor // {
        type = q: if at q then overAtA check at q.elemType else np.attrsWith q;
      };
      nestedTypes.elemType = elem;
    };
  enumOf = g: n: {
    G = g (np.enum [ "b" ]);
    T = n (np.enum [ "b" ]);
  };
  listVals = {
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
  };
  attrVals = {
    a.k = "a";
    b.k = "b";
    xaa = {
      k = "a";
      j = "a";
    };
    ab = {
      k = "a";
      j = "b";
    };
  };
  eitherL = np.either (np.listOf np.int) np.str;
  attrTagOver =
    t:
    np.attrTag {
      a = nl.mkOption { type = t; };
      b = nl.mkOption { type = np.str; };
    };
  partners = {
    hzP = enumOf gt.listOf np.listOf // {
      p = overAt np.listOf short isA (np.enum [ "a" ]);
      vals = listVals;
    };
    hzN = enumOf gt.nullOr np.nullOr // {
      p = overAt np.nullOr (v: v != null) isA (np.enum [ "a" ]);
      vals = {
        a = "a";
        b = "b";
      };
    };
    hzRA = enumOf gt.attrsOf np.attrsOf // {
      p = overAtA short1 (q: !(isA q)) (np.enum [ "a" ]);
      vals = attrVals;
    };
    hzKA = enumOf gt.attrsOf np.attrsOf // {
      p = overAtA short1 (_: true) (np.enum [ "a" ]);
      vals = attrVals;
    };
    nShort = {
      p = np.attrsOf shortList;
      G = gt.attrsOf (gt.listOf np.int);
      T = np.attrsOf (np.listOf np.int);
      vals = {
        ok.k = [ 2 ];
        long.k = [
          2
          3
        ];
      };
    };
    rawExtra = {
      p = rawExtraAttrs;
      G = aI;
      T = np.attrsOf np.int;
      vals.ok.k = 2;
    };
    # an override in an `attrTag` tag, a role stated as an option
    AT = {
      p = np.attrsOf (attrTagOver shortList);
      G = gt.attrsOf (attrTagOver (np.listOf np.int));
      T = np.attrsOf (attrTagOver (np.listOf np.int));
      vals = {
        a.k.a = [ 2 ];
        b.k.b = "s";
      };
    };
    # an override under `either`, a role other than the element
    E = {
      p = np.attrsOf (np.either shortList np.str);
      G = gt.attrsOf eitherL;
      T = np.attrsOf eitherL;
      vals = {
        ok.k = [ 2 ];
        s.k = "s";
      };
    };
  };
  # a cell "<partner>/<word>/<value>": the word over G (gen's container) and P (the partner through door `d`); the
  # twin reads the word with nixpkgs' `T` for G and the partner raw
  letters = w: builtins.filter (c: builtins.isString c && c != "") (builtins.split "" w);
  cellOf =
    s:
    let
      x = builtins.filter builtins.isString (builtins.split "/" s);
      f = partners.${builtins.elemAt x 0};
    in
    {
      inherit f;
      w = letters (builtins.elemAt x 1);
      v = f.vals.${builtins.elemAt x 2};
    };
  readCells =
    engine: cells:
    builtins.listToAttrs (
      map (s: {
        name = s;
        value = engine (cellOf s);
      }) cells
    );
  bothDoors =
    cells:
    builtins.mapAttrs
      (_: d: readCells (c: gen (map (l: if l == "G" then c.f.G else d c.f.p) c.w) c.v) cells)
      {
        inherit door tdoor;
      };
  twin =
    cells:
    let
      t = readCells (c: npe (map (l: if l == "G" then c.f.T else c.f.p) c.w) c.v) cells;
    in
    {
      door = t;
      tdoor = t;
    };
  refusedIn =
    cells:
    builtins.mapAttrs (_: _: builtins.mapAttrs (_: _: "REFUSED") (readCells (_: null) cells)) {
      inherit door tdoor;
    };
  # the override families where the door return is the later declaration and nixpkgs' twin refuses the join by L1's
  # name (the element check's own refusals left out); the cells main serves beyond the twin are another row's
  overrideJoins = [
    "hzKA/GP/a"
    "hzKA/GP/ab"
    "hzKA/GP/b"
    "hzKA/GP/xaa"
    "hzKA/PP/a"
    "hzKA/PP/ab"
    "hzKA/PP/b"
    "hzKA/PP/xaa"
    "hzKA/GGP/a"
    "hzKA/GGP/ab"
    "hzKA/GGP/b"
    "hzKA/GGP/xaa"
    "hzKA/GPP/ab"
    "hzKA/GPP/xaa"
    "hzKA/PGP/a"
    "hzKA/PGP/ab"
    "hzKA/PGP/b"
    "hzKA/PGP/xaa"
    "hzKA/PPP/ab"
    "hzKA/PPP/b"
    "hzKA/PPP/xaa"
    "hzKA/GGGP/a"
    "hzKA/GGGP/ab"
    "hzKA/GGGP/b"
    "hzKA/GGGP/xaa"
    "hzKA/GGPP/a"
    "hzKA/GGPP/ab"
    "hzKA/GGPP/xaa"
    "hzKA/GPGP/a"
    "hzKA/GPGP/ab"
    "hzKA/GPGP/b"
    "hzKA/GPGP/xaa"
    "hzKA/GPPP/ab"
    "hzKA/GPPP/xaa"
    "hzKA/PGGP/a"
    "hzKA/PGGP/ab"
    "hzKA/PGGP/b"
    "hzKA/PGGP/xaa"
    "hzKA/PGPP/ab"
    "hzKA/PGPP/b"
    "hzKA/PGPP/xaa"
    "hzKA/PPGP/a"
    "hzKA/PPGP/ab"
    "hzKA/PPGP/b"
    "hzKA/PPGP/xaa"
    "hzKA/PPPP/ab"
    "hzKA/PPPP/b"
    "hzKA/PPPP/xaa"
    "hzRA/GP/a"
    "hzRA/GP/ab"
    "hzRA/GP/b"
    "hzRA/GP/xaa"
    "hzRA/PP/ab"
    "hzRA/PP/b"
    "hzRA/GGP/a"
    "hzRA/GGP/ab"
    "hzRA/GGP/b"
    "hzRA/GGP/xaa"
    "hzRA/PGP/a"
    "hzRA/PGP/ab"
    "hzRA/PGP/b"
    "hzRA/PGP/xaa"
    "hzRA/PPP/ab"
    "hzRA/PPP/b"
    "hzRA/GGGP/a"
    "hzRA/GGGP/ab"
    "hzRA/GGGP/b"
    "hzRA/GGGP/xaa"
    "hzRA/GPGP/a"
    "hzRA/GPGP/ab"
    "hzRA/GPGP/b"
    "hzRA/GPGP/xaa"
    "hzRA/PGGP/a"
    "hzRA/PGGP/ab"
    "hzRA/PGGP/b"
    "hzRA/PGGP/xaa"
    "hzRA/PPGP/a"
    "hzRA/PPGP/ab"
    "hzRA/PPGP/b"
    "hzRA/PPGP/xaa"
    "hzRA/PPPP/ab"
    "hzRA/PPPP/b"
    "nShort/GP/long"
    "nShort/GP/ok"
    "nShort/PP/long"
    "nShort/PP/ok"
    "nShort/GGP/long"
    "nShort/GGP/ok"
    "nShort/GPP/long"
    "nShort/PGP/long"
    "nShort/PGP/ok"
    "nShort/PPP/long"
    "nShort/PPP/ok"
    "nShort/GGGP/long"
    "nShort/GGGP/ok"
    "nShort/GGPP/long"
    "nShort/GPGP/long"
    "nShort/GPGP/ok"
    "nShort/GPPP/long"
    "nShort/PGGP/long"
    "nShort/PGGP/ok"
    "nShort/PGPP/long"
    "nShort/PGPP/ok"
    "nShort/PPGP/long"
    "nShort/PPGP/ok"
    "nShort/PPPP/long"
    "nShort/PPPP/ok"
    "rawExtra/GP/ok"
    "rawExtra/PP/ok"
    "rawExtra/GGP/ok"
    "rawExtra/PGP/ok"
    "rawExtra/PPP/ok"
    "rawExtra/GGGP/ok"
    "rawExtra/GPGP/ok"
    "rawExtra/PGGP/ok"
    "rawExtra/PPGP/ok"
    "rawExtra/PPPP/ok"
  ];
  eitherWords = [
    "GP"
    "GGP"
    "GGGP"
    "GPGP"
  ];
  # where the bare type is the later declaration, nixpkgs serves G's coherent join
  eitherResidueWords = [
    "PG"
    "PGG"
    "PGGG"
    "GPG"
    "GGPG"
    "GPGG"
    "GPPG"
  ];
  atCells =
    ws:
    builtins.concatMap (w: [
      "AT/${w}/a"
      "AT/${w}/b"
    ]) ws;
  eCells =
    ws:
    builtins.concatMap (w: [
      "E/${w}/ok"
      "E/${w}/s"
    ]) ws;
  widening =
    builtins.concatMap
      (w: [
        "hzP/${w}/a"
        "hzP/${w}/ab"
        "hzP/${w}/b"
        "hzN/${w}/a"
        "hzN/${w}/b"
      ])
      [
        "GPG"
        "GGPG"
        "GPGG"
      ];
  readAll = engine: builtins.mapAttrs (_: r: engine (builtins.elemAt r 0) (builtins.elemAt r 1));
  # every declaration list of length 2, 3 and 4 over the bare type and its two door returns, in every order
  seqs =
    n: xs: if n == 0 then [ [ ] ] else builtins.concatMap (s: map (x: [ x ] ++ s) xs) (seqs (n - 1) xs);
  orders =
    xs:
    builtins.concatMap (n: seqs n xs) [
      2
      3
      4
    ];
  kinds = bare: {
    b = bare;
    d = door bare;
    t = tdoor bare;
  };
  everyOrder =
    engine: bare: v:
    let
      k = kinds bare;
    in
    builtins.listToAttrs (
      map (s: {
        name = builtins.concatStringsSep "" s;
        value = engine (map (n: k.${n}) s) v;
      }) (orders (builtins.attrNames k))
    );
  shapes = {
    aoInt = [
      aI
      { k = 2; }
    ];
    laoInt = [
      (gt.lazyAttrsOf np.int)
      { k = 2; }
    ];
    dm = [
      gt.deferredModule
      { }
    ];
    inLo = [
      (gt.listOf aI)
      [ { k = 2; } ]
    ];
  };
  everyShape =
    engine:
    builtins.mapAttrs (_: s: everyOrder engine (builtins.elemAt s 0) (builtins.elemAt s 1)) shapes;
  # the check oracle at every count and order: the bare type beside the door returns of its checked copy, at a value
  # the element check rejects. Refused wherever a checked declaration is present (THE MEET); nixpkgs' engine drops
  # the check
  checked = {
    r5 = [
      (gt.attrsOf sub)
      (gt.attrsOf (np.addCheck sub p))
      { k.a = 1; }
    ];
    tdLaoSub = [
      (gt.lazyAttrsOf sub)
      (gt.lazyAttrsOf (np.addCheck sub p))
      { k.a = 1; }
    ];
    inAo = [
      (gt.attrsOf (gt.attrsOf sub))
      (gt.attrsOf (door (gt.attrsOf (np.addCheck sub p))))
      { j.k.a = 1; }
    ];
  };
  checkOracle =
    want:
    builtins.mapAttrs (
      _: c:
      let
        k = {
          b = builtins.elemAt c 0;
          d = door (builtins.elemAt c 1);
          t = tdoor (builtins.elemAt c 1);
        };
        v = builtins.elemAt c 2;
      in
      builtins.listToAttrs (
        map (s: {
          name = builtins.concatStringsSep "" s;
          value = want s (map (n: k.${n}) s) v;
        }) (orders (builtins.attrNames k))
      )
    ) checked;
in
{
  flake.tests.door-partner = {
    test-a-door-return-beside-its-bare-type-reads-nixpkgs-value = {
      expr = readAll gen rows;
      expected = readAll npe rows;
    };
    # RESIDUE (an open defect): where the bare type decides, nixpkgs serves G's coherent join, while the door return's
    # own relation answers the pair with an ad-hoc override; gen does not tell which declaration decides
    # (`elementRelIn` is asked in both orders), so the pair stays refused
    test-a-door-return-whose-own-join-is-an-override-is-refused-in-both-orders = {
      expr = {
        rawExtra = readAll gen {
          TL = [
            [
              aI
              (door rawExtraAttrs)
            ]
            { k = 2; }
          ];
          LT = [
            [
              (door rawExtraAttrs)
              aI
            ]
            { k = 2; }
          ];
        };
        E = bothDoors (eCells eitherResidueWords);
        AT = bothDoors (atCells eitherResidueWords);
      };
      expected = {
        rawExtra = {
          TL = "REFUSED";
          LT = "REFUSED";
        };
        E = refusedIn (eCells eitherResidueWords);
        AT = refusedIn (atCells eitherResidueWords);
      };
    };
    test-a-door-return-whose-own-join-is-an-override-reads-nixpkgs-refusal-where-it-decides = {
      expr = bothDoors overrideJoins;
      expected = twin overrideJoins;
    };
    test-an-override-under-either-in-a-door-return-own-join-reads-nixpkgs-refusal = {
      expr = bothDoors (eCells eitherWords);
      expected = twin (eCells eitherWords);
    };
    test-an-override-in-an-attrtag-tag-of-a-door-return-own-join-reads-nixpkgs-refusal = {
      expr = bothDoors (map (w: "AT/${w}/a") eitherWords);
      expected = twin (map (w: "AT/${w}/a") eitherWords);
    };
    # three and four declarations: a door return gen reads whole stays gen's partner
    test-a-payload-dependent-door-return-at-three-and-four-declarations-reads-nixpkgs-value = {
      expr = bothDoors widening;
      expected = twin widening;
    };
    test-the-carrying-types-read-whole-and-the-leaves-are-served-as-before = {
      expr = readAll gen controls;
      expected = readAll npe controls;
    };
    # two, three and four declarations, every order over the bare type and both doors
    test-every-declaration-count-and-order-reads-nixpkgs-value = {
      expr = everyShape gen;
      expected = everyShape npe;
    };
    test-a-checked-door-return-refuses-a-value-its-check-rejects-at-every-count-and-order = {
      expr = checkOracle (_: gen);
      expected = checkOracle (
        s: ts: v:
        if builtins.all (n: n == "b") s then npe ts v else "REFUSED"
      );
    };
    # the door over `deferredModuleWith { staticModules }`: the served module value nests the static module one
    # `imports` level deeper than nixpkgs' copy, so it is compared by the configuration it evaluates to
    test-a-door-return-of-a-static-deferred-module-evaluates-to-nixpkgs-config = {
      expr = {
        TL = configOf (genV [ gt.deferredModule (door staticA) ] { a = 2; });
        LT = configOf (genV [ (door staticA) gt.deferredModule ] { a = 2; });
      };
      expected = {
        TL = configOf (npV [ np.deferredModule staticA ] { a = 2; });
        LT = configOf (npV [ staticA np.deferredModule ] { a = 2; });
      };
    };
  };
}
