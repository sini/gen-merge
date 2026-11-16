# AN OUTPUT SLOT THAT MERGES BY SHAPE, OVER `raw`: the README recipe a framework running inside nixpkgs'
# `lib.evalModules` mounts as a freeform, and the law it states. `_fixtures/output-slot-over-raw.nix` is the
# README spelling verbatim; this file holds the law's cells.
#
# THE LAW (the README section states it in full). Definitions reach a fold in reverse module order, so the
# fold's head is the last module.
#   1. every definition a list: their concatenation, elements carried as written;
#   2. every definition an attrset that is neither a derivation nor a construction (`? __mint`): the per-key
#      fold of nixpkgs' `lazyAttrsOf` over the slot itself, lazy, each key through the engine's spine;
#   3. everything else: `raw`'s fold. One definition is its value; several are served when all are `==`
#      to the head and refused by name otherwise; a served string carries every definition's context.
# "Agree" is Nix's own `==`: it compares derivations by `outPath`, and on functions it is the evaluator's
# own answer (`f == f` is false on Nix and Determinate and true on Lix), so those cells read the
# evaluator's `==` rather than a literal. A construction is never rebuilt: any `__mint` definition sends
# the fold to arm 3, so a merged body under one mark cannot form (ADR-0034, "a comparison mints nothing").
#
# ★ EVERY CELL READS BOTH ENGINES: nixpkgs' `lib.evalModules` (`np`) and `genMerge.evalModuleTree` (`gen`).
# ★ THE RELATIVES ARE READ BESIDE IT (`_fixtures/output-slot-relatives.nix`): nixpkgs' twin, dungeon's
# `leaf` and den v1's `mergeableType`. They equal the slot except on the five construction cells (the
# twin and dungeon rebuild a marked body per key) and den's two lone-definition cells (den returns one
# definition as written, so a nested property marker reaches the value as data).
#
# RED, each measured: the relatives' mutants move their families (`noMint` the 5 construction cells, 4 on
# Lix; `drvKeys` 3 derivation cells; `serveHead` 13, 11 on Lix; `strict` the 5 laziness cells), and they
# are read here as the same-run live reds. The leaf's context half reds on the leaf fold's old collapse
# (`ctxThenPlain` 0, `twoContexts` 1); its full grid is `merge-leaf.nix`. The conflict text is
# `../tests-error.nix`, `output-slot-over-raw`.
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  lib = nixpkgsLib;
  slot = import ./_fixtures/output-slot-over-raw.nix { inherit lib genMerge; };
  rel = import ./_fixtures/output-slot-relatives.nix { inherit lib genMerge genTypes; };

  # the evaluator's own `==` on functions, which the law defers to
  f = x: x;
  g = x: x;
  fnEq = f == f;
  served = c: v: if c then v else "REFUSED";

  evalWith =
    eng: mods:
    if eng == "np" then lib.evalModules { modules = mods; } else genMerge.evalModuleTree { } mods;
  mo = eng: if eng == "np" then lib.mkOption else genMerge.mkOption;
  run =
    eng: t: vs:
    (evalWith eng ([ { options.x = mo eng { type = t; }; } ] ++ map (v: { config.x = v; }) vs))
    .config.x;
  try =
    e:
    let
      r = builtins.tryEval (builtins.deepSeq e e);
    in
    if r.success then r.value else "REFUSED";
  show =
    v:
    if lib.isDerivation v then
      {
        drv = v.outPath;
        meta = v.meta or null;
        override = if v ? override then v.override null else null;
      }
    else if builtins.isFunction v then
      "<lambda>"
    else if builtins.isAttrs v && v ? outPath then
      {
        stringLike = v.outPath;
        keys = builtins.attrNames v;
      }
    else if builtins.isAttrs v then
      lib.mapAttrs (_: show) v
    else if builtins.isList v then
      map show v
    else
      v;
  read =
    eng: t: vs:
    try (show (run eng t vs));

  drv =
    op: extra:
    {
      type = "derivation";
      outPath = op;
      name = "d";
    }
    // extra;
  drvShow = meta: override: {
    drv = "/nix/store/aaaa-d";
    inherit meta override;
  };
  # each cell: its definitions in module order, and the law's value
  law = {
    one = {
      defs = [ 1 ];
      value = 1;
    };
    scalarEq = {
      defs = [
        1
        1
      ];
      value = 1;
    };
    scalarNe = {
      defs = [
        1
        2
      ];
      value = "REFUSED";
    };
    strEq3 = {
      defs = [
        "s"
        "s"
        "s"
      ];
      value = "s";
    };
    lists = {
      defs = [
        [ 1 ]
        [ 2 ]
      ];
      value = [
        2
        1
      ];
    };
    listsEq = {
      defs = [
        [ 1 ]
        [ 1 ]
      ];
      value = [
        1
        1
      ];
    };
    lists4 = {
      defs = [
        [ 1 ]
        [ 2 ]
        [ 3 ]
        [ 4 ]
      ];
      value = [
        4
        3
        2
        1
      ];
    };
    # a string-coercible set that is not a derivation merges per key
    stringLike = {
      defs = [
        {
          outPath = "/x";
          a = 1;
        }
        {
          outPath = "/x";
          b = 2;
        }
      ];
      value = {
        stringLike = "/x";
        keys = [
          "a"
          "b"
          "outPath"
        ];
      };
    };
    attrsDisjoint = {
      defs = [
        { a = 1; }
        { b = 2; }
      ];
      value = {
        a = 1;
        b = 2;
      };
    };
    attrsNestedEq = {
      defs = [
        { a = 1; }
        { a = 1; }
      ];
      value.a = 1;
    };
    attrsNestedNe = {
      defs = [
        { a = 1; }
        { a = 2; }
      ];
      value = "REFUSED";
    };
    deepLists = {
      defs = [
        { a.b = [ 1 ]; }
        { a.b = [ 2 ]; }
      ];
      value.a.b = [
        2
        1
      ];
    };
    mixedListAttrs = {
      defs = [
        [ 1 ]
        { a = 1; }
      ];
      value = "REFUSED";
    };
    mixedDrvAttrs = {
      defs = [
        (drv "/nix/store/aaaa-d" { })
        { a = 1; }
      ];
      value = "REFUSED";
    };
    # derivations agree by `outPath`, and the head is served whole
    drvIdentical = {
      defs = [
        (drv "/nix/store/aaaa-d" { })
        (drv "/nix/store/aaaa-d" { })
      ];
      value = drvShow null null;
    };
    drvSameOutPathOtherMeta = {
      defs = [
        (drv "/nix/store/aaaa-d" { meta = 1; })
        (drv "/nix/store/aaaa-d" { meta = 2; })
      ];
      value = drvShow 2 null;
    };
    drvDiffOutPath = {
      defs = [
        (drv "/nix/store/aaaa-d" { })
        (drv "/nix/store/bbbb-d" { })
      ];
      value = "REFUSED";
    };
    drvOverride = {
      defs = [
        (drv "/nix/store/aaaa-d" { override = _: 1; })
        (drv "/nix/store/aaaa-d" { override = _: 2; })
      ];
      value = drvShow null 2;
    };
    sameFn = {
      defs = [
        f
        f
      ];
      value = served fnEq "<lambda>";
    };
    twoFns = {
      defs = [
        f
        g
      ];
      value = "REFUSED";
    };
    fnInAttrs = {
      defs = [
        { k = f; }
        { k = f; }
      ];
      value = served fnEq { k = "<lambda>"; };
    };
    # constructions: served whole where every definition is `==` to the head, refused otherwise
    mintEq = {
      defs = [
        {
          __mint = "m";
          v = 1;
        }
        {
          __mint = "m";
          v = 1;
        }
      ];
      value = {
        __mint = "m";
        v = 1;
      };
    };
    mintFn = {
      defs = [
        {
          __mint = "m";
          k = f;
        }
        {
          __mint = "m";
          k = f;
        }
      ];
      value = {
        __mint = "m";
        k = "<lambda>";
      };
    };
    mintNe = {
      defs = [
        {
          __mint = "m";
          v = 1;
        }
        {
          __mint = "m";
          v = 2;
        }
      ];
      value = "REFUSED";
    };
    mintLists = {
      defs = [
        {
          __mint = "m";
          l = [ 1 ];
        }
        {
          __mint = "m";
          l = [ 2 ];
        }
      ];
      value = "REFUSED";
    };
    mintMixed = {
      defs = [
        {
          __mint = "m";
          v = 1;
        }
        { v = 1; }
      ];
      value = "REFUSED";
    };
    mintMixedListsDiffer = {
      defs = [
        {
          __mint = "m";
          l = [ 1 ];
        }
        { l = [ 2 ]; }
      ];
      value = "REFUSED";
    };
    mintMixedKeyAdded = {
      defs = [
        {
          __mint = "m";
          v = 1;
        }
        { w = 2; }
      ];
      value = "REFUSED";
    };
    # properties below the top level take the engine's spine, a lone definition included
    singleNestedForce = {
      defs = [ { a = lib.mkForce 1; } ];
      value.a = 1;
    };
    # `a`'s every definition discharges, so `a` is present and refuses when read (lazyAttrsOf), and the
    # deep read refuses
    singleNestedIfFalse = {
      defs = [
        {
          a = lib.mkIf false 1;
          b = 2;
        }
      ];
      value = "REFUSED";
    };
    nestedForceTwo = {
      defs = [
        { a = lib.mkForce 1; }
        { a = 2; }
      ];
      value.a = 1;
    };
    # list elements are carried as written, a property marker included
    listMkIfElem = {
      defs = [ [ (lib.mkIf false 1) ] ];
      value = [
        {
          _type = "if";
          condition = false;
          content = 1;
        }
      ];
    };
    emptyAttrs = {
      defs = [ { } ];
      value = { };
    };
  };

  # where a relative departs from the law, and what it reads there
  marked =
    x:
    {
      __mint = "m";
    }
    // x;
  constructionRebuilt = {
    mintFn = served fnEq (marked {
      k = "<lambda>";
    });
    mintLists = marked {
      l = [
        2
        1
      ];
    };
    mintMixed = marked { v = 1; };
    mintMixedListsDiffer = marked {
      l = [
        2
        1
      ];
    };
    mintMixedKeyAdded = marked {
      v = 1;
      w = 2;
    };
  };
  denLeaks = {
    singleNestedForce.a = {
      _type = "override";
      content = 1;
      priority = 50;
    };
    singleNestedIfFalse = {
      a = {
        _type = "if";
        condition = false;
        content = 1;
      };
      b = 2;
    };
  };
  lawValues = lib.mapAttrs (_: c: c.value) law;

  # the laziness cells: a sibling that throws is never forced, and the key set forces no value
  lazyOf = eng: t: {
    siblingThrow =
      try
        (run eng t [
          {
            a = 1;
            b = throw "forced b";
          }
          { c = 2; }
        ]).a;
    siblingThrowOne =
      try
        (run eng t [
          {
            a = 1;
            b = throw "forced b";
          }
        ]).a;
    keysOnly = try (
      builtins.attrNames (
        run eng t [
          { a = throw "forced a"; }
          { b = throw "forced b"; }
        ]
      )
    );
    nestedSibling =
      try
        (run eng t [
          { p.a = 1; }
          { p.b = throw "forced p.b"; }
        ]).p.a;
    # a key whose every definition discharges is present, and refuses when read
    ifFalseKeyNames = try (
      builtins.attrNames (
        run eng t [
          { a = lib.mkIf false 1; }
          { b = 2; }
        ]
      )
    );
  };
  lazyLaw = {
    siblingThrow = 1;
    siblingThrowOne = 1;
    keysOnly = [
      "a"
      "b"
    ];
    nestedSibling = 1;
    ifFalseKeyNames = [
      "a"
      "b"
    ];
  };

  # the leaf's string context, through the slot: the served string's context-entry count
  ctxA = builtins.toFile "output-slot-ctx-a" "a";
  ctxB = builtins.toFile "output-slot-ctx-b" "b";
  plainA = builtins.unsafeDiscardStringContext ctxA;
  ctxAB = plainA + builtins.substring 0 0 ctxB;
  nCtx = s: builtins.length (builtins.attrNames (builtins.getContext s));
  ctxOf = eng: t: {
    ctxAlone = try (nCtx (run eng t [ ctxA ]));
    ctxThenPlain = try (
      nCtx (
        run eng t [
          ctxA
          plainA
        ]
      )
    );
    twoContexts = try (
      nCtx (
        run eng t [
          ctxA
          ctxAB
        ]
      )
    );
    nestedCtxThenPlain = try (
      nCtx
        (run eng t [
          { k = ctxA; }
          { k = plainA; }
        ]).k
    );
    # the residue: a construction is compared whole, and a non-string collapse keeps the head's context
    mintCtxThenPlain = try (
      nCtx
        (run eng t [
          {
            __mint = "m";
            s = ctxA;
          }
          {
            __mint = "m";
            s = plainA;
          }
        ]).s
    );
    listElements = try (
      map nCtx (
        run eng t [
          [ plainA ]
          [ ctxA ]
        ]
      )
    );
  };
  ctxLaw = {
    ctxAlone = 1;
    ctxThenPlain = 1;
    twoContexts = 2;
    nestedCtxThenPlain = 1;
    mintCtxThenPlain = 0;
    listElements = [
      1
      0
    ];
  };

  # the refined check: a refinement of the slot (four spellings) declared beside the slot in six shapes; each
  # reading is <np planted><np accepted><gen planted><gen accepted>, S served and R refused. The planted value
  # `{ b = 1; }` fails the refinement; `{ a = 1; }` passes it.
  np = lib.types;
  p = v: builtins.isAttrs v && v ? a;
  forms = base: {
    add = np.addCheck base p;
    ovr = base // {
      check = x: base.check x && p x;
    };
    ver = base // {
      verify = v: if p v then null else "needs a";
    };
    door = genMerge.mkOptionType (
      base
      // {
        verify = v: if p v then null else "needs a";
      }
    );
  };
  ok = c: if (builtins.tryEval (builtins.deepSeq c.x c.x)).success then "S" else "R";
  runDecl =
    eng: ts: vs:
    ok
      (evalWith eng (map (t: { options.x = mo eng { type = t; }; }) ts ++ map (v: { x = v; }) vs)).config;
  shapes = base: r: {
    alone = [ r ];
    "2-after" = [
      base
      r
    ];
    "2-before" = [
      r
      base
    ];
    "3-mid" = [
      base
      r
      base
    ];
    "4-last" = [
      base
      base
      base
      r
    ];
    "4-first" = [
      r
      base
      base
      base
    ];
  };
  refined =
    ts: vsP: vsA:
    lib.concatMapStrings (eng: runDecl eng ts vsP + runDecl eng ts vsA) [
      "np"
      "gen"
    ];
  grid =
    base:
    lib.mapAttrs (
      _: r: lib.mapAttrs (_: ts: refined ts [ { b = 1; } ] [ { a = 1; } ]) (shapes base r)
    ) (forms base);
  # the cell the leaf's serve beyond nixpkgs `raw` actually reaches: one refinement, the value defined twice
  twice =
    base:
    lib.mapAttrs (
      _: r:
      refined [ r ]
        [
          { b = 1; }
          { b = 1; }
        ]
        [
          { a = 1; }
          { a = 1; }
        ]
    ) (forms base);
  # the live red: a refinement whose check is dropped serves the planted value
  dropped = base: (np.addCheck base p) // { check = _: true; };
  gridLaw =
    let
      redeclared = {
        "2-after" = "RRRR";
        "2-before" = "RRRR";
        "3-mid" = "RRRR";
        "4-last" = "RRRR";
        "4-first" = "RRRR";
      };
      checked = redeclared // {
        alone = "RSRS";
      };
    in
    {
      add = checked;
      ovr = checked;
      door = checked;
      # nixpkgs' evaluation never reads `verify` (ADR-0039 Not covered)
      ver = redeclared // {
        alone = "SSRS";
      };
    };
  twiceLaw = {
    add = "RSRS";
    ovr = "RSRS";
    door = "RSRS";
    ver = "SSRS";
  };

  # `raw` itself against the law it folds by (nixpkgs' `mergeEqualOption` decision); nixpkgs `raw` beside it
  eqLaw = lib.mkOptionType {
    name = "eqLaw";
    merge = lib.mergeEqualOption;
  };
  rawCells = {
    one = [ 1 ];
    scalarEq = [
      1
      1
    ];
    scalarEq3 = [
      1
      1
      1
    ];
    scalarNe = [
      1
      2
    ];
    attrsEq = [
      { a = 1; }
      { a = 1; }
    ];
    drvSameOutPath = [
      (drv "/nix/store/aaaa-d" { meta = 1; })
      (drv "/nix/store/aaaa-d" { meta = 2; })
    ];
    sameFn = [
      f
      f
    ];
    forced = [
      (lib.mkForce 1)
      2
    ];
  };
  rawLaw = {
    one = 1;
    scalarEq = 1;
    scalarEq3 = 1;
    scalarNe = "REFUSED";
    attrsEq.a = 1;
    drvSameOutPath = drvShow 2 null;
    sameFn = served fnEq "<lambda>";
    forced = 1;
  };
  # nixpkgs `raw` (`mergeOneOption`) refuses any second definition, equal or not
  npRawLaw = rawLaw // {
    scalarEq = "REFUSED";
    scalarEq3 = "REFUSED";
    attrsEq = "REFUSED";
    drvSameOutPath = "REFUSED";
    sameFn = "REFUSED";
  };
  both = v: {
    np = v;
    gen = v;
  };
in
{
  flake.tests.output-slot-over-raw = {
    # the README's block is the fixture's, line for line, fenced. Read as line lists: a substring search over
    # the whole README overflows the default stack.
    test-the-readme-spelling-is-the-fixture =
      let
        linesOf = f: builtins.filter builtins.isString (builtins.split "\n" (builtins.readFile f));
        lines = linesOf ./_fixtures/output-slot-over-raw.nix;
        readme = linesOf ../../README.md;
        idx = l: xs: lib.lists.findFirstIndex (x: x == l) null xs;
        begin = idx "  # README-BEGIN" lines;
        body = map (lib.removePrefix "  ") (
          lib.sublist (begin + 1) (idx "  # README-END" lines - begin - 1) lines
        );
        n = builtins.length body;
        at = idx (builtins.head body) readme;
      in
      {
        expr = {
          nonEmpty = n > 10;
          inReadme =
            at != null
            && builtins.elemAt readme (at - 1) == "```nix"
            && lib.sublist at n readme == body
            && builtins.elemAt readme (at + n) == "```";
        };
        expected = {
          nonEmpty = true;
          inReadme = true;
        };
      };

    # C1: the law, on both engines
    test-the-slot-folds-by-the-law = {
      expr = lib.genAttrs [ "np" "gen" ] (eng: lib.mapAttrs (_: c: read eng slot c.defs) law);
      expected = both lawValues;
    };
    # its relatives, on nixpkgs' engine: equal but for the construction cells and den's lone definitions
    test-the-relatives-read-the-law-but-where-named = {
      expr = lib.genAttrs [ "npTwin" "dungeon" "den" ] (
        a: lib.mapAttrs (_: c: read "np" rel.${a} c.defs) law
      );
      expected = {
        npTwin = lawValues // constructionRebuilt;
        dungeon = lawValues // constructionRebuilt;
        den = lawValues // constructionRebuilt // denLeaks;
      };
    };
    # the mutants, the same run's live reds: each moves its family off the law
    test-each-mutant-moves-its-family =
      let
        moved = t: builtins.attrNames (lib.filterAttrs (n: c: read "np" t c.defs != lawValues.${n}) law);
      in
      {
        expr = lib.genAttrs [ "noMint" "drvKeys" "serveHead" ] (a: moved rel.${a});
        expected = lib.mapAttrs (_: lib.sort lib.lessThan) {
          noMint = builtins.attrNames (lib.filterAttrs (n: v: v != lawValues.${n}) constructionRebuilt);
          drvKeys = [
            "drvOverride"
            "drvSameOutPathOtherMeta"
            "mixedDrvAttrs"
          ];
          serveHead = [
            "attrsNestedNe"
            "drvDiffOutPath"
            "mintLists"
            "mintMixed"
            "mintMixedKeyAdded"
            "mintMixedListsDiffer"
            "mintNe"
            "mixedDrvAttrs"
            "mixedListAttrs"
            "scalarNe"
            "twoFns"
          ]
          ++ lib.optionals (!fnEq) [
            "fnInAttrs"
            "sameFn"
          ];
        };
      };

    # C6: laziness, both engines; the strict mutant forces what the slot does not
    test-the-slot-is-lazy = {
      expr = lib.genAttrs [ "np" "gen" ] (eng: lazyOf eng slot) // {
        strict = lazyOf "np" rel.strict;
      };
      expected = both lazyLaw // {
        strict = {
          siblingThrow = "REFUSED";
          siblingThrowOne = "REFUSED";
          keysOnly = "REFUSED";
          nestedSibling = "REFUSED";
          # nixpkgs' `attrsOf` drops the discharged key
          ifFalseKeyNames = [ "b" ];
        };
      };
    };

    # the leaf's string context through the slot (the full leaf grid is merge-leaf.nix)
    test-the-slot-keeps-the-leaf-folds-string-context = {
      expr = lib.genAttrs [ "np" "gen" ] (eng: ctxOf eng slot);
      expected = both ctxLaw;
    };

    # C4a: the refined check, nixpkgs' engine and gen's; the grid is nixpkgs' twin's, byte for byte
    test-a-refined-slot-enforces-its-check = {
      expr = {
        slot = grid slot;
        npTwin = grid rel.npTwin;
      };
      expected = {
        slot = gridLaw;
        npTwin = gridLaw;
      };
    };
    # C4b: the cell the serve beyond nixpkgs `raw` reaches, over `raw` and over the slot; and its live red
    test-the-planted-value-defined-twice-is-refused = {
      expr = {
        raw = twice genMerge.types.raw;
        slot = twice slot;
        droppedFirst = builtins.substring 0 1 (refined [ (dropped slot) ] [ { b = 1; } ] [ { a = 1; } ]);
      };
      expected = {
        raw = twiceLaw;
        slot = twiceLaw;
        droppedFirst = "S";
      };
    };

    # C2: gen `raw` folds by nixpkgs' `mergeEqualOption` decision on both engines; nixpkgs `raw` refuses
    # every second definition (the serve beyond it, read under ADR-0039 (b′))
    test-raw-folds-by-the-equal-option-law = {
      expr = {
        raw = lib.genAttrs [ "np" "gen" ] (eng: lib.mapAttrs (_: read eng genMerge.types.raw) rawCells);
        eqLaw = lib.mapAttrs (_: read "np" eqLaw) rawCells;
        npRaw = lib.mapAttrs (_: read "np" lib.types.raw) rawCells;
      };
      expected = {
        raw = both rawLaw;
        eqLaw = rawLaw;
        npRaw = npRawLaw;
      };
    };
  };
}
