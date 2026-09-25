# A foreign type's `check` is enforced on every fold gen-merge OWNS.
#
# nixpkgs' `mergeDefinitions` tests every surviving definition against the option type's `check`
# before the type's `merge` sees it (`checkedAndMerged`). A foreign record reaches gen-merge's fold
# through `interface.importedFold`, which hands the engine that CHECKED fold — so `lib.types.str`
# refuses `1` at every position gen-merge folds, not only under a container nixpkgs owns.
#
# The class is the product of the foreign leaf and the gen-owned position, so the cells quantify
# over the product rather than sampling it. The bad-value cell is paired with a good-value cell (a
# check that refused everything would pass the first alone), and both carry the gen-types `str`
# leaf as a live control, enforced by the spine's own `verify` on both sides of this change.
#
# The cells whose subject is the refusal MESSAGE, and the ones whose stock arm is an uncatchable
# abort, live on `testsError` (`../tests-error.nix`, group `foreign-leaf-check`).
{
  genMerge,
  genMergeWith,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  t = nixpkgsLib.types;
  inherit (builtins)
    attrNames
    concatMap
    deepSeq
    filter
    length
    tryEval
    ;

  accepted = v: (tryEval (deepSeq v v)).success;

  # position : T -> V -> module list, read at `config.p`. Every one is a fold gen-merge owns.
  positions = {
    top = T: V: [
      { options.p = gm.mkOption { type = T; }; }
      { p = V; }
    ];
    default = T: V: [
      {
        options.p = gm.mkOption {
          type = T;
          default = V;
        };
      }
    ];
    imports = T: V: [
      { imports = [ { options.p = gm.mkOption { type = T; }; } ]; }
      { p = V; }
    ];
    freeform = T: V: [
      { freeformType = gt.attrsOf T; }
      { p = V; }
    ];
    submodule = T: V: [
      { options.p = gm.mkOption { type = gt.submodule { options.q = gm.mkOption { type = T; }; }; }; }
      { p.q = V; }
    ];
    attrsOf = T: V: [
      { options.p = gm.mkOption { type = gt.attrsOf T; }; }
      { p.a = V; }
    ];
    listOf = T: V: [
      { options.p = gm.mkOption { type = gt.listOf T; }; }
      { p = [ V ]; }
    ];
    nullOr = T: V: [
      { options.p = gm.mkOption { type = gt.nullOr T; }; }
      { p = V; }
    ];
  };

  # leaf : [ type bad good ]. The last is a `check`-only descriptor built through gen-merge's own
  # `mkOptionType`, which crosses the boundary on the `importType` route rather than `ownFold`.
  foreign = {
    str = [
      t.str
      1
      "x"
    ];
    int = [
      t.int
      "x"
      1
    ];
    bool = [
      t.bool
      1
      true
    ];
    float = [
      t.float
      1
      1.5
    ];
    path = [
      t.path
      1
      /tmp
    ];
    enum = [
      (t.enum [ "a" ])
      "c"
      "a"
    ];
    strMatching = [
      (t.strMatching "a+")
      "b"
      "aa"
    ];
    intsBetween = [
      (t.ints.between 0 1)
      5
      1
    ];
    port = [
      t.port
      70000
      80
    ];
    nonEmptyStr = [
      t.nonEmptyStr
      ""
      "x"
    ];
    nullOrStr = [
      (t.nullOr t.str)
      1
      "x"
    ];
    addCheck = [
      (t.addCheck t.int (x: x > 0))
      (-1)
      1
    ];
    mkOptionType = [
      (gm.mkOptionType {
        name = "evenInt";
        check = x: builtins.isInt x && builtins.bitAnd x 1 == 0;
      })
      3
      2
    ];
  };
  control = [
    gt.str
    1
    "x"
  ];

  run =
    pn: l: v:
    accepted (gm.evalModuleTree { modules = positions.${pn} (builtins.elemAt l 0) v; }).config.p;
  cells = concatMap (pn: map (ln: { inherit pn ln; }) (attrNames foreign)) (attrNames positions);
  table = which: filter (c: run c.pn foreign.${c.ln} (builtins.elemAt foreign.${c.ln} which)) cells;
  controlAccepted =
    which: filter (pn: run pn control (builtins.elemAt control which)) (attrNames positions);

  # A gen structural type sent out through the foreign protocol and back through `mkOptionType`
  # carries `check` (its exported `admits`) and no `verify`, so its fold is checked too. Good values
  # are kept byte-identical to the type used directly; the bad value's refusal is on `testsError`.
  listOfInt = gt.listOf gt.int;
  roundTripped = gm.mkOptionType listOfInt;
  twoDefs =
    T: a: b:
    (gm.evalModuleTree {
      modules = [
        { options.p = gm.mkOption { type = T; }; }
        { p = a; }
        { p = b; }
      ];
    }).config.p;

  # A descriptor stating a foreign `check` and a gen `mergeDefs`, but no `merge`: the check wraps the
  # author's fold, never a leaf fold in its place.
  hybrid = gm.mkOptionType {
    name = "h";
    check = builtins.isList;
    mergeDefs = _loc: defs: builtins.concatLists (map (d: d.value) defs);
  };
  hybridMerge = gm.mkOptionType {
    name = "h";
    check = builtins.isList;
    merge = _loc: defs: builtins.concatLists (map (d: d.value) defs);
  };

  # A foreign leaf vocabulary injected as `types`. Not the whole of nixpkgs' `lib.types`: that
  # overlaps gen-merge's own exports and the namespace assembly refuses it by name, which would make
  # every cell below read "refused" whatever the fold did.
  compat = genMergeWith {
    inherit (t)
      str
      int
      attrs
      listOf
      attrsOf
      ;
    option = t.nullOr;
  };
  compatRun =
    T: v:
    accepted
      (compat.evalModuleTree {
        modules = [
          { options.p = compat.mkOption { type = T; }; }
          { p = v; }
        ];
      }).config.p;

  # A nixpkgs v2 type (its `merge` carries `v2`) given an ad-hoc `check` by `//`: nixpkgs refuses
  # it at every definition (`checkV2MergeCoherence`); the stock type beside it is the control.
  # [ stock-type value ]; each row is overridden with a check that ADMITS the value.
  v2Stock = {
    attrsOf = [
      (t.attrsOf t.int)
      { a = 1; }
    ];
    lazyAttrsOf = [
      (t.lazyAttrsOf t.int)
      { a = 1; }
    ];
    listOf = [
      (t.listOf t.int)
      [ 1 ]
    ];
    nullOr = [
      (t.nullOr t.int)
      1
    ];
    either = [
      (t.either t.int t.str)
      1
    ];
    coercedTo = [
      (t.coercedTo t.int toString t.str)
      1
    ];
    addCheck = [
      (t.addCheck (t.listOf t.int) (_: true))
      [ 1 ]
    ];
  };
  adHoc = T: T // { check = _: true; };
  v2Cells = cellsOf v2Stock;
  cellsOf = rows: concatMap (pn: map (ln: { inherit pn ln; }) (attrNames rows)) (attrNames positions);
  acceptedOf =
    rows: wrap:
    filter (
      c:
      accepted
        (gm.evalModuleTree {
          modules = positions.${c.pn} (wrap (builtins.elemAt rows.${c.ln} 0)) (
            builtins.elemAt rows.${c.ln} 1
          );
        }).config.p
    ) (cellsOf rows);
  v2Accepted = acceptedOf v2Stock;
  # A submodule-bearing v2 type: nixpkgs rebuilds it at declaration (`substSubModules`) and so ERASES
  # an ad-hoc `check`; gen-merge refuses that override by name instead of reproducing the erasure.
  sub = t.submodule { options.q = nixpkgsLib.mkOption { type = t.int; }; };
  subStock = {
    submodule = [
      sub
      { q = 1; }
    ];
    attrsOfSubmodule = [
      (t.attrsOf sub)
      { a.q = 1; }
    ];
  };
  # A fold replaced WHOLE by `//` on a record that crossed `mkOptionType`: the replacement governs at
  # every site, the freeformType included (`mergeDefs.unchecked` rides on the fold it replaces).
  replaced = T: T // { mergeDefs = _: _: { p = "REPLACED"; }; };
  replacedAt = T: {
    freeform = freeformRead T 1;
    option =
      (gm.evalModuleTree {
        modules = [
          { options.p = gm.mkOption { type = T; }; }
          { p.a = 1; }
        ];
      }).config.p.p;
  };
  forged = f: {
    __functor = _: f;
    isV2MergeCoherent = true;
  };
  # a hand-written v2 `merge` answering `answer` merged over a well-formed result
  v2Answer = answer: {
    __functor =
      self: loc: defs:
      (self.v2 { inherit loc defs; }).value;
    v2 =
      { loc, defs }:
      {
        headError = null;
        value.p = 7;
        valueMeta = { };
      }
      // answer;
  };
  freeformRead =
    T: v:
    let
      p =
        (gm.evalModuleTree {
          modules = [
            { freeformType = T; }
            { p = v; }
          ];
        }).config.p;
      r = tryEval (deepSeq p p);
    in
    if r.success then r.value else "REFUSED";
  freeformRows =
    let
      B = t.attrsOf t.int;
    in
    {
      control = {
        T = B;
        v = 1;
      };
      checkAccepting = {
        T = B // {
          check = builtins.isAttrs;
        };
        v = 1;
      };
      v2HeadError = {
        T = B // {
          merge = v2Answer { headError.message = "boom"; };
        };
        v = 1;
      };
      checkFalseV2 = {
        T = B // {
          check = _: false;
        };
        v = 1;
      };
      checkFalseNonV2 = {
        T = t.attrs // {
          check = _: false;
        };
        v = 1;
      };
      checkRemoved = {
        T = builtins.removeAttrs B [ "check" ];
        v = 1;
      };
      lazyCheck = {
        T = t.lazyAttrsOf t.int // {
          check = builtins.isAttrs;
        };
        v = 1;
      };
      elemBad = {
        T = B;
        v = "x";
      };
      routedCheckFalse = {
        T = gm.mkOptionType (B // { check = _: false; });
        v = 1;
      };
      routedCheckAccepting = {
        T = gm.mkOptionType (B // { check = builtins.isAttrs; });
        v = 1;
      };
      routedDescriptor = {
        T = gm.mkOptionType {
          name = "h";
          check = _: false;
        };
        v = 1;
      };
    };
  topAccepted =
    T: v:
    accepted
      (gm.evalModuleTree {
        modules = [
          { options.p = gm.mkOption { type = T; }; }
          { p = v; }
        ];
      }).config.p;
in
{
  flake.tests.foreign-leaf-check = {
    # 13 foreign types × 8 gen-owned positions, bad value each: every cell REFUSED. `cells` pins the
    # product's size, so an empty table cannot read as a clean pass.
    test-foreign-type-check-refused-at-every-gen-position = {
      expr = {
        cells = length cells;
        accepted = map (c: "${c.pn}/${c.ln}") (table 1);
        controlAccepted = controlAccepted 1;
      };
      expected = {
        cells = 104;
        accepted = [ ];
        controlAccepted = [ ];
      };
    };
    test-foreign-type-check-admits-the-good-value = {
      expr = {
        cells = length cells;
        refused = map (c: "${c.pn}/${c.ln}") (
          filter (c: !(run c.pn foreign.${c.ln} (builtins.elemAt foreign.${c.ln} 2))) cells
        );
        controlAccepted = length (controlAccepted 2);
      };
      expected = {
        cells = 104;
        refused = [ ];
        controlAccepted = 8;
      };
    };

    # Compat mode: nixpkgs' `lib.types` injected as the leaf vocabulary reaches the fold through
    # `importType`, the second route into `importedFold`.
    test-compat-vocabulary-str-refuses-a-bad-value = {
      expr = {
        str = compatRun compat.types.str 1;
        listOfStr = compatRun (compat.types.listOf compat.types.str) [ 1 ];
      };
      expected = {
        str = false;
        listOfStr = false;
      };
    };
    test-compat-vocabulary-str-admits-a-good-value = {
      expr = {
        str = compatRun compat.types.str "x";
        listOfStr = compatRun (compat.types.listOf compat.types.str) [ "x" ];
      };
      expected = {
        str = true;
        listOfStr = true;
      };
    };

    test-check-wraps-the-descriptors-own-mergeDefs = {
      expr = twoDefs hybrid [ 1 ] [ 2 ];
      expected = twoDefs hybridMerge [ 1 ] [ 2 ];
    };
    test-check-wraps-the-descriptors-own-mergeDefs-literal = {
      expr = twoDefs hybrid [ 1 ] [ 2 ];
      expected = [
        2
        1
      ];
    };

    test-round-tripped-structural-type-keeps-good-values = {
      expr = twoDefs roundTripped [ 1 ] [ 2 ];
      expected = twoDefs listOfInt [ 1 ] [ 2 ];
    };

    # 7 v2 types x 8 gen-owned positions: the ad-hoc override is refused in every cell, and the
    # stock type admits the same value in every cell.
    test-v2-adhoc-check-override-refused-at-every-gen-position = {
      expr = {
        cells = length v2Cells;
        overrideAccepted = map (c: "${c.pn}/${c.ln}") (v2Accepted adHoc);
        stockAccepted = length (v2Accepted (T: T));
      };
      expected = {
        cells = 56;
        overrideAccepted = [ ];
        stockAccepted = 56;
      };
    };
    # 2 submodule-bearing v2 types x 8 gen-owned positions, each given a check that ADMITS the value:
    # the override is refused in every cell (nixpkgs erases it, and a silent erasure is not
    # reproduced), and the stock type admits the same value in every cell.
    test-submodule-bearing-adhoc-check-override-refused-at-every-gen-position = {
      expr = {
        cells = length (cellsOf subStock);
        overrideAccepted = map (c: "${c.pn}/${c.ln}") (acceptedOf subStock adHoc);
        stockAccepted = length (acceptedOf subStock (T: T));
      };
      expected = {
        cells = 16;
        overrideAccepted = [ ];
        stockAccepted = 16;
      };
    };

    # A whole `mergeDefs` replacement on a routed check-bearing record reaches the freeformType site
    # as it reaches an option site; the gen-native type is the control.
    test-replaced-mergeDefs-governs-at-the-freeformType-site = {
      expr = {
        routed = replacedAt (replaced (gm.mkOptionType (t.attrsOf t.int)));
        native = replacedAt (replaced (gt.attrsOf gt.int));
      };
      expected = {
        routed = {
          freeform = "REPLACED";
          option = "REPLACED";
        };
        native = {
          freeform = "REPLACED";
          option = "REPLACED";
        };
      };
    };

    # The v2 protocol is read whole, as nixpkgs reads it: its `headError` decides, not the record's
    # `check`. A non-v2 type's override stays honoured, as nixpkgs honours it.
    test-v2-protocol-read-whole = {
      expr = {
        forgedWidening = topAccepted (t.either t.int t.str // { check = forged (_: true); }) true;
        forgedNarrowing = topAccepted (t.attrsOf t.int // { check = forged (_: false); }) { a = 1; };
        headError = topAccepted (
          t.attrsOf t.int
          // {
            merge = {
              __functor =
                self: loc: defs:
                (self.v2 { inherit loc defs; }).value;
              v2 =
                { loc, defs }:
                {
                  headError.message = "boom";
                  value = { };
                  valueMeta = { };
                };
            };
          }
        ) { a = 1; };
        checkRemoved = topAccepted (builtins.removeAttrs (t.attrsOf t.int) [ "check" ]) { a = 1; };
        nonV2Widened = topAccepted (t.str // { check = _: true; }) 1;
        wellFormed = topAccepted (t.attrsOf t.int // { merge = v2Answer { headError = null; }; }) {
          a = 1;
        };
      };
      expected = {
        forgedWidening = false;
        forgedNarrowing = true;
        headError = false;
        checkRemoved = false;
        nonV2Widened = true;
        wellFormed = true;
      };
    };

    # A foreign type used AS the freeformType is merged by its raw `merge`, as nixpkgs merges it
    # (`freeformType.merge prefix defs`): no `check`, no coherence guard, no `headError` — on either
    # route in (the record itself, or through `mkOptionType`). The element check inside the type's own
    # merge still fires (`elemBad`), and an OPTION site on the same route is still checked (`optionSite`).
    test-foreign-type-as-freeformType-merges-unchecked = {
      expr = builtins.mapAttrs (_: c: freeformRead c.T c.v) freeformRows // {
        optionSite = topAccepted (gm.mkOptionType (t.attrsOf t.int // { check = builtins.isAttrs; })) {
          a = 1;
        };
      };
      expected = {
        control = 1;
        checkAccepting = 1;
        v2HeadError = 7;
        checkFalseV2 = 1;
        checkFalseNonV2 = 1;
        checkRemoved = 1;
        lazyCheck = 1;
        elemBad = "REFUSED";
        routedCheckFalse = 1;
        routedCheckAccepting = 1;
        routedDescriptor = 1;
        optionSite = false;
      };
    };
  };
}
