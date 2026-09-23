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
  };
}
