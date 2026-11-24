# A CHECK CLASS A CONSTRUCTOR STATES SELECTS A REPRESENTATION, NEVER WHETHER THE CHECK RUNS. `u // intersectAttrs
# { check = null; } s` holds `s`'s check beside `u`'s witness: two submodules stating one class. A test of the two
# checks by `!=` answers by evaluator (the slot on Nix and Determinate, the closure on Lix), so the published door
# handed back differently shaped records; the class the two marks state now picks one representation on every
# evaluator. A `//` keeps the mark beside a functor it replaces, so a rewritten check states the same class: the
# second cell holds that its check still runs, at every door, in both engines and one level down.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  subOf =
    mods:
    gt.submodule (
      [
        {
          options.a = gm.mkOption {
            type = gt.int;
            default = 0;
          };
        }
      ]
      ++ mods
    );
  u = subOf [ ];
  s = subOf [
    {
      options.o9 = gm.mkOption {
        type = gt.int;
        default = 9;
      };
    }
  ];
  notTwo = v: !(v ? a && v.a == 2);
  moved = u // builtins.intersectAttrs { check = null; } s;
  # the only spelling that keeps the check record's `isV2MergeCoherent`, which nixpkgs' v2 guard reads
  functorOverride = u // {
    check = u.check // {
      __functor = _: v: u.check v && notTwo v;
    };
  };
  fnEdit = u // {
    check = u.check // {
      _fn = v: u.check v && notTwo v;
    };
  };
  npAddCheck = nl.types.addCheck u notTwo;
  shapeOf =
    Y: if builtins.isAttrs Y.merge then builtins.attrNames Y.merge else builtins.typeOf Y.merge;
  read =
    eng: Y: v:
    let
      r =
        if eng == "gen" then
          (gm.evalModuleTree { } [
            { options.o = gm.mkOption { type = Y; }; }
            { config.o = v; }
          ]).config.o
        else
          (nl.evalModules {
            modules = [
              { options.o = nl.mkOption { type = Y; }; }
              { config.o = v; }
            ];
          }).config.o;
    in
    if (builtins.tryEval (builtins.deepSeq r r)).success then "served" else "refused";
  # each read of a record: raw, through both published doors, and one level down through the `types` door
  reads = r: {
    rawGen = read "gen" r;
    mkGen = read "gen" (gm.mkOptionType r);
    mkNp = read "np" (gm.mkOptionType r);
    defGen = read "gen" (gt.defineType r);
    defNullOrGen = Y: read "gen" (gt.nullOr (gt.defineType r)) Y;
    defAttrsOfGen = v: read "gen" (gt.attrsOf (gt.defineType r)) { k = v; };
  };
  readAll = r: v: builtins.mapAttrs (_: f: f v) (reads r);
  allAre = x: builtins.mapAttrs (_: _: x) (reads u);
in
{
  flake.tests.check-mark-door = {
    # RED at the base on Nix and Determinate (the moved row), and on every evaluator for the rewritten rows, which
    # crossed in the record-as-itself representation
    test-one-representation-per-class = {
      expr = builtins.mapAttrs (_: r: {
        mk = shapeOf (gm.mkOptionType r) == shapeOf (gm.mkOptionType u);
        types = shapeOf (gt.mkOptionType r) == shapeOf (gt.mkOptionType u);
      }) { inherit moved functorOverride fnEdit; };
      expected = builtins.mapAttrs (_: _: {
        mk = true;
        types = true;
      }) { inherit moved functorOverride fnEdit; };
    };
    # `{ a = 2; }` is a module value `u` serves and only the rewritten check refuses: RED wherever a mark stands in
    # for the check (the check record's own-ness read off the mark, or every check read as its record's own)
    test-rewritten-check-runs = {
      expr = {
        functorOverride = readAll functorOverride { a = 2; };
        fnEdit = readAll fnEdit { a = 2; };
        npAddCheck = readAll npAddCheck { a = 2; };
        functorOverrideServes = readAll functorOverride { a = 1; };
        intact = readAll u { a = 2; };
        moved = readAll moved { a = 2; };
      };
      expected = {
        functorOverride = allAre "refused";
        fnEdit = allAre "refused";
        npAddCheck = allAre "refused";
        functorOverrideServes = allAre "served";
        intact = allAre "served";
        moved = allAre "served";
      };
    };
  };
}
