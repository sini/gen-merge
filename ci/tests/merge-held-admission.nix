# A DECLARATION'S ADMISSION HELD IN ITS `merge` IS OWED AT THE STEP (`lib/interface.nix` `metWith`'s `"holds"` branch;
# den-hoag-wsnn0 v1).
#
# A declaration accepts a definition when it passes `check` AND its `merge` folds it: nixpkgs' containers judge their
# elements in `merge`, and a leaf fold may refuse what its check accepts. Where a join is taken PAST the witness (it
# renames an operand, so the carrier's fold is not that operand's), the step runs each declaration's own fold beside
# the carrier's and demands its value position by position. Each row declares one option over the listed types,
# defines one value, and reads whether the value is SERVED or REFUSED; every expected verdict is what each
# declaration declared alone says (the alone oracle): served where every one serves it, refused where one refuses.
#
# The fixtures:
#  - `bobbinR`: a container whose payload IS its element (C65's spelling) and whose merge throws on an element its
#    element type rejects; `bobbin` the same with a merge that reads no element. Element pair `port` / `int`, so the
#    stated relation's join renames `port` to `int`.
#  - `evenM`: a leaf whose check is `isInt` and whose merge refuses an odd value; `countM`: a leaf whose merge refuses
#    a second definition (nixpkgs' `mergeOneOption`); each relation answers `int` beside `int`.
#  - `evenH`: `evenM`'s admission held in a v2 merge's `headError`, not thrown from `.value`.
# Doors: `mot` (`mkOptionType`, the stated relation `foreignRel`) and `raw` (no door, `importedMerge`).
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins) deepSeq tryEval;

  verdict = r: if r.success then "SERVED" else "REFUSED";
  # gen's engine; `defs` definitions of one value
  ev =
    tys: v: defs:
    let
      res = gm.evalModuleTree { } (
        map (ty: { options.x = gm.mkOption { type = ty; }; }) tys ++ builtins.genList (_: { x = v; }) defs
      );
    in
    verdict (tryEval (deepSeq res.config.x res.config.x));
  evNixpkgs =
    tys: v:
    let
      r =
        (nl.evalModules {
          modules = map (ty: { options.x = nl.mkOption { type = ty; }; }) tys ++ [ { x = v; } ];
        }).config.x;
    in
    verdict (tryEval (deepSeq r r));

  elemFold = defs: builtins.foldl' (acc: d: acc // d.value) { } defs;
  pie =
    name: mergeOf:
    let
      self =
        elemType:
        nl.mkOptionType {
          inherit name;
          check = builtins.isAttrs;
          merge = mergeOf elemType;
          nestedTypes = { inherit elemType; };
          getSubOptions = prefix: elemType.getSubOptions (prefix ++ [ "<name>" ]);
          getSubModules = elemType.getSubModules or null;
          substSubModules = _m: self elemType;
          functor = {
            inherit name;
            payload = elemType;
            binOp = a: b: if a ? typeMerge && b ? functor then a.typeMerge b.functor else null;
            type = self;
          };
        };
    in
    self;
  bobbinR = pie "bobbin" (
    elemType: _loc: defs:
    builtins.mapAttrs (k: x: if elemType.check x then x else throw "bobbin: `${k}' rejected") (
      elemFold defs
    )
  );
  bobbin = pie "bobbin" (
    _elemType: _loc: defs:
    elemFold defs
  );
  leaf =
    name: merge:
    let
      self = nl.mkOptionType {
        inherit name merge;
        check = {
          __functor = _: builtins.isInt;
          isV2MergeCoherent = true;
        };
        functor = np.defaultFunctor name // {
          type = _: self;
          payload = { };
          binOp = _a: _b: { };
        };
        typeMerge = f: if f.name == "int" || f.name == name then np.int else null;
      };
    in
    self;
  evenM = leaf "evenM" (
    loc: defs:
    let
      v = nl.mergeEqualOption loc defs;
    in
    if nl.mod v 2 == 0 then v else throw "odd"
  );
  countM = leaf "countM" nl.mergeOneOption;
  evenH = leaf "evenH" {
    __functor =
      self: loc: defs:
      (self.v2 { inherit loc defs; }).value;
    v2 =
      { loc, defs }:
      let
        v = nl.mergeEqualOption loc defs;
      in
      {
        headError = if nl.mod v 2 != 0 then { message = "odd"; } else null;
        value = v;
        valueMeta = { };
      };
  };

  doors = {
    mot = gm.mkOptionType;
    raw = t: t;
  };
  # every door and both orders of a declaration pair, at each value: `<door>-<order>-<value name>`
  grid =
    pair: vals: defs:
    builtins.listToAttrs (
      builtins.concatMap (
        dn:
        builtins.concatMap
          (
            o:
            let
              ts = map doors.${dn} (if o == "ab" then pair else nl.reverseList pair);
            in
            map (vn: {
              name = "${dn}-${o}-${vn}";
              value = ev ts vals.${vn} defs;
            }) (builtins.attrNames vals)
          )
          [
            "ab"
            "ba"
          ]
      ) (builtins.attrNames doors)
    );
  every =
    vals: verdicts:
    builtins.listToAttrs (
      builtins.concatMap (
        dn:
        builtins.concatMap
          (
            o:
            map (vn: {
              name = "${dn}-${o}-${vn}";
              value = verdicts.${vn};
            }) (builtins.attrNames vals)
          )
          [
            "ab"
            "ba"
          ]
      ) (builtins.attrNames doors)
    );
  pv = {
    good = {
      a = 80;
    };
    bad = {
      a = 70000;
    };
  };
  pvVerdicts = {
    good = "SERVED";
    bad = "REFUSED";
  };
  ev3 = {
    four = 4;
    three = 3;
  };
  evVerdicts = {
    four = "SERVED";
    three = "REFUSED";
  };
in
{
  flake.tests.merge-held-admission = {

    # the element check lives in the container's merge: 70000 is refused, as `bobbinR port` alone refuses it
    test-a-merge-held-element-check-is-owed = {
      expr = grid [ (bobbinR np.port) (bobbinR np.int) ] pv 1;
      expected = every pv pvVerdicts;
    };

    # beside a merge-blind declaration of the same constructor name: two merges, one name
    test-a-merge-held-check-beside-a-blind-merge-is-owed = {
      expr = grid [ (bobbinR np.port) (bobbin np.int) ] pv 1;
      expected = every pv pvVerdicts;
    };

    # the control: neither merge reads its element, so each declaration alone serves 70000, and so does the pair
    test-control-two-blind-merges-serve-what-each-serves = {
      expr = grid [ (bobbin np.port) (bobbin np.int) ] pv 1;
      expected = every pv {
        good = "SERVED";
        bad = "SERVED";
      };
    };

    # a leaf's fold refusing an odd value. Two cells serve nothing at 4 at every tree, pre-G11 included, and are
    # pinned so a landing that moves them does so knowingly:
    #  - `raw-ab-four`: declared raw, the later `int`'s own relation decides, and it joins no `evenM` (nixpkgs refuses
    #    the pair too);
    #  - `mot-ba-four`: nixpkgs serves it; the leaf relation's veto (`nullaryRel` asked of a door-copied `int` beside
    #    an author leaf), den-hoag-wsnn0 v1 OQ4
    test-a-leaf-fold-refusal-is-owed = {
      expr = grid [ evenM np.int ] ev3 1;
      expected = every ev3 evVerdicts // {
        mot-ba-four = "REFUSED";
        raw-ab-four = "REFUSED";
      };
    };

    # a leaf's fold refusing a second definition (one value, defined twice)
    test-a-leaf-fold-refusing-a-second-definition-is-owed = {
      expr = grid [ countM np.int ] { four = 4; } 2;
      expected = every { four = 4; } { four = "REFUSED"; };
    };

    # admission held in a v2 fold's `headError`, which `.value` does not read
    test-a-v2-fold-head-error-is-owed = {
      expr = grid [ evenH np.int ] ev3 1;
      expected = every ev3 evVerdicts // {
        mot-ba-four = "REFUSED";
        raw-ab-four = "REFUSED";
      };
    };

    # BELOW A CONTAINER AND UNDER A UNION: the held pair is an element, so its hold is met at that role
    test-a-merge-held-check-below-a-container-is-owed = {
      expr = {
        listOf = grid [ (np.listOf (bobbinR np.port)) (np.listOf (bobbinR np.int)) ] {
          good = [ { a = 80; } ];
          bad = [ { a = 70000; } ];
        } 1;
        attrsOf = grid [ (np.attrsOf (bobbinR np.port)) (np.attrsOf (bobbinR np.int)) ] {
          good = {
            k.a = 80;
          };
          bad = {
            k.a = 70000;
          };
        } 1;
        nullOr = grid [ (np.nullOr (bobbinR np.port)) (np.nullOr (bobbinR np.int)) ] pv 1;
        either = grid [ (np.either (bobbinR np.port) np.str) (np.either (bobbinR np.int) np.str) ] pv 1;
        listOfLeaf = grid [ (np.listOf evenM) (np.listOf np.int) ] {
          four = [ 4 ];
          three = [ 3 ];
        } 1;
      };
      expected = {
        listOf = every pv pvVerdicts;
        attrsOf = every pv pvVerdicts;
        nullOr = every pv pvVerdicts;
        either = every pv pvVerdicts;
        # 4's two refusals are the leaf's own, as `test-a-leaf-fold-refusal-is-owed` states
        listOfLeaf = every ev3 evVerdicts // {
          mot-ba-four = "REFUSED";
          raw-ab-four = "REFUSED";
        };
      };
    };

    # A HELD RECORD MERGED AGAIN KEEPS ITS HOLD: three declarations, so the second step meets the record the first
    # step held
    test-a-held-record-merged-again-keeps-its-hold = {
      expr = {
        portIntInt = grid [ (bobbinR np.port) (bobbinR np.int) ] pv 1 // {
          three-ba = ev [ (bobbinR np.int) (bobbinR np.int) (bobbinR np.port) ] pv.bad 1;
          three-ba-mot = ev (map gm.mkOptionType [
            (bobbinR np.int)
            (bobbinR np.int)
            (bobbinR np.port)
          ]) pv.bad 1;
          three-mid = ev [ (bobbinR np.int) (bobbinR np.port) (bobbinR np.int) ] pv.bad 1;
          three-mid-mot = ev (map gm.mkOptionType [
            (bobbinR np.int)
            (bobbinR np.port)
            (bobbinR np.int)
          ]) pv.bad 1;
          three-mid-good = ev [ (bobbinR np.int) (bobbinR np.port) (bobbinR np.int) ] pv.good 1;
        };
        leaf = {
          three-ba = ev [ np.int np.int evenM ] 3 1;
          three-ba-mot = ev [ (gm.mkOptionType np.int) (gm.mkOptionType np.int) (gm.mkOptionType evenM) ] 3 1;
        };
      };
      expected = {
        portIntInt = every pv pvVerdicts // {
          three-ba = "REFUSED";
          three-ba-mot = "REFUSED";
          three-mid = "REFUSED";
          three-mid-mot = "REFUSED";
          three-mid-good = "SERVED";
        };
        leaf = {
          three-ba = "REFUSED";
          three-ba-mot = "REFUSED";
        };
      };
    };

    # A HELD RECORD HANDED TO NIXPKGS' ENGINE KEEPS ITS HOLD: its exported `typeMerge` meets a later join with the
    # held record, so `bobbinR int` declared first and the held pair after it refuses 70000, which the held pair alone
    # refuses. The other order is decided by the later raw nixpkgs declaration's own relation (ADR-0039, Not covered).
    test-a-held-record-keeps-its-hold-in-nixpkgs-engine =
      let
        held = d: gm.mergeTypes (d (bobbinR np.int)) (d (bobbinR np.port));
      in
      {
        expr = {
          mot = evNixpkgs [ (gm.mkOptionType (bobbinR np.int)) (held gm.mkOptionType) ] pv.bad;
          mot-good = evNixpkgs [ (gm.mkOptionType (bobbinR np.int)) (held gm.mkOptionType) ] pv.good;
          raw = evNixpkgs [
            (bobbinR np.int)
            (held (t: t))
          ] pv.bad;
          held-alone = evNixpkgs [ (held (t: t)) ] pv.bad;
        };
        expected = {
          mot = "REFUSED";
          mot-good = "SERVED";
          raw = "REFUSED";
          held-alone = "REFUSED";
        };
      };
  };
}
