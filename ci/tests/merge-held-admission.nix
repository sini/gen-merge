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
  # an author NAMED `int` whose admission lives in its merge (refuses an odd value), stating a relation that answers an
  # `int` partner with a join keeping every name: nixpkgs' protocol (`typeMerge`, through the door) and gen's
  # (`typeMergeRel`); neither relation is one gen-merge constructed (den-hoag-1yqkr)
  evenNamedInt =
    let
      self = nl.mkOptionType {
        name = "int";
        check = builtins.isInt;
        merge = evenMerge;
        functor = np.defaultFunctor "int" // {
          type = _: self;
        };
        typeMerge = f: if f.name == "int" then np.int else null;
      };
    in
    gm.mkOptionType self;
  evenNamedIntRel = gm.mkOptionType {
    name = "int";
    check = builtins.isInt;
    merge = evenMerge;
    typeMergeRel =
      o: if (o.name or null) == "int" then { merged = gm.types.int; } else { refused = "not an int"; };
  };
  evenMerge =
    loc: defs:
    let
      v = nl.mergeEqualOption loc defs;
    in
    if nl.mod v 2 == 0 then v else throw "odd";
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

    # a leaf's fold refusing an odd value. One cell serves nothing at 4 at every tree, pre-G11 included, and is
    # pinned so a landing that moves it does so knowingly: `raw-ab-four`, declared raw, where the later `int`'s own
    # relation decides and joins no `evenM` (nixpkgs refuses the pair too). `mot-ba-four` serves 4, as nixpkgs does:
    # the leaf relation's refusal of the door-copied author leaf decides only as the decider (`nullaryRel`)
    test-a-leaf-fold-refusal-is-owed = {
      expr = grid [ evenM np.int ] ev3 1;
      expected = every ev3 evVerdicts // {
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
        # 4's refusal is the leaf's own, as `test-a-leaf-fold-refusal-is-owed` states
        listOfLeaf = every ev3 evVerdicts // {
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

    # A JOIN KEEPING EVERY NAME CERTIFIES NO FOLD: an author named `int` beside nixpkgs' or gen's `int`, its relation not
    # one gen-merge constructed, is held at the step, so 3 (its merge refuses it) is refused and 4 served, both orders
    test-an-uncertified-relation-keeping-names-holds-its-fold = {
      expr = builtins.listToAttrs (
        builtins.concatMap
          (
            p:
            builtins.concatMap
              (o: [
                {
                  name = "${p.n}-${o}-three";
                  value = ev (if o == "ab" then p.ts else nl.reverseList p.ts) 3 1;
                }
                {
                  name = "${p.n}-${o}-four";
                  value = ev (if o == "ab" then p.ts else nl.reverseList p.ts) 4 1;
                }
              ])
              [
                "ab"
                "ba"
              ]
          )
          [
            {
              n = "np-np";
              ts = [
                evenNamedInt
                np.int
              ];
            }
            {
              n = "np-gen";
              ts = [
                evenNamedInt
                gm.types.int
              ];
            }
            {
              n = "rel-np";
              ts = [
                evenNamedIntRel
                np.int
              ];
            }
            {
              n = "rel-gen";
              ts = [
                evenNamedIntRel
                gm.types.int
              ];
            }
          ]
      );
      expected = builtins.listToAttrs (
        builtins.concatMap
          (n: [
            {
              name = "${n}-three";
              value = "REFUSED";
            }
            {
              name = "${n}-four";
              value = "SERVED";
            }
          ])
          [
            "np-np-ab"
            "np-np-ba"
            "np-gen-ab"
            "np-gen-ba"
            "rel-np-ab"
            "rel-np-ba"
            "rel-gen-ab"
            "rel-gen-ba"
          ]
      );
    };

    # A HELD OPERAND ITS CARRIER DOES NOT HOLD IS OWED: `x` is the met record of `listOf int` and `listOf positive`,
    # `y` of `listOf int` and `listOf (between 0 10)`, each re-declared as an author does (`type = options.o.type`).
    # Declared together, the step meets a carrier holding one of them beside the other, so `[ 0 ]`, which `x` alone
    # refuses, is refused on both engines; a carrier owes nothing again only for an operand it states it holds.
    test-a-held-operand-its-carrier-does-not-hold-is-owed =
      let
        mt =
          tys:
          (gm.evalModuleTree { } (map (ty: { options.o = gm.mkOption { type = ty; }; }) tys)).options.o.type;
        x = mt [
          (gm.types.listOf gm.types.int)
          (gm.types.listOf np.ints.positive)
        ];
        y = mt [
          (gm.types.listOf gm.types.int)
          (gm.types.listOf (np.ints.between 0 10))
        ];
      in
      {
        expr = {
          gen = ev [ x y ] [ 0 ] 1;
          gen-good = ev [ x y ] [ 5 ] 1;
          nixpkgs = evNixpkgs [ x y ] [ 0 ];
          nixpkgs-good = evNixpkgs [ x y ] [ 5 ];
          x-alone = ev [ x ] [ 0 ] 1;
          y-alone = ev [ y ] [ 0 ] 1;
        };
        expected = {
          gen = "REFUSED";
          gen-good = "SERVED";
          nixpkgs = "REFUSED";
          nixpkgs-good = "SERVED";
          x-alone = "REFUSED";
          y-alone = "SERVED";
        };
      };

    # A HELD RECORD COPIED WITH ITS CHECK OR ITS FOLD REPLACED HOLDS NOTHING: `z` is the element record of `x` and `y`
    # declared together, a held record stating it holds `x`'s element (`px`). A `//` copy answering itself from its own
    # `typeMerge` and replacing `check` (`tTrue`, `tInt`) or the fold (`fDefs`, `fNested`, the fold record copied with
    # its `__functor` replaced) is not the record that statement was made for, so `px` beside it is owed: `0` and `-1`,
    # which `px` alone refuses, and the two definitions `1` and `2`, which `px`'s fold refuses, are refused. A copy
    # replacing only `typeMerge` (`tm`) keeps the check and the fold the statement was made for, so `px` owes nothing
    # beside it and is still refused by that check. A copy keeping `check` and `mergeDefs` but stating a v2 `merge`
    # (`mv2`, nixpkgs' merge protocol, serving the head definition) is folded by that `merge`, so it is not the record
    # the statement was made for either, and `px` beside it is owed.
    test-a-held-record-copied-with-its-check-or-fold-replaced-holds-nothing =
      let
        mt =
          tys:
          (gm.evalModuleTree { } (map (ty: { options.o = gm.mkOption { type = ty; }; }) tys)).options.o.type;
        el = r: r.nestedTypes.elemType;
        x = mt [
          (gm.types.listOf gm.types.int)
          (gm.types.listOf np.ints.positive)
        ];
        y = mt [
          (gm.types.listOf gm.types.int)
          (gm.types.listOf (np.ints.between 0 10))
        ];
        px = el x;
        z = el (mt [
          x
          y
        ]);
        first = _: defs: (builtins.head defs).value;
        tTrue = z // {
          check = _: true;
          typeMerge = _: tTrue;
        };
        tInt = z // {
          check = gm.types.int.check;
          typeMerge = _: tInt;
        };
        fDefs = z // {
          mergeDefs = first;
          typeMerge = _: fDefs;
        };
        fNested = z // {
          mergeDefs =
            if builtins.isAttrs z.mergeDefs then z.mergeDefs // { __functor = _: first; } else first;
          typeMerge = _: fNested;
        };
        tm = z // {
          typeMerge = _: tm;
        };
        mv2 = z // {
          merge = {
            __functor = _: first;
            v2 = args: {
              value = (builtins.head args.defs).value;
              headError = null;
              valueMeta = { };
            };
          };
          typeMerge = _: mv2;
        };
        # gen's engine over distinct definitions
        evDefs =
          tys: vs:
          let
            res = gm.evalModuleTree { } (
              map (ty: { options.x = gm.mkOption { type = ty; }; }) tys ++ map (v: { x = v; }) vs
            );
          in
          verdict (tryEval (deepSeq res.config.x res.config.x));
      in
      {
        expr = {
          check-true = evDefs [ px tTrue ] [ 0 ];
          check-true-twice = evDefs [ px px tTrue ] [ (-1) ];
          check-int = evDefs [ px tInt ] [ 0 ];
          check-int-twice = evDefs [ px px tInt ] [ (-1) ];
          check-true-good = evDefs [ px tTrue ] [ 5 ];
          fold = evDefs [ px fDefs ] [ 1 2 ];
          fold-nested = evDefs [ px fNested ] [ 1 2 ];
          fold-good = evDefs [ px fDefs ] [ 5 ];
          type-merge = evDefs [ px tm ] [ 0 ];
          type-merge-good = evDefs [ px tm ] [ 5 ];
          merge-v2 = evDefs [ px mv2 ] [ 0 ];
          merge-v2-two = evDefs [ px mv2 ] [ 1 2 ];
          merge-v2-twice = evDefs [ px px mv2 ] [ 0 ];
          merge-v2-twice-two = evDefs [ px px mv2 ] [ 1 2 ];
          merge-v2-good = evDefs [ px mv2 ] [ 5 ];
          px-alone = evDefs [ px ] [ 0 ];
          px-alone-two = evDefs [ px ] [ 1 2 ];
          copy-alone = evDefs [ tTrue ] [ 0 ];
        };
        expected = {
          check-true = "REFUSED";
          check-true-twice = "REFUSED";
          check-int = "REFUSED";
          check-int-twice = "REFUSED";
          check-true-good = "SERVED";
          fold = "REFUSED";
          fold-nested = "REFUSED";
          fold-good = "SERVED";
          type-merge = "REFUSED";
          type-merge-good = "SERVED";
          merge-v2 = "REFUSED";
          merge-v2-two = "REFUSED";
          merge-v2-twice = "REFUSED";
          merge-v2-twice-two = "REFUSED";
          merge-v2-good = "SERVED";
          px-alone = "REFUSED";
          px-alone-two = "REFUSED";
          copy-alone = "SERVED";
        };
      };

    # HELD RECORDS THROUGH BOTH DOORS SERVE WHAT EACH SERVES: `px`, `py` and `z` (above) raw, through `mkOptionType` and
    # through `types.mkOptionType`, declared in every word of two to four of them. Gen's engine refuses a word's
    # definitions exactly where one of its records declared alone refuses them, and otherwise serves what each serves
    # (the alone oracle), for `0`, `11`, `5`, `-1` and the two definitions `1` and `2`. `expr` lists the words that
    # break it.
    test-held-records-through-both-doors-serve-what-each-serves =
      let
        mt =
          tys:
          (gm.evalModuleTree { } (map (ty: { options.o = gm.mkOption { type = ty; }; }) tys)).options.o.type;
        el = r: r.nestedTypes.elemType;
        x = mt [
          (gm.types.listOf gm.types.int)
          (gm.types.listOf np.ints.positive)
        ];
        y = mt [
          (gm.types.listOf gm.types.int)
          (gm.types.listOf (np.ints.between 0 10))
        ];
        z = el (mt [
          x
          y
        ]);
        letters = {
          px = el x;
          py = el y;
          inherit z;
          d1px = gm.mkOptionType (el x);
          d1z = gm.mkOptionType z;
          d2px = gm.types.mkOptionType (el x);
          d2z = gm.types.mkOptionType z;
        };
        names = builtins.attrNames letters;
        wordsOf =
          n:
          if n == 1 then
            map (c: [ c ]) names
          else
            builtins.concatMap (w: map (c: w ++ [ c ]) names) (wordsOf (n - 1));
        words = wordsOf 2 ++ wordsOf 3 ++ wordsOf 4;
        values = {
          zero = [ 0 ];
          eleven = [ 11 ];
          five = [ 5 ];
          negative = [ (-1) ];
          two = [
            1
            2
          ];
        };
        served =
          tys: vs:
          let
            r = tryEval (
              let
                v =
                  (gm.evalModuleTree { } (
                    map (ty: { options.x = gm.mkOption { type = ty; }; }) tys ++ map (v: { x = v; }) vs
                  )).config.x;
              in
              deepSeq v v
            );
          in
          if r.success then { value = r.value; } else null;
        alone = builtins.mapAttrs (c: t: builtins.mapAttrs (_: served [ t ]) values) letters;
      in
      {
        expr = builtins.concatMap (
          w:
          builtins.concatMap (
            k:
            let
              each = map (c: alone.${c}.${k}) w;
              want = if builtins.elem null each then null else builtins.head each;
            in
            if served (map (c: letters.${c}) w) values.${k} == want then
              [ ]
            else
              [ "${builtins.concatStringsSep "," w} ${k}" ]
          ) (builtins.attrNames values)
        ) words;
        expected = [ ];
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
