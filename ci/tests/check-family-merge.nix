# A FOREIGN JOIN THAT DROPS AN OPERAND'S CHECK REFUSES (`lib/interface.nix`, the witness).
#
# nixpkgs' `addCheck` keeps its base's `functor` and `typeMerge`, so redeclaring `port`, `u8` or
# `ints.between` joins to bare `int` and the check is gone: nixpkgs accepts 70000 for a `port`. The
# witness takes a foreign join only where it keeps each operand's stated name at every depth the
# operand wraps a type, and refuses otherwise; a pair that is one shared value keeps the operand.
#
# Each row declares one option over the listed types, defines one value, and reads the merged type's
# name and whether the value was accepted. The control cell pins what the witness must NOT refuse,
# including the joins that GAIN a role (a freeform submodule, an `attrTag` union) and the mixed
# gen/nixpkgs container pairs whose roles are spelled in two vocabularies.
{
  genMerge,
  genMergeCore,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  t = nixpkgsLib.types;
  inherit (builtins) deepSeq tryEval;

  ev =
    tys: val:
    let
      res = gm.evalModuleTree { } (
        map (ty: { options.p = gm.mkOption { type = ty; }; }) tys ++ [ { p = val; } ]
      );
      ty = tryEval (deepSeq res.options.p.type.name res.options.p.type.name);
      v = tryEval (deepSeq res.config.p res.config.p);
    in
    if ty.success then
      "MERGED ${ty.value} / ${if v.success then "ACCEPTED" else "REJECTED"}"
    else
      "REFUSED";

  # the relation alone, for a pair no value distinguishes
  merged =
    a: b:
    let
      r = gm.mergeTypes a b;
    in
    if r == null then "REFUSED" else r.name;

  imp = gm.mkOptionType;

  ff = t.submodule { freeformType = t.attrsOf t.str; };
  opt = t.submodule { options.x = nixpkgsLib.mkOption { type = t.int; }; };
  # `tagOf` generalises `tag` with the tag's own carried type, so a redeclaration under the SAME
  # tag key (D1) is expressible; `tag` keeps its int default for the distinct-key control below.
  tagOf = k: ty: t.attrTag { ${k} = nixpkgsLib.mkOption { type = ty; }; };
  tag = k: tagOf k t.int;
  gsub = gt.submodule { options.x = gm.mkOption { type = gt.int; }; };

  # Two wrappers built through `mkOptionType` whose stated `nestedTypes` no payload carries across,
  # so the join their relation answers is a gen record that cannot spell the operand's role.
  # `refinedLike` is gen-schema's `refined` (base's `nestedTypes`, `null` payload, a relation that
  # asks `mergeTypes` for the base and rebuilds); `rootWith` is a container carrying the element
  # itself as payload whose `binOp` asks the element's own foreign `typeMerge`. That relation is
  # NOT gen-aspects' `aspectsRoot`: its `aspectsRootWith` binds `binOp` to `mergeElemTypes`, which
  # is gen-merge's `mergeTypes`, so it is judged the way `refinedLike` is.
  refinedLike =
    base:
    let
      self = imp (
        removeAttrs base [
          "functor"
          "typeMerge"
        ]
        // {
          __base = base;
          typeMerge =
            f:
            let
              p = f.type or null;
              j = if p ? __base then gm.mergeTypes base p.__base else null;
            in
            if j == null then null else refinedLike j;
          functor = {
            name = "refined<${base.name}>";
            type = self;
            payload = null;
            binOp = _a: _b: null;
          };
        }
      );
    in
    self;
  rootWith =
    elemType:
    imp {
      name = "root";
      check = builtins.isAttrs;
      merge = _loc: defs: builtins.foldl' (acc: d: acc // d.value) { } defs;
      nestedTypes = { inherit elemType; };
      getSubOptions = prefix: elemType.getSubOptions (prefix ++ [ "<name>" ]);
      getSubModules = elemType.getSubModules or null;
      substSubModules = _m: rootWith elemType;
      functor = {
        name = "root";
        payload = elemType;
        binOp = a: b: if a ? typeMerge && b ? functor then a.typeMerge b.functor else null;
        type = rootWith;
      };
    };
  # a carried role (`payload.elemType`) whose relation answers `int` whatever it is asked: the
  # operand read in the join's vocabulary still states its element, so the drop stays visible
  intWrap =
    elemType:
    imp {
      name = "wrap";
      check = builtins.isList;
      merge = _loc: defs: builtins.concatMap (d: d.value) defs;
      nestedTypes = { inherit elemType; };
      getSubOptions = _prefix: { };
      getSubModules = null;
      substSubModules = _m: intWrap elemType;
      functor = {
        name = "wrap";
        payload = { inherit elemType; };
        binOp = _a: _b: { elemType = t.int; };
        type = { elemType }: intWrap elemType;
      };
    };
in
{
  flake.tests.check-family-merge = {

    test-a-renaming-check-family-pair-refuses = {
      expr = {
        r01 = ev [ (t.ints.between 0 10) (t.ints.between 100 200) ] 5;
        r04 = ev [ t.port t.int ] 70000;
        r05 = ev [ t.int t.port ] 70000;
        r06 = ev [ t.ints.u8 t.ints.u16 ] 300;
        r14 = ev [ t.ints.unsigned t.ints.positive ] 0;
        r16 = ev [ (t.numbers.between 0 1) (t.numbers.between 5 6) ] 3;
        r17 = ev [ (t.passwdEntry t.str) t.str ] "a:b";
        # D1: the same tag key carrying different types is a drop UNDER the tag, which the walk must
        # reach through `attrTag`'s option-record members (`roles`' foreign arm), not stop at them.
        r23 = ev [ (tagOf "a" t.port) (tagOf "a" t.int) ] { a = 70000; };
        r24 = ev [ (tagOf "a" t.int) (tagOf "a" t.port) ] { a = 70000; };
      };
      expected = {
        r01 = "REFUSED";
        r04 = "REFUSED";
        r05 = "REFUSED";
        r06 = "REFUSED";
        r14 = "REFUSED";
        r16 = "REFUSED";
        r17 = "REFUSED";
        r23 = "REFUSED";
        r24 = "REFUSED";
      };
    };

    # two calls build two values, so the twin is not one reified value and does not keep its operand
    test-a-constructed-check-family-twin-refuses = {
      expr = {
        r08 = ev [ (t.ints.between 0 1) (t.ints.between 0 1) ] 5;
        r22 = ev [ (t.ints.between 0 1) (t.ints.between 0 1) (t.ints.between 0 1) ] 5;
      };
      expected = {
        r08 = "REFUSED";
        r22 = "REFUSED";
      };
    };

    test-a-shared-check-family-twin-keeps-its-check = {
      expr = {
        r09 = ev [ t.port t.port ] 70000;
        r09-good = ev [ t.port t.port ] 8080;
      };
      expected = {
        r09 = "MERGED unsignedInt16 / REJECTED";
        r09-good = "MERGED unsignedInt16 / ACCEPTED";
      };
    };

    test-the-refusal-reaches-under-a-container = {
      expr = {
        r20 = ev [ (t.listOf (t.ints.between 0 1)) (t.listOf (t.ints.between 0 1)) ] [ 5 ];
        r21 = ev [ (gt.listOf (t.ints.between 0 1)) (gt.listOf (t.ints.between 0 1)) ] [ 5 ];
      };
      expected = {
        r20 = "REFUSED";
        r21 = "REFUSED";
      };
    };

    # a record imported through `mkOptionType` states `functor.binOp`, so it merges on `foreignRel`
    test-an-imported-check-family-pair-refuses = {
      expr = {
        between-twin = ev [ (imp (t.ints.between 0 1)) (imp (t.ints.between 0 1)) ] 0;
        port-int = ev [ (imp t.port) (imp t.int) ] 8080;
        int-port = ev [ (imp t.int) (imp t.port) ] 8080;
        ctl-int-twin = ev [ (imp t.int) (imp t.int) ] 1;
      };
      expected = {
        between-twin = "REFUSED";
        port-int = "REFUSED";
        int-port = "REFUSED";
        ctl-int-twin = "MERGED int / ACCEPTED";
      };
    };

    # ★ A KNOWN BOUNDARY, PINNED: the sealed-limb twin clause is dead on `foreignRel`, because
    # pointer identity does not survive the import, so ONE shared imported record declared twice
    # refuses where the bare twin keeps its operand. A landing that makes the clause live flips this.
    test-a-shared-imported-twin-refuses = {
      expr =
        let
          impPort = imp t.port;
        in
        {
          imported = ev [ impPort impPort ] 8080;
          bare = ev [ t.port t.port ] 8080;
        };
      expected = {
        imported = "REFUSED";
        bare = "MERGED unsignedInt16 / ACCEPTED";
      };
    };

    # A TYPE REDECLARED AS ITSELF DROPS NOTHING. Each operand is built separately, so no identity
    # carries it; the join is a gen record and the operand is read in its vocabulary. The planted
    # rows keep refusing: a different base, a different element, and a carried role renamed.
    test-a-self-redeclaration-through-a-gen-join-merges = {
      expr = {
        refined-listOf = ev [ (refinedLike (t.listOf t.str)) (refinedLike (t.listOf t.str)) ] [ "a" ];
        refined-listOf-listOf =
          ev
            [
              (refinedLike (t.listOf (t.listOf t.str)))
              (refinedLike (t.listOf (t.listOf t.str)))
            ]
            [ [ "a" ] ];
        refined-gen-listOf = ev [ (refinedLike (gt.listOf t.str)) (refinedLike (gt.listOf t.str)) ] [ "a" ];
        listOf-refined =
          ev
            [
              (t.listOf (refinedLike (t.listOf t.str)))
              (t.listOf (refinedLike (t.listOf t.str)))
            ]
            [ [ "a" ] ];
        root = ev [ (rootWith t.str) (rootWith t.str) ] { a = "x"; };
        root-three = ev [ (rootWith t.str) (rootWith t.str) (rootWith t.str) ] { a = "x"; };
        imported-listOf = ev [ (imp (t.listOf t.str)) (imp (t.listOf t.str)) ] [ "a" ];
        planted-refined-element =
          ev
            [ (refinedLike (t.listOf t.str)) (refinedLike (t.listOf t.int)) ]
            [ "a" ];
        planted-refined-check = ev [ (refinedLike (t.listOf t.port)) (refinedLike (t.listOf t.int)) ] [ 1 ];
        planted-carried-rename = ev [ (intWrap t.port) (intWrap t.port) ] [ 70000 ];
        # the refusal is the witness's, not a malformed fixture's
        planted-carried-rename-reason = ((intWrap t.port).typeMergeRel (intWrap t.port)).refused or null;
      };
      expected = {
        refined-listOf = "MERGED listOf / ACCEPTED";
        refined-listOf-listOf = "MERGED listOf / ACCEPTED";
        refined-gen-listOf = "MERGED listOf / ACCEPTED";
        listOf-refined = "MERGED listOf / ACCEPTED";
        root = "MERGED root / ACCEPTED";
        root-three = "MERGED root / ACCEPTED";
        imported-listOf = "MERGED listOf / ACCEPTED";
        planted-refined-element = "REFUSED";
        planted-refined-check = "REFUSED";
        planted-carried-rename = "REFUSED";
        planted-carried-rename-reason = "`wrap' and `wrap', which the first type's own `functor' joins to `wrap', a type that states neither declaration's own check";
      };
    };

    # A ROLE STATED IN `nestedTypes` IS CARRIED, so a gen join is judged over it: `rootWith`'s relation
    # asks the element's own foreign `typeMerge`, which joins `port ∥ int` to `int`, and the witness now
    # sees the element's check dropped.
    test-a-drop-under-a-stated-nested-role-is-seen = {
      expr = ev [ (rootWith t.port) (rootWith t.int) ] { a = 70000; };
      expected = "REFUSED";
    };

    # D2: the text is false whenever the join keeps ONE operand's own name — `int ∥ port` joins to
    # `int`, which IS `int`'s own name, so only `port`'s check is gone and "neither" over-claims.
    # "Neither" is pinned true only where the join renames past BOTH operands (`between ∥ between`).
    test-the-refusal-names-the-join = {
      expr =
        let
          reason = genMergeCore.mergeTypesReason t.int t.port;
          reasonBothDrop = genMergeCore.mergeTypesReason (t.ints.between 0 10) (t.ints.between 100 200);
        in
        {
          inherit reason reasonBothDrop;
          imported = ((imp t.int).typeMergeRel (imp t.port)).refused or null;
          importedBothDrop =
            ((imp (t.ints.between 0 10)).typeMergeRel (imp (t.ints.between 100 200))).refused or null;
          ctl = genMergeCore.mergeTypesReason t.int t.int;
        };
      expected = {
        reason = "`int' and `unsignedInt16', which their own relation joins to `int', a type that states the check `int' declares but not the check `unsignedInt16' declares";
        reasonBothDrop = "`intBetween' and `intBetween', which their own relation joins to `int', a type that states neither declaration's own check";
        imported = "`int' and `unsignedInt16', which the first type's own `functor' joins to `int', a type that states the check `int' declares but not the check `unsignedInt16' declares";
        importedBothDrop = "`intBetween' and `intBetween', which the first type's own `functor' joins to `int', a type that states neither declaration's own check";
        ctl = null;
      };
    };

    # A MERGE THAT WOULD DROP A WRAPPER'S CHECK MEETS IT, AT EVERY DEPTH (`mergeTypes`, lib/modules.nix;
    # den-hoag-l1j4q, owner-ruled 2026-10-06). `addCheck` over a gen record keeps its base's name and
    # relation, so the relation answers the bare base; the step restricts that answer by the wrapper's
    # check (`interface.metWith`), so the pair merges to the base's record and rejects what the wrapper
    # rejects: wrapper first or second, under a gen parametric, under a container, and in a
    # three-declaration list. nixpkgs serves every row.
    test-a-dropped-wrapper-check-is-met =
      let
        pos = x: x > 0;
        wi = t.addCheck gt.int pos;
        wi2 = t.addCheck gt.int pos;
        u = gt.union [ gt.int ];
        wu = t.addCheck u pos;
      in
      {
        expr = {
          plainThenWrapped = ev [ gt.int wi ] (-1);
          wrappedThenPlain = ev [ wi gt.int ] (-1);
          twoConstructions = ev [ wi wi2 ] (-1);
          genAddCheckTwin = ev [
            (t.addCheck gt.int (_: false))
            (t.addCheck gt.int (_: false))
          ] 5;
          threePlainWrappedPlain = ev [ gt.int wi gt.int ] (-1);
          uPlainThenWrapped = ev [ u wu ] (-1);
          uWrappedThenPlain = ev [ wu u ] (-1);
          lPlainThenWrapped = ev [ (gt.listOf gt.int) (gt.listOf wi) ] [ (-1) ];
          lWrappedThenPlain = ev [ (gt.listOf wi) (gt.listOf gt.int) ] [ (-1) ];
        };
        expected = {
          plainThenWrapped = "MERGED int / REJECTED";
          wrappedThenPlain = "MERGED int / REJECTED";
          twoConstructions = "MERGED int / REJECTED";
          genAddCheckTwin = "MERGED int / REJECTED";
          threePlainWrappedPlain = "MERGED int / REJECTED";
          uPlainThenWrapped = "MERGED union<int> / REJECTED";
          uWrappedThenPlain = "MERGED union<int> / REJECTED";
          lPlainThenWrapped = "MERGED listOf / REJECTED";
          lWrappedThenPlain = "MERGED listOf / REJECTED";
        };
      };

    # A MET RECORD MERGED AGAIN KEEPS THE ENUM UNION (`interface.meetOf`'s `typeMerge`, which meets the
    # next join through `metWith`; den-hoag-n8cpq item 2 on the meet). Three nixpkgs `enum`s over one
    # member each fold, in gen's engine, to their union in every order, so the member of the operand
    # joined last is served as nixpkgs serves it; a wrapper over a widened operand is still met, so the
    # value it rejects is rejected in every order while its other member is served, and also where
    # another declaration admits it (`wrappedOverlapB`: the wrapped operand's own members admit `b`, so
    # its check is owed there, ADR-0039's reading 2). A FRESH join met again is met, not served whole:
    # gen `either (listOf int) str` before two foreign ones refining their `int` elements still refuses
    # the element one of them refuses (`unionOfLists`).
    test-a-met-enum-merged-again-keeps-the-union =
      let
        ea = t.enum [ "a" ];
        eb = t.enum [ "b" ];
        ec = t.enum [ "c" ];
        w = t.addCheck (t.enum [
          "a"
          "b"
        ]) (v: v != "a");
        wOv = t.addCheck (t.enum [
          "a"
          "b"
        ]) (v: v != "b");
        # a foreign `int` refinement whose relation answers only its own kind (gen-schema's `refined`)
        rejInt =
          n:
          let
            self = nixpkgsLib.mkOptionType {
              name = "int";
              check = x: builtins.isInt x && x != n;
              merge = nixpkgsLib.options.mergeEqualOption;
              functor = nixpkgsLib.types.defaultFunctor "int" // {
                type = _: self;
                payload = {
                  refined = true;
                };
                binOp = a: _b: a;
              };
              typeMerge =
                f:
                if
                  f.name == "int"
                  && (
                    f.payload == null
                    ||
                      f.payload == {
                        refined = true;
                      }
                  )
                then
                  self
                else
                  null;
            };
          in
          self;
        orders = l: [
          l
          [
            (builtins.elemAt l 0)
            (builtins.elemAt l 2)
            (builtins.elemAt l 1)
          ]
          [
            (builtins.elemAt l 1)
            (builtins.elemAt l 0)
            (builtins.elemAt l 2)
          ]
          [
            (builtins.elemAt l 1)
            (builtins.elemAt l 2)
            (builtins.elemAt l 0)
          ]
          [
            (builtins.elemAt l 2)
            (builtins.elemAt l 0)
            (builtins.elemAt l 1)
          ]
          [
            (builtins.elemAt l 2)
            (builtins.elemAt l 1)
            (builtins.elemAt l 0)
          ]
        ];
        at = l: v: map (o: ev o v) (orders l);
        all6 = r: builtins.genList (_: r) 6;
      in
      {
        expr = {
          a = at [ ea eb ec ] "a";
          b = at [ ea eb ec ] "b";
          c = at [ ea eb ec ] "c";
          wrappedA = at [ w eb ec ] "a";
          wrappedB = at [ w eb ec ] "b";
          wrappedOverlapB = at [ wOv eb ec ] "b";
          unionOfLists =
            ev
              [
                (gt.either (gt.listOf gt.int) gt.str)
                (t.either (t.listOf (rejInt 7)) t.str)
                (t.either (t.listOf (rejInt 9)) t.str)
              ]
              [ 7 ];
        };
        expected = {
          a = all6 "MERGED enum / ACCEPTED";
          b = all6 "MERGED enum / ACCEPTED";
          c = all6 "MERGED enum / ACCEPTED";
          wrappedA = all6 "MERGED enum / REJECTED";
          wrappedB = all6 "MERGED enum / ACCEPTED";
          wrappedOverlapB = all6 "MERGED enum / REJECTED";
          unionOfLists = "MERGED either / REJECTED";
        };
      };

    # AN ENUM UNDER A STEP-FREE WRAPPER FOLDS TO THE UNION (`interface.metWith`'s `widens`, which reads
    # the whole parameter tree; den-hoag-kbiu2). Two nixpkgs `nullOr`, `uniq` or `either` declarations over
    # one-member enums are relativised to their own parameters as the bare enums are, so each member is
    # served in both orders, as nixpkgs serves it, and a value in no member is still rejected. Under a
    # step (`listOf`) the element level reaches the same union. A wrapper under the `nullOr` stays owed:
    # its rejected member is rejected, and the members it admits are served.
    test-an-enum-under-a-step-free-wrapper-folds-to-the-union =
      let
        ea = t.enum [ "a" ];
        eb = t.enum [ "b" ];
        ec = t.enum [ "c" ];
        w = t.addCheck (t.enum [
          "a"
          "b"
        ]) (v: v != "a");
        both = W: v: [
          (ev [ (W ea) (W eb) ] v)
          (ev [ (W eb) (W ea) ] v)
        ];
        eitherInt = x: t.either x t.int;
      in
      {
        expr = {
          nullOrA = both t.nullOr "a";
          nullOrB = both t.nullOr "b";
          nullOrNull = both t.nullOr null;
          nullOrZ = both t.nullOr "z";
          uniqB = both t.uniq "b";
          eitherB = both eitherInt "b";
          eitherZ = both eitherInt "z";
          nestedB = both (x: t.listOf (t.nullOr x)) [ "b" ];
          wrappedA = ev [ (t.nullOr w) (t.nullOr ec) ] "a";
          wrappedB = ev [ (t.nullOr w) (t.nullOr ec) ] "b";
          wrappedC = ev [ (t.nullOr ec) (t.nullOr w) ] "c";
        };
        expected = {
          nullOrA = [
            "MERGED nullOr / ACCEPTED"
            "MERGED nullOr / ACCEPTED"
          ];
          nullOrB = [
            "MERGED nullOr / ACCEPTED"
            "MERGED nullOr / ACCEPTED"
          ];
          nullOrNull = [
            "MERGED nullOr / ACCEPTED"
            "MERGED nullOr / ACCEPTED"
          ];
          nullOrZ = [
            "MERGED nullOr / REJECTED"
            "MERGED nullOr / REJECTED"
          ];
          uniqB = [
            "MERGED unique / ACCEPTED"
            "MERGED unique / ACCEPTED"
          ];
          eitherB = [
            "MERGED either / ACCEPTED"
            "MERGED either / ACCEPTED"
          ];
          eitherZ = [
            "MERGED either / REJECTED"
            "MERGED either / REJECTED"
          ];
          nestedB = [
            "MERGED listOf / ACCEPTED"
            "MERGED listOf / ACCEPTED"
          ];
          wrappedA = "MERGED nullOr / REJECTED";
          wrappedB = "MERGED nullOr / ACCEPTED";
          wrappedC = "MERGED nullOr / ACCEPTED";
        };
      };

    # A GEN ENUM UNDER A NIXPKGS WRAPPER FOLDS TO THE UNION (den-hoag-kbiu2 over n8cpq item 2): a gen
    # enum completed under nixpkgs' `enum` row, wrapped by each step-free nixpkgs wrapper and their nests
    # beside the same wrapper over a nixpkgs enum, serves both members in both orders, as nixpkgs serves
    # the all-nixpkgs pair. A value in neither member is still rejected.
    test-a-gen-enum-under-a-nixpkgs-wrapper-folds-to-the-union =
      let
        both = W: v: [
          (ev [
            (W.w (gt.enum "e1" [ "a" ]))
            (W.w (t.enum [ "b" ]))
          ] (W.put v))
          (ev [
            (W.w (t.enum [ "b" ]))
            (W.w (gt.enum "e1" [ "a" ]))
          ] (W.put v))
        ];
        two = x: [
          x
          x
        ];
        id = x: x;
        ws = {
          nullOr = {
            n = "nullOr";
            w = t.nullOr;
            put = id;
          };
          uniq = {
            n = "unique";
            w = t.uniq;
            put = id;
          };
          unique = {
            n = "unique";
            w = t.unique { message = "m"; };
            put = id;
          };
          eitherL = {
            n = "either";
            w = x: t.either x t.int;
            put = id;
          };
          eitherR = {
            n = "either";
            w = t.either t.int;
            put = id;
          };
          oneOf = {
            n = "either";
            w =
              x:
              t.oneOf [
                x
                t.int
              ];
            put = id;
          };
          nullOrNullOr = {
            n = "nullOr";
            w = x: t.nullOr (t.nullOr x);
            put = id;
          };
          nullOrUniq = {
            n = "nullOr";
            w = x: t.nullOr (t.uniq x);
            put = id;
          };
          uniqNullOr = {
            n = "unique";
            w = x: t.uniq (t.nullOr x);
            put = id;
          };
          listOfNullOr = {
            n = "listOf";
            w = x: t.listOf (t.nullOr x);
            put = v: [ v ];
          };
          attrsOfNullOr = {
            n = "attrsOf";
            w = x: t.attrsOf (t.nullOr x);
            put = v: { k = v; };
          };
        };
      in
      {
        expr = builtins.mapAttrs (_: W: {
          a = both W "a";
          b = both W "b";
          z = both W "z";
        }) ws;
        expected = builtins.mapAttrs (_: W: {
          a = two "MERGED ${W.n} / ACCEPTED";
          b = two "MERGED ${W.n} / ACCEPTED";
          z = two "MERGED ${W.n} / REJECTED";
        }) ws;
      };

    # A TREE'S ELEMENTS ARE THE ROLES THE MEET MEETS (`interface.metWith`'s `elementsOf`, as `carriedAt`
    # reads them): a foreign union of THREE members is not a pair the role meet reaches, so its members
    # state no element of the tree and the operand is owed whole. Its strict third member (positive ints,
    # beside nixpkgs' `int`) keeps rejecting -5 in both orders, while member 1 widens; a constructor whose
    # `functor.type` takes the member list is judged the same way. The two-member `either` beside the same
    # strict member is the control the role meet does reach.
    test-a-three-member-union-is-owed-whole-beside-a-widening-member =
      let
        dF = t.defaultFunctor;
        tri =
          ty: ts:
          nixpkgsLib.mkOptionType {
            name = "tri";
            check = v: builtins.any (x: x.check v) ts;
            merge = nixpkgsLib.options.mergeEqualOption;
            functor = dF "tri" // {
              type = ty;
              payload.elemType = ts;
              binOp = _: _: null;
            };
            typeMerge =
              f:
              if f.name != "tri" then
                null
              else
                let
                  ms = builtins.genList (
                    i: (builtins.elemAt ts i).typeMerge (builtins.elemAt f.payload.elemType i).functor
                  ) 3;
                in
                if builtins.any (m: m == null) ms then null else tri ty ms;
          };
        triP = tri (p: triP p.elemType);
        triL = tri triL;
        sInt = nixpkgsLib.mkOptionType {
          name = "int";
          check = v: builtins.isInt v && v > 0;
          merge = nixpkgsLib.options.mergeEqualOption;
        };
        both = a: b: v: [
          (ev [ a b ] v)
          (ev [ b a ] v)
        ];
        pair =
          T:
          both
            (T [
              (t.enum [ "a" ])
              t.str
              sInt
            ])
            (T [
              (t.enum [ "b" ])
              t.str
              t.int
            ]);
        two = x: [
          x
          x
        ];
        either2 = both (t.either (t.enum [ "a" ]) sInt) (t.either (t.enum [ "b" ]) t.int);
      in
      {
        expr = {
          triNeg = pair triP (-5);
          triPos = pair triP 7;
          triB = pair triP "b";
          listTypeNeg = pair triL (-5);
          listTypePos = pair triL 7;
          either2Neg = either2 (-5);
          either2B = either2 "b";
        };
        expected = {
          triNeg = two "MERGED tri / REJECTED";
          triPos = two "MERGED tri / ACCEPTED";
          triB = two "MERGED tri / ACCEPTED";
          listTypeNeg = two "MERGED tri / REJECTED";
          listTypePos = two "MERGED tri / ACCEPTED";
          either2Neg = two "MERGED either / REJECTED";
          either2B = two "MERGED either / ACCEPTED";
        };
      };

    # CONTROL: one wrapped value declared twice is one value, so it keeps its operand and its check:
    # the value the wrapper accepts is served and the one it refuses is rejected by the carried check.
    # Two separate containers over one shared wrapped element are the same case one level down.
    test-a-shared-wrapped-value-declared-twice-keeps-its-check =
      let
        wi = t.addCheck gt.int (x: x > 0);
        wu = t.addCheck (gt.union [ gt.int ]) (x: x > 0);
        lw = gt.listOf wi;
      in
      {
        expr = {
          wrappedTwicePos = ev [ wi wi ] 5;
          wrappedTwiceNeg = ev [ wi wi ] (-1);
          uWrappedTwicePos = ev [ wu wu ] 5;
          uWrappedTwiceNeg = ev [ wu wu ] (-1);
          lSharedTwicePos = ev [ lw lw ] [ 5 ];
          lSharedTwiceNeg = ev [ lw lw ] [ (-1) ];
          lSeparateTwicePos = ev [ (gt.listOf wi) (gt.listOf wi) ] [ 5 ];
          lSeparateTwiceNeg = ev [ (gt.listOf wi) (gt.listOf wi) ] [ (-1) ];
          ctlWrappedAlone = ev [ wi ] (-1);
          ctlPlainTwice = ev [ gt.int gt.int ] (-1);
        };
        expected = {
          wrappedTwicePos = "MERGED int / ACCEPTED";
          wrappedTwiceNeg = "MERGED int / REJECTED";
          uWrappedTwicePos = "MERGED union<int> / ACCEPTED";
          uWrappedTwiceNeg = "MERGED union<int> / REJECTED";
          lSharedTwicePos = "MERGED listOf / ACCEPTED";
          lSharedTwiceNeg = "MERGED listOf / REJECTED";
          lSeparateTwicePos = "MERGED listOf / ACCEPTED";
          lSeparateTwiceNeg = "MERGED listOf / REJECTED";
          ctlWrappedAlone = "MERGED int / REJECTED";
          ctlPlainTwice = "MERGED int / ACCEPTED";
        };
      };

    # A NIXPKGS `addCheck` AROUND A GEN LEAF IS THE SAME IN EVERY ORDER (den-hoag-7kj5s, ADR-0034's Decision,
    # ADR-0039's serve half and its correctness bound). The wrapper is a `//` copy whose only departure from
    # its completion is a witnessed `check`, and the meet carries that check, so the rename witness and the
    # relation's payload read take the copy's CARRIER (`interface.joinRenames`' `bare`, restated at the
    # entry of `default.nix`'s parametric relation), as they take the join of a met record `meetOf` built.
    # Every permutation of each declaration set reads one verdict per value, the law's: a value the
    # wrapper rejects is REJECTED, a value some declared enum admits and every declaration's own parameters
    # allow is ACCEPTED, a value no declaration admits is REJECTED.
    test-a-nixpkgs-wrapper-over-a-gen-leaf-is-the-same-in-every-order =
      let
        verdict = r: if r == "REFUSED" then r else builtins.elemAt (builtins.split " / " r) 2;
        perms =
          xs:
          if xs == [ ] then
            [ [ ] ]
          else
            builtins.concatLists (
              nixpkgsLib.imap0 (
                i: x:
                map (p: [ x ] ++ p) (
                  perms (nixpkgsLib.sublist 0 i xs ++ nixpkgsLib.sublist (i + 1) (builtins.length xs - i - 1) xs)
                )
              ) xs
            );
        # every order's verdict, collapsed to the set of distinct verdicts: one element is order-independence
        orders = tys: v: nixpkgsLib.unique (map (o: verdict (ev o v)) (perms tys));
        notA = x: x != "a";
        even = gt.typedef "even" (v: builtins.isInt v && v / 2 * 2 == v);
        Wg = t.addCheck (gt.enum "e" [
          "a"
          "b"
        ]) notA;
        N = t.enum [
          "b"
          "c"
        ];
        G = gt.enum "g" [
          "b"
          "c"
        ];
        H = gt.enum "h" [
          "c"
          "d"
        ];
        Nsame = t.enum [
          "a"
          "b"
        ];
        # a met record (`y` rejected by its wrapped operand) re-completed by `mkOptionType`: the completion
        # keeps its witnessed check (den-hoag-59gnz C1), so it is read as its join and the meet owes it the
        # met check, in every order.
        recompleted = gm.mkOptionType (
          (gm.evalModuleTree { } [
            {
              options.q = gm.mkOption {
                type = t.addCheck (gt.enum "g" [
                  "x"
                  "y"
                ]) (v: v != "y");
              };
            }
            { options.q = gm.mkOption { type = gt.enum "k" [ "x" ]; }; }
          ]).options.q.type
        );
        under = c: map c;
        put = {
          bare = v: v;
          listOf = v: [ v ];
        };
        C = {
          bare = x: x;
          listOf = t.listOf;
        };
        # a gen leaf wrapped, beside its nixpkgs twin `n`
        leaf =
          l: n: p: ok: bad: c:
          let
            tys = under C.${c} [
              (t.addCheck l (x: x != p))
              n
            ];
          in
          {
            ok = orders tys (put.${c} ok);
            p = orders tys (put.${c} p);
            bad = orders tys (put.${c} bad);
          };
        enumSet = c: tys: {
          a = orders (under C.${c} tys) (put.${c} "a");
          b = orders (under C.${c} tys) (put.${c} "b");
          c = orders (under C.${c} tys) (put.${c} "c");
          z = orders (under C.${c} tys) (put.${c} "z");
        };
      in
      {
        expr = {
          wN = enumSet "bare" [
            Wg
            N
          ];
          wG = enumSet "bare" [
            Wg
            G
          ];
          wNsame = enumSet "bare" [
            Wg
            Nsame
          ];
          wNG = enumSet "bare" [
            Wg
            N
            G
          ];
          wGH = enumSet "bare" [
            Wg
            G
            H
          ];
          listOf-wN = enumSet "listOf" [
            Wg
            N
          ];
          listOf-wGH = enumSet "listOf" [
            Wg
            G
            H
          ];
          # a nullary gen leaf under a nixpkgs container, beside its nixpkgs twin
          listOf-number = leaf gt.number t.number 1 3 "s" "listOf";
          listOf-str = leaf gt.str t.str "a" "c" 1 "listOf";
          # control: a nullary leaf the same in every order at base, bare and under the container
          int = leaf gt.int t.int 1 3 "s" "bare";
          listOf-int = leaf gt.int t.int 1 3 "s" "listOf";
          # a refinement (MINTED) and a registered custom type (COMPARED), wrapped beside themselves: the
          # sealed limb decides the CARRIER the same type, and the meet owes the wrapper
          refined =
            leaf (gt.refined gt.int gt.refinements.positive) (gt.refined gt.int gt.refinements.positive) 2 3
              (-1)
              "bare";
          typedef = leaf even even 2 4 3 "bare";
          recompleted = {
            x = orders [
              recompleted
              (gt.enum "h" [
                "x"
                "y"
              ])
            ] "x";
            y = orders [
              recompleted
              (gt.enum "h" [
                "x"
                "y"
              ])
            ] "y";
            z = orders [
              recompleted
              (gt.enum "h" [
                "x"
                "y"
              ])
            ] "z";
          };
        };
        expected =
          let
            acc = [ "ACCEPTED" ];
            rej = [ "REJECTED" ];
            ref = [ "REFUSED" ];
          in
          {
            wN = {
              a = rej;
              b = acc;
              c = acc;
              z = rej;
            };
            wG = {
              a = rej;
              b = acc;
              c = acc;
              z = rej;
            };
            wNsame = {
              a = rej;
              b = acc;
              c = rej;
              z = rej;
            };
            wNG = {
              a = rej;
              b = acc;
              c = acc;
              z = rej;
            };
            wGH = {
              a = rej;
              b = acc;
              c = acc;
              z = rej;
            };
            listOf-wN = {
              a = rej;
              b = acc;
              c = acc;
              z = rej;
            };
            listOf-wGH = {
              a = rej;
              b = acc;
              c = acc;
              z = rej;
            };
            listOf-number = {
              ok = acc;
              p = rej;
              bad = rej;
            };
            listOf-str = {
              ok = acc;
              p = rej;
              bad = rej;
            };
            int = {
              ok = acc;
              p = rej;
              bad = rej;
            };
            listOf-int = {
              ok = acc;
              p = rej;
              bad = rej;
            };
            refined = {
              ok = acc;
              p = rej;
              bad = rej;
            };
            typedef = {
              ok = acc;
              p = rej;
              bad = rej;
            };
            # re-completion keeps the met record's witnessed check (den-hoag-59gnz C1), so the meet owes
            # it and every order reads the law's verdict
            recompleted = {
              x = acc;
              y = rej;
              z = rej;
            };
          };
      };

    # A `//` COPY DEPARTING ANYWHERE BUT `check` IS MET IN EVERY ORDER (den-hoag-ndgcz, den-hoag-69w3d).
    # A copy that replaces `verify` keeps its completion's `check`, witness and relation, so the step's
    # owed test (`rewritesCheck`) cannot see it, and the carrier read it as its own record: beside its
    # plain twin the meet dropped its verify (ADR-0025 item 1), and beside nixpkgs' `enum` its verdict
    # depended on the order. Each row is the set of verdicts over every order of the declarations: one
    # element is order-independence, and `REJECTED` where the copy rejects is the meet (ADR-0039).
    test-a-copy-departing-anywhere-but-check-is-met-in-every-order =
      let
        verdict = r: if r == "REFUSED" then r else builtins.elemAt (builtins.split " / " r) 2;
        perms =
          xs:
          if xs == [ ] then
            [ [ ] ]
          else
            builtins.concatLists (
              nixpkgsLib.imap0 (
                i: x:
                map (p: [ x ] ++ p) (
                  perms (nixpkgsLib.sublist 0 i xs ++ nixpkgsLib.sublist (i + 1) (builtins.length xs - i - 1) xs)
                )
              ) xs
            );
        orders = tys: v: nixpkgsLib.unique (map (o: verdict (ev o v)) (perms tys));
        E = gt.enum "e" [
          "a"
          "b"
        ];
        notA = v: if v == "a" then "rejected by notA" else E.verify v;
        copies = {
          verify = E // {
            verify = notA;
          };
          described = E // {
            description = "a described copy";
          };
          # a control: renamed only, so every member is served
          renamedOnly = E // {
            name = "r";
          };
          renamed = E // {
            name = "r";
            verify = notA;
          };
          # den-hoag-69w3d's shape: `check` replaced, `verify` opened
          checkAndVerify = E // {
            check = v: v != "a";
            verify = _: null;
          };
          # the meet owes a copy's `check` AND its `verify`: here each rejects a different value
          split = E // {
            check = v: E.check v && v != "a";
            verify = v: if v == "b" then "rejected by notB" else E.verify v;
          };
        };
        twins = {
          plain = E;
          nixpkgs = t.enum [
            "a"
            "b"
          ];
          widening = t.enum [
            "b"
            "c"
          ];
          wideningGen = gt.enum "g" [
            "b"
            "c"
          ];
        };
        wraps = {
          bare = {
            ty = x: x;
            v = x: x;
          };
          listOf = {
            ty = t.listOf;
            v = x: [ x ];
          };
        };
        row =
          copy: twin: w:
          builtins.listToAttrs (
            map
              (v: {
                name = v;
                value = orders (map wraps.${w}.ty [
                  copy
                  twin
                ]) (wraps.${w}.v v);
              })
              [
                "a"
                "b"
                "c"
              ]
          );
        # a nullary leaf and a record that states `verify` with no completion stamp, beside themselves
        intCopy = gt.int // {
          verify = v: if v == 1 then "rejected by not1" else gt.int.verify v;
        };
        rawCopy = gt.raw // {
          verify = v: if v == 1 then "rejected by not1" else null;
        };
        leaf = copy: twin: {
          "1" = orders [ copy twin ] 1;
          "2" = orders [ copy twin ] 2;
        };
        # a caller `typedef`: two of its copies are one type only through the carrier
        even = gt.typedef "even" (v: builtins.isInt v && v / 2 * 2 == v);
        sealed = copy: {
          "2" = orders [ copy even ] 2;
          "3" = orders [ copy even ] 3;
          "4" = orders [ copy even ] 4;
        };
        # DISTINCT partners, each rejecting its own value, beside a twin in every order of three and of
        # four declarations: a check lost BETWEEN two partners is invisible where one partner is placed
        # twice. `vA` and `vC` replace `verify`, `cB` replaces `check`.
        F = gt.enum "e" [
          "a"
          "b"
          "c"
          "d"
        ];
        rejects = x: v: if v == x then "rejected by not${x}" else F.verify v;
        vA = F // {
          verify = rejects "a";
        };
        cB = F // {
          check = v: F.check v && v != "b";
        };
        vC = F // {
          verify = rejects "c";
        };
        distinct =
          partners:
          builtins.mapAttrs
            (
              _: twin:
              builtins.listToAttrs (
                map
                  (v: {
                    name = v;
                    value = orders (partners ++ [ twin ]) v;
                  })
                  [
                    "a"
                    "b"
                    "c"
                    "d"
                  ]
              )
            )
            {
              plain = F;
              nixpkgs = t.enum [
                "a"
                "b"
                "c"
                "d"
              ];
            };
      in
      {
        expr =
          builtins.mapAttrs (
            _: copy:
            builtins.mapAttrs (_: twin: row copy twin "bare") twins
            // {
              listOf = row copy twins.widening "listOf";
            }
          ) copies
          // {
            int = leaf intCopy gt.int;
            intBesideNixpkgs = leaf intCopy t.int;
            raw = leaf rawCopy gt.raw;
            typedef = sealed (even // { verify = v: if v == 2 then "rejected by not2" else even.verify v; });
            typedefDescribed = sealed (even // { description = "a described typedef"; });
            distinctThree = distinct [
              vA
              cB
            ];
            distinctFour = distinct [
              vA
              cB
              vC
            ];
          };
        expected =
          let
            acc = [ "ACCEPTED" ];
            rej = [ "REJECTED" ];
          in
          {
            checkAndVerify = {
              listOf = {
                a = rej;
                b = acc;
                c = acc;
              };
              nixpkgs = {
                a = rej;
                b = acc;
                c = rej;
              };
              plain = {
                a = rej;
                b = acc;
                c = rej;
              };
              widening = {
                a = rej;
                b = acc;
                c = acc;
              };
              wideningGen = {
                a = rej;
                b = acc;
                c = acc;
              };
            };
            described = {
              listOf = {
                a = acc;
                b = acc;
                c = acc;
              };
              nixpkgs = {
                a = acc;
                b = acc;
                c = rej;
              };
              plain = {
                a = acc;
                b = acc;
                c = rej;
              };
              widening = {
                a = acc;
                b = acc;
                c = acc;
              };
              wideningGen = {
                a = acc;
                b = acc;
                c = acc;
              };
            };
            renamedOnly = {
              listOf = {
                a = acc;
                b = acc;
                c = acc;
              };
              nixpkgs = {
                a = acc;
                b = acc;
                c = rej;
              };
              plain = {
                a = acc;
                b = acc;
                c = rej;
              };
              widening = {
                a = acc;
                b = acc;
                c = acc;
              };
              wideningGen = {
                a = acc;
                b = acc;
                c = acc;
              };
            };
            int = {
              "1" = rej;
              "2" = acc;
            };
            intBesideNixpkgs = {
              "1" = rej;
              "2" = acc;
            };
            raw = {
              "1" = rej;
              "2" = acc;
            };
            typedef = {
              "2" = rej;
              "3" = rej;
              "4" = acc;
            };
            typedefDescribed = {
              "2" = acc;
              "3" = rej;
              "4" = acc;
            };
            distinctThree =
              let
                r = {
                  a = rej;
                  b = rej;
                  c = acc;
                  d = acc;
                };
              in
              {
                plain = r;
                nixpkgs = r;
              };
            distinctFour =
              let
                r = {
                  a = rej;
                  b = rej;
                  c = rej;
                  d = acc;
                };
              in
              {
                plain = r;
                nixpkgs = r;
              };
            renamed = {
              listOf = {
                a = rej;
                b = acc;
                c = acc;
              };
              nixpkgs = {
                a = rej;
                b = acc;
                c = rej;
              };
              plain = {
                a = rej;
                b = acc;
                c = rej;
              };
              widening = {
                a = rej;
                b = acc;
                c = acc;
              };
              wideningGen = {
                a = rej;
                b = acc;
                c = acc;
              };
            };
            split = {
              listOf = {
                a = rej;
                b = rej;
                c = acc;
              };
              nixpkgs = {
                a = rej;
                b = rej;
                c = rej;
              };
              plain = {
                a = rej;
                b = rej;
                c = rej;
              };
              widening = {
                a = rej;
                b = rej;
                c = acc;
              };
              wideningGen = {
                a = rej;
                b = rej;
                c = acc;
              };
            };
            verify = {
              listOf = {
                a = rej;
                b = acc;
                c = acc;
              };
              nixpkgs = {
                a = rej;
                b = acc;
                c = rej;
              };
              plain = {
                a = rej;
                b = acc;
                c = rej;
              };
              widening = {
                a = rej;
                b = acc;
                c = acc;
              };
              wideningGen = {
                a = rej;
                b = acc;
                c = acc;
              };
            };
          };
      };

    # A RE-COMPLETION DOOR CARRIES A `//` COPY DEPARTING WITHIN ITS CARRIER AS IT IS (den-hoag-5kzqp).
    # Re-completed from its gen datum alone, a copy of a completed leaf lost the row its completion was
    # built under (`enum` published its caller's name with no payload, `string` published `string`) and
    # became its own record to every carrier reader, so through `defineType` it was refused where the
    # raw copy is served: beside a widening gen `enum` the union-admitted `c` (ADR-0039, the enum union),
    # beside nixpkgs' `str` the value its verify admits. The door returns it as it is, its declared domain
    # published as a witnessed rewrite and its `typeMerge` met with itself. Each gen row is the set of
    # verdicts over both orders; `parity` lists every (copy, twin, wrapper) whose door row is not the raw
    # copy's. `foreign` reads nixpkgs' own `evalModules` over the door's output.
    test-a-door-carries-a-copy-departing-within-its-carrier =
      let
        verdict = r: if r == "REFUSED" then r else builtins.elemAt (builtins.split " / " r) 2;
        orders =
          a: b: v:
          nixpkgsLib.unique [
            (verdict (ev [ a b ] v))
            (verdict (ev [ b a ] v))
          ];
        E = gt.enum "e" [
          "a"
          "b"
        ];
        notA = v: if v == "a" then "rejected by notA" else E.verify v;
        copies = {
          verify = E // {
            verify = notA;
          };
          renamed = E // {
            name = "r";
            verify = notA;
          };
          checkOnly = E // {
            check = v: E.check v && v != "a";
          };
          described = E // {
            description = "a described copy";
          };
        };
        twins = {
          wideningGen = gt.enum "g" [
            "b"
            "c"
          ];
          nixpkgs = t.enum [
            "a"
            "b"
          ];
          widening = t.enum [
            "b"
            "c"
          ];
        };
        wraps = {
          bare = {
            ty = x: x;
            v = x: x;
          };
          listOf = {
            ty = t.listOf;
            v = x: [ x ];
          };
        };
        row =
          door: copy: twin: w:
          builtins.listToAttrs (
            map
              (v: {
                name = v;
                value = orders (wraps.${w}.ty (door copy)) (wraps.${w}.ty twin) (wraps.${w}.v v);
              })
              [
                "a"
                "b"
                "c"
              ]
          );
        parity = builtins.concatLists (
          nixpkgsLib.mapAttrsToList (
            cn: copy:
            builtins.concatLists (
              nixpkgsLib.mapAttrsToList (
                tn: twin:
                builtins.concatMap (
                  w: if row gt.defineType copy twin w == row (x: x) copy twin w then [ ] else [ "${cn}/${tn}/${w}" ]
                ) (builtins.attrNames wraps)
              ) twins
            )
          ) copies
        );
        S = gt.string // {
          verify = v: if v == "a" then "rejected by notA" else null;
        };
        np =
          tys: v:
          let
            r = nixpkgsLib.evalModules {
              modules = map (ty: { options.p = nixpkgsLib.mkOption { type = ty; }; }) tys ++ [ { p = v; } ];
            };
            o = tryEval (deepSeq r.config.p r.config.p);
          in
          if o.success then "ACCEPTED" else "REJECTED";
        door = gt.defineType copies.verify;
      in
      {
        expr = {
          inherit parity;
          wideningGen = {
            verify = row gt.defineType copies.verify twins.wideningGen "bare";
            renamed = row gt.defineType copies.renamed twins.wideningGen "listOf";
          };
          string = {
            a = orders (gt.defineType S) t.str "a";
            b = orders (gt.defineType S) t.str "b";
          };
          foreign = {
            alone = {
              a = np [ door ] "a";
              b = np [ door ] "b";
            };
            # nixpkgs asks the later declaration's `typeMerge`: here the door's
            asksTheDoor = {
              a = np [ twins.nixpkgs door ] "a";
              b = np [ twins.nixpkgs door ] "b";
            };
            union = {
              a = np [ (gt.listOf door) (gt.listOf twins.wideningGen) ] [ "a" ];
              c = np [ (gt.listOf door) (gt.listOf twins.wideningGen) ] [ "c" ];
            };
          };
        };
        expected = {
          parity = [ ];
          wideningGen = {
            verify = {
              a = [ "REJECTED" ];
              b = [ "ACCEPTED" ];
              c = [ "ACCEPTED" ];
            };
            renamed = {
              a = [ "REJECTED" ];
              b = [ "ACCEPTED" ];
              c = [ "ACCEPTED" ];
            };
          };
          string = {
            a = [ "REJECTED" ];
            b = [ "ACCEPTED" ];
          };
          foreign = {
            alone = {
              a = "REJECTED";
              b = "ACCEPTED";
            };
            asksTheDoor = {
              a = "REJECTED";
              b = "ACCEPTED";
            };
            union = {
              a = "REJECTED";
              c = "ACCEPTED";
            };
          };
        };
      };

    # THE IMPORT DOOR CARRIES A `//` COPY DEPARTING WITHIN ITS CARRIER AS IT IS (den-hoag-r23mj). Imported as a
    # record of its own, a copy of a completed gen type was rebuilt from its own functor and entered unminted,
    # so through `mkOptionType` it was refused where the raw copy is served: beside its gen twin in both orders
    # (`enum`, `struct`, `typedef`; beside a widening gen `enum` the union-admitted `c` too), beside nixpkgs'
    # twin in one order. The door returns it as `defineType` does (`interface.carriedCopy`). `parity` lists
    # every (copy, twin, wrapper) whose door row is not the raw copy's; `identity` reads ADR-0034 on the door's
    # output: the copy keeps its mark and its stale stamp, so `idOf` and `typeEq` refuse it by name, while the
    # completion answers for itself.
    test-the-import-door-carries-a-copy-departing-within-its-carrier =
      let
        verdict = r: if r == "REFUSED" then r else builtins.elemAt (builtins.split " / " r) 2;
        orders =
          a: b: v:
          nixpkgsLib.unique [
            (verdict (ev [ a b ] v))
            (verdict (ev [ b a ] v))
          ];
        notBad =
          bad: base: v:
          if v == bad then "rejected by notBad" else (base.verify or (_: null)) v;
        E = gt.enum "e" [
          "a"
          "b"
        ];
        St = gt.struct "s" { a = gt.int; };
        Td = gt.typedef "td" builtins.isInt;
        # each copy with the values it is read at and the twins it is declared beside
        cases = {
          enumVerify = {
            copy = E // {
              verify = notBad "a" E;
            };
            vals = [
              "a"
              "b"
              "c"
            ];
            twins = {
              gen = E;
              wideningGen = gt.enum "g" [
                "b"
                "c"
              ];
              nixpkgs = t.enum [
                "a"
                "b"
              ];
              widening = t.enum [
                "b"
                "c"
              ];
            };
          };
          enumRenamed = cases.enumVerify // {
            copy = E // {
              name = "r";
              verify = notBad "a" E;
            };
          };
          enumCheckOnly = cases.enumVerify // {
            copy = E // {
              check = v: E.check v && v != "a";
            };
          };
          structVerify = {
            copy = St // {
              verify = notBad { a = 1; } St;
            };
            vals = [
              { a = 1; }
              { a = 2; }
            ];
            twins = {
              gen = St;
              nixpkgs = t.attrs;
            };
          };
          typedefVerify = {
            copy = Td // {
              verify = notBad 1 Td;
            };
            vals = [
              1
              2
            ];
            twins = {
              gen = Td;
              nixpkgs = t.int;
            };
          };
          stringVerify = {
            copy = gt.string // {
              verify = notBad "a" gt.string;
            };
            vals = [
              "a"
              "b"
            ];
            twins = {
              nixpkgs = t.str;
            };
          };
        };
        wraps = {
          bare = {
            ty = x: x;
            v = x: x;
          };
          listOf = {
            ty = t.listOf;
            v = x: [ x ];
          };
        };
        row =
          door: c: twin: w:
          map (v: orders (wraps.${w}.ty (door c.copy)) (wraps.${w}.ty twin) (wraps.${w}.v v)) c.vals;
        parity = builtins.concatLists (
          nixpkgsLib.mapAttrsToList (
            cn: c:
            builtins.concatLists (
              nixpkgsLib.mapAttrsToList (
                tn: twin:
                builtins.concatMap (
                  w: if row imp c twin w == row (x: x) c twin w then [ ] else [ "${cn}/${tn}/${w}" ]
                ) (builtins.attrNames wraps)
              ) c.twins
            )
          ) cases
        );
        refused = e: !(tryEval (deepSeq e e)).success;
        identity =
          base: copy:
          let
            d = imp copy;
          in
          {
            minted = d.__mint ? minted;
            idOf = refused (genTypes.idOf d == genTypes.idOf base);
            typeEq = refused (gt.typeEq base d);
          };
      in
      {
        expr = {
          inherit parity;
          gen = {
            enum = row imp cases.enumVerify E "bare";
            struct = row imp cases.structVerify St "bare";
            typedef = row imp cases.typedefVerify Td "bare";
            union = row imp cases.enumVerify cases.enumVerify.twins.wideningGen "bare";
          };
          string = row imp cases.stringVerify t.str "bare";
          identity = {
            enum = identity E cases.enumVerify.copy;
            struct = identity St cases.structVerify.copy;
            typedef = identity Td cases.typedefVerify.copy;
          };
          # the predicates answer: the completion compares equal to itself
          control = {
            enum = gt.typeEq E (imp E);
            idOf = genTypes.idOf (imp E) == genTypes.idOf E;
          };
        };
        expected = {
          parity = [ ];
          gen = {
            enum = [
              [ "REJECTED" ]
              [ "ACCEPTED" ]
              [ "REJECTED" ]
            ];
            struct = [
              [ "REJECTED" ]
              [ "ACCEPTED" ]
            ];
            typedef = [
              [ "REJECTED" ]
              [ "ACCEPTED" ]
            ];
            union = [
              [ "REJECTED" ]
              [ "ACCEPTED" ]
              [ "ACCEPTED" ]
            ];
          };
          string = [
            [ "REJECTED" ]
            [ "ACCEPTED" ]
          ];
          identity = {
            enum = {
              minted = true;
              idOf = true;
              typeEq = true;
            };
            struct = {
              minted = true;
              idOf = true;
              typeEq = true;
            };
            typedef = {
              minted = true;
              idOf = true;
              typeEq = true;
            };
          };
          control = {
            enum = true;
            idOf = true;
          };
        };
      };

    # THE TWO CARRIER SPELLINGS AGREE (den-hoag-7kj5s). `interface.joinRenames`' `bare` is restated at the
    # entry of `default.nix`'s parametric relation rather than shared, for the load gates' cost, so the
    # carrier has two spellings. Each is read off its source and evaluated, and over one population both
    # name the same carrier, the one each record's class states: a `//` copy departing from its
    # completion only at fields the meet owes (`check`, `verify`) or that translate nothing (the
    # name-carried ones) its completion (den-hoag-ndgcz), the met record `meetOf` built its join, and
    # every other record itself — a met record re-completed by `mkOptionType` (its witness is no
    # longer its join's) among them. The population deliberately holds no met record over a foreign join
    # whose `check` is a bare function: `==` decides that witness differently per evaluator (Lix reads
    # the record as its join, Nix and Determinate as itself), so no one expected carrier holds there.
    test-the-two-carrier-spellings-agree =
      let
        inherit (genMergeCore) interface;
        scope = {
          inherit (interface)
            rewritesCheck
            exportClasses
            departsWithinCarrier
            carrierTolerated
            ;
          stampOk = genTypes.stampOk;
          checkedTypes = genTypes;
          core = { inherit interface; };
        };
        spelling =
          file:
          let
            lines = builtins.filter builtins.isString (builtins.split "\n" (builtins.readFile file));
            n = builtins.length lines;
            at = builtins.filter (i: builtins.match " *bare =" (builtins.elemAt lines i) != null) (
              builtins.genList (i: i) n
            );
            indent = builtins.head (builtins.match "( *)bare =" (builtins.elemAt lines (builtins.head at)));
            body =
              i:
              let
                l = builtins.elemAt lines i;
              in
              if i < n && (l == "" || builtins.match "${indent} .*" l != null) then
                [ l ] ++ body (i + 1)
              else
                [ ];
          in
          {
            count = builtins.length at;
            read = import (builtins.toFile "carrier.nix" ''
              { rewritesCheck, exportClasses, departsWithinCarrier, carrierTolerated, stampOk, checkedTypes, core }:
              let
                bare =
              ${builtins.concatStringsSep "\n" (body (builtins.head at + 1))}
              in
              bare
            '') scope;
          };
        joinRenames = spelling ../../lib/interface.nix;
        relation = spelling ../../lib/default.nix;
        # which record a spelling names: the carrier's name, how many meets it still records, and
        # whether its `check` is still rewritten
        meets = r: if r ? __meetJoin then 1 + meets r.__meetJoin else 0;
        shape = r: {
          inherit (r) name;
          meets = meets r;
          rewrites = interface.rewritesCheck r;
        };
        metOf =
          tys:
          (gm.evalModuleTree { } (map (ty: { options.q = gm.mkOption { type = ty; }; }) tys)).options.q.type;
        notA = x: x != "a";
        wrapped = t.addCheck (gt.enum "e" [
          "a"
          "b"
        ]) notA;
        population = {
          raw = gt.enum "e" [
            "a"
            "b"
          ];
          nixpkgs = t.enum [
            "b"
            "c"
          ];
          checkOnly = wrapped;
          descriptionCopy = wrapped // {
            description = "a described wrapper";
          };
          verifyCopy =
            gt.enum "e" [
              "a"
              "b"
            ]
            // {
              check = notA;
              verify = _: null;
            };
          verifyOnlyCopy =
            gt.enum "e" [
              "a"
              "b"
            ]
            // {
              verify = v: if v == "a" then "rejected by notA" else null;
            };
          descriptionOnlyCopy =
            gt.enum "e" [
              "a"
              "b"
            ]
            // {
              description = "a described enum";
            };
          met = metOf [
            wrapped
            (gt.enum "g" [
              "b"
              "c"
            ])
          ];
          # a fold re-meets the carrier, so a met record over a met join is built by `meetOf` itself
          metOfMet =
            interface.meetOf
              (metOf [
                wrapped
                (gt.enum "g" [
                  "b"
                  "c"
                ])
              ])
              [
                (t.addCheck (gt.enum "h" [
                  "c"
                  "d"
                ]) (v: v != "d"))
              ];
          recompletedMet = gm.mkOptionType (metOf [
            (t.addCheck (gt.enum "g" [
              "x"
              "y"
            ]) (v: v != "y"))
            (gt.enum "k" [ "x" ])
          ]);
        };
      in
      {
        expr = {
          spellings = {
            joinRenames = joinRenames.count;
            relation = relation.count;
          };
          carriers = builtins.mapAttrs (_: x: {
            record = shape x;
            agree = shape (joinRenames.read x) == shape (relation.read x);
            carrier = shape (joinRenames.read x);
          }) population;
          completions = builtins.mapAttrs (_: x: {
            joinRenames = genTypes.stampOk (joinRenames.read x);
            relation = genTypes.stampOk (relation.read x);
          }) { inherit (population) verifyOnlyCopy descriptionOnlyCopy; };
        };
        expected = {
          completions =
            let
              both = {
                joinRenames = true;
                relation = true;
              };
            in
            {
              verifyOnlyCopy = both;
              descriptionOnlyCopy = both;
            };
          spellings = {
            joinRenames = 1;
            relation = 1;
          };
          # each record's class, and the carrier both spellings name for it
          carriers =
            let
              sh = name: meets: rewrites: { inherit name meets rewrites; };
              row = record: carrier: {
                inherit record carrier;
                agree = true;
              };
            in
            {
              raw = row (sh "e" 0 false) (sh "e" 0 false);
              nixpkgs = row (sh "enum" 0 false) (sh "enum" 0 false);
              checkOnly = row (sh "e" 0 true) (sh "e" 0 false);
              descriptionCopy = row (sh "e" 0 true) (sh "e" 0 false);
              verifyCopy = row (sh "e" 0 true) (sh "e" 0 false);
              verifyOnlyCopy = row (sh "e" 0 false) (sh "e" 0 false);
              descriptionOnlyCopy = row (sh "e" 0 false) (sh "e" 0 false);
              met = row (sh "g" 1 true) (sh "g" 0 false);
              metOfMet = row (sh "g" 2 true) (sh "g" 0 false);
              # re-completed, it keeps its witnessed check (den-hoag-59gnz C1): a met record read as its join
              recompletedMet = row (sh "k" 1 true) (sh "k" 0 false);
            };
        };
      };

    # CONTROL: what the witness must not refuse. The first rows are joins that keep their operands'
    # names; the rest GAIN a role or spell one in the other vocabulary, and merge on nixpkgs too.
    test-a-non-renaming-foreign-join-is-unchanged = {
      expr = {
        c03 = ev [ (t.strMatching "a+") (t.strMatching "a+") ] "b";
        c04 = ev [ t.int t.int ] "x";
        c06 = ev [
          (t.enum [ "a" ])
          (t.enum [ "b" ])
        ] "b";
        c10 = ev [
          (t.submodule {
            options.a = nixpkgsLib.mkOption {
              type = t.str;
              default = "d";
            };
          })
          (t.submodule {
            options.b = nixpkgsLib.mkOption {
              type = t.int;
              default = 0;
            };
          })
        ] { b = 1; };
        c11 = ev [
          (gt.submodule {
            options.a = gm.mkOption {
              type = gt.str;
              default = "d";
            };
          })
          (gt.submodule {
            options.b = gm.mkOption {
              type = gt.int;
              default = 0;
            };
          })
        ] { b = 1; };
        c12 = ev [ (t.listOf t.str) (t.listOf t.str) ] [ 1 ];
        int-twin = ev [ t.int t.int ] 1;
        freeform-12 = ev [ ff opt ] {
          x = 1;
          y = "a";
        };
        freeform-21 = ev [ opt ff ] {
          x = 1;
          y = "a";
        };
        freeform-attrsOf = ev [ (t.attrsOf ff) (t.attrsOf opt) ] {
          k = {
            x = 1;
            y = "a";
          };
        };
        freeform-listOf = merged (t.listOf ff) (t.listOf opt);
        freeform-nullOr = merged (t.nullOr ff) (t.nullOr opt);
        attrTag = merged (tag "a") (tag "b");
        mixed-listOf-12 = merged (t.listOf t.str) (gt.listOf t.str);
        mixed-listOf-21 = merged (gt.listOf t.str) (t.listOf t.str);
        mixed-nullOr-12 = merged (t.nullOr t.str) (gt.nullOr t.str);
        mixed-nullOr-21 = merged (gt.nullOr t.str) (t.nullOr t.str);
        mixed-either-12 = merged (t.either t.str t.int) (gt.either t.str t.int);
        mixed-either-21 = merged (gt.either t.str t.int) (t.either t.str t.int);
        mixed-submodule-12 = merged opt gsub;
        mixed-submodule-21 = merged gsub opt;
      };
      expected = {
        c03 = ''MERGED strMatching "a+" / REJECTED'';
        c04 = "MERGED int / REJECTED";
        c06 = "MERGED enum / ACCEPTED";
        c10 = "MERGED submodule / ACCEPTED";
        c11 = "MERGED submodule / ACCEPTED";
        c12 = "MERGED listOf / REJECTED";
        int-twin = "MERGED int / ACCEPTED";
        freeform-12 = "MERGED submodule / ACCEPTED";
        freeform-21 = "MERGED submodule / ACCEPTED";
        freeform-attrsOf = "MERGED attrsOf / ACCEPTED";
        freeform-listOf = "listOf";
        freeform-nullOr = "nullOr";
        attrTag = "attrTag";
        mixed-listOf-12 = "listOf";
        mixed-listOf-21 = "listOf";
        mixed-nullOr-12 = "nullOr";
        mixed-nullOr-21 = "nullOr";
        mixed-either-12 = "either";
        mixed-either-21 = "either";
        mixed-submodule-12 = "submodule";
        # the gen operand decides through its own `typeMergeRel`, which hands the pair to the partner's
        # relation (4v489), so both orders answer nixpkgs' `submodule` and the witness is never reached

        mixed-submodule-21 = "submodule";
      };
    };
  };
}
