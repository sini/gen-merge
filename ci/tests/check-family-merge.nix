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
      res = gm.evalModuleTree {
        modules = map (ty: { options.p = gm.mkOption { type = ty; }; }) tys ++ [ { p = val; } ];
      };
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
        # the gen operand decides through its own `typeMergeRel`, so the witness is never reached

        mixed-submodule-21 = "REFUSED";
      };
    };
  };
}
