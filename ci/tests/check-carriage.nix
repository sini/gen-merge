# A check a nixpkgs wrapper states over a gen record survives gen-merge's fold and re-home
# (den-hoag-4ifgb, den-hoag-q3yjf).
#
# nixpkgs states a domain as the descriptor's `check` and refines it there: `addCheck t p` rewrites
# `check`, and `nonEmptyListOf` is `addCheck (listOf t) (l: l != [ ])`. gen reads its own datum
# (`verify` | `admits`), so a rewritten `check` over a gen record (member A) and a stock container
# re-homed as gen's own (member B) were folded without it: a value the declared type forbids, served
# silently. Each refusal below is paired with its passing twin (a carry that refused everything
# would pass the first alone), and the residue the landing leaves is pinned as a value, so a change
# to it is seen rather than read as a fix.
#
# The cells whose subject is a refusal's MESSAGE live on `testsError` (`../tests-error.nix`, group
# `check-carriage`).
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  np = nixpkgsLib.types;
  ac = np.addCheck;
  no = _: false;
  small = x: x < 3;
  inherit (builtins) deepSeq tryEval;

  opt =
    T: V:
    (gm.evalModuleTree { } [
      { options.s = gm.mkOption { type = T; }; }
      { s = V; }
    ]).config.s;
  served = T: V: tryEval (deepSeq (opt T V) (opt T V));
  accepted = T: V: (served T V).success;

  treeMods = [
    {
      options.a = gm.mkOption {
        type = gt.int;
        default = 0;
      };
    }
  ];
  tree = (gm.evalModuleTree { } treeMods).type;
  sub = gt.submodule { imports = treeMods; };
  eitherTree = gt.either tree gt.str;
  m = {
    a = 5;
  };
in
{
  flake.tests.check-carriage = {
    # MEMBER A: the rewritten check is carried at every route gen folds a gen record by — the
    # option's own fold, the leaf, the threaded fold of a nesting union, an element, a union member
    # and the `mkOptionType` door.
    test-a-rewritten-check-over-a-gen-record-is-carried = {
      expr = {
        leaf = accepted (ac gt.int small) 5;
        adHoc = accepted (gt.int // { check = no; }) 5;
        door = accepted (gt.mkOptionType (ac gt.int small)) 5;
        container = accepted (ac (gt.listOf gt.int) no) [ 5 ];
        threaded = accepted (ac (gt.either sub gt.str) no) m;
        submodule = accepted (ac sub no) m;
        element = accepted (gt.listOf (ac gt.int small)) [ 5 ];
      };
      expected = {
        leaf = false;
        adHoc = false;
        door = false;
        container = false;
        threaded = false;
        submodule = false;
        element = false;
      };
    };
    test-a-passing-rewritten-check-keeps-the-value = {
      expr = {
        leaf = opt (ac gt.int small) 2;
        door = opt (gt.mkOptionType (ac gt.int small)) 2;
        threaded = opt (ac (gt.either sub gt.str) (_: true)) m;
        element = opt (gt.listOf (ac gt.int small)) [ 2 ];
      };
      expected = {
        leaf = 2;
        door = 2;
        threaded = m;
        element = [ 2 ];
      };
    };
    # A union's member choice asks the member's rewritten check too, as nixpkgs' union reads its
    # members' `check`: `5` is outside the first member and inside the second, which folds it.
    test-a-union-member-refined-away-is-not-chosen = {
      expr = opt (gt.either (ac gt.int small) gt.int) 5;
      expected = 5;
    };
    # The gen base still refuses what the wrapper widened: gen reads `// { check }` as a refinement.
    test-the-gen-domain-still-refuses-under-a-rewritten-check = {
      expr = accepted (ac gt.int (_: true)) "x";
      expected = false;
    };
    # The published `check` is a callable record, and the witness is that record, so a record that
    # keeps it (re-bound by selection, rebuilt by `inherit`, passed through `mapAttrs`) is its own on
    # every evaluator. Over `either tree str` a rewritten check is refused by name, so a value here
    # is the reading "own".
    test-a-record-keeping-its-check-record-is-its-own = {
      expr = {
        kind = nixpkgsLib.isFunction eitherTree.check;
        builtinKind = builtins.isFunction eitherTree.check;
        rebound = opt (eitherTree // { inherit (eitherTree) check; }) "s";
        inheritRebuilt = opt (eitherTree // { inherit (eitherTree) check _checkWitness; }) "s";
        mapAttrsIdentity = opt (builtins.mapAttrs (_: v: v) eitherTree) "s";
      };
      expected = {
        kind = true;
        builtinKind = false;
        rebound = "s";
        inheritRebuilt = "s";
        mapAttrsIdentity = "s";
      };
    };

    # MEMBER B: a stock container re-homed over a nesting element carries its own check.
    test-a-re-homed-stock-container-carries-its-check = {
      expr = {
        nonEmptySub = accepted (np.nonEmptyListOf sub) [ ];
        nonEmptyTree = accepted (np.nonEmptyListOf tree) [ ];
        listOfSub = accepted (ac (np.listOf sub) no) [ m ];
        listOfTree = accepted (ac (np.listOf tree) no) [ m ];
        attrsOfTree = accepted (ac (np.attrsOf tree) no) { k = m; };
        eitherSub = accepted (ac (np.either sub np.str) no) m;
        nullOrSub = accepted (ac (np.nullOr sub) no) m;
      };
      expected = {
        nonEmptySub = false;
        nonEmptyTree = false;
        listOfSub = false;
        listOfTree = false;
        attrsOfTree = false;
        eitherSub = false;
        nullOrSub = false;
      };
    };
    test-a-re-homed-stock-container-keeps-a-passing-value = {
      expr = {
        nonEmptySub = opt (np.nonEmptyListOf sub) [ m ];
        nonEmptyTree = opt (np.nonEmptyListOf tree) [ m ];
        eitherSub = opt (ac (np.either sub np.str) (_: true)) m;
      };
      expected = {
        nonEmptySub = [ m ];
        nonEmptyTree = [ m ];
        eitherSub = m;
      };
    };

    # A `//` COPY'S `verify` IS ENFORCED INSIDE A NIXPKGS CONTAINER (den-hoag-dyww5). The copy publishes its
    # base's `check`, and a foreign container's fold reads an element's `check` alone, so declared alone
    # under any nixpkgs container the value its `verify` rejects was served, while bare and under a gen
    # container it is refused. Each wrapper's row reads the rejected value and its passing twin, `submodule`
    # and `attrTag` included, whose interiors are nixpkgs' own option evaluation, read at the nested option
    # (den-hoag-dk6zg, the cells below). The residue is pinned as a value: `coercedTo` over a container
    # holding the copy, and a record outside the stock vocabulary whose `nestedTypes` hold it (`box`), are
    # refused whole; on
    # `coercedTo`'s coercion side under a container the copy is read as its head, as both engines read a
    # check copy there. `weak` reads a copy whose `verify` admits what its base's `check` rejects: served
    # where the container's fold reads the copy alone, as gen serves it bare, and refused under `nullOr`,
    # `either` and `uniq`, whose own `check` is its base's; `weakUnstamped` reads it with no completion
    # stamp, re-homed and rebuilt alike, so every arm gives it one domain. `untouched` reads a value no
    # declared check touches, beside a copy on the coercion side: served.
    test-a-verify-copy-inside-a-foreign-container-is-enforced =
      let
        E = gt.enum "e" [
          "a"
          "b"
        ];
        C = E // {
          verify = v: if v == "a" then "rejected by the copy" else E.verify v;
        };
        W = gt.int // {
          verify = _: null;
        };
        # the same copy with no completion stamp, so the published door does not carry it
        H = builtins.removeAttrs W [ "__typeSelf" ];
        box =
          inner:
          nixpkgsLib.mkOptionType {
            name = "box";
            check = builtins.isAttrs;
            merge = loc: defs: {
              v =
                (nixpkgsLib.modules.mergeDefinitions loc inner (
                  map (d: {
                    inherit (d) file;
                    value = d.value.v;
                  }) defs
                )).mergedValue;
            };
            nestedTypes.inner = inner;
          };
        wraps = {
          listOf = {
            w = np.listOf;
            v = x: [ x ];
          };
          nonEmptyListOf = {
            w = np.nonEmptyListOf;
            v = x: [ x ];
          };
          attrsOf = {
            w = np.attrsOf;
            v = x: { k = x; };
          };
          lazyAttrsOf = {
            w = np.lazyAttrsOf;
            v = x: { k = x; };
          };
          attrsWithPlaceholder = {
            w =
              e:
              np.attrsWith {
                elemType = e;
                lazy = false;
                placeholder = "p";
              };
            v = x: { k = x; };
          };
          nullOr = {
            w = np.nullOr;
            v = x: x;
          };
          either = {
            w = e: np.either e np.bool;
            v = x: x;
          };
          oneOf = {
            w =
              e:
              np.oneOf [
                e
                np.bool
              ];
            v = x: x;
          };
          coercedTo = {
            w = np.coercedTo np.bool (_: "b");
            v = x: x;
          };
          uniq = {
            w = np.uniq;
            v = x: x;
          };
          functionTo = {
            w = np.functionTo;
            v = x: _: x;
            call = true;
          };
          listOfAttrsOf = {
            w = e: np.listOf (np.attrsOf e);
            v = x: [ { k = x; } ];
          };
          genListOfListOf = {
            w = e: gt.listOf (np.listOf e);
            v = x: [ [ x ] ];
          };
          submodule = {
            w = e: np.submodule { options.y = nixpkgsLib.mkOption { type = e; }; };
            v = x: { y = x; };
          };
          coercedToListOf = {
            w = e: np.coercedTo np.bool (_: [ "b" ]) (np.listOf e);
            v = x: [ x ];
          };
          attrTag = {
            w = e: np.attrTag { y = nixpkgsLib.mkOption { type = e; }; };
            v = x: { y = x; };
          };
          partialAttrsOf = {
            w = e: gm.partialAttrsOf (np.listOf e);
            v = x: { k = [ x ]; };
          };
          box = {
            w = box;
            v = x: { v = x; };
          };
          coercedFromCopy = {
            w = e: np.coercedTo e (x: "coerced-${x}") np.str;
            v = x: x;
          };
          coercedFromListOf = {
            w = e: np.coercedTo (np.listOf e) (_: "coerced") np.str;
            v = x: [ x ];
          };
        };
        # a function's body is folded when it is called
        at =
          c: w: x:
          let
            o = opt (w.w c) (w.v x);
            r = if w ? call then o null else o;
          in
          (tryEval (deepSeq r r)).success;
      in
      {
        expr = {
          copy = builtins.mapAttrs (_: w: {
            a = at C w "a";
            b = at C w "b";
          }) wraps;
          weak = builtins.mapAttrs (_: w: at W w "s") {
            inherit (wraps)
              listOf
              attrsOf
              attrsWithPlaceholder
              functionTo
              nullOr
              either
              uniq
              ;
          };
          weakUnstamped = {
            listOf = at H wraps.listOf "s";
            attrsWithPlaceholder = at H wraps.attrsWithPlaceholder "s";
          };
          untouched = {
            coercedFromCopy = at C wraps.coercedFromCopy "x";
            coercedFromListOf = at C (wraps.coercedFromListOf // { v = x: x; }) "x";
          };
        };
        expected = {
          copy =
            builtins.mapAttrs (_: _: {
              a = false;
              b = true;
            }) wraps
            // {
              coercedToListOf = {
                a = false;
                b = false;
              };
              box = {
                a = false;
                b = false;
              };
              coercedFromListOf = {
                a = true;
                b = true;
              };
            };
          weak = {
            listOf = true;
            attrsOf = true;
            attrsWithPlaceholder = true;
            functionTo = true;
            nullOr = false;
            either = false;
            uniq = false;
          };
          weakUnstamped = {
            listOf = true;
            attrsWithPlaceholder = true;
          };
          untouched = {
            coercedFromCopy = true;
            coercedFromListOf = true;
          };
        };
      };

    # A `//` COPY'S `verify` IS ENFORCED INSIDE A NIXPKGS SUBMODULE, AT THE OPTION'S OWN READ (den-hoag-dk6zg).
    # nixpkgs' option evaluation reads an option's `check` alone, so a copy declared inside a stock
    # `submodule` (or as an `attrTag` tag) was served at the value its `verify` rejects. Each reach is read at
    # the rejected value and its passing twin; `lazy` reads `y` beside a sibling whose type is an error, which
    # nixpkgs never forces while only `y` is read, so the guard judges an option only where it is read.
    # `freeform` pins OPEN DEFECT D4 on den-hoag-dk6zg as a value: a copy below a freeform type is still served.
    test-a-verify-copy-inside-a-nixpkgs-submodule-is-enforced-at-its-read =
      let
        C = gt.int // {
          verify = v: if v == 7 then "rejected by the copy" else gt.int.verify v;
        };
        sub = t: np.submodule { options.y = nixpkgsLib.mkOption { type = t; }; };
        tag = t: np.attrTag { y = nixpkgsLib.mkOption { type = t; }; };
        reach = {
          submodule = {
            w = sub;
            v = x: { y = x; };
          };
          twoDeep = {
            w = t: sub (sub t);
            v = x: { y.y = x; };
          };
          attrsOfSubmodule = {
            w = t: np.attrsOf (sub t);
            v = x: { k.y = x; };
          };
          listOfSubmodule = {
            w = t: np.listOf (sub t);
            v = x: [ { y = x; } ];
          };
          genAttrsOfSubmodule = {
            w = t: gt.attrsOf (sub t);
            v = x: { k.y = x; };
          };
          attrTag = {
            w = tag;
            v = x: { y = x; };
          };
          submoduleInAttrTag = {
            w = t: tag (sub t);
            v = x: { y.y = x; };
          };
          listOfInSubmodule = {
            w = t: sub (np.listOf t);
            v = x: { y = [ x ]; };
          };
          apply = {
            w =
              t:
              np.submodule {
                options.y = nixpkgsLib.mkOption {
                  type = t;
                  apply = x: x + 100;
                };
              };
            v = x: { y = x; };
          };
        };
        lazy = np.submodule {
          options.y = nixpkgsLib.mkOption { type = C; };
          options.z = nixpkgsLib.mkOption { type = throw "the unread sibling's type"; };
        };
      in
      {
        expr = {
          reach = builtins.mapAttrs (_: w: {
            rejected = accepted (w.w C) (w.v 7);
            twin = accepted (w.w C) (w.v 1);
          }) reach;
          lazy = (opt lazy { y = 1; }).y;
          freeform = (opt (np.submodule { freeformType = np.attrsOf C; }) { k = 7; }).k;
        };
        expected = {
          reach = builtins.mapAttrs (_: _: {
            rejected = false;
            twin = true;
          }) reach;
          lazy = 1;
          freeform = 7;
        };
      };

    # THE GUARD READS ONLY WHAT NIXPKGS' OWN READ FORCES, AND JUDGES THE VALUE BEFORE `apply` (den-hoag-dk6zg v1).
    # `served` rows are working cells: an `apply` above a nested submodule or container that restructures or drops
    # the value, and a type member nixpkgs never forces (an `either`'s unchosen right member, `coercedTo`'s coerced
    # `either`), each at nixpkgs' value. `refused` rows are reaches through `either`, `oneOf`, `coercedTo` and
    # `attrListOf`, at the root and nested, and below a `coercedTo`'s final member, where the copy's rejected value
    # was served. `open` pins the silent residue this landing leaves as OPEN DEFECTS on den-hoag-dk6zg (a value, so
    # a change to it is seen): a copy read through a sibling's cross-read inside the evaluation (D1), below a record
    # outside nixpkgs' vocabulary (D3), and below a freeform type (D4).
    test-a-verify-copy-inside-a-nixpkgs-submodule-is-read-where-nixpkgs-reads =
      let
        C = gt.int // {
          verify = v: if v == 7 then "rejected by the copy" else gt.int.verify v;
        };
        never = throw "never forced";
        sub = t: np.submodule { options.y = nixpkgsLib.mkOption { type = t; }; };
        mid =
          t: apply:
          np.submodule {
            options.m = nixpkgsLib.mkOption {
              inherit apply;
              type = t;
            };
          };
        got = T: V: (served T V).value;
      in
      {
        expr = {
          served = {
            applyMiddle = got (mid (sub (np.listOf C)) (c: c // { y = [ 0 ]; })) { m.y = [ 1 ]; };
            applyReverse = got (mid (np.listOf (sub (np.listOf C))) builtins.tail) {
              m = [
                { y = [ 1 ]; }
                { y = [ 2 ]; }
              ];
            };
            applyDropsRejected = got (mid (sub C) (_: {
              y = 0;
            })) { m.y = 7; };
            eitherRightUnforced = got (sub (np.either np.int never)) { y = 1; };
            # nixpkgs modules.sh `freeform-deprecated-malicous`: an `either` freeform with no `attrsOf`, warned and served
            freeformEither =
              (got (np.submodule { freeformType = np.either np.int np.int; }) { int = "foo"; }).int;
            coercedEitherUnforced =
              got (sub (np.coercedTo (np.either np.str never) (_: { y = 2; }) (sub np.int)))
                {
                  y = "s";
                };
          };
          # a function's body is folded when it is called
          calledFunctionTo =
            (tryEval (deepSeq ((opt (sub (np.functionTo (sub C))) { y = _: { y = 7; }; }).y null) null))
            .success;
          refused = builtins.mapAttrs (_: w: accepted w.t w.v) {
            either = {
              t = np.either (sub C) np.str;
              v = {
                y = 7;
              };
            };
            oneOf = {
              t = np.oneOf [
                np.str
                (sub C)
              ];
              v = {
                y = 7;
              };
            };
            coercedTo = {
              t = np.coercedTo np.str (_: { y = 7; }) (sub C);
              v = "s";
            };
            attrListOf = {
              t = np.attrListOf (sub C);
              v = {
                a.y = 7;
              };
            };
            nestedAttrListOfCopy = {
              t = sub (np.attrListOf C);
              v = {
                y.a = 7;
              };
            };
            nestedEitherCopy = {
              t = sub (np.either np.str C);
              v = {
                y = 7;
              };
            };
            nestedApplyIdentity = {
              t = mid (np.either (sub C) np.str) (c: c);
              v = {
                m.y = 7;
              };
            };
            # the copy below `coercedTo`'s final member, defined as it is and coerced to it
            coercedFinalListOf = {
              t = sub (np.coercedTo np.str (_: [ 7 ]) (np.listOf C));
              v.y = [ 7 ];
            };
            coercedFinalListOfCoerced = {
              t = sub (np.coercedTo np.str (_: [ 7 ]) (np.listOf C));
              v.y = "s";
            };
            coercedFinalAttrsOf = {
              t = sub (np.coercedTo np.str (_: { k = 7; }) (np.attrsOf C));
              v.y = "s";
            };
            coercedFinalEither = {
              t = sub (np.coercedTo np.str (_: 7) (np.either np.bool C));
              v.y = "s";
            };
            # the copy below an `either` below the member `oneOf` chose
            oneOfListOfEither = {
              t = sub (
                np.oneOf [
                  np.str
                  (np.listOf (np.either np.bool C))
                ]
              );
              v.y = [ 7 ];
            };
          };
          open = {
            # only `z` is read: `y` itself is refused
            crossRead =
              (opt (np.submodule (
                { config, ... }:
                {
                  options.y = nixpkgsLib.mkOption { type = C; };
                  options.z = nixpkgsLib.mkOption { type = np.int; };
                  config.z = config.y;
                }
              )) { y = 7; }).z;
            nonStock = got (sub (
              nixpkgsLib.mkOptionType {
                name = "box";
                check = builtins.isAttrs;
                merge = loc: defs: { v = (builtins.head defs).value.v; };
                nestedTypes.inner = C;
              }
            )) { y.v = 7; };
            freeform = (got (np.submodule { freeformType = np.attrsOf (np.either np.str C); }) { k = 7; }).k;
          };
        };
        expected = {
          served = {
            applyMiddle.m.y = [ 0 ];
            applyReverse.m = [ { y = [ 2 ]; } ];
            applyDropsRejected.m.y = 0;
            eitherRightUnforced.y = 1;
            coercedEitherUnforced.y.y = 2;
            freeformEither = "foo";
          };
          calledFunctionTo = false;
          refused = builtins.mapAttrs (_: _: false) {
            either = null;
            oneOf = null;
            coercedTo = null;
            attrListOf = null;
            nestedAttrListOfCopy = null;
            nestedEitherCopy = null;
            nestedApplyIdentity = null;
            coercedFinalListOf = null;
            coercedFinalListOfCoerced = null;
            coercedFinalAttrsOf = null;
            coercedFinalEither = null;
            oneOfListOfEither = null;
          };
          open = {
            crossRead = 7;
            nonStock.y.v = 7;
            freeform = 7;
          };
        };
      };
    # THE RESIDUE (README "The prices, stated"): a check over the bare tree, served, as pinned here.
    # A stock `either`/`oneOf`/`nullOr` over the bare tree is NOT in it: the tree's `check` is its
    # module-value domain, so the rewritten check over the union is carried (member B) and refuses,
    # as nixpkgs does for `either`/`oneOf` and stricter than nixpkgs for `nullOr`. Nor is the same
    # check stated against the bare tree a container offers: the tree is a type built at the
    # crossing site, so the stated element and the offered one are two records, and that is refused
    # by name, as it is over `submodule` (stricter than nixpkgs, which ignores the stated check).
    test-the-residue-is-the-bare-tree = {
      expr = {
        bareTree = opt (ac tree no) m;
        eitherTree = accepted (ac (np.either tree np.str) no) m;
        oneOfTree = accepted (ac (np.oneOf [
          tree
          np.str
        ]) no) m;
        nullOrTree = accepted (ac (np.nullOr tree) no) m;
        # A tree stated with only its `check` rewritten against the tree offered.
        statedCheckOverOfferedTree = accepted (np.listOf tree // { nestedTypes.elemType = ac tree no; }) [
          m
        ];
      };
      expected = {
        bareTree = m;
        eitherTree = false;
        oneOfTree = false;
        nullOrTree = false;
        statedCheckOverOfferedTree = false;
      };
    };
  };
}
