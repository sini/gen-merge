# A foreign record crossing a door comes back closed under the rebuilds a fold calls on it, with its check and its
# `verify` stated where that fold asks membership (den-hoag-dw8d3, den-hoag-kw5bx, den-hoag-f66c6). nixpkgs' union
# chooses a v2 member by its merge's `headError` and a non-v2 member by `check` per definition, so a `verify` stated
# only in the merged value commits the union to the member and then refuses: these cells hold the union's choice. A
# stock host redeclaring the copy rebuilds it through `typeMerge`, and its freeform plane through `substSubModules`:
# these cells hold the check across both. Each cell is red with its site reverted (`interface.rebuildClosed` and its
# members, `carryBy`, `carriedAtDepth`, `carriedCopy`, `eitherChosen`, the gen containers' element rebuild).
{
  genMerge,
  interface,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins)
    all
    attrValues
    isAttrs
    isInt
    length
    stringLength
    ;
  # "np": nixpkgs' `evalModules` over the gen-published records; "gen": gen-merge's `evalModuleTree`
  run =
    en: ts: dv:
    let
      mods =
        map (t: { options.x = (if en == "gen" then gm.mkOption else nl.mkOption) { type = t; }; }) ts
        ++ map (v: { x = v; }) dv;
      c =
        if en == "gen" then
          (gm.evalModuleTree { } mods).config
        else
          (nl.evalModules { modules = mods; }).config;
      o = builtins.tryEval (builtins.deepSeq c.x c.x);
    in
    if o.success then o.value else "REFUSED";
  host = t: np.submodule { options.y = nl.mkOption { type = t; }; };
  pA = v: !(isAttrs v) || all (x: !(isInt x) || x < 10) (attrValues v);
  vA = v: if pA v then null else "rejected";
  pL = v: length v < 2;
  pI = v: v < 10;
  Y = np.attrsOf np.int;
  X = gt.defineType (np.attrsOf np.int // { verify = vA; });
  Xn = gt.defineType (np.attrs // { verify = vA; });

  # the freeform plane of a stock host, `gt.lazyAttrsOf F` declared in two modules (dw8d3, kw5bx)
  rejects = v: isAttrs v && (v.a or 0) == 1 && (v.b or null) == null;
  vf = v: if rejects v then "a is 1 and b is unset" else null;
  npSub = np.submodule {
    options.a = nl.mkOption { type = np.int; };
    options.b = nl.mkOption { type = np.nullOr np.int; };
    config.a = nl.mkOptionDefault 7;
    config.b = nl.mkOptionDefault null;
  };
  gSub = gt.submodule {
    options.a = gm.mkOption { type = gt.int; };
    options.b = gm.mkOption { type = gt.nullOr gt.int; };
    config.a = gm.mkOptionDefault 7;
    config.b = gm.mkOptionDefault null;
  };
  freeform =
    ts: d:
    let
      o = builtins.tryEval (
        let
          v =
            (gm.evalModuleTree { } [
              {
                options.h = gm.mkOption {
                  type = np.submodule { imports = map (t: { freeformType = gt.lazyAttrsOf t; }) ts; };
                };
              }
              { h.x = d; }
            ]).config.h.x;
        in
        builtins.deepSeq v v
      );
    in
    if o.success then o.value else "REFUSED";

  # a member-reading predicate over a nixpkgs submodule, for the value a coercion folds
  npSubAB = np.submodule {
    options.a = nl.mkOption {
      type = np.int;
      default = 0;
    };
    options.b = nl.mkOption {
      type = np.int;
      default = 0;
    };
  };
  notTwo = v: if isAttrs v && isInt (v.a or null) && v.a == 2 then "rejected" else null;
  coerced = np.coercedTo np.str (s: { a = stringLength s; }) (
    gt.defineType (npSubAB // { verify = notTwo; })
  );
  # an ad-hoc check override of a v2 type that is not a module set, through the door
  # a v2 type's `merge.v2` over one definition
  at = v: {
    loc = [ "x" ];
    defs = [
      {
        file = "def.nix";
        value = v;
      }
    ];
  };
  headErrorOf = t: v: (t.merge.v2 (at v)).headError;
  notA2 = v: !(isAttrs v) || (v.a or 0) != 2;
  shortList = gt.defineType (
    np.listOf np.int
    // {
      check = v: (np.listOf np.int).check v && pL v;
    }
  );
in
{
  flake.tests.verify-carriage = {
    # S1: a foreign `addCheck` and a foreign `verify` copy through the door, redeclared in a stock host after its
    # plain base: nixpkgs' redeclaration calls the copy's `typeMerge`, which comes back with the check carried.
    test-an-addcheck-copy-redeclared-in-a-stock-host-refuses-what-its-check-rejects = {
      expr = {
        bad =
          run "np"
            [
              (host (np.listOf np.int))
              (host (gt.defineType (np.addCheck (np.listOf np.int) pL)))
            ]
            [
              {
                y = [
                  1
                  2
                ];
              }
            ];
        ok =
          run "np"
            [
              (host (np.listOf np.int))
              (host (gt.defineType (np.addCheck (np.listOf np.int) pL)))
            ]
            [ { y = [ 1 ]; } ];
      };
      expected = {
        bad = "REFUSED";
        ok.y = [ 1 ];
      };
    };
    test-a-verify-copy-redeclared-in-a-stock-host-refuses-what-its-verify-rejects = {
      expr =
        let
          V = gt.defineType (np.int // { verify = v: if pI v then null else "rejected"; });
        in
        {
          bad = run "np" [ (host np.int) (host V) ] [ { y = 20; } ];
          ok = run "np" [ (host np.int) (host V) ] [ { y = 2; } ];
        };
      expected = {
        bad = "REFUSED";
        ok.y = 2;
      };
    };
    # F1: the carried `verify` is stated in the v2 `headError`, so a nixpkgs union whose other member admits the
    # definitions moves on to it, as it does past nixpkgs' own `addCheck`; a value both members reject is refused.
    test-a-union-moves-past-a-v2-copy-whose-verify-rejects-to-the-member-that-admits = {
      expr = {
        either = run "np" [ (np.either X Y) ] [ { a = 20; } ];
        planted = run "np" [ (np.either X Y) ] [ { a = "s"; } ];
        oneOfTL =
          run "np"
            [
              (np.oneOf [
                Y
                Y
              ])
              (np.oneOf [
                X
                Y
              ])
            ]
            [ { a = 20; } ];
        alone = run "np" [ X ] [ { a = 20; } ];
      };
      expected = {
        either.a = 20;
        planted = "REFUSED";
        oneOfTL.a = 20;
        alone = "REFUSED";
      };
    };
    # gen's stock-host guard (`eitherChosen`) asks a v2 member by its `headError` as nixpkgs' `either` does
    test-gen-reads-a-stock-host-union-member-by-its-head-error = {
      expr = run "gen" [ (host (np.either Y Y)) (host (np.either X Y)) ] [ { y.a = 20; } ];
      expected.y.a = 20;
    };
    # a non-v2 copy is lifted into the v2 protocol: its check is the `headError` on every definition, its `verify`
    # the `headError` on the merged value
    test-a-union-moves-past-a-lifted-non-v2-copy-whose-verify-rejects = {
      expr = {
        bad = run "np" [ (np.either Xn Y) ] [ { a = 20; } ];
        ok = run "np" [ (np.either Xn Y) ] [ { a = 2; } ];
        aloneTL = run "np" [ np.attrs Xn ] [ { a = 20; } ];
      };
      expected = {
        bad.a = 20;
        ok.a = 2;
        aloneTL = "REFUSED";
      };
    };
    # F2: a constant constructor's own record crosses the door as itself; a wrapper over it is carried
    test-a-constant-constructor-crosses-the-door-as-itself = {
      expr = {
        int = gt.defineType np.int == np.int;
        addCheck =
          let
            a = np.addCheck np.int pI;
          in
          gt.defineType a == a;
      };
      expected = {
        int = true;
        addCheck = false;
      };
    };
    # G1: the freeform plane of a stock host declared in two modules. A foreign `addCheck` (`carryBy` under the
    # record's own `substSubModules`), a nixpkgs submodule copied with a `verify` declared after its base
    # (`carriedAtDepth`), and a gen submodule copied with a `verify` (a gen container's element rebuild).
    test-a-stock-host-freeform-plane-declared-twice-keeps-each-element-check = {
      expr = {
        addLL = freeform [
          (np.addCheck npSub (v: !(rejects v)))
          (np.addCheck npSub (v: !(rejects v)))
        ] { a = 1; };
        vSLT = freeform [
          (npSub // { verify = vf; })
          npSub
        ] { a = 1; };
        vGLL = freeform [
          (gSub // { verify = vf; })
          (gSub // { verify = vf; })
        ] { a = 1; };
        vGLLok = freeform [
          (gSub // { verify = vf; })
          (gSub // { verify = vf; })
        ] { a = 2; };
      };
      expected = {
        addLL = "REFUSED";
        vSLT = "REFUSED";
        vGLL = "REFUSED";
        vGLLok = {
          a = 2;
          b = null;
        };
      };
    };
    # S3: a nixpkgs container over a gen submodule copied with a `verify`, through `mkOptionType`, redeclared after its
    # plain twin under nixpkgs' `evalModules`: the owed `verify` rides on the rebuilt element (`carriedAtDepth`), read
    # on the element's merged value.
    test-a-nixpkgs-container-over-a-verify-copy-redeclared-keeps-the-verify-on-its-element =
      let
        # no `default`: the two declarations' module sets merge, and two copies of one option both
        # stating `default` are refused (nixpkgs' `bothHave`), so each value defines both options
        gSubAB = gt.submodule {
          options.a = gm.mkOption { type = gt.int; };
          options.b = gm.mkOption { type = gt.int; };
        };
        copy = gm.mkOptionType (np.attrsOf (gSubAB // { verify = notTwo; }));
      in
      {
        expr = {
          bad =
            run "np"
              [ (np.attrsOf gSubAB) copy ]
              [
                {
                  k.a = 2;
                  k.b = 0;
                }
              ];
          ok =
            run "np"
              [ (np.attrsOf gSubAB) copy ]
              [
                {
                  k.a = 1;
                  k.b = 0;
                }
              ];
        };
        expected = {
          bad = "REFUSED";
          ok.k = {
            a = 1;
            b = 0;
          };
        };
      };
    # S5: a reader that takes a v2 value past its `headError` (gen's called form of a coercion) still meets the
    # carried `verify`: the value refuses by name on a rejection.
    test-a-coercion-onto-a-verify-copy-refuses-the-folded-value-its-verify-rejects = {
      expr = {
        bad = run "gen" [ coerced ] [ { a = 2; } ];
        ok = run "gen" [ coerced ] [ { a = 1; } ];
      };
      expected = {
        bad = "REFUSED";
        ok = {
          a = 1;
          b = 0;
        };
      };
    };
    # S1 (iii): an ad-hoc `// { check }` override crossing the door is carried as a check where nixpkgs rebuilds
    # it: the value it admits is nixpkgs' own, and the value it rejects is refused, in both engines.
    test-an-ad-hoc-check-override-through-the-door-is-carried-at-a-redeclaration = {
      expr = {
        npBad =
          run "np"
            [ (host (np.listOf np.int)) (host shortList) ]
            [
              {
                y = [
                  1
                  2
                ];
              }
            ];
        npOk = run "np" [ (host (np.listOf np.int)) (host shortList) ] [ { y = [ 1 ]; } ];
        genBad =
          run "gen"
            [ (host (np.listOf np.int)) (host shortList) ]
            [
              {
                y = [
                  1
                  2
                ];
              }
            ];
        genOk = run "gen" [ (host (np.listOf np.int)) (host shortList) ] [ { y = [ 1 ]; } ];
        npOkLL = run "np" [ (host shortList) (host shortList) ] [ { y = [ 1 ]; } ];
      };
      expected = {
        npBad = "REFUSED";
        npOk.y = [ 1 ];
        genBad = "REFUSED";
        genOk.y = [ 1 ];
        npOkLL.y = [ 1 ];
      };
    };
    # D: the check `mkOptionType` carries over a re-homed nixpkgs container is stated in its `merge.v2`'s `headError`,
    # the only part of it nixpkgs' fold reads, beside the definition the check admits (den-hoag-qb4hj)
    test-a-check-carried-over-a-rehomed-container-is-stated-in-its-head-error =
      let
        either = gm.mkOptionType (np.addCheck (np.either gSub np.str) notA2);
        nullOr = gm.mkOptionType (np.addCheck (np.nullOr gSub) notA2);
      in
      {
        expr = {
          eitherBad = headErrorOf either { a = 2; } != null;
          eitherOk = headErrorOf either { a = 1; };
          nullOrBad = headErrorOf nullOr { a = 2; } != null;
          nullOrOk = headErrorOf nullOr { a = 1; };
          npBad = run "np" [ either ] [ { a = 2; } ];
          npOk = run "np" [ either ] [ { a = 1; } ];
        };
        expected = {
          eitherBad = true;
          eitherOk = null;
          nullOrBad = true;
          nullOrOk = null;
          npBad = "REFUSED";
          npOk = {
            a = 1;
            b = null;
          };
        };
      };
    # `lifted` over a v2 merge states the base's `headError` first and its check only where the base states none, as
    # nixpkgs' `addCheck` does: on a definition both reject the base's own is stated, equal to it
    test-a-lifted-v2-merge-states-the-base-head-error-before-its-check =
      let
        m = (gt.nullOr gt.int).merge;
        c0 = v: v == null || (isInt v && v < 10);
        l = interface.rebuildClosed.verifiedMerge.lifted c0 m;
      in
      {
        expr = {
          bothBase = headErrorOf { merge = m; } "s" != null;
          bothLifted = headErrorOf { merge = l; } "s" == headErrorOf { merge = m; } "s";
          checkBase = headErrorOf { merge = m; } 20;
          checkLifted = headErrorOf { merge = l; } 20 != null;
          admitted = l.v2 (at 5);
        };
        expected = {
          bothBase = true;
          bothLifted = true;
          checkBase = null;
          checkLifted = true;
          admitted = m.v2 (at 5);
        };
      };
  };
}
