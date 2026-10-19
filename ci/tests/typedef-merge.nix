# A `typedef` STATING ITS OWN FOLD (den-hoag-6orb8 U3, the spec's U3 cells). gen-types carries
# `typedef { merge = m; } "tally" isInt`'s `merge` uninterpreted; the import boundary reads it as the
# leaf's fold (`interface.statesFold`), as nixpkgs' `mergeDefinitions` folds a `mkOptionType`: each
# definition passes the type before the fold, `merge loc` must be a function, and the result passes
# the type again. A nixpkgs mount reads the exported record's `merge`. Names are invented (ADR-0035).
{
  genMerge,
  genTypesFlake,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  T = gm.types;
  nl = nixpkgsLib;
  algebra = genTypesFlake.inputs.gen-algebra.lib;
  identity = genTypesFlake.inputs.gen-identity.lib;
  tr =
    e:
    let
      r = builtins.tryEval (builtins.deepSeq e e);
    in
    if r.success then r.value else "REFUSED";
  ev =
    tys: vals:
    tr
      (gm.evalModuleTree { } (
        map (ty: { options.o = gm.mkOption { type = ty; }; }) tys ++ map (v: { config.o = v; }) vals
      )).config.o;
  mounted =
    tys: vals:
    tr
      (nl.evalModules {
        modules =
          map (ty: { options.o = nl.mkOption { type = ty; }; }) tys ++ map (v: { config.o = v; }) vals;
      }).config.o;
  isInt = v: builtins.isInt v;
  sum = _loc: defs: builtins.foldl' (a: d: a + d.value) 0 defs;
  sum' = _loc: defs: builtins.foldl' (a: d: a + d.value) 0 defs;
  tallies = {
    revision = "r1";
    members.sum =
      _a: _loc: defs:
      builtins.foldl' (a: d: a + d.value) 0 defs;
  };
  sumOf = algebra.mkIntensional identity.hashIdentity tallies "sum";
  tally = T.typedef { merge = sum; } "tally" isInt;
in
{
  flake.tests.typedef-merge = {
    test-u3-m1-the-stated-merge-folds = {
      expr = ev [ tally ] [ 2 3 ];
      expected = 5;
    };
    test-u3-m2-mounted-in-nixpkgs-the-exported-merge-folds = {
      expr = mounted [ tally ] [ 2 3 ];
      expected = 5;
    };
    # the positional form is refused by name where it is applied (message: ../tests-error.nix)
    test-u3-m3-the-positional-form-is-refused = {
      expr = ev [ (T.typedef "tally" isInt) ] [ 2 3 ];
      expected = "REFUSED";
    };
    # the fold's result passes the type again, in both engines; the planted arm (the post-fold verify
    # removed) admits it, the control a fold staying inside the type
    test-u3-m4-a-result-outside-the-type-is-refused = {
      expr = {
        gen = ev [ (T.typedef { merge = _: _: "x"; } "tally" isInt) ] [ 2 3 ];
        mounted = mounted [ (T.typedef { merge = _: _: "x"; } "tally" isInt) ] [ 2 3 ];
        control = ev [ (T.typedef { merge = _: _: 4; } "tally" isInt) ] [ 2 3 ];
      };
      expected = {
        gen = "REFUSED";
        mounted = "REFUSED";
        control = 4;
      };
    };
    test-u3-m5-an-unknown-option-is-refused = {
      expr = ev [ (T.typedef { mrege = sum; } "tally" isInt) ] [ 2 3 ];
      expected = "REFUSED";
    };
    # two typedefs sharing one registered merge term merge; one lambda binding redeclared merges; two
    # separately written lambdas refuse
    test-u3-m6-a-shared-merge-redeclared-merges = {
      expr = {
        registered =
          ev
            [
              (T.typedef { merge = sumOf { }; } "tally" isInt)
              (T.typedef { merge = sumOf { }; } "tally" isInt)
            ]
            [
              2
              3
            ];
        oneBinding =
          ev
            [ tally tally ]
            [
              2
              3
            ];
        twoLambdas =
          ev
            [
              tally
              (T.typedef { merge = sum'; } "tally" isInt)
            ]
            [
              2
              3
            ];
        mountedOneBinding =
          mounted
            [ tally tally ]
            [
              2
              3
            ];
      };
      expected = {
        registered = 5;
        oneBinding = 5;
        twoLambdas = "REFUSED";
        mountedOneBinding = 5;
      };
    };
    test-u3-m7-mkOptionType-custom-merge-control = {
      expr =
        ev
          [
            (gm.mkOptionType {
              name = "tally";
              check = isInt;
              merge = sum;
            })
          ]
          [ 2 3 ];
      expected = 5;
    };
    # verify before the fold, in both engines: a bad definition never reaches the caller's fold
    # (whose `+` would abort uncatchably on a string)
    test-each-definition-is-verified-before-the-fold = {
      expr = {
        gen =
          ev
            [ tally ]
            [
              2
              "a"
            ];
        mounted =
          mounted
            [ tally ]
            [
              2
              "a"
            ];
      };
      expected = {
        gen = "REFUSED";
        mounted = "REFUSED";
      };
    };
    # totality: `merge loc` no function is refused before `defs` is applied; the caller's own throw
    # propagates; one definition still folds through `merge`
    test-totality-of-the-caller-fold = {
      expr = {
        locNotAFunction = ev [ (T.typedef { merge = _: 3; } "tally" isInt) ] [ 2 3 ];
        callerThrows = ev [ (T.typedef { merge = _: _: throw "own"; } "tally" isInt) ] [ 2 3 ];
        oneDefinition =
          ev
            [ (T.typedef { merge = _: defs: 10 * (builtins.head defs).value; } "tally" isInt) ]
            [ 7 ];
      };
      expected = {
        locNotAFunction = "REFUSED";
        callerThrows = "REFUSED";
        oneDefinition = 70;
      };
    };
    # inside containers the element folds by it, and beside a witnessed rewrite the meet still owes
    # the rewrite's check (den-hoag-l1j4q), which nixpkgs drops (13 there)
    test-the-fold-reaches-elements-and-the-meet = {
      expr = {
        attrsOf =
          ev
            [ (T.attrsOf tally) ]
            [
              { a = 2; }
              { a = 3; }
            ];
        nullOr =
          ev
            [ (T.nullOr tally) ]
            [
              2
              3
            ];
        meetRefuses =
          ev
            [
              tally
              (nl.types.addCheck tally (v: v < 7))
            ]
            [
              6
              7
            ];
        meetAdmits =
          ev
            [
              tally
              (nl.types.addCheck tally (v: v < 10))
            ]
            [
              6
              7
            ];
        mountedMeet =
          mounted
            [
              tally
              (nl.types.addCheck tally (v: v < 7))
            ]
            [
              6
              7
            ];
      };
      expected = {
        attrsOf.a = 5;
        nullOr = 5;
        meetRefuses = "REFUSED";
        meetAdmits = 13;
        mountedMeet = 13;
      };
    };
  };
}
