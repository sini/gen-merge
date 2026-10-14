# A CALLER'S check laid on a gen record before a door (den-hoag-1b55t). A door's return is a gen record whose rebuilds
# (`typeMerge`, `substSubModules`) and whose gen data (`typeMergeRel`, `retainedRelation`, `substructure.rebuild`) were
# closed over the check its caller handed the door (den-hoag-d61ws, den-hoag-dyagb). nixpkgs' `addCheck` over that
# return (`q`) is a `//` copy: those rebuilds and data ride into it closed over the first check only, and a second door
# completed it from them, so nixpkgs' join (declared twice) and its fixup (a module set, declared once) dropped `q`. The
# published doors close a gen record whose check departs from its witness (`rewritesCheck`) over that check before they
# complete it, unless its check is still its completion's (`departsOnlyOutside { check = null; }`). Each cell is one
# composition in nixpkgs' `lib.evalModules`; every refusal stands beside a definition the checks admit.
# Red at gen-merge 78b6555 (den-hoag-1b55t spec v0): `relation`, `module-set`, `derivation`, `third-door` and
# `union-dispatch`; `untouched-return` is the control the stamp guard holds (red where every rewritten record is closed),
# and `metadata-copy` the control that the guard asks of the check alone (red where it asks the whole stamp).
{ genMerge, nixpkgsLib, ... }:
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
    ;
  run =
    ts: v:
    let
      c =
        (nl.evalModules {
          modules = map (t: { options.x = nl.mkOption { type = t; }; }) ts ++ [ { x = v; } ];
        }).config;
      o = builtins.tryEval (builtins.deepSeq c.x c.x);
    in
    if o.success then o.value else "REFUSED";
  sub = gt.submodule {
    key = "caller-check-re-doored";
    options.a = gm.mkOption {
      type = gt.int;
      default = 0;
    };
  };
  below10 = x: !(isInt x) || x < 10;
  notFive = x: x != 5;
  notTwo = v: !(isAttrs v) || v.a or 0 != 2;
  notThree = v: !(isAttrs v) || v.a or 0 != 3;
  laidInt = np.addCheck (gm.mkOptionType (np.addCheck np.int below10)) notFive;
  laidSub = np.addCheck (gm.mkOptionType (np.addCheck (np.nullOr sub) notTwo)) notThree;
in
{
  flake.tests.caller-check-re-doored = {
    # the relation stage: the second door's join is derived from the return's relation data
    test-a-check-laid-on-a-return-survives-the-second-door-s-join =
      let
        mk = gm.mkOptionType laidInt;
        def = gt.defineType laidInt;
      in
      {
        expr = {
          mk-ok = run [ mk mk ] 3;
          mk-laid = run [ mk mk ] 5;
          mk-first = run [ mk mk ] 20;
          def-laid = run [ np.int def ] 5;
        };
        expected = {
          mk-ok = 3;
          mk-laid = "REFUSED";
          mk-first = "REFUSED";
          def-laid = "REFUSED";
        };
      };
    # the rebuild stage: a module set's fixup reads the return's `substSubModules`, declared once
    test-a-check-laid-on-a-module-set-return-survives-the-second-door-s-fixup =
      let
        def = gt.defineType laidSub;
        der = gm.deriveType { } "caller-check-re-doored" laidSub;
      in
      {
        expr = {
          def-ok = run [ def ] { a = 1; };
          def-laid = run [ def ] { a = 3; };
          def-first = run [ def ] { a = 2; };
          der-ok = run [ der ] { a = 1; };
          der-laid = run [ der ] { a = 3; };
        };
        expected = {
          def-ok = {
            a = 1;
          };
          def-laid = "REFUSED";
          def-first = "REFUSED";
          der-ok = {
            a = 1;
          };
          der-laid = "REFUSED";
        };
      };
    # three doors: the check laid between the first two survives a third, and one laid between the last two too
    test-a-check-laid-between-any-two-of-three-doors-survives =
      let
        p12 = gt.defineType (gm.mkOptionType laidInt);
        p23 = gm.mkOptionType (
          np.addCheck (gt.defineType (gm.mkOptionType (np.addCheck np.int below10))) notFive
        );
      in
      {
        expr = {
          p12-ok = run [ p12 p12 ] 3;
          p12-laid = run [ p12 p12 ] 5;
          p23-ok = run [ p23 p23 ] 3;
          p23-laid = run [ p23 p23 ] 5;
        };
        expected = {
          p12-ok = 3;
          p12-laid = "REFUSED";
          p23-ok = 3;
          p23-laid = "REFUSED";
        };
      };
    # one door over a gen constructor record a caller checked: a nixpkgs union dispatches on the closed check, so a
    # definition the member's check rejects goes to the other member (the `either` law, nixpkgs' own value declared
    # once, and the `defineType` door's at the same cell)
    test-a-checked-gen-record-behind-one-door-dispatches-a-union-on-its-check =
      let
        pA = v: !(isAttrs v) || all (x: !(isInt x) || x < 10) (attrValues v);
        subAB = gt.submodule {
          key = "caller-check-re-doored-ab";
          options.a = gm.mkOption {
            type = gt.int;
            default = 0;
          };
          options.b = gm.mkOption {
            type = gt.int;
            default = 0;
          };
        };
        x = np.either (gm.mkOptionType (np.addCheck subAB pA)) (np.attrsOf np.int);
      in
      {
        expr = {
          other = run [ x x ] { a = 20; };
          member = run [ x x ] { a = 1; };
          neither = run [ x x ] { a = "s"; };
        };
        expected = {
          other = {
            a = 20;
          };
          member = {
            a = 1;
            b = 0;
          };
          neither = "REFUSED";
        };
      };
    # CONTROL: a return no caller touched is its completion's own output, and is not closed again (a re-completion
    # would rename its `attrsWith` functor and refuse beside the plain `attrsOf`)
    test-control-an-untouched-module-set-return-is-not-closed-again =
      let
        pK = v: !(isAttrs v) || all (e: !(isAttrs e) || e.a or 0 != 2) (attrValues v);
        S = np.attrsOf sub;
        x = gt.defineType (gm.mkOptionType (gm.mkOptionType (np.addCheck S pK)));
      in
      {
        expr = {
          ok = run [ S x ] { k.a = 1; };
          bad = run [ S x ] { k.a = 2; };
        };
        expected = {
          ok = {
            k.a = 1;
          };
          bad = "REFUSED";
        };
      };
    # CONTROL: a caller's metadata-only copy (`// { description }`) of an untouched return departs from its completion
    # outside its check, so it is not closed again either, three doors deep beside the plain `attrsOf`
    test-control-a-metadata-copy-of-an-untouched-return-is-not-closed-again =
      let
        pK = v: !(isAttrs v) || all (e: !(isAttrs e) || e.a or 0 != 2) (attrValues v);
        S = np.attrsOf sub;
        copied = t: gt.defineType (gm.mkOptionType (gm.mkOptionType t) // { description = "copied"; });
        raw = copied S;
        checked = copied (np.addCheck S pK);
      in
      {
        expr = {
          raw-ok = run [ S raw ] { k.a = 1; };
          raw-bad = run [ S raw ] { k.a = 2; };
          checked-ok = run [ S checked ] { k.a = 1; };
          checked-bad = run [ S checked ] { k.a = 2; };
        };
        expected = {
          raw-ok = {
            k.a = 1;
          };
          raw-bad = {
            k.a = 2;
          };
          checked-ok = {
            k.a = 1;
          };
          checked-bad = "REFUSED";
        };
      };
  };
}
