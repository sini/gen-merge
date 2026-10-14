# A CALLER'S check the doors' `verify` arm answered before it was closed, and a check carried onto a redeclared module
# set's join but not onto the join's headError (den-hoag-jyisy, the residue of den-hoag-1b55t). A caller's check laid on
# a `// { verify }` copy of a gen record reaches the published doors' `verify` arm, which answers ahead of the arm that
# closes a caller's check: a copy the door re-completes was completed from gen data closed over the earlier checks only,
# so nixpkgs' join (declared twice) dropped the laid check; a copy `carriedCopy` returns as itself kept its completion's
# module-set rebuild, so nixpkgs' fixup dropped it declared once. And `carryBy` at a root laid a check on a v2 record's
# `check`, marked coherent, and not on its `merge.v2` headError, which is all nixpkgs' `mergeDefinitions` reads: a
# checked gen `nullOr` of a keyed nixpkgs submodule through `defineType`, declared twice, served what the check rejects.
# Each cell is one composition in nixpkgs' `lib.evalModules`; every refusal stands beside a definition the checks admit.
# Red at gen-merge main (den-hoag-jyisy spec v0): `re-completed-verify-copy` (and red with the door closure removed),
# `verify-copy-as-itself` (red with carriedCopy's rebuild closure removed), `redeclared-foreign-submodule` (red with the
# root carriage's headError removed). `closure-keeps-the-verify` is green at main and the control that the closure
# carries the copy's `verify` with its check (red where it carries the check alone).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins) isAttrs isInt;
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
    key = "caller-check-residue";
    options.a = gm.mkOption {
      type = gt.int;
      default = 0;
    };
  };
  # a nixpkgs submodule with a `key`, so a redeclaration names one module and evaluates
  npSub = np.submodule {
    key = "caller-check-residue-np";
    options.a = nl.mkOption {
      type = np.int;
      default = 0;
    };
  };
  below10 = x: !(isInt x) || x < 10;
  notFive = x: x != 5;
  notThree = v: !(isAttrs v) || v.a or 0 != 3;
  notTwo = v: !(isAttrs v) || v.a or 0 != 2;
  vacuous = _: null;
  laidInt = np.addCheck (
    gm.mkOptionType (np.addCheck np.int below10) // { verify = vacuous; }
  ) notFive;
  copied = gt.nullOr sub // {
    verify = vacuous;
  };
  laidCopy = copied // {
    check = v: copied.check v && notThree v;
  };
  laidNp = np.addCheck (gt.nullOr npSub) notTwo;
  # a `verify` laid after a check: the closure replaces the copy's module-set rebuild, which carried that `verify`
  laidVerify = np.addCheck (gt.nullOr sub) notTwo // {
    verify = v: if notTwo v then null else "rejected by notTwo";
  };
in
{
  flake.tests.caller-check-residue = {
    # the verify arm's re-completion: a verify copy the door re-completes is closed over the laid check first
    test-a-check-laid-on-a-re-completed-verify-copy-survives-the-join =
      let
        mk = gm.mkOptionType laidInt;
        def = gt.defineType laidInt;
      in
      {
        expr = {
          mk-ok = run [ mk mk ] 3;
          mk-laid = run [ mk mk ] 5;
          mk-first = run [ mk mk ] 20;
          def-ok = run [ def def ] 3;
          def-laid = run [ def def ] 5;
          def-first = run [ def def ] 20;
        };
        expected = {
          mk-ok = 3;
          mk-laid = "REFUSED";
          mk-first = "REFUSED";
          def-ok = 3;
          def-laid = "REFUSED";
          def-first = "REFUSED";
        };
      };
    # the verify arm's as-itself return: the copy's module-set rebuild carries the laid check
    test-a-check-laid-on-a-verify-copy-returned-as-itself-survives-the-fixup =
      let
        mk = gm.mkOptionType laidCopy;
        def = gt.defineType laidCopy;
      in
      {
        expr = {
          mk-ok = run [ mk ] { a = 1; };
          mk-laid = run [ mk ] { a = 3; };
          def-ok = run [ def ] { a = 1; };
          def-laid = run [ def ] { a = 3; };
        };
        expected = {
          mk-ok = {
            a = 1;
          };
          mk-laid = "REFUSED";
          def-ok = {
            a = 1;
          };
          def-laid = "REFUSED";
        };
      };
    # the root carriage: a check carried onto a redeclared module-set join is stated on its headError too
    test-a-checked-container-of-a-foreign-submodule-redeclared-keeps-its-check =
      let
        def = gt.defineType laidNp;
        plain = gt.nullOr npSub;
      in
      {
        expr = {
          ll-ok = run [ def def ] { a = 1; };
          ll-laid = run [ def def ] { a = 2; };
          tl-ok = run [ plain def ] { a = 1; };
          tl-laid = run [ plain def ] { a = 2; };
          once-laid = run [ def ] { a = 2; };
        };
        expected = {
          ll-ok = {
            a = 1;
          };
          ll-laid = "REFUSED";
          tl-ok = {
            a = 1;
          };
          tl-laid = "REFUSED";
          once-laid = "REFUSED";
        };
      };
    # the closure carries the copy's `verify` with its check: a definition the check cannot see (a module function) is
    # judged by the `verify` on the merged value
    test-the-closure-keeps-a-verify-copy-s-verify =
      let
        mk = gm.mkOptionType laidVerify;
      in
      {
        expr = {
          fn-ok = run [ mk ] ({ ... }: { a = 1; });
          fn-laid = run [ mk ] ({ ... }: { a = 2; });
          ll-fn-laid = run [ mk mk ] ({ ... }: { a = 2; });
        };
        expected = {
          fn-ok = {
            a = 1;
          };
          fn-laid = "REFUSED";
          ll-fn-laid = "REFUSED";
        };
      };
  };
}
