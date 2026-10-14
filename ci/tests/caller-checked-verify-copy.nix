# A caller-checked `// { verify }` copy the doors re-complete keeps its own `verify` where nixpkgs reads it
# (den-hoag-fzbap). A caller may lay a check (nixpkgs' `addCheck`, or `// { check }`) on a verify copy before a published
# door completes it. Where `carriedCopy` cannot return the copy as itself (its base is a door's import of a nixpkgs
# record, which carries no mint, or nixpkgs' `addCheck` replaced the `merge` of a gen record), the door re-completes it
# as a check rewrite, and a rewrite's check is published as the caller wrote it. Declared once in nixpkgs'
# `lib.evalModules`, and below a nixpkgs container in either engine, nothing nixpkgs reads stated the copy's `verify`, so
# a value only the `verify` rejects was served. The doors now state the copy's domain in its check before they close it
# (`interface.rebuildClosed.stated`), as `carriedCopy` publishes one. Every refusal stands beside a definition all the
# checks admit, and the overlapping union serves `4` through its other member, as nixpkgs' `addCheck` twin does.
# Red at gen-merge main 81cbdd9 (den-hoag-fzbap spec v0): every `*-verify` and `*-el` / `*-no` key; green there: every
# `*-ok`, `*-laid`, `*-first` key and the union.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins) isInt;
  run =
    eng: ts: v:
    let
      c =
        if eng == "gen" then
          (gm.evalModuleTree { } (map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ [ { x = v; } ]))
          .config
        else
          (nl.evalModules {
            modules = map (t: { options.x = nl.mkOption { type = t; }; }) ts ++ [ { x = v; } ];
          }).config;
      o = builtins.tryEval (builtins.deepSeq c.x c.x);
    in
    if o.success then o.value else "REFUSED";
  np1 = run "np";
  below10 = x: !(isInt x) || x < 10;
  notFive = x: x != 5;
  # the copy's own `verify`: it alone rejects 4
  notFour = v: if v == 4 then "rejected by the copy's verify" else null;
  # a verify copy of a door's import of a nixpkgs record (no mint, so `carriedCopy` does not admit it)
  imported = gm.mkOptionType (np.addCheck np.int below10) // {
    verify = notFour;
  };
  added = np.addCheck imported notFive;
  overridden = imported // {
    check = v: imported.check v && notFive v;
  };
  # a verify copy of a gen `nullOr`, whose `merge` nixpkgs' `addCheck` replaces
  replaced = np.addCheck (gt.nullOr gt.int // { verify = notFour; }) notFive;
in
{
  flake.tests.caller-checked-verify-copy = {
    test-a-caller-checked-verify-copy-of-a-door-import-keeps-its-verify-declared-once =
      let
        cells = {
          mk-add = gm.mkOptionType added;
          def-add = gt.defineType added;
          mk-ovr = gm.mkOptionType overridden;
          def-ovr = gt.defineType overridden;
        };
        row = t: {
          ok = np1 [ t ] 3;
          verify = np1 [ t ] 4;
          laid = np1 [ t ] 5;
          first = np1 [ t ] 20;
        };
      in
      {
        expr = builtins.mapAttrs (_: row) cells;
        expected = builtins.mapAttrs (_: _: {
          ok = 3;
          verify = "REFUSED";
          laid = "REFUSED";
          first = "REFUSED";
        }) cells;
      };
    test-a-verify-copy-whose-merge-addcheck-replaced-keeps-its-verify =
      let
        mk = gm.mkOptionType replaced;
        def = gt.defineType replaced;
      in
      {
        expr = {
          mk-ok = np1 [ mk ] 3;
          mk-verify = np1 [ mk ] 4;
          mk-laid = np1 [ mk ] 5;
          def-ok = np1 [ def ] 3;
          def-verify = np1 [ def ] 4;
          def-laid = np1 [ def ] 5;
          # below a nixpkgs container in gen's own engine
          gen-el-verify = run "gen" [ (np.listOf mk) ] [ 4 ];
          gen-no-verify = run "gen" [ (np.nullOr mk) ] 4;
          gen-el-ok = run "gen" [ (np.listOf mk) ] [ 3 ];
        };
        expected = {
          mk-ok = 3;
          mk-verify = "REFUSED";
          mk-laid = "REFUSED";
          def-ok = 3;
          def-verify = "REFUSED";
          def-laid = "REFUSED";
          gen-el-verify = "REFUSED";
          gen-no-verify = "REFUSED";
          gen-el-ok = [ 3 ];
        };
      };
    test-below-a-nixpkgs-container-and-at-an-overlapping-union =
      let
        def = gt.defineType added;
      in
      {
        expr = {
          el-verify = np1 [ (np.listOf def) ] [ 4 ];
          el-ok = np1 [ (np.listOf def) ] [ 3 ];
          no-verify = np1 [ (np.nullOr def) ] 4;
          no-ok = np1 [ (np.nullOr def) ] 3;
          union-verify = np1 [ (np.either def np.int) ] 4;
          union-laid = np1 [ (np.either def np.int) ] 5;
          twin-union-verify = np1 [
            (np.either (np.addCheck (np.addCheck np.int (v: notFour v == null)) notFive) np.int)
          ] 4;
        };
        expected = {
          el-verify = "REFUSED";
          el-ok = [ 3 ];
          no-verify = "REFUSED";
          no-ok = 3;
          union-verify = 4;
          union-laid = 5;
          twin-union-verify = 4;
        };
      };
  };
}
