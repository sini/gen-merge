# A FOREIGN record's `verify` through the published `mkOptionType` (den-hoag-xj4tw). A nixpkgs record copied with gen's
# `verify` (`np.int // { verify }`) is imported by `mkOptionType`, and nixpkgs re-derives the declared type through the
# return's rebuilds: the later declaration's `typeMerge` at a redeclaration, and `substSubModules` at a module set's
# fixup. Those rebuilds are the nixpkgs constructor's own, closed by `rebuildClosed.own` over the record's check alone,
# so they stated no `verify`, and nixpkgs' evaluation served what the `verify` rejects. Each cell is one composition
# in nixpkgs' `lib.evalModules`; every refusal stands beside a definition the `verify` admits, and every row is also read
# through the published `defineType`, which closes the same record under its rebuilds with its `verify` carried.
# Red at gen-merge main 81cbdd9: `redeclared`, `fixup`. `union` is green at main and the control that the carriage is
# stated where a union reads it (red where the `verify` is carried on the merge alone: J7's arm, den-hoag-jyisy spec v0).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins) isAttrs;
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
  # a nixpkgs submodule with a `key`, so a redeclaration names one module and evaluates
  npSub = np.submodule {
    key = "foreign-verify-mk-option-type";
    options.a = nl.mkOption {
      type = np.int;
      default = 0;
    };
  };
  not20 = v: if v == 20 then "twenty" else null;
  notTwo = v: if isAttrs v && (v.a or 0) == 2 then "a = 2" else null;
  both = f: {
    mk = f gm.mkOptionType;
    def = f gt.defineType;
  };
in
{
  flake.tests.foreign-verify-mk-option-type = {
    # declared twice, and after its uncopied base: the redeclaration's join states the `verify`
    test-a-foreign-verify-copy-redeclared-keeps-its-verify =
      let
        rows =
          door: base: ok: bad: vf:
          let
            y = door (base // { verify = vf; });
          in
          {
            ll-ok = run [ y y ] ok;
            ll-bad = run [ y y ] bad;
            tl-bad = run [ base y ] bad;
          };
        f = door: {
          int = rows door np.int 1 20 not20;
          lines = rows door np.lines "x" "x\n20" (v: if v == "x\n20" then "twenty" else null);
          attrsOfInt = rows door (np.attrsOf np.int) { a = 1; } { a = 2; } notTwo;
        };
      in
      {
        expr = both f;
        expected =
          let
            e = ok: {
              ll-ok = ok;
              ll-bad = "REFUSED";
              tl-bad = "REFUSED";
            };
            x = {
              int = e 1;
              lines = e "x";
              attrsOfInt = e { a = 1; };
            };
          in
          {
            mk = x;
            def = x;
          };
      };
    # declared once: nixpkgs mounts a module set's fixup rebuild, which states the `verify`
    test-a-foreign-verify-copy-of-a-module-set-keeps-its-verify-at-the-fixup =
      let
        f = door: {
          sub = run [ (door (npSub // { verify = notTwo; })) ] { a = 2; };
          sub-ok = run [ (door (npSub // { verify = notTwo; })) ] { a = 1; };
          nullOrSub = run [ (door (np.nullOr npSub // { verify = notTwo; })) ] { a = 2; };
          attrsOfSub = run [
            (door (
              np.attrsOf npSub // { verify = v: if isAttrs v && notTwo (v.k or { }) != null then "k" else null; }
            ))
          ] { k.a = 2; };
        };
        x = {
          sub = "REFUSED";
          sub-ok = {
            a = 1;
          };
          nullOrSub = "REFUSED";
          attrsOfSub = "REFUSED";
        };
      in
      {
        expr = both f;
        expected = {
          mk = x;
          def = x;
        };
      };
    # declared twice inside an `either` whose other member admits the rejected value: the union moves on to that member
    test-a-foreign-verify-copy-redeclared-in-a-union-yields-to-the-other-member =
      let
        f = door: {
          int =
            let
              u = np.either (door (np.int // { verify = not20; })) np.int;
            in
            run [ u u ] 20;
          sub =
            let
              u = np.either (door (npSub // { verify = notTwo; })) (np.attrsOf np.int);
            in
            run [ u u ] { a = 2; };
        };
        x = {
          int = 20;
          sub = {
            a = 2;
          };
        };
      in
      {
        expr = both f;
        expected = {
          mk = x;
          def = x;
        };
      };
  };
}
