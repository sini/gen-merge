# A role the declaration fold hosts is met again over the record it serves (den-hoag-fsgy9; ADR-0039 THE MEET). Under
# gen's engine a gen container's element pair is joined and met inside the container relation's element step, before
# the fold sees the answer; the fold hosts a nixpkgs submodule at that role afterwards, rebuilding the container over
# the hosted role. Every check the declarations state binds the record served, so the rebuilt role is met again with
# its two operands. The shape: a gen container W over a gen union whose member is a nixpkgs submodule `Tn` (an inner
# `addCheck`), declared beside a copy of the same container over a union with a plain submodule `P`, the copy stating
# its own obligation (a defineType `verify`, a `// { check }` copy, or nixpkgs' `addCheck` over the union). n = -1 is
# `Tn`'s inner check, n = 7 the copy's obligation, n = 5 valid; both declaration orders.
# Red at gen-merge main 7115674: every n = -1 row served (the inner check dropped, the defect fsgy9 names). Red where
# the fold rebuilds the hosted role without meeting it again: the `verify` copy's n = 7 row served under attrsOf,
# listOf and nullOr, both orders (6 readings).
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  Tn = np.submodule { options.n = nl.mkOption { type = np.addCheck np.int (x: x > 0); }; };
  P = np.submodule { options.n = nl.mkOption { type = np.int; }; };
  not7 = v: !(builtins.isAttrs v && (v.n or null) == 7);
  copies = {
    verify = gt.defineType (
      gt.either P gt.str // { verify = v: if not7 v then null else "n = 7 rejected"; }
    );
    check =
      let
        e = gt.either P gt.str;
      in
      e // { check = v: e.check v && not7 v; };
    addCheck = np.addCheck (gt.either P gt.str) not7;
  };
  read =
    w: ts: v:
    let
      r = builtins.tryEval (
        let
          x =
            w.get
              (gm.evalModuleTree { } (
                map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ [ { x = w.put v; } ]
              )).config.x;
        in
        builtins.deepSeq x x
      );
    in
    if r.success then r.value else "REFUSED";
  rows =
    w:
    builtins.mapAttrs (
      _: c:
      let
        e = w.w (gt.either Tn gt.str);
        cw = w.w c;
      in
      {
        inner = [
          (read w [ e cw ] (-1))
          (read w [ cw e ] (-1))
        ];
        copy = [
          (read w [ e cw ] 7)
          (read w [ cw e ] 7)
        ];
        valid = [
          (read w [ e cw ] 5)
          (read w [ cw e ] 5)
        ];
      }
    ) copies;
  held = {
    inner = [
      "REFUSED"
      "REFUSED"
    ];
    copy = [
      "REFUSED"
      "REFUSED"
    ];
    valid = [
      5
      5
    ];
  };
  expected = {
    verify = held;
    check = held;
    addCheck = held;
  };
in
{
  flake.tests.fold-hosted-role-meet = {
    test-a-hosted-root-union-meets-every-check = {
      expr = rows {
        w = t: t;
        put = v: { n = v; };
        get = x: x.n;
      };
      inherit expected;
    };
    test-a-hosted-attrsOf-role-meets-every-check = {
      expr = rows {
        w = gt.attrsOf;
        put = v: { a.n = v; };
        get = x: x.a.n;
      };
      inherit expected;
    };
    test-a-hosted-listOf-role-meets-every-check = {
      expr = rows {
        w = gt.listOf;
        put = v: [ { n = v; } ];
        get = x: (builtins.head x).n;
      };
      inherit expected;
    };
    test-a-hosted-nullOr-role-meets-every-check = {
      expr = rows {
        w = gt.nullOr;
        put = v: { n = v; };
        get = x: x.n;
      };
      inherit expected;
    };
  };
}
