# gen-merge: the re-completion doors carry a gen-merge completion's `//` copy as it is (`interface.carriedCopy`)
# and decide that without forcing a field whose WHNF reads the members, so a self-referential checked container
# through either door has a WHNF and is a usable type. A raw gen-types record is imported, never carried: its
# `check` is gen-types' two-argument form, not a predicate. The refusals these copies meet beside a twin are
# pinned by name on the error plane (`tests-error.nix`, `carried-copy-door`). Tripwires are `abort`.
{ genMerge, genTypes, ... }:
let
  gm = genMerge;
  gt = genTypes;
  t = gm.types;
  inherit (builtins) deepSeq seq tryEval;
  whnf = x: seq x "whnf";
  ev =
    tys: val:
    let
      p =
        (gm.evalModuleTree { } (
          map (ty: { options.p = gm.mkOption { type = ty; }; }) tys ++ [ { p = val; } ]
        )).config.p;
      r = tryEval (deepSeq p p);
    in
    if r.success then r.value else "REFUSED";
  rejA = v: if v == "a" then "no" else null;
  twin = t.enum "e" [
    "a"
    "b"
  ];
  sub = p: t.submodule ({ ... }: p "carried-copy-door: the module set was evaluated");
in
{
  flake.tests.carried-copy-door = {
    # RED (uncatchable infinite recursion) where the admission compares the copy's name or stamp: the name of
    # `checkedListOf s` renders `s`, which is the door's own result
    test-a-self-referential-checked-container-has-a-whnf = {
      expr = {
        door = whnf (
          let
            s = gm.mkOptionType (gt.checkedListOf s);
          in
          s
        );
        doorTry =
          let
            s = gm.mkOptionType (gt.checkedListOf s);
          in
          tryEval (seq s null);
        verifyCopy = whnf (
          let
            s = gm.mkOptionType (gt.checkedListOf s // { verify = _: null; });
          in
          s
        );
        renamed = whnf (
          let
            s = gm.mkOptionType (gt.checkedListOf s // { name = "r"; });
          in
          s
        );
        defineType = whnf (
          let
            s = t.defineType (gt.checkedListOf s);
          in
          s
        );
        defineTypeVerifyCopy = whnf (
          let
            s = t.defineType (gt.checkedListOf s // { verify = _: null; });
          in
          s
        );
      };
      expected = {
        door = "whnf";
        doorTry = {
          success = true;
          value = null;
        };
        verifyCopy = "whnf";
        renamed = "whnf";
        defineType = "whnf";
        defineTypeVerifyCopy = "whnf";
      };
    };
    # ... and is a usable type past it
    test-a-self-referential-checked-container-checks-its-values = {
      expr =
        let
          s = gm.mkOptionType (gt.checkedListOf s);
        in
        [
          (s.check [
            [ ]
            [ [ ] ]
          ])
          (s.check [ 1 ])
        ];
      expected = [
        true
        false
      ];
    };
    # a raw gen-types verify copy is imported, so declared twice its relation is the import's and it serves; RED
    # (refused) where it is carried
    test-a-raw-gen-types-verify-copy-declared-twice-serves = {
      expr =
        let
          d = gm.mkOptionType (
            gt.enum "e" [
              "a"
              "b"
            ]
            // {
              verify = rejA;
            }
          );
        in
        ev [ d d ] "b";
      expected = "b";
    };
    # the live controls for the error plane's refusals: a gen-merge completion's verify copy is carried and
    # serves beside its twin, as the twin serves beside itself
    test-a-gen-merge-verify-copy-is-carried-beside-its-twin = {
      expr = {
        copy = ev [
          (gm.mkOptionType (twin // { verify = rejA; }))
          twin
        ] "b";
        twins = ev [
          twin
          twin
        ] "b";
      };
      expected = {
        copy = "b";
        twins = "b";
      };
    };
    # RED (the abort) with a record's own-evaluation fields compared by the admission: inside a registry knot
    # forcing them evaluates the knot
    test-the-admission-forces-no-module-set = {
      expr = whnf (gm.mkOptionType (sub abort // { verify = _: null; }));
      expected = "whnf";
    };
    # a verify copy of a record that does not evaluate its own roles, forging `nestedTypes`, through
    # `defineType`: imported, so its `nestedTypes` is re-derived from what it carries; RED (`string` over an
    # `int` fold) where the admission carries the forged field
    test-a-forged-nested-type-is-re-derived = {
      expr =
        (t.defineType (
          t.attrsOf t.int
          // {
            verify = _: null;
            nestedTypes.elemType = t.str;
          }
        )).nestedTypes.elemType.name;
      expected = "int";
    };
  };
}
