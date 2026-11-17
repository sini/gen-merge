# A SUBMODULE JOIN IS GEN-MERGE'S CONSTRUCTION OVER ITS TWO OPERANDS (den-hoag-2vtgj). The relation's union
# of two submodule declarations states `gen-merge.submodule-join`, each operand a member by its mark and sealed
# where its own identity is, in the order their module sets concatenate. So joins of two different statements
# are two types even over one shared module list, a statement beside a plain `submodule` keeps it, and the
# join's identity is ordered as its value is. A join is not its operand: the union is not idempotent. Every
# reading is the type the declaration stratum hands back, compared by `typeEq`, since the rebuilt module set
# is a sealed component and `idOf` refuses it.
{ genMerge, ... }:
let
  gm = genMerge;
  gt = gm.types;
  mods = [ { options.a = gm.mkOption { default = 1; }; } ];
  stating = n: {
    ctor = "lib-a.inst";
    members = [ ];
    args = _: { inherit n; };
    sealed = [ ];
  };
  over = n: gm.refusingSubmodule (stating n) [ "config" ] mods;
  plain = gt.submodule { options.b = gm.mkOption { default = 2; }; };
  joined =
    tys:
    (gm.evalModuleTree { } (map (t: { options.o = gm.mkOption { type = t; }; }) tys)).options.o.type;
  # `typeEq`'s answer, or "refused" where it gives none
  eq =
    a: b:
    let
      r = builtins.tryEval (builtins.deepSeq (gt.typeEq a b) (gt.typeEq a b));
    in
    if r.success then r.value else "refused";
  oneBinding = [
    (over 1)
    (over 1)
  ];
in
{
  flake.tests.submodule-join-identity = {
    test-joins-of-two-statements-over-one-module-list-are-two-types = {
      expr =
        eq
          (joined [
            (over 1)
            (over 1)
          ])
          (joined [
            (over 2)
            (over 2)
          ]);
      expected = false;
    };
    test-a-statement-beside-a-plain-submodule-is-kept = {
      expr =
        eq
          (joined [
            (over 1)
            plain
          ])
          (joined [
            (over 2)
            plain
          ]);
      expected = false;
    };
    # the union's value is ordered (a list option both sets define reads in module order), so its identity is
    test-the-join-in-the-other-order-is-another-type = {
      expr =
        eq
          (joined [
            (over 1)
            plain
          ])
          (joined [
            plain
            (over 1)
          ]);
      expected = false;
    };
    # controls
    test-a-join-is-not-its-operand = {
      expr = eq (joined [
        (over 1)
        (over 1)
      ]) (joined [ (over 1) ]);
      expected = false;
    };
    test-one-join-binding-is-one-type = {
      expr = eq (joined oneBinding) (joined oneBinding);
      expected = true;
    };
    test-separately-built-twin-joins-are-one-type = {
      expr =
        eq
          (joined [
            (over 1)
            (over 1)
          ])
          (joined [
            (over 1)
            (over 1)
          ]);
      expected = true;
    };
    test-plain-twin-joins-are-one-type = {
      expr =
        eq
          (joined [
            plain
            plain
          ])
          (joined [
            plain
            plain
          ]);
      expected = true;
    };
  };
}
