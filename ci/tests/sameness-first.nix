# THE LEAF RELATION DECIDES SAMENESS FIRST (den-hoag-6orb8 U1; design §1, "Where both operands carry a
# gen identity … gen-merge decides redeclaration on that identity"). A parametric gen-types leaf
# declared twice merges when the vocabulary's `typeEq` says the two are one type, and a digest match
# never merges on its own where either operand seals a component (a caller lambda, a registered
# construction). Names are invented (ADR-0035): a `basting` registry, a `stitch` constructor.
{
  genMerge,
  genTypesFlake,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  algebra = genTypesFlake.inputs.gen-algebra.lib;
  identity = genTypesFlake.inputs.gen-identity.lib;
  inherit (builtins) deepSeq tryEval;

  ev =
    tys: val:
    let
      res = gm.evalModuleTree { } (
        map (ty: { options.p = gm.mkOption { type = ty; }; }) tys ++ [ { p = val; } ]
      );
      v = tryEval (deepSeq res.config.p res.config.p);
    in
    if v.success then v.value else "REFUSED";

  basting = {
    revision = "r1";
    members.stitch = a: v: builtins.isInt v && v >= a.lo && v <= a.hi;
  };
  its = args: algebra.mkIntensional identity.hashIdentity basting "stitch" args;
  td = gt.typedef "stitched";
  r1 = its {
    lo = 1;
    hi = 9;
  };
  r1' = its {
    lo = 1;
    hi = 9;
  };
  r9 = its {
    lo = 1;
    hi = 10;
  };
  even = v: builtins.isInt v && builtins.bitAnd v 1 == 0;
  even' = v: builtins.isInt v && builtins.bitAnd v 1 == 0;
in
{
  flake.tests.sameness-first = {
    # Two constructions of one registered term redeclared are one type and merge; two different terms
    # share a mark and are still refused by name; the term's own check still decides the value.
    test-registered-twins-merge-and-different-terms-refuse = {
      expr = {
        twins = ev [ (td r1) (td r1') ] 5;
        twinsOutOfRange = ev [ (td r1) (td r1') ] 50;
        different = ev [ (td r1) (td r9) ] 5;
      };
      expected = {
        twins = 5;
        twinsOutOfRange = "REFUSED";
        different = "REFUSED";
      };
    };

    # A lambda `typedef` is sealed in its slot: one binding redeclared merges (G2), and two separately
    # written lambdas sharing a mark are refused (G3) — the pair a digest match alone would merge.
    test-a-sealed-lambda-merges-only-as-one-binding = {
      expr =
        let
          x = gt.typedef "even" even;
        in
        {
          oneBinding = ev [ x x ] 4;
          twoLambdas = ev [ (gt.typedef "even" even) (gt.typedef "even" even') ] 4;
          markShared = (gt.typedef "even" even).__mint.minted == (gt.typedef "even" even').__mint.minted;
        };
      expected = {
        oneBinding = 4;
        twoLambdas = "REFUSED";
        markShared = true;
      };
    };

    # KEEP: the reconciliation law and the minted relation are untouched — the enum union under one
    # name, a `listOf` element join, and two enum names refused.
    test-the-enum-union-law-is-untouched = {
      expr = {
        union = ev [
          (gt.enum "spool" [ "a" ])
          (gt.enum "spool" [ "b" ])
        ] "b";
        elementJoin =
          ev
            [
              (gt.listOf (gt.enum "spool" [ "a" ]))
              (gt.listOf (gt.enum "spool" [ "b" ]))
            ]
            [
              "a"
              "b"
            ];
        twoNames = ev [
          (gt.enum "spool" [ "a" ])
          (gt.enum "bobbin" [ "b" ])
        ] "b";
      };
      expected = {
        union = "b";
        elementJoin = [
          "a"
          "b"
        ];
        twoNames = "REFUSED";
      };
    };
  };
}
