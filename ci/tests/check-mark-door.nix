# A `check` MOVED FROM ANOTHER CONSTRUCTION, read at the published door. `u // intersectAttrs { check = null; } s` holds
# `s`'s published check beside `u`'s witness: two submodules whose domain is one predicate. The door decides whether the
# record's check is its own from the marks the two check records carry, so every evaluator hands back one record: a
# decision taken by `==` over the two records answered by evaluator (the record's slot on Nix and Determinate, the
# closure on Lix), and the door's output differed in shape while its values agreed. The value cells beside it hold the
# check oracle: what the moved check refuses is refused through the door, on both engines.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  subOf =
    mods:
    gt.submodule (
      [
        {
          options.a = gm.mkOption {
            type = gt.int;
            default = 0;
          };
        }
      ]
      ++ mods
    );
  u = subOf [ ];
  s = subOf [
    {
      options.o9 = gm.mkOption {
        type = gt.int;
        default = 9;
      };
    }
  ];
  moved = u // builtins.intersectAttrs { check = null; } s;
  shapeOf =
    Y: if builtins.isAttrs Y.merge then builtins.attrNames Y.merge else builtins.typeOf Y.merge;
  read =
    eng: Y: v:
    let
      r =
        if eng == "gen" then
          (gm.evalModuleTree { } [
            { options.o = gm.mkOption { type = Y; }; }
            { config.o = v; }
          ]).config.o
        else
          (nl.evalModules {
            modules = [
              { options.o = nl.mkOption { type = Y; }; }
              { config.o = v; }
            ];
          }).config.o;
      e = builtins.tryEval (builtins.deepSeq r r);
    in
    if e.success then e.value else "REFUSED";
in
{
  flake.tests.check-mark-door = {
    # the door returns the record a check of the construction's own predicate gets, on every evaluator (red where the
    # door reads the moved check as a rewrite on one evaluator and as its own on another)
    test-a-check-moved-from-a-submodule-of-one-predicate-crosses-the-door-as-its-own = {
      expr = {
        published = shapeOf (gm.mkOptionType moved);
        types = shapeOf (gt.mkOptionType moved);
      };
      expected = {
        published = [
          "__functor"
          "completed"
          "unchecked"
        ];
        types = [
          "__functor"
          "completed"
          "unchecked"
        ];
      };
    };
    # what the record keeps is served, and what its check refuses is refused, through the door on both engines
    test-a-moved-check-through-the-door-serves-what-it-admits-and-refuses-the-rest = {
      expr = nl.genAttrs [ "gen" "np" ] (eng: {
        good = read eng (gm.mkOptionType moved) { a = 1; };
        bad = read eng (gm.mkOptionType moved) { a = "s"; };
      });
      expected = nl.genAttrs [ "gen" "np" ] (_: {
        good = {
          a = 1;
        };
        bad = "REFUSED";
      });
    };
  };
}
