# A PARTIAL fold keeps its priority (den-hoag-fjdnf): `mergeDefsPartial` over some of a position's definitions
# is a definition again, its winners merged under the priority that selected them, so folding it with the
# remaining definitions is the fold over all of them. `filterOverrides` is a fold of the (priority, values)
# monoid; a partial result that dropped its priority would leave the monoid, and a `mkForce` among the first
# definitions would lose to a plain one among the rest.
#
# ★ THE REFERENCE IS nixpkgs OVER ALL THE DEFINITIONS AT ONCE, and each cell runs it. The gen arm folds the
# first group partially, then folds that result with the second group.
#
# A partial fold is partial at the positions of the type it folds by, and only there: `anything` below it
# resolves its own nested priorities, so a nested priority is carried only through a `partialAttrsOf` key.
#
# RED: `mergeDefsPartial` returning its value without the wrapper gives the plain second group's value where
# the first group's `mkForce` should win (`force`, `nested`), and both groups' content where `mkDefault`
# should lose (`default`). With no winners, an empty value at the default priority in place of the identity
# beats the second group's `mkDefault` (`empty`).
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  np = nixpkgsLib;
  inherit (genMerge.types) anything;
  # the two groups, written with constructor set `L`
  fx = L: {
    force = {
      p = [
        (L.mkForce { a = "P"; })
        { b = "Q"; }
      ];
      f = [ { c = "F"; } ];
    };
    default = {
      p = [ (L.mkDefault { a = "P"; }) ];
      f = [ { c = "F"; } ];
    };
    tie = {
      p = [ (L.mkForce { a = "P"; }) ];
      f = [ (L.mkForce { c = "F"; }) ];
    };
    plain = {
      p = [ { a = "P"; } ];
      f = [ { c = "F"; } ];
    };
    # no winners: the partial result is the monoid's identity, so a later `mkDefault` still wins
    empty = {
      p = [ (L.mkIf false { a = "P"; }) ];
      f = [ (L.mkDefault { c = "F"; }) ];
    };
    # the priority one key down: partial at that key too (`partialAttrsOf`), then folded by the full type
    nested = {
      p = [ { s = L.mkForce { x = "P"; }; } ];
      f = [ { s.y = "F"; } ];
    };
  };
  defsOf = map (value: {
    file = "f";
    inherit value;
  });
  # the partial type and the full type each case folds by
  types =
    n:
    if n == "nested" then
      {
        partial = genMerge.partialAttrsOf anything;
        full = genMerge.types.lazyAttrsOf anything;
      }
    else
      {
        partial = anything;
        full = anything;
      };
  gen =
    n:
    let
      c = (fx genMerge).${n};
      t = types n;
    in
    genMerge.mergeDefs [ "o" ] t.full (
      defsOf ([ (genMerge.mergeDefsPartial [ "o" ] t.partial (defsOf c.p)) ] ++ c.f)
    );
  nixpkgs =
    n:
    let
      c = (fx np).${n};
    in
    (np.evalModules {
      modules = [
        { options.o = np.mkOption { type = np.types.anything; }; }
      ]
      ++ map (v: { o = v; }) (c.p ++ c.f);
    }).config.o;
  ref = {
    force.a = "P";
    default.c = "F";
    tie = {
      a = "P";
      c = "F";
    };
    plain = {
      a = "P";
      c = "F";
    };
    empty.c = "F";
    nested.s.x = "P";
  };
in
{
  flake.tests.partial-fold =
    builtins.listToAttrs (
      map (n: {
        name = "test-${n}";
        value = {
          expr = {
            gen = gen n;
            nixpkgs = nixpkgs n;
          };
          expected = {
            gen = ref.${n};
            nixpkgs = ref.${n};
          };
        };
      }) (builtins.attrNames ref)
    )
    // {
      # the partial result's shape: a definition at the winning priority, the plain value at the default,
      # and with no winners a definition that discharges to nothing
      test-the-partial-result-is-a-definition = {
        expr = {
          force = genMerge.mergeDefsPartial [ "o" ] anything (defsOf (fx genMerge).force.p);
          plain = genMerge.mergeDefsPartial [ "o" ] anything (defsOf (fx genMerge).plain.p);
          empty = genMerge.mergeDefsPartial [ "o" ] anything (defsOf (fx genMerge).empty.p);
        };
        expected = {
          force = {
            _type = "override";
            priority = 50;
            content.a = "P";
          };
          plain.a = "P";
          empty = {
            _type = "if";
            condition = false;
            content = { };
          };
        };
      };
      # `partialAttrsOf` through an evaluation, whose nested trees fold on the threaded path: each key is
      # its partial result
      test-partial-attrs-of-a-nested-tree = {
        expr =
          (genMerge.evalModuleTree { } [
            {
              options.o = genMerge.mkOption {
                type = genMerge.partialAttrsOf (
                  genMerge.types.submodule { freeformType = genMerge.types.lazyAttrsOf anything; }
                );
              };
            }
            { o.k = genMerge.mkForce { x = "P"; }; }
            { o.k.y = "Q"; }
            { o.j.z = "Z"; }
          ]).config.o;
        expected = {
          k = {
            _type = "override";
            priority = 50;
            content.x = "P";
          };
          j.z = "Z";
        };
      };
    };
}
