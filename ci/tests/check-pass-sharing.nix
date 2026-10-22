# THE CHECK PASSES ALLOCATE LESS AND KEEP EVERY ANSWER (den-hoag-c7jkw.3, den-hoag-83wmp): the
# declaration guard's spine walk, the closed-set stratum, the declaration-plane misuse walk, the
# orphan refusal's grouping and the order pass's marker scan (`lib/modules.nix`) each drop an
# allocation their answer never read. The refusals through the same sites are pinned on
# `testsError` (`../tests-error.nix`, group `check-pass-sharing`).
#
# The order pass at `mergeDefsWith` and at `mergeDefsPartial` had no discriminating cell: dropping
# either site's sort read both suites green. Each order cell below reds exactly its own site.
#
# RED: `validateDeclSubtree` returning a group whose children are all leaves without copying it
# forces the stratum-1 fold's throwing sibling (`declared-lazy-…`), and on `testsError` changes
# which of two throwing declarations refuses. That fold is `declarationsOf`, read through the core:
# the public door reads the value path's declarations, whose guard forces the sibling as nixpkgs'
# `.options` does (den-hoag-qqywn).
{ genMerge, genMergeCore, ... }:
let
  gm = genMerge;
  t = gm.types;
  orderDefs = [
    {
      file = "/a";
      value = [ "b" ];
    }
    {
      file = "/b";
      value = gm.mkBefore [ "a" ];
    }
  ];
in
{
  flake.tests.check-pass-sharing = {
    test-order-value-fold-sorts-a-before-definition = {
      expr = gm.mergeDefs [ "l" ] (t.listOf t.str) orderDefs;
      expected = [
        "a"
        "b"
      ];
    };
    test-order-partial-fold-sorts-a-before-definition = {
      expr = gm.mergeDefsPartial [ "l" ] (t.listOf t.str) orderDefs;
      expected = [
        "a"
        "b"
      ];
    };
    test-declared-lazy-fold-does-not-force-a-throwing-sibling = {
      expr =
        (genMergeCore.declarationsOf {
          modules = [
            {
              options.a = gm.mkOption {
                type = t.int;
                default = 0;
              };
              options.b = throw "LAZY";
            }
          ];
        }).a.loc;
      expected = [ "a" ];
    };
  };
}
