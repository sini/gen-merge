# A CALLER'S DEFINITION RECORDS REACH A FOLD AS THE SPINE HANDS THEM (den-hoag-c922w): `mergeDefsWith` folds a list
# whose values carry no property marker without discharge, `filterOverrides` or the order pass, which are the identity
# on its values, and hands the engine's own records on whole. The passes project each record to `{ file; value; }`, so
# the published `mergeDefs` projects a caller's records to that shape where they enter: a fold that reads its
# definition records sees the same fields on both paths.
#
# Each cell is a caller's record carrying a field beside `file` and `value`, handed through the published `mergeDefs` to
# a foreign type whose fold returns the field names it was handed.
#
# RED: the published `mergeDefs` without its projection gives `[ [ "extra" "file" "value" ] ]` in
# `test-extra-field-never-reaches-the-fold`; with that and the fast path also admitting a record stating `priority`,
# `test-stated-priority-never-reaches-the-fold` gives `[ [ "file" "priority" "value" ] ]`.
{ genMerge, nixpkgsLib, ... }:
let
  observing = nixpkgsLib.types.mkOptionType {
    name = "observing";
    merge = _loc: defs: map builtins.attrNames defs;
  };
in
{
  flake.tests.property-free-fold = {
    test-extra-field-never-reaches-the-fold = {
      expr = genMerge.mergeDefs [ "a" ] observing [
        {
          file = "a";
          value = 1;
          extra = true;
        }
      ];
      expected = [
        [
          "file"
          "value"
        ]
      ];
    };
    test-stated-priority-never-reaches-the-fold = {
      expr = genMerge.mergeDefs [ "a" ] observing [
        {
          file = "a";
          value = 1;
          priority = 1500;
        }
      ];
      expected = [
        [
          "file"
          "value"
        ]
      ];
    };
  };
}
