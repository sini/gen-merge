# ONE option loc declared with a type by 12800 modules evaluates: the declaration fold's depth does not
# grow with the module count. The leaf fold forces each step as it is made (`mergeOptionDeclTrees`);
# folded through a lazy accumulator the n-step chain is forced from the outside, to depth n, and the
# evaluator refuses with `max-call-depth exceeded` at this size. This is the cell for that `seq`.
{ genMerge, ... }:
let
  inherit (genMerge) evalModuleTree mkOption types;
  n = 12800;
in
{
  flake.tests.same-loc-depth = {
    test-one-loc-declared-in-n-modules-evaluates = {
      expr =
        (evalModuleTree {
          modules =
            builtins.genList (_: {
              options.p = mkOption { type = types.str; };
            }) n
            ++ [ { config.p = "v"; } ];
        }).config.p;
      expected = "v";
    };
  };
}
