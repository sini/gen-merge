# P5's SCANNER — every public operation answers or refuses BY NAME (ADR-0025 item 1; premise §7.1 P5).
#
# The `structural-domain` battery made total over the public surface by GENERATION: the operations
# are read from the library value, never from a list, so an entry point added to the surface is
# scanned the day it lands. An operation is
#   · a CALLABLE top-level member of `genMerge` (`op`),
#   · a callable member of `genMerge.types` (`types-op`), and that member applied to `types.int`
#     taken as an option type (`fold-of-int`),
#   · a value member of `genMerge.types`, taken as an option type (`fold`): the fold is the operation
#     a user reaches through `evalModuleTree`, driven with the arm as the option's one definition.
# CALLABLE is a function OR a functor set: `evalModuleTree`, `declaredOptions`, `deriveType` and
# `types.mkValidator` are functors, and `builtins.isFunction` alone reads them as values
# (den-hoag-25dd7 gate C1).
#
# ONE CELL PER (operation, arm), `test-<family>-<op>-on-<arm>`, over one wrong-shape value per Nix
# type. The cell forces the result under `tryEval`: an answer is rethrown as the marker
# `p5-scan answered`, a catchable refusal is re-forced so its own message surfaces. An interpreter
# error escapes `tryEval` and the cell dies with the interpreter's text, which matches neither
# alternative of the verdict, so the cell fails BY ITS NAME. A bare `assert` and an unprefixed throw
# fail it too: the item says a NAMED refusal.
#
# THE BOUND. One arm, at the first argument. An interpreter error reachable only through a
# structured input (a second argument, two definitions) passes the scanner; the hand-written
# diagnostic cells cover those paths. Nested namespaces (`moduleSyntax`) are not walked.
#
# EXCEPTIONS are the register `./tests-error-p5-scan-exceptions.nix`, one entry per cell, argued.
# An excepted cell asserts the COMPLEMENT of the verdict, so a pair that is fixed, or starts
# answering, reds until its entry is removed: the register cannot decay into a suppression list.
# The complement never pins an interpreter's wording, so it holds under all three evaluators.
{ genMerge, ... }:
let
  gm = genMerge;
  t = gm.types;
  battery = {
    null = null;
    int = 5;
    str = "s";
    list = [ 5 ];
    attrs = {
      k = 5;
    };
    fn = x: x;
    bool = true;
    float = 1.5;
  };
  verdict = "^(p5-scan answered|gen-[a-z-]+[.:])";
  complement = "^(?!p5-scan answered|gen-[a-z-]+[.:])";
  exceptions = import ./tests-error-p5-scan-exceptions.nix;
  judge =
    v:
    if (builtins.tryEval (builtins.deepSeq v null)).success then
      throw "p5-scan answered"
    else
      builtins.deepSeq v null;
  fold =
    ty: v:
    (gm.evalModuleTree { } [
      { options.o = gm.mkOption { type = ty; }; }
      {
        _file = "/p/F.nix";
        o = v;
      }
    ]).config.o;
  callable = v: builtins.isFunction v || (builtins.isAttrs v && v ? __functor);
  cellsOver =
    family: names: body:
    builtins.listToAttrs (
      builtins.concatMap (
        n:
        map (
          a:
          let
            name = "test-${family}-${n}-on-${a}";
          in
          {
            inherit name;
            value = {
              expr = judge (body n battery.${a});
              expectedError.msg = if exceptions ? ${name} then complement else verdict;
            };
          }
        ) (builtins.attrNames battery)
      ) names
    );
  topOps = builtins.filter (n: callable gm.${n}) (builtins.attrNames gm);
  typeOps = builtins.filter (n: callable t.${n}) (builtins.attrNames t);
  typeVals = builtins.filter (n: !(callable t.${n})) (builtins.attrNames t);
  cells =
    cellsOver "op" topOps (n: arm: gm.${n} arm)
    // cellsOver "types-op" typeOps (n: arm: t.${n} arm)
    // cellsOver "fold" typeVals (n: arm: fold t.${n} arm)
    // cellsOver "fold-of-int" typeOps (n: arm: fold (t.${n} t.int) arm);
in
{
  # A register entry naming no generated cell is refused by name: a renamed operation or a retired
  # arm cannot leave an entry behind that excepts nothing.
  flake.tests.p5-scan.test-every-exception-names-a-generated-cell = {
    expr = builtins.filter (n: !(cells ? ${n})) (builtins.attrNames exceptions);
    expected = [ ];
  };
  flake.testsError.p5-scan = cells;
}
