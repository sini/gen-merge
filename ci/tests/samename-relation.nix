# TWO SAME-NAMED `mkOptionType` DECLARATIONS MERGE ONLY WHEN THEY ARE ONE CONSTRUCTION
# (`lib/types.nix` `mkOptionType`, den-hoag-bfc0k).
#
# A descriptor stating no relation used to merge on its NAME, and the later declaration won with
# its own check: `gauge<10` then `gauge>100` refused 5 and accepted 500, and swapping the order
# swapped the answer. The relation now compares the reified value under Nix `==`, over
# `closuresFirst`'s subject (`lib/interface.nix`), and refuses every other same-named partner.
#
# ★ THE DISCRIMINATOR CARRIES ITS BACK-EDGE UNDER `description`. An exported record is cyclic
# (`functor.type`), and `==` walks attributes in symbol-interning order, so whether a bare `==`
# between two constructions answers or overflows depends on what text was parsed first. This suite's
# parse interns a differing field first, so a pair of plain records answers here even under a bare
# `==`. `description` is interned when the evaluator starts, so `==` reaches it before any closure in
# every context: the `backEdgeUnderDescription` pair overflows under a bare `==` and refuses here.
# Each value below is one the LATER declaration's check accepts, so a last-wins merge reds the cell.
{
  genMerge,
  genMergeCompat,
  ...
}:
let
  inherit (builtins) deepSeq tryEval;
  verdict =
    engine: tys: val:
    let
      res = engine.evalModuleTree {
        modules = map (ty: { options.p = engine.mkOption { type = ty; }; }) tys ++ [ { p = val; } ];
      };
      v = tryEval (deepSeq res.config.p res.config.p);
    in
    if v.success then "ACCEPTED" else "REFUSED";
  ev = verdict genMerge;
  t = genMerge.types;
  lt10 = v: builtins.isInt v && v < 10;
  gt100 = v: builtins.isInt v && v > 100;
  mk =
    check:
    t.mkOptionType {
      name = "gauge";
      inherit check;
    };
  g1 = mk lt10;
  g2 = mk gt100;
  cyc =
    tag:
    let
      r = {
        inherit tag;
        self = r;
      };
    in
    r;
  described =
    tag:
    t.mkOptionType {
      name = "gauge";
      description = cyc tag;
      check = lt10;
    };
in
{
  flake.tests.samename-relation = {
    test-two-constructions-refuse = {
      expr = {
        lt10ThenGt100 = ev [ g1 g2 ] 500;
        gt100ThenLt10 = ev [ g2 g1 ] 5;
        triple = ev [ g1 g2 g1 ] 5;
        oneLambdaTwice = ev [ g1 (mk lt10) ] 5;
        namedLikeALeaf = ev [
          (t.mkOptionType {
            name = "int";
            check = lt10;
          })
          t.int
        ] 5;
        leafThenNamedLikeIt = ev [
          t.int
          (t.mkOptionType {
            name = "int";
            check = lt10;
          })
        ] 5;
        backEdgeUnderDescription = ev [ (described 1) (described 1) ] 5;
        compatEngine = verdict genMergeCompat [
          (genMergeCompat.mkOptionType {
            name = "gauge";
            check = lt10;
          })
          (genMergeCompat.mkOptionType {
            name = "gauge";
            check = gt100;
          })
        ] 500;
      };
      expected = {
        lt10ThenGt100 = "REFUSED";
        gt100ThenLt10 = "REFUSED";
        triple = "REFUSED";
        oneLambdaTwice = "REFUSED";
        namedLikeALeaf = "REFUSED";
        leafThenNamedLikeIt = "REFUSED";
        backEdgeUnderDescription = "REFUSED";
        compatEngine = "REFUSED";
      };
    };

    # One construction declared twice merges and keeps its check: a relation refusing everything reds
    # this cell.
    test-one-construction-merges = {
      expr =
        let
          sel = { inherit g1; };
          d = described 1;
        in
        {
          twinAccepts = ev [ g1 g1 ] 5;
          twinKeepsCheck = ev [ g1 g1 ] 500;
          reachedTwice = ev [ sel.g1 sel.g1 ] 5;
          describedTwin = ev [ d d ] 5;
        };
      expected = {
        twinAccepts = "ACCEPTED";
        twinKeepsCheck = "REFUSED";
        reachedTwice = "ACCEPTED";
        describedTwin = "ACCEPTED";
      };
    };

    # A `//` derivation of a built record is another value, and its relation is still the base's, so
    # it refuses against the base and against itself. A subject reduced to the closures would merge
    # `g1` with `g1 // { description; }` — it keeps every closure slot — and reds `derivedVsBase`.
    test-a-derivation-is-another-value = {
      expr =
        let
          d = g1 // {
            description = "derived";
          };
        in
        {
          derivedVsBase = ev [ g1 d ] 5;
          derivedTwin = ev [ d d ] 5;
          derivedCheck = ev [
            g1
            (g1 // { check = gt100; })
          ] 5;
        };
      expected = {
        derivedVsBase = "REFUSED";
        derivedTwin = "REFUSED";
        derivedCheck = "REFUSED";
      };
    };
  };
}
