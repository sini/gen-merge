# Two separate `defineType` completions of one `mkType` leaf record, by name (den-hoag-oqqa5): the error-plane half
# of `tests/two-completions.nix`, over its fixtures. gen's engine names both operands and the discriminating fact;
# nixpkgs' engine gives its stock `already declared`, because the export's derived `typeMerge` is the seal's null.
# The forms the seal leaves alone keep the answer they had, aborts included: those are pinned here by their
# `EvalError`, so a move from an abort to a served value or to another refusal reds a cell.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  f = import ./tests/_fixtures/two-completions.nix { inherit genMerge nixpkgsLib; };
  inherit (f)
    gt
    gen
    npe
    force
    m
    T
    Tc
    C
    V
    Rd
    ;
  refuses = expr: msg: {
    expr = force expr;
    expectedError = {
      type = "ThrownError";
      inherit msg;
    };
  };
  aborts = expr: msg: {
    expr = force expr;
    expectedError = {
      type = "EvalError";
      inherit msg;
    };
  };
  sealed =
    n:
    "^gen-merge: option `x' is declared with types that do not merge \\(`${n}' and `${n}', two separate `defineType' completions of one name";
  declared = "The option `x' in `.*' is already declared in";
  merge = "attribute 'merge' missing";
  depr = "attribute 'deprecationMessage' missing";
in
{
  flake.testsError.two-completions = {
    # cell 1: the ruled forms, gen's engine, in both orders, at N = 3, and `s` refused by the declaration, never
    # by the value's check (a refusal by the value would mean the declarations merged)
    test-twob-refuses-by-name = refuses (gen f.twob 4) (sealed "nm");
    test-twob-reversed-refuses-by-name = refuses (gen f.twobR 4) (sealed "nm");
    test-two2-refuses-by-name = refuses (gen f.two2 4) (sealed "nm");
    test-twob3-refuses-by-name = refuses (gen f.twob3 4) (sealed "nm");
    test-twob-s-refuses-at-the-declaration = refuses (gen f.twob "s") (sealed "nm");
    # cell 2: nixpkgs' engine
    test-twob-refuses-on-nixpkgs-engine = refuses (npe f.twob 4) declared;
    test-two2-refuses-on-nixpkgs-engine = refuses (npe f.two2 4) declared;
    test-twob-s-refuses-on-nixpkgs-engine = refuses (npe f.twob "s") declared;
    # cell 6: the verify hazard is two completions, refused by name, never served
    test-the-verify-hazard-refuses-by-name = refuses (gen f.hz 4) (sealed "nm");
    # cell 8: the stock-named pair names `int'
    test-the-stock-named-pair-refuses-by-name = refuses (gen f.TiTi 4) (sealed "int");
    test-the-stock-named-pair-refuses-on-nixpkgs-engine = refuses (npe f.TiTi 4) declared;
    # cell 9: at depth the element pair refuses; the verify-less leaf and a stated fold refuse (K2)
    test-two-completions-in-attrsOf-refuse-at-the-element =
      refuses (gen f.aoTT2 { a = 4; })
        "`attrsOf' over `nm' and `attrsOf' over `nm', whose element types do not merge: `nm' and `nm', two separate `defineType' completions";
    test-two-completions-in-listOf-refuse-at-the-element = refuses (gen f.loTT2 [
      4
    ]) "two separate `defineType' completions of one name";
    test-the-verify-less-leaf-refuses-by-name = refuses (gen f.nvTwob 4) (sealed "nv");
    test-a-stated-fold-refuses-by-name = refuses (gen f.mDTwob 4) (sealed "nm");
    # K2 (protected): an imported check record's two completions serve, and `s` is refused by its check
    test-an-imported-check-record-keeps-its-check = refuses (gen f.mCMTwob "s") "a definition for option `x' is not of type `nm'";
    # held aborts (rule (3) admits no move without a ruling): one completion on nixpkgs' engine (cell 3), the
    # one-completion direct `typeMerge`'s check (K4, P3), the copy grid's verify-replaced and re-completed pairs
    # (cell 4), the mixed pair (cell 5), and an imported `check` record without a fold
    test-bare2-on-nixpkgs-engine-holds-its-abort = aborts (npe [ T T ] 4) depr;
    test-copy2-on-nixpkgs-engine-holds-its-abort = aborts (npe [ Tc Tc ] 4) depr;
    test-the-direct-typemerge-check-holds-its-abort = aborts ((T.typeMerge T.functor).check 4) merge;
    test-the-copy-direct-typemerge-check-holds-its-abort = aborts ((T.typeMerge C.functor).check "s") merge;
    test-copy2-s-own-direct-typemerge-check-holds-its-abort = aborts ((Tc.typeMerge Tc.functor).check 4) merge;
    test-the-direct-typemerge-deprecation-holds-its-abort = aborts (T.typeMerge T.functor).deprecationMessage depr;
    test-a-verify-replaced-copy-holds-its-abort = aborts (gen [ T V ] 4) merge;
    test-a-re-completed-copy-holds-its-abort = aborts (gen [ T Rd ] 4) merge;
    test-the-mixed-pair-holds-its-abort = aborts (gen [ T m ] 4) merge;
    test-an-imported-check-record-without-a-fold-holds-its-abort = aborts (gen [
      (gt.defineType (
        gt.mkType {
          name = "nm";
          check = builtins.isInt;
        }
      ))
      (gt.defineType (
        gt.mkType {
          name = "nm";
          check = builtins.isInt;
        }
      ))
    ] 4) merge;
  };
}
