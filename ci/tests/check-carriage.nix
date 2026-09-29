# A check a nixpkgs wrapper states over a gen record survives gen-merge's fold and re-home
# (den-hoag-4ifgb, den-hoag-q3yjf).
#
# nixpkgs states a domain as the descriptor's `check` and refines it there: `addCheck t p` rewrites
# `check`, and `nonEmptyListOf` is `addCheck (listOf t) (l: l != [ ])`. gen reads its own datum
# (`verify` | `admits`), so a rewritten `check` over a gen record (member A) and a stock container
# re-homed as gen's own (member B) were folded without it: a value the declared type forbids, served
# silently. Each refusal below is paired with its passing twin (a carry that refused everything
# would pass the first alone), and the residue the landing leaves is pinned as a value, so a change
# to it is seen rather than read as a fix.
#
# The cells whose subject is a refusal's MESSAGE live on `testsError` (`../tests-error.nix`, group
# `check-carriage`).
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  np = nixpkgsLib.types;
  ac = np.addCheck;
  no = _: false;
  small = x: x < 3;
  inherit (builtins) deepSeq tryEval;

  opt =
    T: V:
    (gm.evalModuleTree {
      modules = [
        { options.s = gm.mkOption { type = T; }; }
        { s = V; }
      ];
    }).config.s;
  served = T: V: tryEval (deepSeq (opt T V) (opt T V));
  accepted = T: V: (served T V).success;

  treeMods = [
    {
      options.a = gm.mkOption {
        type = gt.int;
        default = 0;
      };
    }
  ];
  tree = (gm.evalModuleTree { modules = treeMods; }).type;
  sub = gt.submodule { imports = treeMods; };
  eitherTree = gt.either tree gt.str;
  m = {
    a = 5;
  };
in
{
  flake.tests.check-carriage = {
    # MEMBER A: the rewritten check is carried at every route gen folds a gen record by — the
    # option's own fold, the leaf, the threaded fold of a nesting union, an element, a union member
    # and the `mkOptionType` door.
    test-a-rewritten-check-over-a-gen-record-is-carried = {
      expr = {
        leaf = accepted (ac gt.int small) 5;
        adHoc = accepted (gt.int // { check = no; }) 5;
        door = accepted (gt.mkOptionType (ac gt.int small)) 5;
        container = accepted (ac (gt.listOf gt.int) no) [ 5 ];
        threaded = accepted (ac (gt.either sub gt.str) no) m;
        submodule = accepted (ac sub no) m;
        element = accepted (gt.listOf (ac gt.int small)) [ 5 ];
      };
      expected = {
        leaf = false;
        adHoc = false;
        door = false;
        container = false;
        threaded = false;
        submodule = false;
        element = false;
      };
    };
    test-a-passing-rewritten-check-keeps-the-value = {
      expr = {
        leaf = opt (ac gt.int small) 2;
        door = opt (gt.mkOptionType (ac gt.int small)) 2;
        threaded = opt (ac (gt.either sub gt.str) (_: true)) m;
        element = opt (gt.listOf (ac gt.int small)) [ 2 ];
      };
      expected = {
        leaf = 2;
        door = 2;
        threaded = m;
        element = [ 2 ];
      };
    };
    # A union's member choice asks the member's rewritten check too, as nixpkgs' union reads its
    # members' `check`: `5` is outside the first member and inside the second, which folds it.
    test-a-union-member-refined-away-is-not-chosen = {
      expr = opt (gt.either (ac gt.int small) gt.int) 5;
      expected = 5;
    };
    # The gen base still refuses what the wrapper widened: gen reads `// { check }` as a refinement.
    test-the-gen-domain-still-refuses-under-a-rewritten-check = {
      expr = accepted (ac gt.int (_: true)) "x";
      expected = false;
    };
    # The published `check` is a callable record, and the witness is that record, so a record that
    # keeps it (re-bound by selection, rebuilt by `inherit`, passed through `mapAttrs`) is its own on
    # every evaluator. Over `either tree str` a rewritten check is refused by name, so a value here
    # is the reading "own".
    test-a-record-keeping-its-check-record-is-its-own = {
      expr = {
        kind = nixpkgsLib.isFunction eitherTree.check;
        builtinKind = builtins.isFunction eitherTree.check;
        rebound = opt (eitherTree // { inherit (eitherTree) check; }) "s";
        inheritRebuilt = opt (eitherTree // { inherit (eitherTree) check _checkWitness; }) "s";
        mapAttrsIdentity = opt (builtins.mapAttrs (_: v: v) eitherTree) "s";
      };
      expected = {
        kind = true;
        builtinKind = false;
        rebound = "s";
        inheritRebuilt = "s";
        mapAttrsIdentity = "s";
      };
    };

    # MEMBER B: a stock container re-homed over a nesting element carries its own check.
    test-a-re-homed-stock-container-carries-its-check = {
      expr = {
        nonEmptySub = accepted (np.nonEmptyListOf sub) [ ];
        nonEmptyTree = accepted (np.nonEmptyListOf tree) [ ];
        listOfSub = accepted (ac (np.listOf sub) no) [ m ];
        listOfTree = accepted (ac (np.listOf tree) no) [ m ];
        attrsOfTree = accepted (ac (np.attrsOf tree) no) { k = m; };
        eitherSub = accepted (ac (np.either sub np.str) no) m;
        nullOrSub = accepted (ac (np.nullOr sub) no) m;
      };
      expected = {
        nonEmptySub = false;
        nonEmptyTree = false;
        listOfSub = false;
        listOfTree = false;
        attrsOfTree = false;
        eitherSub = false;
        nullOrSub = false;
      };
    };
    test-a-re-homed-stock-container-keeps-a-passing-value = {
      expr = {
        nonEmptySub = opt (np.nonEmptyListOf sub) [ m ];
        nonEmptyTree = opt (np.nonEmptyListOf tree) [ m ];
        eitherSub = opt (ac (np.either sub np.str) (_: true)) m;
      };
      expected = {
        nonEmptySub = [ m ];
        nonEmptyTree = [ m ];
        eitherSub = m;
      };
    };

    # THE RESIDUE (README "Two prices, stated"): a check over the bare tree, which has no witness
    # (member A), the same stated against the bare tree a container offers (M0), and a stock `either`/`oneOf`/`nullOr` over the bare tree, whose stock check reads
    # the tree and so can be neither carried nor detected (member B). Each is served, as pinned here.
    test-the-residue-is-served = {
      expr = {
        bareTree = opt (ac tree no) m;
        eitherTree = opt (ac (np.either tree np.str) no) m;
        oneOfTree = opt (ac (np.oneOf [
          tree
          np.str
        ]) no) m;
        nullOrTree = opt (ac (np.nullOr tree) no) m;
        # A tree stated with only its `check` rewritten against the tree offered: the two agree on
        # `merge`, the one slot a tree is compared on (M0 gate F3).
        statedCheckOverOfferedTree = opt (np.listOf tree // { nestedTypes.elemType = ac tree no; }) [ m ];
      };
      expected = {
        bareTree = m;
        eitherTree = m;
        oneOfTree = m;
        nullOrTree = m;
        statedCheckOverOfferedTree = [ m ];
      };
    };
  };
}
