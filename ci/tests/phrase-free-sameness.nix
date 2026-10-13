# ONE VALUE IS DECIDED WITHOUT THE PHRASE (den-hoag-olrmz N1). Two declarations of one option whose types
# differ ONLY in their phrase (`description`, or `descriptionClass`) are one value to the merge step: the wrapped
# check each states is kept, so a rejected value is refused in either declaration order, and the merged type
# publishes the phrase nixpkgs' merge publishes, its functor rebuild's, in either order (owner-ruled 2026-10-12:
# nixpkgs' order, the base wins). The expected phrase is read off nixpkgs' twin, never written here. A slice of the gate's
# `descpairs3` population: the one-value arm's `.bad` rows over `addCheck` and `verify` copies.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins) deepSeq tryEval;

  noOne = v: v != 1;
  described = x: x // { description = "a described copy"; };
  families = {
    addCheck = np.addCheck gt.int noOne;
    verifyCopy = gm.mkOptionType (gt.int // { verify = v: if v == 1 then "must not be 1" else null; });
  };
  classed = x: x // { descriptionClass = "conjunction"; };
  ordersBy = d: x: {
    same = [
      x
      x
    ];
    descLater = [
      x
      (d x)
    ];
    descEarlier = [
      (d x)
      x
    ];
  };
  orders = x: {
    same = [
      x
      x
    ];
    descLater = [
      x
      (described x)
    ];
    descEarlier = [
      (described x)
      x
    ];
  };
  genTree =
    tys: val:
    gm.evalModuleTree { } (
      map (ty: { options.x = gm.mkOption { type = ty; }; }) tys ++ [ { x = val; } ]
    );
  served =
    tys: val:
    let
      v = tryEval (deepSeq (genTree tys val).config.x (genTree tys val).config.x);
    in
    if v.success then v.value else "REFUSED";
  phrase = tys: (genTree tys 2).options.x.type.description;
  phraseClass = tys: (genTree tys 2).options.x.type.descriptionClass;
  npClass =
    tys:
    (nl.evalModules {
      modules = map (ty: { options.x = nl.mkOption { type = ty; }; }) tys ++ [ { x = 2; } ];
    }).options.x.type.descriptionClass;
  npPhrase =
    tys:
    (nl.evalModules {
      modules = map (ty: { options.x = nl.mkOption { type = ty; }; }) tys ++ [ { x = 2; } ];
    }).options.x.type.description;
  npTwin = orders (np.addCheck np.int noOne);
  each = f: builtins.mapAttrs (_: x: builtins.mapAttrs (_: f) (orders x)) families;
in
{
  flake.tests.phrase-free-sameness = {
    # The wrapped check survives the merge in every order: 2 is served and 1 refused.
    test-a-description-only-pair-keeps-its-check-in-either-order = {
      expr = each (tys: {
        ok = served tys 2;
        bad = served tys 1;
      });
      expected = builtins.mapAttrs (
        _: _:
        builtins.mapAttrs (_: _: {
          ok = 2;
          bad = "REFUSED";
        }) (orders null)
      ) families;
    };
    # The merged phrase is nixpkgs' in both declaration orders, so it does not depend on which one came last.
    test-a-description-only-pair-publishes-nixpkgs-phrase-in-both-orders = {
      expr = each phrase;
      expected = builtins.mapAttrs (_: _: builtins.mapAttrs (_: npPhrase) npTwin) families;
    };
    # The same of a pair that differs only in `descriptionClass`: nixpkgs' class, in both orders.
    test-a-description-class-only-pair-publishes-nixpkgs-class-in-both-orders = {
      expr = builtins.mapAttrs (_: x: builtins.mapAttrs (_: phraseClass) (ordersBy classed x)) families;
      expected = builtins.mapAttrs (
        _: _: builtins.mapAttrs (_: npClass) (ordersBy classed (np.addCheck np.int noOne))
      ) families;
    };
    # The control: nixpkgs' twin reads one phrase in all three arrangements, so the cell above pins an order.
    test-control-nixpkgs-phrase-is-order-free = {
      expr = builtins.attrNames (builtins.groupBy npPhrase (builtins.attrValues npTwin));
      expected = [ "signed integer" ];
    };
  };
}
