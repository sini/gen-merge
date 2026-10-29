# ONE VALUE IS DECIDED WITHOUT THE PHRASE (den-hoag-olrmz N1). Two declarations of one option whose types
# differ ONLY in their phrase (`description`, or `descriptionClass`) are one value to the merge step: the wrapped
# check each states is kept, so a rejected value is refused in either declaration order, and the merged type
# publishes the phrase nixpkgs' merge publishes, its functor rebuild's, in either order (owner-ruled 2026-10-12:
# nixpkgs' order, the base wins). The expected phrase is read off nixpkgs' twin, never written here. A slice of the gate's
# `descpairs3` population: the one-value arm's `.bad` rows over `addCheck` and `verify` copies.
{
  genMerge,
  nixpkgsLib,
  interface,
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

  # ── THE SUBJECT LEAVES OUT A MODULE SET'S OWN EVALUATION (den-hoag-stage3-rolesmet-nestedtypes-xr243) ──
  # On a record stating a module set, `nestedTypes`, `unroledNested` and `descriptionClass` are outputs of that
  # set's evaluation, and "one value" never forces them: the set itself is compared. On any other record
  # `nestedTypes` is the carrying spelling and is still compared.
  npSub = np.submodule { options.a = nl.mkOption { type = np.int; }; };
  gSub = gt.submodule { options.a = nl.mkOption { type = np.int; }; };
  npL = np.listOf np.int;
  gL = gt.attrsOf gt.int;
  pairs = {
    npSelf = [
      npSub
      npSub
    ];
    npTwoCtor = [
      npSub
      (np.submodule { options.a = nl.mkOption { type = np.int; }; })
    ];
    npGraftName = [
      npSub
      (npSub // { name = "other"; })
    ];
    npGraftNested = [
      npSub
      (npSub // { nestedTypes.freeformType = np.int; })
    ];
    npListGraftNested = [
      npL
      (npL // { nestedTypes.elemType = np.str; })
    ];
    gSelf = [
      gSub
      gSub
    ];
    gGraftName = [
      gSub
      (gSub // { name = "other"; })
    ];
    gGraftNested = [
      gSub
      (gSub // { nestedTypes.freeformType = gt.int; })
    ];
    gGraftUnroled = [
      gSub
      (gSub // { unroledNested.freeformType = gt.int; })
    ];
    gLGraftUnroled = [
      gL
      (gL // { unroledNested.x = gt.str; })
    ];
  };
  # a forged `//` copy of gen's submodule departing only in `nestedTypes`, declared beside its honest base
  forged = gSub // {
    nestedTypes.freeformType = gt.int;
  };
  forgedTree =
    tys:
    gm.evalModuleTree { } (
      map (ty: { options.s = gm.mkOption { type = ty; }; }) tys ++ [ { s.a = 3; } ]
    );
  forgedRead =
    tys:
    let
      e = forgedTree tys;
      v = tryEval (deepSeq e.config.s.a e.config.s.a);
    in
    {
      value = if v.success then v.value else "REFUSED";
      nested = builtins.attrNames e.options.s.type.nestedTypes;
    };
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
    # One value over record pairs. A module-set record and its `//` copy departing only at its own evaluation's
    # outputs are one value; a container's copy departing in its carrying spelling, a name, or a second
    # construction is not.
    test-one-value-leaves-out-a-module-sets-own-evaluation = {
      expr = builtins.mapAttrs (
        _: p: interface.sameValue (builtins.elemAt p 0) (builtins.elemAt p 1)
      ) pairs;
      expected = {
        npSelf = true;
        npTwoCtor = false;
        npGraftName = false;
        npGraftNested = true;
        npListGraftNested = false;
        gSelf = true;
        gGraftName = false;
        gGraftNested = true;
        gGraftUnroled = true;
        gLGraftUnroled = false;
      };
    };
    # ★ THE STATED PRICE, pinned at the served surface: a forged copy and its honest base are one value, and in
    # either declaration order the merged type publishes the `nestedTypes` its module set decides and serves the
    # value. A forged copy declared alone publishes it too, because the evaluation re-derives the field from the
    # set. No honest declaration authors the field (error, not forgery). Control: a module set stating a
    # `freeformType` publishes it, so the read sees the field.
    test-a-forged-own-evaluation-copy-serves-the-honest-type = {
      expr = {
        honestFirst = forgedRead [
          gSub
          forged
        ];
        forgedFirst = forgedRead [
          forged
          gSub
        ];
        forgedAlone = forgedRead [ forged ];
        freeformControl = forgedRead [ (gt.submodule { freeformType = gt.attrsOf gt.int; }) ];
      };
      expected = {
        honestFirst = {
          value = 3;
          nested = [ ];
        };
        forgedFirst = {
          value = 3;
          nested = [ ];
        };
        forgedAlone = {
          value = 3;
          nested = [ ];
        };
        freeformControl = {
          value = 3;
          nested = [ "freeformType" ];
        };
      };
    };
  };
}
