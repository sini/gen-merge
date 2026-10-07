# A check nixpkgs' `addCheck` states over a nixpkgs submodule is enforced in gen's engine, alone and
# beside another submodule declaration, at the top and as a container's element, through a gen
# container too (den-hoag-8ip0d).
#
# nixpkgs rebuilds a module-set type at declaration (`fixupOptionType`, `substSubModules`), which
# erases a wrapper's check, and a declaration fold joins module sets without one, so nixpkgs serves a
# value the wrapper rejects. A foreign record states no check witness, so no merge step can see the
# drop; the mount and the declaration list's fixup carry every foreign declaration's check instead
# (`interface.carriedAtDepth`). Each refusal is paired with its passing twin, so a carriage that refused
# everything would not pass.

{
  genMerge,
  nixpkgsLib,
  ...
}:

let
  gm = genMerge;
  gt = gm.types;
  np = nixpkgsLib.types;
  inherit (builtins) deepSeq tryEval;

  accepted =
    ts: v:
    let
      x =
        (gm.evalModuleTree { } (map (t: { options.x = gm.mkOption { type = t; }; }) ts ++ [ { x = v; } ]))
        .config.x;
    in
    (tryEval (deepSeq x x)).success;

  intOpt = mk: t: n: {
    options.${n} = mk {
      type = t;
      default = 0;
    };
  };
  not7 = v: !(builtins.isAttrs v && (v.a or 0) == 7);
  W = np.addCheck (np.submodule (intOpt nixpkgsLib.mkOption np.int "a")) not7;
  N = np.submodule (intOpt nixpkgsLib.mkOption np.int "b");
  G = gt.submodule (intOpt gm.mkOption gt.int "c");
  both = ts: ok: bad: {
    ok = accepted ts ok;
    bad = accepted ts bad;
  };
  top = ts: both ts { a = 1; } { a = 7; };
  attrs = ts: both ts { k.a = 1; } { k.a = 7; };
  list = ts: both ts [ { a = 1; } ] [ { a = 7; } ];
  nested = ts: both ts { k.j.a = 1; } { k.j.a = 7; };
  enforced = {
    ok = true;
    bad = false;
  };
in

{
  flake.tests.module-set-carriage = {
    test-a-foreign-wrapper-over-a-submodule-beside-another-declaration-is-enforced = {
      expr = {
        alone = top [ W ];
        gen = top [
          W
          G
        ];
        genFirst = top [
          G
          W
        ];
        foreign = top [
          N
          W
        ];
        three = top [
          G
          N
          W
        ];
      };
      expected = {
        alone = enforced;
        gen = enforced;
        genFirst = enforced;
        foreign = enforced;
        three = enforced;
      };
    };
    test-a-foreign-wrapper-over-a-submodule-element-is-enforced = {
      expr = {
        attrsAlone = attrs [ (np.attrsOf W) ];
        attrsGen = attrs [
          (gt.attrsOf G)
          (np.attrsOf W)
        ];
        attrsForeign = attrs [
          (np.attrsOf W)
          (np.attrsOf N)
        ];
        listAlone = list [ (np.listOf W) ];
        listGen = list [
          (np.listOf W)
          (gt.listOf G)
        ];
      };
      expected = {
        attrsAlone = enforced;
        attrsGen = enforced;
        attrsForeign = enforced;
        listAlone = enforced;
        listGen = enforced;
      };
    };
    # the walk descends through a container that owes nothing itself, a gen one included
    test-a-foreign-wrapper-below-a-gen-container-in-a-foreign-one-is-enforced = {
      expr = nested [ (np.attrsOf (gt.attrsOf W)) ];
      expected = enforced;
    };
    test-a-foreign-wrapper-below-a-gen-container-beside-its-gen-twin-is-enforced = {
      expr = nested [
        (gt.attrsOf (gt.attrsOf W))
        (gt.attrsOf (gt.attrsOf G))
      ];
      expected = enforced;
    };
  };
}
