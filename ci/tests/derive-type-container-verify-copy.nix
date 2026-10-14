# `deriveType` over a `verify`-stating copy of a nixpkgs container of a gen submodule EVALUATES THE DEFINITION
# (den-hoag-mym0d D3). The import re-homes the stock container and hands the overlay back unhomed, so without the
# overlay riding on that re-home the derivation's fold is a leaf's: a definition `{ a = 1; }` is served as itself,
# the submodule's own `b` default never applied. One cell per container and copy kind, each read in nixpkgs'
# `lib.evalModules` and in gen's `evalModuleTree`, as the option's own type and inside `either _ int`: an admitted
# definition is served evaluated (`b = 0`), and a definition one of the copy's own predicates rejects is refused.
# The `verify` that admits everything rejects nothing, so its `{ a = 2; }` is served evaluated too.
# Red, every cell, with the overlay left unhomed in `deriveTypeCore`.
{ genMerge, nixpkgsLib, ... }:
let
  gm = genMerge;
  gt = gm.types;
  nl = nixpkgsLib;
  np = nl.types;
  inherit (builtins)
    any
    attrValues
    deepSeq
    isAttrs
    isList
    listToAttrs
    tryEval
    ;
  sub = gt.submodule {
    key = "derive-type-container-verify-copy-sub";
    options.a = gm.mkOption {
      type = gt.int;
      default = 0;
    };
    options.b = gm.mkOption {
      type = gt.int;
      default = 0;
    };
  };
  # rejects a value holding `a = 2` anywhere
  bad = v: if isAttrs v then v.a or null == 2 || any bad (attrValues v) else isList v && any bad v;
  p = v: !(bad v);
  ver = v: if p v then null else "derive-type-container-verify-copy: rejected";
  # each container over the gen submodule, and how a submodule value sits in it
  containers = {
    nullOr = {
      t = np.nullOr sub;
      w = v: v;
    };
    eitherLeft = {
      t = np.either sub np.str;
      w = v: v;
    };
    eitherRight = {
      t = np.either np.str sub;
      w = v: v;
    };
    oneOf = {
      t = np.oneOf [
        np.str
        sub
      ];
      w = v: v;
    };
    attrsOf = {
      t = np.attrsOf sub;
      w = v: { k = v; };
    };
    lazyAttrsOf = {
      t = np.lazyAttrsOf sub;
      w = v: { k = v; };
    };
    listOf = {
      t = np.listOf sub;
      w = v: [ v ];
    };
  };
  # each copy kind stating `verify`, and whether it rejects `{ a = 2; }`
  copies = {
    verify = {
      c = t: t // { verify = ver; };
      rejects = true;
    };
    addCheckVerify = {
      c = t: np.addCheck t p // { verify = ver; };
      rejects = true;
    };
    checkVerify = {
      c =
        t:
        t
        // {
          check = v: t.check v && p v;
          verify = ver;
        };
      rejects = true;
    };
    nulledVerify = {
      c =
        t:
        t
        // {
          getSubModules = null;
          verify = ver;
        };
      rejects = true;
    };
    admitVerify = {
      c = t: t // { verify = _: null; };
      rejects = false;
    };
    addCheckAdmitVerify = {
      c = t: np.addCheck t p // { verify = _: null; };
      rejects = true;
    };
  };
  npRun =
    t: v:
    (nl.evalModules {
      modules = [
        { options.x = nl.mkOption { type = t; }; }
        { x = v; }
      ];
    }).config.x;
  genRun =
    t: v:
    (gm.evalModuleTree { } [
      { options.x = gm.mkOption { type = t; }; }
      { x = v; }
    ]).config.x;
  read =
    run: t: v:
    let
      o = tryEval (deepSeq (run t v) (run t v));
    in
    if o.success then o.value else "REFUSED";
  # every engine x position x definition of one derived copy
  cellsOf =
    C: d:
    listToAttrs (
      builtins.concatMap
        (
          e:
          builtins.concatMap
            (pos: [
              {
                name = "${e.name}-${pos.name}-admitted";
                value = read e.value (pos.value d) (C.w { a = 1; });
              }
              {
                name = "${e.name}-${pos.name}-a2";
                value = read e.value (pos.value d) (C.w { a = 2; });
              }
            ])
            [
              {
                name = "root";
                value = t: t;
              }
              {
                name = "union";
                value = t: np.either t np.int;
              }
            ]
        )
        [
          {
            name = "nixpkgs";
            value = npRun;
          }
          {
            name = "gen";
            value = genRun;
          }
        ]
    );
  expectedOf =
    C: K:
    listToAttrs (
      builtins.concatMap
        (n: [
          {
            name = "${n}-admitted";
            value = C.w {
              a = 1;
              b = 0;
            };
          }
          {
            name = "${n}-a2";
            value =
              if K.rejects then
                "REFUSED"
              else
                C.w {
                  a = 2;
                  b = 0;
                };
          }
        ])
        [
          "nixpkgs-root"
          "nixpkgs-union"
          "gen-root"
          "gen-union"
        ]
    );
in
{
  flake.tests.derive-type-container-verify-copy = listToAttrs (
    builtins.concatMap (
      cn:
      map (
        kn:
        let
          C = containers.${cn};
          K = copies.${kn};
        in
        {
          name = "test-${cn}-${kn}";
          value = {
            expr = cellsOf C (gm.deriveType { } "derive-type-container-verify-copy" (K.c C.t));
            expected = expectedOf C K;
          };
        }
      ) (builtins.attrNames copies)
    ) (builtins.attrNames containers)
  );
}
