# A door's return for an unmarked `// { check; verify }` copy of a v2 nixpkgs container states the coherence that copy
# declared (den-hoag-8irpj, `rebuildClosed.root`): the copy's check is an ad-hoc override, not an `addCheck`, so
# nixpkgs' coherence guard refuses the door's return as it refuses the copy raw, at the option's root and inside a
# union, and gen's engine refuses it by name at the root. Both doors (`mkOptionType`, `types.mkOptionType`), the
# admitted definition refused. Beside them the lawful positives stay served evaluated (`b = 0`): an `addCheck` copy
# carries nixpkgs' own coherent mark, and a gen submodule's copy is not a v2 type, so its check stays coherent. A
# definition the copy's own predicates reject is refused everywhere.
# Red, the witnesses, with `rebuildClosed.root`'s check stating `isV2MergeCoherent = true` whatever `t` declared.
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
  gs = gt.submodule {
    key = "door-container-verify-copy-gs";
    options.a = gm.mkOption {
      type = gt.int;
      default = 0;
    };
    options.b = gm.mkOption {
      type = gt.int;
      default = 0;
    };
  };
  ns = np.submodule {
    key = "door-container-verify-copy-ns";
    options.a = nl.mkOption {
      type = np.int;
      default = 0;
    };
    options.b = nl.mkOption {
      type = np.int;
      default = 0;
    };
  };
  # rejects a value holding `a = 2` anywhere
  bad = v: if isAttrs v then v.a or null == 2 || any bad (attrValues v) else isList v && any bad v;
  p = v: !(bad v);
  ver = v: if p v then null else "door-container-verify-copy: rejected";
  checkVerify =
    t:
    t
    // {
      check = v: t.check v && p v;
      verify = ver;
    };
  addCheckVerify = t: np.addCheck t p // { verify = ver; };
  read =
    run: t: v:
    let
      o = tryEval (deepSeq (run t v) (run t v));
    in
    if o.success then o.value else "REFUSED";
  engines = {
    nixpkgs =
      t: v:
      (nl.evalModules {
        modules = [
          { options.x = nl.mkOption { type = t; }; }
          { x = v; }
        ];
      }).config.x;
    gen =
      t: v:
      (gm.evalModuleTree { } [
        { options.x = gm.mkOption { type = t; }; }
        { x = v; }
      ]).config.x;
  };
  positions = {
    root = t: t;
    union = t: np.either t np.int;
  };
  doors = {
    mkOptionType = gm.mkOptionType;
    types-mkOptionType = gt.mkOptionType;
  };
  # name, the copy, how a submodule value sits in it, the (engine, position) readings, and whether the admitted
  # definition is refused
  cases = [
    {
      name = "attrsOf-nixpkgs-submodule-check-verify";
      c = checkVerify (np.attrsOf ns);
      w = v: { k = v; };
      at = [
        [
          "nixpkgs"
          "union"
        ]
      ];
      refused = true;
    }
    {
      name = "either-gen-submodule-check-verify";
      c = checkVerify (np.either gs np.str);
      w = v: v;
      at = [
        [
          "nixpkgs"
          "root"
        ]
        [
          "gen"
          "root"
        ]
      ];
      refused = true;
    }
    {
      name = "attrsOf-nixpkgs-submodule-add-check-verify";
      c = addCheckVerify (np.attrsOf ns);
      w = v: { k = v; };
      at = [
        [
          "nixpkgs"
          "union"
        ]
      ];
      refused = false;
    }
    {
      name = "either-gen-submodule-add-check-verify";
      c = addCheckVerify (np.either gs np.str);
      w = v: v;
      at = [
        [
          "nixpkgs"
          "root"
        ]
        [
          "gen"
          "root"
        ]
      ];
      refused = false;
    }
    {
      name = "gen-submodule-check-verify";
      c = checkVerify gs;
      w = v: v;
      at = [
        [
          "nixpkgs"
          "root"
        ]
        [
          "nixpkgs"
          "union"
        ]
        [
          "gen"
          "root"
        ]
        [
          "gen"
          "union"
        ]
      ];
      refused = false;
    }
  ];
  readingsOf =
    C: d:
    listToAttrs (
      builtins.concatMap (
        ep:
        let
          e = builtins.elemAt ep 0;
          pos = builtins.elemAt ep 1;
          run = engines.${e};
          t = positions.${pos} d;
        in
        [
          {
            name = "${e}-${pos}-admitted";
            value = read run t (C.w { a = 1; });
          }
          {
            name = "${e}-${pos}-a2";
            value = read run t (C.w { a = 2; });
          }
        ]
      ) C.at
    );
  expectedOf =
    C:
    listToAttrs (
      builtins.concatMap (ep: [
        {
          name = "${builtins.elemAt ep 0}-${builtins.elemAt ep 1}-admitted";
          value =
            if C.refused then
              "REFUSED"
            else
              C.w {
                a = 1;
                b = 0;
              };
        }
        {
          name = "${builtins.elemAt ep 0}-${builtins.elemAt ep 1}-a2";
          value = "REFUSED";
        }
      ]) C.at
    );
in
{
  flake.tests.door-container-verify-copy = listToAttrs (
    builtins.concatMap (
      dn:
      map (C: {
        name = "test-${dn}-${C.name}";
        value = {
          expr = readingsOf C (doors.${dn} C.c);
          expected = expectedOf C;
        };
      }) cases
    ) (builtins.attrNames doors)
  );
}
