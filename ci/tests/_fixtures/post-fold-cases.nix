# `types.postFold`'s cases, one plane at a time, read by `tests/post-fold.nix` (values) and `tests-error-post-fold.nix`
# (refusals). A case is a plain value of the plane's vocabulary, or a throw:
#   native : gen-merge's `evalModuleTree` over gen-merge's types (the constructor itself)
#   ref    : nixpkgs' `evalModules` over nixpkgs' types, `postFold g e` spelled as nixpkgs spells it, the `//` override of
#            `e`'s merge (the twin)
#   mount  : nixpkgs' `evalModules` over gen-merge's types (the same gen declaration, in the foreign engine)
{
  genMerge,
  genTypes,
  nixpkgsLib,
}:
plane:
let
  gm = genMerge;
  nl = nixpkgsLib;
  gt = genTypes;
  over =
    g: a:
    a
    // {
      merge = loc: defs: g (a.merge loc defs);
      substSubModules = m: over g (a.substSubModules m);
    };
  V =
    {
      native = {
        t = gm.types;
        top = gm;
        inherit (gm)
          mkOption
          mkIf
          mkForce
          mkDefault
          mkOverride
          ;
        eval = ms: (gm.evalModuleTree { } ms).config;
        evalOpts = ms: (gm.evalModuleTree { } ms).options;
      };
      ref = {
        t = nl.types // {
          postFold = over;
        };
        top = nl.types;
        inherit (nl)
          mkOption
          mkIf
          mkForce
          mkDefault
          mkOverride
          ;
        eval = ms: (nl.evalModules { modules = ms; }).config;
        evalOpts = ms: (nl.evalModules { modules = ms; }).options;
      };
      mount = {
        t = gm.types;
        top = gm;
        inherit (nl)
          mkOption
          mkIf
          mkForce
          mkDefault
          mkOverride
          ;
        eval = ms: (nl.evalModules { modules = ms; }).config;
        evalOpts = ms: (nl.evalModules { modules = ms; }).options;
      };
    }
    .${plane};
  inherit (V) t;
  np = nl.types;
  sub = t.submodule {
    options.a = V.mkOption {
      type = t.int;
      default = 0;
    };
  };
  subND = t.submodule { options.a = V.mkOption { type = t.int; }; };
  # the residue's chain: a gen submodule under gen and nixpkgs containers
  X = np.lazyAttrsOf (np.attrsOf (t.attrsOf sub));
  filtVal = nl.filterAttrs (_: v: v.j.k.a == 1);
  filtValOr = nl.filterAttrs (_: v: (v.j.k.a or 0) == 1);
  mapVal = builtins.mapAttrs (_: v: if v.j.k.a == 1 then v else { });
  addKey = v: v // { added.j.k.a = 7; };
  addA = v: v // { added = v.a + 1; };
  swap =
    r:
    r
    // {
      foo = r.bar;
      bar = r.foo;
    };
  bySwap = v: if (v.baz.j.k.a or 0) == 3 then v else swap v;
  names = builtins.attrNames;
  one = ty: defs: (V.eval ([ { options.s = V.mkOption { type = ty; }; } ] ++ defs)).s;
  # one type value declared n times, then the definitions
  rdN =
    n: ty: defs:
    (V.eval ((builtins.genList (_: { options.s = V.mkOption { type = ty; }; }) n) ++ defs)).s;
  decl = tys: defs: (V.eval (map (ty: { options.s = V.mkOption { type = ty; }; }) tys ++ defs)).s;
  two = {
    s.foo.j.k.a = 1;
    s.bar.j.k.a = 2;
  };
  sumOf = _: defs: builtins.foldl' (a: d: a + d.value) 0 defs;
  ctl = V.top.mkOptionType {
    name = "n";
    check = builtins.isInt;
    merge = sumOf;
  };
  subN = t.submodule (
    { name, ... }:
    {
      options.n = V.mkOption {
        type = t.str;
        default = name;
      };
      options.a = V.mkOption {
        type = t.int;
        default = 0;
      };
    }
  );
  # ── the `rewrites` arm: one option declared twice, one declaration carrying a debt (nixpkgs' `addCheck`, a `//`
  # copy keeping the functor) at a step above the redeclared constructor or on the constructor itself
  rw =
    let
      g = nl.filterAttrs (n: _: n != "drop");
      el = t.postFold g (np.attrsOf np.int);
      pEl = v: !(builtins.isAttrs v && v ? bad);
      pTop = v: !(builtins.isAttrs v && v ? x && builtins.isAttrs v.x && v.x ? bad);
      d =
        bad:
        {
          k = 1;
          drop = 2;
        }
        // (if bad then { bad = 3; } else { });
      on =
        a: b: dv:
        decl [ a b ] [ { s = dv; } ];
    in
    {
      elemAB = bad: on (np.attrsOf (np.addCheck el pEl)) (np.attrsOf el) { x = d bad; };
      elemBA = bad: on (np.attrsOf el) (np.attrsOf (np.addCheck el pEl)) { x = d bad; };
      topAB = bad: on (np.addCheck (np.attrsOf el) pTop) (np.attrsOf el) { x = d bad; };
      topBA = bad: on (np.attrsOf el) (np.addCheck (np.attrsOf el) pTop) { x = d bad; };
      rootAB = bad: on (np.addCheck el pEl) el (d bad);
      rootBA = bad: on el (np.addCheck el pEl) (d bad);
    };
in
{
  inherit rw;
  # ── nested wrappers
  wrapNested2 = names (one (np.uniq (t.postFold filtValOr (t.postFold mapVal X))) [ two ]);
  wrapNested2Nested =
    names
      (one (np.attrsOf (np.uniq (t.postFold filtValOr (t.postFold mapVal X)))) [ { s.x = two.s; } ]).x;
  wrapUnderNullOr = names (one (np.nullOr (t.postFold filtVal X)) [ two ]);
  wrapUnderGenNullOr = names (one (t.nullOr (t.postFold filtVal X)) [ two ]);
  wrapUnderCoerced = names (
    one (np.coercedTo np.str (_: {
      foo.j.k.a = 1;
      bar.j.k.a = 2;
    }) (t.postFold filtVal X)) [ { s = "x"; } ]
  );
  wrapUnderEither = names (one (np.either np.str (t.postFold filtVal X)) [ two ]);
  wrapAddCheck = names (one (np.addCheck (t.postFold filtVal X) (v: v ? foo)) [ two ]);
  wrapOverGen = names (one (t.postFold filtVal (t.lazyAttrsOf (t.attrsOf (t.attrsOf sub)))) [ two ]);
  wrapOverGenNested =
    names
      (one (np.attrsOf (t.postFold filtVal (t.lazyAttrsOf (t.attrsOf (t.attrsOf sub))))) [
        { s.x = two.s; }
      ]).x;
  wrapLeaf = one (t.postFold (v: v + 1) t.int) [ { s = 1; } ];
  wrapListLeaf = one (np.attrsOf (t.postFold (builtins.filter (x: x > 1)) (np.listOf np.int))) [
    {
      s.x = [
        1
        2
      ];
    }
    { s.x = [ 3 ]; }
  ];
  # ── priorities: each keeps `foo` iff the winning definition is 1, beside a `bar` that `g` drops
  prioForce =
    names
      (one (np.attrsOf (t.postFold filtVal X)) [
        { s.x.foo.j.k.a = V.mkForce 1; }
        {
          s.x.foo.j.k.a = 2;
          s.x.bar.j.k.a = 2;
        }
      ]).x;
  prioDefault =
    names
      (one (np.attrsOf (t.postFold filtVal X)) [
        { s.x.foo.j.k.a = V.mkDefault 2; }
        {
          s.x.foo.j.k.a = 1;
          s.x.bar.j.k.a = 2;
        }
      ]).x;
  prioOverride =
    names
      (one (np.attrsOf (t.postFold filtVal X)) [
        { s.x.foo.j.k.a = V.mkOverride 10 1; }
        {
          s.x.foo.j.k.a = V.mkOverride 20 2;
          s.x.bar.j.k.a = 2;
        }
      ]).x;
  # the forced set wins whole
  prioWhole =
    names
      (one (np.attrsOf (t.postFold filtVal X)) [
        {
          s.x = V.mkForce {
            bar.j.k.a = 1;
            baz.j.k.a = 2;
          };
        }
        two
      ]).x;
  prioIfFalse =
    names
      (one (np.attrsOf (t.postFold filtVal X)) [
        { s.x = V.mkIf false { baz.j.k.a = 1; }; }
        { s.x = two.s; }
      ]).x;
  # ── checks
  checkElemRejects =
    (one (np.attrsOf (t.postFold filtVal X)) [ { s.x.foo.j.k.a = "notInt"; } ]).x.foo.j.k.a;
  checkAddCheckRejects =
    names
      (one (np.attrsOf (np.addCheck (t.postFold filtVal X) (v: !(v ? bar)))) [ { s.x = two.s; } ]).x;
  checkAddCheckRejectsCtl =
    names
      (one (np.attrsOf (np.addCheck X (v: !(v ? bar)))) [ { s.x = two.s; } ]).x;
  checkAddCheckRoot = names (one (np.addCheck (t.postFold filtVal X) (v: !(v ? bar))) [ two ]);
  checkPostValueOutside = one (np.attrsOf (t.postFold (_: "notASet") X)) [ { s.x = two.s; } ];
  checkLeafPostOutside = one (t.postFold (_: "str") t.int) [ { s = 1; } ];
  # ── the doors under the constructor
  doorTypes =
    one
      (t.postFold (v: v * 2) (
        t.mkOptionType {
          name = "n";
          check = builtins.isInt;
          merge = sumOf;
        }
      ))
      [
        { s = 1; }
        { s = 2; }
      ];
  doorTop = one (t.postFold (v: v * 2) ctl) [
    { s = 1; }
    { s = 2; }
  ];
  doorRaw =
    one
      (t.postFold (v: v * 2) (
        np.mkOptionType {
          name = "n";
          check = builtins.isInt;
          merge = sumOf;
        }
      ))
      [
        { s = 1; }
        { s = 2; }
      ];
  doorDefine =
    one
      (t.postFold (v: v * 2) (
        t.defineType {
          name = "n";
          verify = v: if builtins.isInt v then null else "not int";
          mergeDefs = sumOf;
        }
      ))
      [
        { s = 1; }
        { s = 2; }
      ];
  # ── identity is the declaring position: a tree `g` moves keeps the name its definitions declared
  identDeclPos =
    (one (np.attrsOf (t.postFold swap (np.lazyAttrsOf subN))) [
      {
        s.x = {
          foo.a = 1;
          bar.a = 2;
        };
      }
    ]).x.foo;
  identDeclPosRoot =
    (one (np.uniq (t.postFold swap (np.lazyAttrsOf subN))) [
      {
        s = {
          foo.a = 1;
          bar.a = 2;
        };
      }
    ]).foo;
  # ── `g` never sees the definitions: its argument is the folded value
  gSeesFolded = one (np.attrsOf (t.postFold builtins.typeOf X)) [ { s.x = two.s; } ];
  gSeesFoldedList = one (t.postFold builtins.typeOf (np.listOf np.int)) [
    { s = [ 1 ]; }
    { s = [ 2 ]; }
  ];
  # ── the empty fold: `g` of the element's empty value, `apply`'s value at the root and in a submodule option
  emptyDiscrOvr = one (np.lazyAttrsOf (t.postFold addKey X)) [ { s.x = V.mkIf false two.s; } ];
  emptyDiscrPfUndefS1 =
    (one (t.submodule { options.x = V.mkOption { type = t.postFold addKey X; }; }) [ ]).x;
  emptyDiscrApplyUndef =
    (one (t.submodule {
      options.x = V.mkOption {
        type = X;
        apply = addKey;
      };
    }) [ ]).x;
  emptyDiscrRootUndef = one (t.postFold addKey X) [ ];
  emptyDiscrRootApplyUndef =
    (V.eval [
      {
        options.s = V.mkOption {
          type = X;
          apply = addKey;
        };
      }
    ]).s;
  emptyNested = one (np.lazyAttrsOf (t.postFold filtVal X)) [ { s.x = V.mkIf false two.s; } ];
  # ── identity regime (gen-types `idOf` / `typeEq`)
  idOfRefuses = gt.idOf (t.postFold filtVal X);
  idOfLeafPf = gt.idOf (t.postFold (v: v) t.int);
  idOfElementCtl = builtins.isString (builtins.toJSON (gt.idOf (t.attrsOf t.int)));
  typeEqBinding = gt.typeEq (t.postFold filtVal t.int) (t.postFold filtVal t.int);
  typeEqOtherG = gt.typeEq (t.postFold filtVal t.int) (t.postFold filtValOr t.int);
  # ── poison stays lazy unless demanded
  poisonThrowUnread =
    (one (np.attrsOf (t.postFold swap X)) [
      {
        s.x = {
          foo.j.k.a = 1;
          bar.j.k.a = throw "poison-bar";
        };
      }
    ]).x.bar.j.k.a;
  poisonAbortUnread =
    (one (np.attrsOf (t.postFold swap X)) [
      {
        s.x = {
          foo.j.k.a = 1;
          bar.j.k.a = abort "poison-bar";
        };
      }
    ]).x.bar.j.k.a;
  poisonThrowRead =
    (one (np.attrsOf (t.postFold swap X)) [
      {
        s.x = {
          foo.j.k.a = 1;
          bar.j.k.a = throw "poison-bar";
        };
      }
    ]).x.foo.j.k.a;
  poisonGUnread = names (
    one (np.attrsOf (t.postFold (_: throw "poison-g") X)) [
      { s.x = two.s; }
      { s.y = two.s; }
    ]
  );
  # ── redeclaration: one construction redeclared is that construction, where the element's own redeclaration serves
  redeclLeaf = n: rdN n (t.postFold (v: v + 1) t.int) [ { s = 1; } ];
  redeclLeafPfPlain =
    decl
      [
        (t.postFold (v: v + 1) t.int)
        t.int
      ]
      [ { s = 1; } ];
  redeclLeafPlainPf =
    decl
      [
        t.int
        (t.postFold (v: v + 1) t.int)
      ]
      [ { s = 1; } ];
  redeclLeafABA =
    let
      a = t.postFold (v: v + 1) t.int;
      b = t.postFold (v: v + 2) t.int;
    in
    decl [ a b a ] [ { s = 1; } ];
  redeclTwo = names (decl [ (t.postFold filtVal X) (t.postFold mapVal X) ] [ two ]);
  redeclVsPlain = names (decl [ (t.postFold filtVal X) X ] [ two ]);
  rdList =
    n:
    rdN n (t.postFold (builtins.filter (x: x > 1)) (np.listOf np.int)) [
      {
        s = [
          1
          2
        ];
      }
      { s = [ 3 ]; }
    ];
  rdNpAttrs =
    n:
    rdN n (t.postFold (nl.filterAttrs (_: v: v > 1)) (np.attrsOf np.int)) [
      {
        s = {
          a = 1;
          b = 2;
        };
      }
    ];
  rdGenAttrs =
    n:
    rdN n (t.postFold (nl.filterAttrs (_: v: v > 1)) (t.attrsOf t.int)) [
      {
        s = {
          a = 1;
          b = 2;
        };
      }
    ];
  rdSubND = n: rdN n (t.postFold addA subND) [ { s.a = 1; } ];
  rdSub = n: rdN n (t.postFold addA sub) [ { s.a = 1; } ];
  # ── the docs face: the constructor reads as its element
  description =
    (V.evalOpts [ { options.s = V.mkOption { type = np.attrsOf (t.postFold filtVal X); }; } ])
    .s.type.description;
  # ── the gen-demo shape: both `baz` arms in one read; `[ 1 1 ]` if `g` is dropped
  demoNested =
    map
      (
        baz:
        (one (np.attrsOf (np.uniq (t.postFold bySwap X))) [
          {
            s.x = {
              foo.j.k.a = 1;
              bar.j.k.a = 2;
              baz.j.k.a = baz;
            };
          }
        ]).x.foo.j.k.a
      )
      [
        3
        4
      ];
  demoRoot =
    map
      (
        baz:
        (one (np.uniq (t.postFold bySwap X)) [
          {
            s = {
              foo.j.k.a = 1;
              bar.j.k.a = 2;
              baz.j.k.a = baz;
            };
          }
        ]).foo.j.k.a
      )
      [
        3
        4
      ];
}
