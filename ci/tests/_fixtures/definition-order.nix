# Definition ORDER inside nesting types (den-hoag-yjmwc): a type's own module (`q`) against the seed definitions
# (`def`, `def2`). `eng`: `np` is nixpkgs' `evalModules` over nixpkgs' types (the reference), `gm` gen-merge's
# `evalModuleTree` over gen's nesting types and leaves, `br` nixpkgs' `evalModules` over gen's nesting types (the
# export bridge), `gmnp` gen-merge's engine over nixpkgs' types. Read by ci/tests/gen-nesting-definition-order.nix.
{
  gm,
  eng,
  np,
}:
let
  isGmEng = eng == "gm" || eng == "gmnp";
  L = if eng == "gm" then gm else np;
  # nesting constructors: gen-merge's own under gm and br, nixpkgs' under np and gmnp
  N = if eng == "np" || eng == "gmnp" then np.types else gm;
  # leaves: gen-types' under gm, nixpkgs' otherwise
  T = if eng == "gm" then gm.types else np.types;
  P = np.types;
  mkOption = L.mkOption;
  ev = mods: if isGmEng then gm.evalModuleTree { } mods else np.evalModules { modules = mods; };
  leafList = T.listOf T.str;
  base = ty: {
    options.x = mkOption {
      type = ty;
      default = [ ];
    };
  };
  # the type's own module: imports the declaring module, states x
  own = ty: tdef: {
    _file = "q.nix";
    imports = [ (base ty) ];
    x = tdef;
  };
  # one option `o` of nesting type `nt` over the own module, defined by def.nix and def2.nix at `at`
  run =
    {
      nt ? N.submodule,
      ty ? leafList,
      tdef ? [ "q" ],
      d1 ? [ "def" ],
      d2 ? [ "def2" ],
      ownM ? own ty tdef,
      wrapD ? (d: { x = d; }),
      at ? (v: v),
      read ? (o: o.x),
    }:
    let
      r = ev [
        {
          _file = "decl.nix";
          options.o = mkOption { type = nt ownM; };
        }
        {
          _file = "def.nix";
          config.o = at (wrapD d1);
        }
        {
          _file = "def2.nix";
          config.o = at (wrapD d2);
        }
      ];
    in
    read r.config.o;
  key = v: { k = v; };
  # the PUBLISHED module set of a redeclared option defined by attrsets (no value moves there): the option's type's
  # `getSubModules` and the nested evaluation's own `moduleType`'s, each module described by its location chain
  descr =
    m:
    if builtins.isPath m || builtins.isString m then
      "P:" + baseNameOf m
    else if builtins.isFunction m then
      "fn"
    else if builtins.isAttrs m then
      (m._file or m.key or "-")
      + (if m ? imports then "[" + builtins.concatStringsSep "," (map descr m.imports) + "]" else "")
    else
      "?";
  subMods = t: if t ? getSubModules then t.getSubModules else t.substructure.modules;
  redSet =
    elem:
    let
      nt = m: if elem then N.attrsOf (N.submodule m) else N.submodule m;
      at = v: if elem then { k = v; } else v;
      mt =
        { moduleType, ... }:
        {
          options.mt = mkOption { default = map descr (subMods moduleType); };
        };
      r = ev [
        {
          _file = "decl.nix";
          options.o = mkOption {
            type = nt [
              (own leafList [ "q" ])
              mt
            ];
          };
        }
        {
          _file = "decl2.nix";
          options.o = mkOption {
            type = nt {
              _file = "r.nix";
              x = [ "r" ];
            };
          };
        }
        {
          _file = "def.nix";
          config.o = at { x = [ "def" ]; };
        }
        {
          _file = "def2.nix";
          config.o = at { x = [ "def2" ]; };
        }
      ];
    in
    {
      published = map descr (subMods r.options.o.type);
      moduleType = (if elem then r.config.o.k else r.config.o).mt;
    };
  # the redeclared option (`redImp`) over another seed form, at the root or at an `attrsOf` element
  redSeed =
    con: elem: seed:
    let
      nt = m: if elem then con (N.submodule m) else N.submodule m;
      at = v: if elem then { k = v; } else v;
      o =
        (ev [
          {
            _file = "decl.nix";
            options.o = mkOption { type = nt (own leafList [ "q" ]); };
          }
          {
            _file = "decl2.nix";
            options.o = mkOption {
              type = nt {
                _file = "r.nix";
                x = [ "r" ];
              };
            };
          }
          {
            _file = "def.nix";
            config.o = at seed;
          }
          {
            _file = "def2.nix";
            config.o = at { x = [ "def2" ]; };
          }
        ]).config.o;
    in
    if elem then o.k.x else o.x;
  # a nixpkgs `attrTag` whose tag is a `submodule`, redeclared, defined at its tag
  redTag =
    seed:
    let
      tg =
        m:
        P.attrTag {
          t = mkOption { type = P.submodule m; };
        };
    in
    (ev [
      {
        _file = "decl.nix";
        options.o = mkOption { type = tg (own leafList [ "q" ]); };
      }
      {
        _file = "decl2.nix";
        options.o = mkOption {
          type = tg {
            _file = "r.nix";
            x = [ "r" ];
          };
        };
      }
      {
        _file = "def.nix";
        config.o.t = seed;
      }
      {
        _file = "def2.nix";
        config.o.t.x = [ "def2" ];
      }
    ]).config.o.t.x;
  optionTypeRed =
    seed:
    let
      ty =
        (ev [
          {
            _file = "t.nix";
            options.ty = mkOption { type = P.optionType; };
          }
          {
            _file = "t1.nix";
            ty = P.submodule (own leafList [ "q" ]);
          }
          {
            _file = "t2.nix";
            ty = P.submodule {
              _file = "r.nix";
              x = [ "r" ];
            };
          }
        ]).config.ty;
    in
    (ev [
      {
        _file = "decl.nix";
        options.o = mkOption { type = ty; };
      }
      {
        _file = "def.nix";
        config.o = seed;
      }
      {
        _file = "def2.nix";
        config.o.x = [ "def2" ];
      }
    ]).config.o.x;
  # the redeclared option beneath a gen nesting type where gen-merge's engine runs over nixpkgs' types (the
  # nested evaluation's own option, gate C2), beneath the arm's own `submodule` everywhere else
  redUnderGen =
    seed:
    (ev [
      {
        _file = "n.nix";
        options.n = mkOption {
          type = (if eng == "gmnp" then gm.submodule else N.submodule) {
            imports = [
              {
                _file = "decl.nix";
                options.o = mkOption { type = N.submodule (own leafList [ "q" ]); };
              }
              {
                _file = "decl2.nix";
                options.o = mkOption {
                  type = N.submodule {
                    _file = "r.nix";
                    x = [ "r" ];
                  };
                };
              }
            ];
          };
          default = { };
        };
      }
      {
        _file = "def.nix";
        config.n.o = seed;
      }
      {
        _file = "def2.nix";
        config.n.o.x = [ "def2" ];
      }
    ]).config.n.o.x;
  seedFnPlain = { ... }: { x = [ "def" ]; };
  seedFnNested =
    { ... }:
    {
      imports = [
        {
          _file = "w.nix";
          imports = [
            {
              _file = "y.nix";
              x = [ "y" ];
            }
          ];
          x = [ "w" ];
        }
      ];
      x = [ "def" ];
    };
  treeOf =
    m:
    if eng == "np" || eng == "gmnp" then
      (np.evalModules { modules = [ m ]; }).type
    else
      (gm.evalModuleTree { } [ m ]).type;
in
{
  # ── controls: no nesting type, so no own module; expected to agree ──
  ctlTop =
    (ev [
      (base leafList)
      {
        _file = "q.nix";
        x = [ "q" ];
      }
      {
        _file = "def.nix";
        x = [ "def" ];
      }
      {
        _file = "def2.nix";
        x = [ "def2" ];
      }
    ]).config.x;
  ctlTopImp =
    (ev [
      (base leafList)
      {
        _file = "q.nix";
        imports = [
          {
            _file = "w.nix";
            x = [ "w" ];
          }
        ];
        x = [ "q" ];
      }
      {
        _file = "def.nix";
        x = [ "def" ];
      }
    ]).config.x;

  # ── axis 1: the nesting type (merge listOf str; own module q, seeds def, def2) ──
  sub = run { };
  at = run {
    nt = m: N.attrsOf (N.submodule m);
    at = key;
    read = o: o.k.x;
  };
  lz = run {
    nt = m: N.lazyAttrsOf (N.submodule m);
    at = key;
    read = o: o.k.x;
  };
  ls = run {
    nt = m: N.listOf (N.submodule m);
    at = v: [ v ];
    read = o: map (e: e.x) o;
  };
  no = run { nt = m: N.nullOr (N.submodule m); };
  ei = run { nt = m: N.either T.int (N.submodule m); };
  aa = run {
    nt = m: N.attrsOf (N.attrsOf (N.submodule m));
    at = v: { k.j = v; };
    read = o: o.k.j.x;
  };
  mx = run {
    nt = m: P.attrsOf (N.submodule m);
    at = key;
    read = o: o.k.x;
  };
  tr = run { nt = treeOf; };
  wa = run {
    nt =
      m:
      if eng == "np" || eng == "gmnp" then
        P.submoduleWith {
          modules = [ m ];
          specialArgs = {
            a = 1;
          };
          shorthandOnlyDefinesConfig = true;
        }
      else
        (N.submodule m).withArgs { a = 1; };
  };
  ps = run { nt = m: if eng == "np" || eng == "gmnp" then P.submodule m else gm.partialSubmodule m; };
  pa = run {
    nt =
      m:
      if eng == "np" || eng == "gmnp" then
        P.lazyAttrsOf (P.submodule m)
      else
        gm.partialAttrsOf (gm.submodule m);
    at = key;
    read = o: o.k.x;
  };
  sgt = run { nt = m: if eng == "np" || eng == "gmnp" then P.submodule m else gm.types.submodule m; };
  # depth 2: the own module of a submodule nested inside a submodule's own module
  d2 = run {
    nt =
      m:
      N.submodule {
        _file = "mid.nix";
        options.d = mkOption {
          type = N.submodule m;
          default = { };
        };
      };
    at = v: { d = v; };
    read = o: o.d.x;
  };
  # the option declared twice (the redeclared path locates each own module at its declaring file)
  red =
    (ev [
      {
        _file = "decl.nix";
        options.o = mkOption { type = N.submodule (own leafList [ "q" ]); };
      }
      {
        _file = "decl2.nix";
        options.o = mkOption {
          type = N.submodule {
            _file = "r.nix";
            x = [ "r" ];
          };
        };
      }
      {
        _file = "def.nix";
        config.o.x = [ "def" ];
      }
      {
        _file = "def2.nix";
        config.o.x = [ "def2" ];
      }
    ]).config.o.x;

  # ── axis 2: the definition source (on `sub`) ──
  ownImp = run {
    ownM = {
      _file = "q.nix";
      imports = [
        (base leafList)
        {
          _file = "w.nix";
          x = [ "w" ];
        }
      ];
      x = [ "q" ];
    };
  };
  ownFn = run {
    ownM = { ... }: {
      _file = "q.nix";
      imports = [ (base leafList) ];
      x = [ "q" ];
    };
  };
  ownPath = run {
    nt =
      m:
      N.submodule [
        (base leafList)
        ./definition-order-own-path.nix
      ];
  };
  ownTwo = run {
    nt =
      m:
      N.submodule [
        m
        {
          _file = "q2.nix";
          x = [ "q2" ];
        }
      ];
  };
  seedFn = run { wrapD = d: { ... }: { x = d; }; };
  seedImp = run {
    wrapD = d: { ... }: {
      imports = [
        {
          _file = "y.nix";
          x = [ "y" ];
        }
      ];
      x = d;
    };
  };
  oneSeed =
    (ev [
      {
        _file = "decl.nix";
        options.o = mkOption { type = N.submodule (own leafList [ "q" ]); };
      }
      {
        _file = "def.nix";
        config.o.x = [ "def" ];
      }
    ]).config.o.x;
  ownBefore = run { tdef = L.mkBefore [ "q" ]; };
  ownAfter = run { tdef = L.mkAfter [ "q" ]; };
  ownOrd1000 = run { tdef = L.mkOrder 1000 [ "q" ]; };
  seedBefore = run { d1 = L.mkBefore [ "def" ]; };
  ownDefault = run { tdef = L.mkDefault [ "q" ]; };
  allDefault = run {
    tdef = L.mkDefault [ "q" ];
    d1 = L.mkDefault [ "def" ];
    d2 = L.mkDefault [ "def2" ];
  };
  ownForce = run {
    tdef = L.mkForce [ "q" ];
    d1 = L.mkForce [ "def" ];
  };
  ownMerge = run {
    tdef = L.mkMerge [
      [ "q1" ]
      [ "q2" ]
    ];
  };
  ownIf = run { tdef = L.mkIf true [ "q" ]; };
  # the child option's definition files, read inside the child
  files = run {
    ownM = { options, ... }: {
      _file = "q.nix";
      imports = [ (base leafList) ];
      options.f = mkOption { default = options.x.files; };
      config.x = [ "q" ];
    };
    read = o: o.f;
  };

  # ── axis 3: the order-sensitive merge (on `sub`) ──
  lsNp = run { ty = P.listOf P.str; };
  lines = run {
    ty = P.lines;
    tdef = "q";
    d1 = "def";
    d2 = "def2";
  };
  commas = run {
    ty = P.commas;
    tdef = "q";
    d1 = "def";
    d2 = "def2";
  };
  fnTo = run {
    ty = P.functionTo (P.listOf P.str);
    tdef = _: [ "q" ];
    d1 = _: [ "def" ];
    d2 = _: [ "def2" ];
    read = o: o.x null;
  };
  attrsL = run {
    ty = T.attrsOf leafList;
    tdef = {
      a = [ "q" ];
    };
    d1 = {
      a = [ "def" ];
    };
    d2 = {
      a = [ "def2" ];
    };
    read = o: o.x.a;
  };
  # ── axis 4: shapes that discriminate a reorder from the level, and the position-decided merges ──
  # last-wins (attrs: `res // def.value`): one definition decides, by its position
  lastW = run {
    ty = P.attrs;
    tdef = {
      a = "q";
    };
    d1 = {
      a = "def";
    };
    d2 = {
      a = "def2";
    };
    read = o: o.x.a;
  };
  unspec = run {
    ty = P.unspecified;
    tdef = {
      a = "q";
    };
    d1 = {
      a = "def";
    };
    d2 = {
      a = "def2";
    };
    read = o: o.x.a;
  };
  # the own module imports w AND each seed imports y: own subtree and seed subtree interleave by level
  bothImp = run {
    ownM = {
      _file = "q.nix";
      imports = [
        (base leafList)
        {
          _file = "w.nix";
          x = [ "w" ];
        }
      ];
      x = [ "q" ];
    };
    wrapD = d: { ... }: {
      imports = [
        {
          _file = "y.nix";
          x = [ "y" ];
        }
      ];
      x = d;
    };
  };
  # a key the own module's import and a seed's import share: which occurrence the closure keeps
  keyShare = run {
    ownM = {
      _file = "q.nix";
      imports = [
        (base leafList)
        {
          key = "kk";
          x = [ "kOwn" ];
        }
      ];
      x = [ "q" ];
    };
    wrapD = d: { ... }: {
      imports = [
        {
          key = "kk";
          x = [ "kSeed" ];
        }
      ];
      x = d;
    };
  };
  # the own module states `disabledModules` (the removal walk), empty and naming a keyed import
  disE = run {
    ownM = {
      _file = "q.nix";
      imports = [ (base leafList) ];
      x = [ "q" ];
      disabledModules = [ ];
    };
  };
  disK = run {
    nt =
      m:
      N.submodule [
        {
          _file = "q.nix";
          imports = [
            (base leafList)
            {
              key = "kk";
              x = [ "k" ];
            }
            {
              _file = "w.nix";
              x = [ "w" ];
            }
          ];
          x = [ "q" ];
        }
        {
          _file = "q2.nix";
          disabledModules = [ { key = "kk"; } ];
          x = [ "q2" ];
        }
      ];
  };
  oneOf = run {
    nt =
      m:
      N.oneOf [
        T.int
        (N.submodule m)
      ];
  };
  # one untyped and one typed declaration (no type merge: the fold keeps the raw type)
  ut =
    (ev [
      {
        _file = "decl.nix";
        options.o = mkOption { description = "d"; };
      }
      {
        _file = "decl2.nix";
        options.o = mkOption { type = N.submodule (own leafList [ "q" ]); };
      }
      {
        _file = "def.nix";
        config.o.x = [ "def" ];
      }
      {
        _file = "def2.nix";
        config.o.x = [ "def2" ];
      }
    ]).config.o.x;
  # the same, the untyped declaration's field shadowed (the record carries `overridden`, the type stays raw);
  # the field is `defaultText`, outside the four both engines refuse two declarations stating
  utShadow =
    (ev [
      {
        _file = "decl.nix";
        options.o = mkOption { defaultText = "d"; };
      }
      {
        _file = "decl2.nix";
        options.o = mkOption {
          defaultText = "e";
          type = N.submodule (own leafList [ "q" ]);
        };
      }
      {
        _file = "def.nix";
        config.o.x = [ "def" ];
      }
      {
        _file = "def2.nix";
        config.o.x = [ "def2" ];
      }
    ]).config.o.x;
  # the redeclared option with seeds that import (a rotation of the redeclared wrappers would move it)
  redImp =
    (ev [
      {
        _file = "decl.nix";
        options.o = mkOption { type = N.submodule (own leafList [ "q" ]); };
      }
      {
        _file = "decl2.nix";
        options.o = mkOption {
          type = N.submodule {
            _file = "r.nix";
            x = [ "r" ];
          };
        };
      }
      {
        _file = "def.nix";
        config.o = { ... }: {
          imports = [
            {
              _file = "y.nix";
              x = [ "y" ];
            }
          ];
          x = [ "def" ];
        };
      }
      {
        _file = "def2.nix";
        config.o.x = [ "def2" ];
      }
    ]).config.o.x;
  # `redImp` through `attrsOf`: the redeclared null root under a container
  redAtImp =
    (ev [
      {
        _file = "decl.nix";
        options.o = mkOption { type = N.attrsOf (N.submodule (own leafList [ "q" ])); };
      }
      {
        _file = "decl2.nix";
        options.o = mkOption {
          type = N.attrsOf (
            N.submodule {
              _file = "r.nix";
              x = [ "r" ];
            }
          );
        };
      }
      {
        _file = "def.nix";
        config.o.k = { ... }: {
          imports = [
            {
              _file = "y.nix";
              x = [ "y" ];
            }
          ];
          x = [ "def" ];
        };
      }
      {
        _file = "def2.nix";
        config.o.k.x = [ "def2" ];
      }
    ]).config.o.k.x;
  # `redImp` typed, untyped, typed: two typed declarations around an untyped one
  red3Imp =
    (ev [
      {
        _file = "decl.nix";
        options.o = mkOption { type = N.submodule (own leafList [ "q" ]); };
      }
      {
        _file = "decl2.nix";
        options.o = mkOption { description = "d"; };
      }
      {
        _file = "decl3.nix";
        options.o = mkOption {
          type = N.submodule {
            _file = "r.nix";
            x = [ "r" ];
          };
        };
      }
      {
        _file = "def.nix";
        config.o = { ... }: {
          imports = [
            {
              _file = "y.nix";
              x = [ "y" ];
            }
          ];
          x = [ "def" ];
        };
      }
      {
        _file = "def2.nix";
        config.o.x = [ "def2" ];
      }
    ]).config.o.x;
  # the redeclared option over a function seed with no imports, a path seed and a function seed importing twice
  # over, at the root and at an `attrsOf` element
  redFn = redSeed N.attrsOf false seedFnPlain;
  redAtFn = redSeed N.attrsOf true seedFnPlain;
  redPath = redSeed N.attrsOf false ./definition-order-seed.nix;
  redAtPath = redSeed N.attrsOf true ./definition-order-seed.nix;
  redNested = redSeed N.attrsOf false seedFnNested;
  redAtNested = redSeed N.attrsOf true seedFnNested;
  # the same under gen-merge's own `attrsOf` over the element where gen-merge's engine runs (a gen container over a
  # nixpkgs element is mounted as a foreign root is), nixpkgs' `attrsOf` where nixpkgs' engine runs
  redGconFn = redSeed (if isGmEng then gm.types.attrsOf else P.attrsOf) true seedFnPlain;
  redGconImp = redSeed (if isGmEng then gm.types.attrsOf else P.attrsOf) true seedFnNested;
  # nixpkgs' `attrsOf` over the arm's own `submodule`, redeclared: on gen's nesting types a foreign container over
  # a gen element is threaded, and its root is mounted where the group's positions are walked (gate C2)
  redMxFn = redSeed P.attrsOf true seedFnPlain;
  redMxImp = redSeed P.attrsOf true seedFnNested;
  # the published module set, read where no value moves: located once, as nixpkgs locates it
  redSetPublished = (redSet false).published;
  redSetModuleType = (redSet false).moduleType;
  redAtSetPublished = (redSet true).published;
  redAtSetModuleType = (redSet true).moduleType;
  redUnderGenFn = redUnderGen seedFnPlain;
  redUnderGenImp = redUnderGen seedFnNested;
  redTagFn = redTag seedFnPlain;
  redTagImp = redTag seedFnNested;
  # GUARD: an `optionType` option's merge of two definitions locates each definition's module set, and the option
  # declared with that type locates it again; nixpkgs locates twice here, and so does every engine
  optionTypeRedFn = optionTypeRed seedFnPlain;
  optionTypeRedImp = optionTypeRed seedFnNested;
  # depth 2 with imports on both sides at the inner level
  d2Imp = run {
    nt =
      m:
      N.submodule {
        _file = "mid.nix";
        options.d = mkOption {
          type = N.submodule m;
          default = { };
        };
      };
    ownM = {
      _file = "q.nix";
      imports = [
        (base leafList)
        {
          _file = "w.nix";
          x = [ "w" ];
        }
      ];
      x = [ "q" ];
    };
    at = v: { d = v; };
    read = o: o.d.x;
  };

  # ── deferredModule: no own module; the deferred definitions against a consumer's sibling ──
  dm =
    let
      r = ev [
        {
          _file = "decl.nix";
          options.dm = mkOption { type = N.deferredModule; };
        }
        {
          _file = "def.nix";
          dm.x = [ "def" ];
        }
        {
          _file = "def2.nix";
          dm.x = [ "def2" ];
        }
      ];
    in
    (ev [
      (base leafList)
      {
        _file = "q.nix";
        x = [ "q" ];
      }
      r.config.dm
    ]).config.x;
}
