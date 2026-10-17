# A ONCE-DECLARED GEN NESTING TYPE'S OWN MODULES SIT ONE LEVEL DOWN (den-hoag-yjmwc): nixpkgs hands each own
# module of a type it locates (`mergeOptionDecls` → `fixupOptionType`, wherever the option's type forwards a
# module set) through `setDefaultModuleLocation`, so its definitions sit one breadth-first level below the
# seeds' and are read first. gen-merge's engine over gen's twin type reads them in the same order. The level
# is the nested tree's ROOT order (`rootOrder`), applied after every module's coordinate is assigned, so no
# module node and no declaration address moves (ci/tests/nesting-keys.nix, ci/tests/declaration-address.nix).
#
# - Every forwarding nesting shape: `submodule` (both spellings), `attrsOf`, `lazyAttrsOf`, `listOf`, `nullOr`,
#   `attrsOf ∘ attrsOf`, a nixpkgs `attrsOf` over gen's, `withArgs`, the partial forms, depth two.
# - Every own-module form and definition form: a function, a path, two own modules, imports on either side, a
#   shared key, `disabledModules`, `mkIf`, `mkMerge`, `mkOrder`, every priority, and one untyped declaration.
# - Every order-reading merge: lists, `lines`, `commas`, `functionTo`, `attrsOf (listOf …)`, `attrs` (the last
#   definition decides), and the child option's `files`.
# - Guards, equal before and after: no nesting type, `either` and `oneOf` (nixpkgs locates nothing through a
#   union), a redeclared option (the declaration fold already locates it, `fixupModuleSets`), a tree type,
#   function seeds, `mkBefore`/`mkAfter`, `deferredModule`.
#
# `gm` cells: `expr` is gen-merge's engine over gen's types and `expected` nixpkgs' engine over nixpkgs' types.
# `br` cells: `expr` is nixpkgs' engine over gen's types (the export bridge, whose depth-two child is gen's).
# RED (no root order): `[ "def" "def2" "q" ]` where nixpkgs reads `[ "q" "def" "def2" ]`.
{
  genMerge,
  genMergeCore,
  genScope,
  nixpkgsLib,
  ...
}:
let
  read =
    x:
    let
      r = builtins.tryEval (builtins.deepSeq x x);
    in
    if r.success then r.value else "refused";
  on =
    eng:
    builtins.mapAttrs (_: read) (
      import ./_fixtures/definition-order.nix {
        gm = genMerge;
        np = nixpkgsLib;
        inherit eng;
      }
    );
  np = on "np";
  gm = on "gm";
  br = on "br";
  # nixpkgs refuses an untyped declaration restating a field the typed one states; gen serves it (the
  # ordered declaration fold, ADR-0029), and the type is still the typed declaration's, located by the root
  beyond = [ "utShadow" ];
  g = genMerge;
  t = g.types;
  lf = {
    options.x = g.mkOption {
      type = t.listOf t.str;
      default = [ ];
    };
  };
  w = {
    _file = "w.nix";
    x = [ "w" ];
  };
  own = {
    _file = "q.nix";
    imports = [
      lf
      w
    ];
    x = [ "q" ];
  };
  ownK = {
    key = "ownK";
    imports = [
      lf
      {
        key = "kw";
        x = [ "kw" ];
      }
    ];
    x = [ "q" ];
  };
  ownD = {
    _file = "q.nix";
    imports = [ lf ];
    x = [ "q" ];
    disabledModules = [ ];
  };
  seedFn = d: { ... }: {
    imports = [
      {
        _file = "y.nix";
        x = [ "y" ];
      }
    ];
    x = d;
  };
  host = ty: defs: [ { options.o = g.mkOption { type = ty; }; } ] ++ defs;
  # every minted identifier of a root evaluation whose nested trees hold own modules beside seeds
  ids =
    mods:
    let
      r = genMergeCore.evalModuleTreeExposed { modules = mods; };
      all = builtins.filter (i: genScope.decodeNta i != null) r._evaluation.allNodeIds;
    in
    builtins.length all;
  shapes = {
    imports = host (t.submodule own) [
      { config.o.x = [ "def" ]; }
      { config.o = seedFn [ "def2" ]; }
    ];
    keyed = host (t.attrsOf (t.submodule ownK)) [
      { config.o.a.x = [ "def" ]; }
      { config.o.a.x = [ "def2" ]; }
    ];
    two = host (t.submodule [
      own
      {
        _file = "q2.nix";
        x = [ "q2" ];
      }
    ]) [ { config.o.x = [ "def" ]; } ];
    removal = host (t.submodule ownD) [
      { config.o.x = [ "def" ]; }
      { config.o.x = [ "def2" ]; }
    ];
    refined =
      host
        (t.submodule {
          imports = [
            lf
            (rec_ "a" "m1")
          ];
          x = [ "q" ];
        })
        [
          {
            config.o = { ... }: {
              imports = [ (rec_ "b" "m2") ];
              x = [ "def" ];
            };
          }
        ];
    list = host (t.listOf (t.submodule own)) [
      { config.o = [ { x = [ "def" ]; } ]; }
      { config.o = [ { x = [ "def2" ]; } ]; }
    ];
  };
  # a node key two records construct (two refinements of one meeting): the refined graph (`a3.refinedGraph`)
  rec_ = tag: mark: {
    __moduleKey = "n1";
    __keyEq = {
      subject = { inherit mark; };
      decide = a: b: a == b;
      meeting = "rk";
    };
    __functor = _: _: {
      key = "rk#" + mark;
      x = [ tag ];
    };
  };
  # a type declaring `nests.declAt` (declaration-address.nix's `elemWith`), its own module KEYED, so the
  # anchors walk the closure (`declAnchorOf`'s graph) rather than read an index
  elemK =
    let
      inner = t.submodule [
        {
          options.tag = g.mkOption {
            type = t.str;
            default = "";
          };
          options.seen = g.mkOption {
            type = t.listOf t.anything;
            default = [ ];
          };
        }
      ];
      wrapD =
        ty:
        let
          n = ty.nests;
        in
        t.defineType (
          ty
          // {
            nests = n // {
              entry = d: {
                imports = [ (n.entry { inherit (d) file value; }) ];
                config.seen = [ (d.declAt or null) ];
              };
              declAt = true;
            };
          }
        );
      sub = t.submodule [
        {
          options.tag = g.mkOption {
            type = t.str;
            default = "";
          };
          options.seen = g.mkOption {
            type = t.listOf t.anything;
            default = [ ];
          };
          options.inner = g.mkOption {
            type = t.listOf (wrapD inner);
            default = [ ];
          };
        }
        {
          key = "ownK";
          config.inner = [ { tag = "own"; } ];
        }
      ];
    in
    wrapD sub;
  anchors = mods: map (e: map (i: i.seen) e.inner) (g.evalModuleTree { } mods).config.o;
  twins = builtins.filter (n: !(builtins.elem n beyond)) (builtins.attrNames np);
  twin =
    eng: side:
    map (name: {
      name = "test-${eng}-${name}-equals-nixpkgs";
      value = {
        expr = side.${name};
        expected = np.${name};
      };
    }) twins;
in
{
  flake.tests.gen-nesting-definition-order = builtins.listToAttrs (twin "gm" gm ++ twin "br" br) // {
    # the reference arm is live: no twin cell agrees by both engines refusing it
    test-nixpkgs-serves-every-twin-cell = {
      expr = builtins.filter (name: np.${name} == "refused") twins;
      expected = [ ];
    };
    # ADR-0034: the root order mints no module node (the wrapper arm reds every shape, one node per own
    # module), a refined key's graph and a keyed own module's anchors pair with the reordered collection
    test-the-root-order-mints-no-module-node = {
      expr = builtins.mapAttrs (_: ids) shapes;
      expected = {
        imports = 11;
        keyed = 9;
        list = 13;
        refined = 9;
        removal = 8;
        two = 8;
      };
    };
    test-a-keyed-own-module-anchors-under-the-root-order = {
      expr = anchors (
        host (t.listOf elemK) [
          {
            config.o = [
              { tag = "a"; }
              { tag = "b"; }
            ];
          }
        ]
      );
      expected = [
        [
          [
            [
              "a:1"
              "o"
              0
              { module = 1; }
              "inner"
              0
            ]
          ]
        ]
        [
          [
            [
              "a:1"
              "o"
              1
              { module = 1; }
              "inner"
              0
            ]
          ]
        ]
      ];
    };
    # beyond nixpkgs: the untyped-then-typed order, a field shadowed (`ut` without the shadow is a twin)
    test-gm-utShadow-reads-the-located-order = {
      expr = gm.utShadow;
      expected = np.ut;
    };
  };
}
