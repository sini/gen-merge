# A COMPOSITE'S IDENTITY (den-hoag-6orb8 U2). gen-merge's composites carry the identity fields built
# by gen-types' exported identity half, so two constructions of one composite over one component are
# one type, directly and after transport through `anything`; a composite's constructor is spelled in
# this library's namespace, so gen-types' own `listOf`/`option`/`attrsOf` stay other types; a `//` copy
# is refused at `typeEq` by the completion stamp; and identity and a redeclaration's value are two
# questions: one binding declared twice is one type, and its value is the type's own relation's, the one
# nixpkgs `lib.evalModules` serves.
{
  genMerge,
  genTypes,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  np = nixpkgsLib.types;
  inherit (builtins) deepSeq tryEval;
  refused = e: !(tryEval (deepSeq e e)).success;
  evWith =
    evalModules: mkOption: tys: vals:
    let
      p =
        (evalModules {
          modules = map (ty: { options.p = mkOption { type = ty; }; }) tys ++ map (v: { p = v; }) vals;
        }).config.p;
      r = tryEval (deepSeq p p);
    in
    if r.success then r.value else "REFUSED";
  ev = evWith gm.evalModuleTree gm.mkOption;
  # the same shape under nixpkgs `lib.evalModules`, the reference a redeclaration's value is held to
  evN = evWith nixpkgsLib.evalModules nixpkgsLib.mkOption;
  via =
    ty: v:
    (gm.evalModuleTree {
      modules = [
        { options.k = gm.mkOption { type = ty; }; }
        { config.k = v; }
      ];
    }).config.k;
  anyTwice =
    a: b:
    let
      k =
        (gm.evalModuleTree {
          modules = [
            { options.k = gm.mkOption { type = t.anything; }; }
            { config.k = a; }
            { config.k = b; }
          ];
        }).config.k.description;
      r = tryEval (deepSeq k k);
    in
    if r.success then r.value else "REFUSED";
  minted = ty: (ty.__mint.minted or null) != null;
  spoolOf =
    e:
    gm.deriveType (t.listOf e) {
      id = "spoolOf";
    };
  subA = t.submodule {
    options.a = gm.mkOption {
      type = t.int;
      default = 1;
    };
  };
  subB = t.submodule {
    options.b = gm.mkOption {
      type = t.int;
      default = 2;
    };
  };
  # one binding: its module declares an option and defines it, so a module set doubled reads `[ 1 1 ]`.
  # `bobbin` states a `default` on that option, so nixpkgs refuses it doubled (`already declared`);
  # `spool` states none, so nixpkgs serves it doubled. Each has its nixpkgs twin.
  bobbin = t.submodule {
    options.l = gm.mkOption {
      type = t.listOf t.int;
      default = [ ];
    };
    config.l = [ 1 ];
  };
  bobbinN = np.submodule {
    options.l = nixpkgsLib.mkOption {
      type = np.listOf np.int;
      default = [ ];
    };
    config.l = [ 1 ];
  };
  spool = t.submodule {
    options.l = gm.mkOption { type = t.listOf t.int; };
    config.l = [ 1 ];
  };
  spoolN = np.submodule {
    options.l = nixpkgsLib.mkOption { type = np.listOf np.int; };
    config.l = [ 1 ];
  };
  lOf = r: if builtins.isAttrs r then r.l else r;
in
{
  flake.tests.composite-identity = {
    # Every composite constructor of U2.1's list carries a mark.
    test-every-composite-carries-a-mark = {
      expr = map minted [
        (t.listOf t.int)
        (t.attrsOf t.int)
        (t.lazyAttrsOf t.int)
        (t.nullOr t.int)
        (t.either t.int t.str)
        (t.oneOf [
          t.int
          t.str
          t.bool
        ])
        subA
        (subA.withArgs { x = 1; })
        (spoolOf t.int)
      ];
      expected = [
        true
        true
        true
        true
        true
        true
        true
        true
        true
      ];
    };
    # Two constructions over one component are one type.
    test-two-constructions-are-one-type = {
      expr = {
        listOf = t.typeEq (t.listOf t.int) (t.listOf t.int);
        attrsOf = t.typeEq (t.attrsOf t.int) (t.attrsOf t.int);
        lazyAttrsOf = t.typeEq (t.lazyAttrsOf t.int) (t.lazyAttrsOf t.int);
        nullOr = t.typeEq (t.nullOr t.int) (t.option t.int);
        either = t.typeEq (t.either t.int t.str) (t.either t.int t.str);
        oneOf =
          t.typeEq
            (t.oneOf [
              t.int
              t.str
              t.bool
            ])
            (
              t.oneOf [
                t.int
                t.str
                t.bool
              ]
            );
        submodule =
          let
            m = {
              options.a = gm.mkOption { type = t.int; };
            };
          in
          t.typeEq (t.submodule m) (t.submodule m);
        # A FUNCTION module, the common authored form: the module set is one sealed component whose
        # elements keep the caller's slot, so this is `true` on every evaluator (a slot per module is
        # a fresh thunk, which upstream Nix and Determinate refuse and Lix accepts).
        submoduleFunction =
          let
            f =
              { ... }:
              {
                options.a = gm.mkOption { type = t.int; };
              };
          in
          t.typeEq (t.submodule f) (t.submodule f);
        deriveType = t.typeEq (spoolOf t.int) (spoolOf t.int);
      };
      expected = {
        listOf = true;
        attrsOf = true;
        lazyAttrsOf = true;
        nullOr = true;
        either = true;
        oneOf = true;
        submodule = true;
        submoduleFunction = true;
        deriveType = true;
      };
    };
    # A composite is itself after transport through `anything`, which carries a `__mint` carrier whole.
    test-a-composite-is-itself-after-transport = {
      expr = {
        listOf = t.typeEq (t.listOf t.int) (via t.anything (t.listOf t.int));
        deriveType = t.typeEq (spoolOf t.int) (via t.anything (spoolOf t.int));
      };
      expected = {
        listOf = true;
        deriveType = true;
      };
    };
    # Different components, a different constructor, or gen-types' own spelling of a constructor are
    # other types: this library's constructors mint in its own namespace.
    test-composites-stay-apart = {
      expr = {
        element = t.typeEq (t.listOf t.int) (t.listOf t.str);
        attrsLazy = t.typeEq (t.attrsOf t.int) (t.lazyAttrsOf t.int);
        eitherOrder = t.typeEq (t.either t.int t.str) (t.either t.str t.int);
        args = t.typeEq ((t.submodule { }).withArgs { x = 1; }) ((t.submodule { }).withArgs { x = 2; });
        deriveArg = t.typeEq (spoolOf t.int) (spoolOf t.str);
        genTypesListOf = t.typeEq (t.listOf t.int) (genTypes.listOf genTypes.int);
        genTypesAttrsOf = t.typeEq (t.attrsOf t.int) (genTypes.attrsOf genTypes.int);
        genTypesOption = t.typeEq (t.nullOr t.int) (genTypes.option genTypes.int);
      };
      expected = {
        element = false;
        attrsLazy = false;
        eitherOrder = false;
        args = false;
        deriveArg = false;
        genTypesListOf = false;
        genTypesAttrsOf = false;
        genTypesOption = false;
      };
    };
    # Two submodules share a mark and differ at their module sets, a sealed component: `typeEq` refuses
    # the pair by name, and declared together they still union (the type's own relation).
    test-two-module-sets-refuse-at-typeEq-and-union-as-declared = {
      expr = {
        typeEq = refused (t.typeEq subA subB);
        declared =
          ev
            [
              subA
              subB
            ]
            [ ];
      };
      expected = {
        typeEq = true;
        declared = {
          a = 1;
          b = 2;
        };
      };
    };
    # Identity and value are two questions. One submodule binding declared twice is one type, and its
    # redeclaration's value is still the type's own relation's (the module-set union), so its module set
    # is evaluated twice, as nixpkgs evaluates it: `spool` reads `[ 1 1 ]` in both engines, directly and
    # inside a `listOf`. `bobbin`, whose doubled option states a `default`, is refused by nixpkgs
    # (`already declared`) and served by gen-merge: the stated divergence of den-hoag-00g (ADR-0039,
    # den-hoag-3mc93 open), which this relation neither causes nor decides.
    test-one-submodule-binding-redeclared-is-one-type = {
      expr = {
        typeEq = t.typeEq spool spool;
        gen = lOf (ev [ spool spool ] [ { } ]);
        nixpkgs = lOf (evN [ spoolN spoolN ] [ { } ]);
        genListOf = map lOf (ev [ (t.listOf spool) (t.listOf spool) ] [ [ { } ] ]);
        nixpkgsListOf = map lOf (evN [ (np.listOf spoolN) (np.listOf spoolN) ] [ [ { } ] ]);
        genDefault = lOf (ev [ bobbin bobbin ] [ { } ]);
        nixpkgsDefault = lOf (evN [ bobbinN bobbinN ] [ { } ]);
      };
      expected = {
        typeEq = true;
        gen = [
          1
          1
        ];
        nixpkgs = [
          1
          1
        ];
        genListOf = [
          [
            1
            1
          ]
        ];
        nixpkgsListOf = [
          [
            1
            1
          ]
        ];
        genDefault = [
          1
          1
        ];
        nixpkgsDefault = "REFUSED";
      };
    };
    # A `//` copy of a composite keeps the mark and is refused at `typeEq` by the completion stamp.
    test-a-slash-copy-of-a-composite-is-refused = {
      expr = {
        copy = refused (t.typeEq (t.listOf t.int) ((t.listOf t.int) // { verify = _: null; }));
        same = t.typeEq (t.listOf t.int) (t.listOf t.int);
      };
      expected = {
        copy = true;
        same = true;
      };
    };
    # TWINS IN ONE `anything` SLOT ARE REFUSED (`mergeAnythingDefs`' stated cost, now reaching gen-merge's
    # composites): two constructions are `==`-unequal records carrying `__mint`. One value defined twice
    # folds, and a nixpkgs composite (no `__mint`) is still rebuilt.
    test-twins-in-one-anything-slot-refuse = {
      expr = {
        twoConstructions = anyTwice (t.listOf t.int) (t.listOf t.int);
        oneValue =
          let
            x = t.listOf t.int;
          in
          anyTwice x x;
        noMint = anyTwice (np.listOf np.int) (np.listOf np.int);
      };
      expected = {
        twoConstructions = "REFUSED";
        oneValue = "list of signed integer";
        noMint = "list of signed integer";
      };
    };
  };
}
