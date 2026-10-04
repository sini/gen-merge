# A nixpkgs submodule's `nestedTypes` is never forced where nixpkgs would not force it
# (den-hoag-a0c4z; ADR-0014's rider, its one exception).
#
# nixpkgs' `submoduleWith` states `nestedTypes` as an output of evaluating the type's OWN module set
# with no definitions. That set is complete only once the definitions and the other declarations
# join it, and nixpkgs never takes the read. A walk that took it refused "option does not exist"
# where nixpkgs yields the value: a redeclared submodule whose halves complete each other (the
# stock NixOS `systemd.network` shape), a freeformType stated in the other half, a definition that
# declares what the type's config sets. Each witness row expects nixpkgs' value, and the reference
# row pins that nixpkgs gives it.
#
# The laziness is asserted as a property: the record's `nestedTypes` is POISONED and the value is
# still served, on every route a nixpkgs submodule crosses by. A record the recogniser does not
# admit keeps its carrying spelling read: the same poison on a `listOf`/`attrsOf` fires (on the error
# plane, `../tests-error.nix` group `submodule-laziness`, with the two ruled refusals the
# recogniser must not drop and the undeclared control's message).
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  lib = nixpkgsLib;
  np = lib.types;
  inherit (builtins) deepSeq tryEval;
  int = lib.mkOption { type = np.int; };
  poison = t: t // { nestedTypes = throw "submodule-laziness: nestedTypes forced e975a05c0a"; };

  served =
    eval: read: modules:
    let
      r = tryEval (
        let
          v = read (eval modules).config;
        in
        deepSeq v v
      );
    in
    if r.success then r.value else "refused";
  gen = served (modules: gm.evalModuleTree { } modules);
  genL = served (modules: gm.evalModuleTree { specialArgs = { inherit lib; }; } modules);
  ref = served (modules: lib.evalModules { inherit modules; });
  y = c: c.s.y;

  # a hand-built container whose payload states `modules` beside a STATIC element role
  fakeList =
    elem: payload:
    lib.mkOptionType {
      name = "fakeList";
      check = builtins.isList;
      merge = _loc: defs: lib.concatMap (d: d.value) defs;
      nestedTypes.elemType = elem;
      functor = np.defaultFunctor "fakeList" // {
        inherit payload;
        binOp = a: _b: a;
        type = _p: fakeList elem payload;
      };
    };
  genSub = gm.types.submodule { options.y = int; };

  witness = {
    redeclared = {
      read = y;
      modules = [
        {
          options.s = lib.mkOption {
            type = np.submodule { config.y = 2; };
            default = { };
          };
        }
        { options.s = lib.mkOption { type = np.submodule { options.y = int; }; }; }
      ];
    };
    redeclaredSwapped = {
      read = y;
      modules = [
        { options.s = lib.mkOption { type = np.submodule { options.y = int; }; }; }
        {
          options.s = lib.mkOption {
            type = np.submodule { config.y = 2; };
            default = { };
          };
        }
      ];
    };
    redeclaredAttrsOf = {
      read = c: c.s.k.y;
      modules = [
        {
          options.s = lib.mkOption {
            type = np.attrsOf (np.submodule { config.y = 2; });
            default = { };
          };
        }
        { options.s = lib.mkOption { type = np.attrsOf (np.submodule { options.y = int; }); }; }
        { s.k = { }; }
      ];
    };
    redeclaredFreeformSplit = {
      read = c: c.s.w;
      modules = [
        {
          options.s = lib.mkOption {
            type = np.submodule { config.w = 2; };
            default = { };
          };
        }
        { options.s = lib.mkOption { type = np.submodule { freeformType = np.attrsOf np.int; }; }; }
      ];
    };
    defDeclaresFn = {
      read = y;
      modules = [
        { options.s = lib.mkOption { type = np.submodule { config.y = 2; }; }; }
        { s = { ... }: { options.y = int; }; }
      ];
    };
    defDeclaresFnRedeclared = {
      read = y;
      modules = [
        { options.s = lib.mkOption { type = np.submodule { config.y = 2; }; }; }
        {
          options.s = lib.mkOption {
            type = np.submodule {
              options.x = lib.mkOption {
                type = np.int;
                default = 0;
              };
            };
          };
        }
        { s = { ... }: { options.y = int; }; }
      ];
    };
    # the freeformType joins below the walk's sight (a no-role key, the rider's stated boundary)
    freeformCheckDrop = {
      read = c: c.s.k;
      modules = [
        {
          options.s = lib.mkOption {
            type = np.submodule { freeformType = np.attrsOf np.port; };
            default = { };
          };
        }
        { options.s = lib.mkOption { type = np.submodule { freeformType = np.attrsOf np.int; }; }; }
        { s.k = 70000; }
      ];
    };
    # controls: green before the construction too
    redeclaredFreeform = {
      read = c: c.s.z + c.s.y;
      modules = [
        {
          options.s = lib.mkOption {
            type = np.submodule {
              freeformType = np.attrsOf np.int;
              config.z = 3;
            };
            default = { };
          };
        }
        {
          options.s = lib.mkOption {
            type = np.submodule {
              options.y = int;
              config.y = 2;
            };
          };
        }
      ];
    };
    single = {
      read = y;
      modules = [
        {
          options.s = lib.mkOption {
            type = np.submodule {
              options.y = int;
              config.y = 2;
            };
            default = { };
          };
        }
      ];
    };
    # `y` declared nowhere: both engines refuse (the message is on the error plane)
    undeclared = {
      read = y;
      modules = [
        {
          options.s = lib.mkOption {
            type = np.submodule { config.y = 2; };
            default = { };
          };
        }
        { options.s = lib.mkOption { type = np.submodule { options.x = int; }; }; }
      ];
    };
  };
  witnessExpected = {
    redeclared = 2;
    redeclaredSwapped = 2;
    redeclaredAttrsOf = 2;
    redeclaredFreeformSplit = 2;
    defDeclaresFn = 2;
    defDeclaresFnRedeclared = 2;
    freeformCheckDrop = 70000;
    redeclaredFreeform = 5;
    single = 2;
    undeclared = "refused";
  };

  # every route a poisoned nixpkgs submodule crosses by; each read is `s.y` = 2 in nixpkgs
  poisonedRoutes = {
    poisoned = [
      {
        options.s = lib.mkOption {
          type = poison (np.submodule { options.y = int; });
          default = { };
        };
      }
      { s.y = 2; }
    ];
    poisonedRedeclared = [
      {
        options.s = lib.mkOption {
          type = poison (np.submodule { config.y = 2; });
          default = { };
        };
      }
      { options.s = lib.mkOption { type = poison (np.submodule { options.y = int; }); }; }
    ];
    freeformPoisoned = [
      { freeformType = np.attrsOf (poison (np.submodule { options.y = int; })); }
      { s.y = 2; }
    ];
  };

  # a payload-null copy (`mkOptionType`'s default functor) of a module-set record, every other field
  # kept: no recogniser admits it, so only the root's mount serves it (den-hoag-2lmky)
  copy =
    r:
    lib.mkOptionType {
      name = "submodule";
      inherit (r)
        check
        merge
        getSubOptions
        getSubModules
        substSubModules
        nestedTypes
        emptyValue
        description
        ;
    };
  declaresFn = { ... }: { options.y = int; };
  declaresPath = ./_fixtures/declares-y.nix;
  setsY = np.submodule { config.y = 2; };
  shorthandSetsY = np.submoduleWith {
    modules = [ { config.y = 2; } ];
    shorthandOnlyDefinesConfig = true;
  };
  at = type: def: [
    { options.s = lib.mkOption { inherit type; }; }
    { s = def; }
  ];
  # a copy whose definition DECLARES what the type's module set sets, at an option root, as a
  # function and as a path, over `submodule` and over a shorthand `submoduleWith`; the same below a
  # stock `attrsOf`; and a copy whose `nestedTypes` is poisoned
  copyDeclares = {
    copyFn = [
      y
      (at (copy setsY) declaresFn)
    ];
    copyPath = [
      y
      (at (copy setsY) declaresPath)
    ];
    copyShorthandFn = [
      y
      (at (copy shorthandSetsY) declaresFn)
    ];
    copyShorthandPath = [
      y
      (at (copy shorthandSetsY) declaresPath)
    ];
    attrsOfCopyFn = [
      (c: c.s.k.y)
      (at (np.attrsOf (copy setsY)) { k = declaresFn; })
    ];
    copyPoisoned = [
      y
      (at (poison (copy setsY)) declaresFn)
    ];
  };
in
{
  flake.tests.submodule-laziness = {
    test-the-witness-serves-nixpkgs-value = {
      expr = builtins.mapAttrs (_: a: gen a.read a.modules) witness;
      expected = witnessExpected;
    };
    # the reference row: nixpkgs at the ci pin gives the values the witness row expects
    test-nixpkgs-gives-the-witness-values = {
      expr = builtins.mapAttrs (_: a: ref a.read a.modules) witness;
      expected = witnessExpected;
    };

    test-a-poisoned-submodule-is-never-forced = {
      expr = builtins.mapAttrs (_: gen y) poisonedRoutes // {
        attrsOfPoisoned = gen (c: c.s.k.y) [
          {
            options.s = lib.mkOption {
              type = np.attrsOf (poison (np.submodule { options.y = int; }));
              default = { };
            };
          }
          { s.k.y = 2; }
        ];
        genListOfPoisoned = gen (c: (builtins.head c.s).y) [
          {
            options.s = lib.mkOption {
              type = gm.types.listOf (poison (np.submodule { options.y = int; }));
              default = [ ];
            };
          }
          { s = [ { y = 2; } ]; }
        ];
        doorPoisoned = gen y [
          {
            options.s = lib.mkOption {
              type = gm.mkOptionType (poison (np.submodule { options.y = int; }));
              default = { };
            };
          }
          { s.y = 2; }
        ];
      };
      expected = {
        poisoned = 2;
        poisonedRedeclared = 2;
        freeformPoisoned = 2;
        attrsOfPoisoned = 2;
        genListOfPoisoned = 2;
        doorPoisoned = 2;
      };
    };
    # nixpkgs serves every poisoned route too: the poison is never nixpkgs' read
    test-nixpkgs-never-forces-the-poison = {
      expr = builtins.mapAttrs (_: ref y) poisonedRoutes;
      expected = {
        poisoned = 2;
        poisonedRedeclared = 2;
        freeformPoisoned = 2;
      };
    };

    # the `mkOptionType` door imports the record whole: a partial module set completed by a definition
    test-the-door-keeps-a-partial-module-set-unforced = {
      expr = gen y [
        { options.s = lib.mkOption { type = gm.mkOptionType (np.submodule { config.y = 2; }); }; }
        { s = { ... }: { options.y = int; }; }
      ];
      expected = 2;
    };

    # ★ THE STATED RESIDUE, pinned so a change to it is a red cell. (R1) a record stating
    # `payload.modules`, a non-null `getSubModules` AND a static role in `nestedTypes` is served as a
    # module set, its static role unread: a hand-built container whose substitution lies about its
    # roles, the same with a coherent substitution, and a nixpkgs submodule given an element by `//`.
    # (R3) a payload-null copy of a partial submodule is not recognised, and at an option root it is
    # mounted as nixpkgs' `fixupOptionType` mounts it: its rebuild, a stock submodule, is served.
    # Control: `fakeNesting` (the same container stating no `getSubModules`) is refused by name on
    # the error plane.
    test-the-residue-is-served-as-a-module-set = {
      expr = {
        fakeSubstLiar = gen (c: c.s) [
          {
            options.s = lib.mkOption {
              type = fakeList genSub { modules = [ ]; } // {
                getSubModules = [ ];
                substSubModules = _m: np.submodule { };
              };
              default = [ ];
            };
          }
          { s = [ { y = 2; } ]; }
        ];
        fakeSubstSelf = gen (c: c.s) [
          {
            options.s = lib.mkOption {
              type =
                let
                  s = fakeList genSub { modules = [ ]; } // {
                    getSubModules = [ ];
                    substSubModules = _m: s;
                  };
                in
                s;
              default = [ ];
            };
          }
          { s = [ { y = 2; } ]; }
        ];
        subWithElemType = gen y [
          {
            options.s = lib.mkOption {
              type = np.submodule { options.y = int; } // {
                nestedTypes.elemType = genSub;
              };
              default = { };
            };
          }
          { s.y = 2; }
        ];
        copyDefDeclaresFn = gen y [
          {
            options.s = lib.mkOption {
              type =
                let
                  sub = np.submodule { config.y = 2; };
                in
                lib.mkOptionType {
                  name = "submodule";
                  inherit (sub)
                    check
                    merge
                    getSubOptions
                    getSubModules
                    substSubModules
                    nestedTypes
                    emptyValue
                    description
                    ;
                };
            };
          }
          { s = { ... }: { options.y = int; }; }
        ];
      };
      expected = {
        fakeSubstLiar = "refused";
        fakeSubstSelf = [ { y = 2; } ];
        subWithElemType = 2;
        copyDefDeclaresFn = 2;
      };
    };

    # A copied submodule is mounted at the root as nixpkgs mounts it, before any read of the record,
    # so a definition completing its module set is served nixpkgs' value (den-hoag-2lmky).
    test-a-copied-submodule-is-mounted-before-any-read = {
      expr = builtins.mapAttrs (_: a: genL (builtins.elemAt a 0) (builtins.elemAt a 1)) copyDeclares;
      expected = builtins.mapAttrs (_: a: ref (builtins.elemAt a 0) (builtins.elemAt a 1)) copyDeclares;
    };
    # the reference row: nixpkgs serves every copy cell
    test-nixpkgs-serves-every-copy-cell = {
      expr = builtins.mapAttrs (_: a: ref (builtins.elemAt a 0) (builtins.elemAt a 1)) copyDeclares;
      expected = builtins.mapAttrs (_: _: 2) copyDeclares;
    };

    # ★ THE LAZINESS'S BLINDNESS INSIDE `freeformType`, pinned (ADR-0014's rider: a stated boundary).
    # A gen nesting type under a recognised submodule's `freeformType` is neither threaded nor refused:
    # it is evaluated standalone through the bridge, as a declared sub-option's is. Under a stock `uniq`
    # this replaces OQ11 (d)'s named refusal with a silent standalone evaluation; both equal nixpkgs.
    test-a-freeform-gen-nesting-type-serves-through-the-bridge = {
      expr =
        let
          freeformGen = np.submodule { freeformType = np.attrsOf genSub; };
          at = type: [
            {
              options.s = lib.mkOption {
                inherit type;
                default = { };
              };
            }
            { s.k.y = 2; }
          ];
        in
        {
          freeformGenSub = gen (c: c.s.k.y) (at freeformGen);
          uniqFreeformGenSub = gen (c: c.s.k.y) (at (np.uniq freeformGen));
        };
      expected = {
        freeformGenSub = 2;
        uniqFreeformGenSub = 2;
      };
    };
    # The lint scans no recognised submodule's `freeformType`: a `functionTo` there is not flagged.
    # Control: the same type as a plain element is.
    test-the-lint-does-not-scan-a-submodule-freeformType = {
      expr =
        let
          lintOf = t: map (f: f.kind) (gm.lint [ { options.s = lib.mkOption { type = t; }; } ]);
        in
        {
          lintFreeformFn = lintOf (np.submodule { freeformType = np.attrsOf (np.functionTo np.int); });
          lintCtl = lintOf (np.attrsOf (np.functionTo np.int));
        };
      expected = {
        lintFreeformFn = [ ];
        lintCtl = [ "function-to" ];
      };
    };
  };
}
