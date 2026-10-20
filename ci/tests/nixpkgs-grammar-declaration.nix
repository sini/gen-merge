# A DECLARATION IN NIXPKGS' GRAMMAR READING ITS OWN EVALUATION AT DECLARATION TIME (den-hoag-2tna3).
# A module not declared gen grammar reads `config`, `options` and module arguments while its
# declarations are folded, as nixpkgs' lazy fold lets it: kubernetes' `mkKubeConfigOptions`, grav's
# `mkPackageOption` default, `misc/nixpkgs.nix`'s `isDefined`, network-interfaces' `with utils;`.
# gen-merge forces what nixpkgs' fold forces, so each cell runs one module set through the engine
# and through nixpkgs' `lib.evalModules` and reads the same projection off both (ADR-0039's serve
# half). A declaration whose own top type constructor is gen's keeps ADR-0033's stratum refusal;
# those cells, with their text, are in `ci/tests-error.nix` (`nixpkgs-grammar-declaration`), and the
# outcomes no `tryEval` can read (nixpkgs' abort and infinite recursion) in `ci/tests-process.nix`.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  lib = nixpkgsLib;
  inherit (lib) mkOption types optionalAttrs;
  gm = genMerge;
  t = gm.types;
  gen = mods: (gm.evalModuleTree { specialArgs = { inherit lib; }; } mods).config;
  cell = mods: r: {
    expr = r (gen mods);
    expected = r (lib.evalModules { modules = mods; }).config;
  };
  # A gen-merge refusal by name is catchable; nixpkgs aborts on the same module set, so there is no
  # reference value and the cell reads catchability alone.
  caught = mods: r: {
    expr = (builtins.tryEval (builtins.deepSeq (r (gen mods)) null)).success;
    expected = false;
  };
  v = {
    options.v = mkOption {
      type = types.int;
      default = 0;
    };
  };
  release = {
    options.v = mkOption {
      type = types.str;
      default = "26.11";
    };
  };
  # grav's shape: `mkPackageOption`'s `default != null` reads a default chosen by config.
  grav = mk: ty: [
    release
    ({ config, ... }: {
      options.p = mk { type = ty; } // optionalAttrs (config.v == "26.11") { default = "grav_2"; };
    })
  ];
  # nixpkgs' lib/tests/modules/option.nix (modules.sh's `anOption` and `aBadOptionDef`): a
  # declaration that IS a config value.
  optionNix =
    { config, options, ... }:
    {
      options = {
        theOption = mkOption { type = types.optionDeclaration; };
        anOption = config.theOption;
        aBadOptionDef = mkOption { type = types.optionDeclaration; };
      };
      config = {
        theOption = mkOption { type = types.int; };
        anOption = 10;
        aBadOptionDef = options.theOption;
      };
    };
  # a nested evaluation whose inner nixpkgs-grammar option `p` reads config at declaration time;
  # `seenP` / `seenV` read the declaring files of that node and of a plain sibling
  inner =
    { config, options, ... }:
    {
      options.v = mkOption {
        type = types.str;
        default = "26.11";
      };
      options.p =
        mkOption { type = types.str; } // optionalAttrs (config.v == "26.11") { default = "grav_2"; };
      options.seenP = mkOption { default = options.p.declarations; };
      options.seenV = mkOption { default = options.v.declarations; };
    };
  nested = submodule: [
    {
      _file = "decl.nix";
      options.s = mkOption {
        type = submodule inner;
        default = { };
      };
    }
  ];
  nm = i: "p${toString i}";
  # x read under d held call frames
  held =
    d: x:
    let
      f = n: if n == 0 then x else f (n - 1) && true;
    in
    f d;
  # p_1 … p_k, the presence of p_i's default reads p_(i-1) under d held frames
  dchain =
    k: d:
    [
      v
      {
        options.${nm 0} = mkOption {
          type = types.int;
          default = 0;
        };
      }
    ]
    ++ map (
      i:
      { config, ... }:
      {
        options.${nm i} =
          mkOption { type = types.int; }
          // optionalAttrs (held d (config.${nm (i - 1)} >= 0)) { default = i; };
      }
    ) (lib.range 1 k);
  # a declaration-time self-cycle whose read sits under d held frames
  deepcyc = mk: bool: d: [
    (
      { config, ... }:
      let
        f = n: if n == 0 then config.c else f (n - 1) || false;
      in
      {
        options.c =
          mk {
            type = bool;
            default = true;
          }
          // (if f d then { } else { });
      }
    )
  ];
  # n declarations, p_i's default chosen by reading p_(i-1)
  fanChain =
    n:
    [ v ]
    ++ [
      {
        options.${nm 0} = mkOption {
          type = types.int;
          default = 0;
        };
      }
    ]
    ++ map (
      i:
      { config, ... }:
      {
        options.${nm i} =
          mkOption { type = types.int; } // optionalAttrs (config.${nm (i - 1)} >= 0) { default = i; };
      }
    ) (lib.range 1 n);
in
{
  flake.tests.nixpkgs-grammar-declaration = {
    test-an-option-that-is-a-config-value = cell [ optionNix ] (c: c.anOption);
    # kubernetes' shape: a declaration built by a function read out of config
    test-a-declaration-built-by-a-config-function = cell [
      {
        options.top.lib = mkOption {
          type = types.attrs;
          default = { };
        };
        config.top.lib.mk =
          p:
          mkOption {
            type = types.str;
            default = p;
          };
      }
      ({ config, ... }: { options.k = config.top.lib.mk "srv"; })
    ] (c: c.k);
    test-a-default-chosen-by-config = cell (grav mkOption types.str) (c: c.p);
    # misc/nixpkgs.nix's read: an evaluated field of an option record
    test-a-declaration-reading-is-defined = cell [
      { options.a = mkOption { type = types.int; }; }
      (
        { options, ... }:
        {
          options.b = mkOption { type = types.int; } // optionalAttrs options.a.isDefined { default = 2; };
        }
      )
      { a = 1; }
    ] (c: c.b);
    test-presence-moving-with-config = cell [
      { options.a = mkOption { type = types.int; }; }
      (
        { config, ... }:
        {
          options.v =
            if config.a == 1 then
              mkOption {
                type = types.int;
                default = 3;
              }
            else
              { };
        }
      )
      { a = 1; }
    ] (c: c.v);
    test-presence-moving-with-config-absent = cell [
      { options.a = mkOption { type = types.int; }; }
      (
        { config, ... }:
        {
          options.v =
            if config.a == 1 then
              mkOption {
                type = types.int;
                default = 3;
              }
            else
              { };
        }
      )
      { a = 2; }
    ] (c: c.a);
    test-presence-moving-with-an-argument-value = cell [
      { _module.args.u.leaf = true; }
      (
        { u, ... }:
        {
          options.p =
            if u.leaf then
              mkOption {
                type = types.int;
                default = 5;
              }
            else
              { };
        }
      )
    ] (c: c.p);
    test-presence-moving-with-an-argument-key-set = cell [
      { _module.args.u.leaf = true; }
      (
        { u, ... }:
        {
          options.p =
            if u ? leaf then
              mkOption {
                type = types.int;
                default = 5;
              }
            else
              { };
        }
      )
    ] (c: c.p);
    # an option or a subtree, by an argument's value
    test-leafness-chosen-by-an-argument = cell [
      { _module.args.u.x = false; }
      (
        { u, ... }:
        {
          options.k =
            if u.x then
              mkOption {
                type = types.int;
                default = 1;
              }
            else
              {
                sub = mkOption {
                  type = types.int;
                  default = 2;
                };
              };
        }
      )
    ] (c: c.k);
    # network-interfaces.nix's `with lib; with utils;`: a bare `mkOption` is looked up in the
    # argument first, so the node's WHNF reads that argument's key set
    test-a-bare-mk-option-under-with-an-argument = cell [
      { _module.args.u.x = 1; }
      ./_fixtures/with-argument-mk-option.nix
    ] (c: c.p);
    test-a-leaf-content-reading-an-argument = cell [
      { _module.args.u.d = 7; }
      (
        { u, ... }:
        {
          options.p = mkOption {
            type = types.int;
            default = u.d;
          };
        }
      )
    ] (c: c.p);
    # the grammar decided by the read: a nixpkgs declaration on the branch taken
    test-a-grammar-chosen-by-config = cell [
      {
        options.g = mkOption {
          type = types.bool;
          default = false;
        };
      }
      (
        { config, ... }:
        {
          options.p =
            if config.g then
              gm.mkOption {
                type = t.str;
                default = "gen";
              }
            else
              mkOption {
                type = types.str;
                default = "np";
              };
        }
      )
    ] (c: c.p);
    # placement: the classifier reads the declaration's own top constructor
    test-a-nixpkgs-declaration-reading-a-gen-typed-option = cell [
      {
        options.v = gm.mkOption {
          type = t.str;
          default = "26.11";
        };
      }
      ({ config, ... }: {
        options.p =
          mkOption { type = types.str; } // optionalAttrs (config.v == "26.11") { default = "grav_2"; };
      })
    ] (c: c.p);
    test-a-nixpkgs-container-over-a-gen-element = cell [
      release
      (
        { config, ... }:
        {
          options.p =
            mkOption { type = types.attrsOf t.int; } // optionalAttrs (config.v == "26.11") { default.a = 1; };
        }
      )
    ] (c: c.p);
    test-a-gen-element-seventy-containers-deep = cell [
      release
      (
        { config, ... }:
        {
          options.p =
            mkOption { type = lib.foldl' (x: _: types.listOf x) t.int (lib.range 1 70); }
            // optionalAttrs (config.v == "26.11") { default = [ ]; };
        }
      )
    ] (c: c.p);
    test-a-gen-element-three-containers-deep = cell [
      release
      (
        { config, ... }:
        {
          options.p =
            mkOption { type = lib.foldl' (x: _: types.listOf x) t.int (lib.range 1 3); }
            // optionalAttrs (config.v == "26.11") { default = [ ]; };
        }
      )
    ] (c: c.p);
    test-a-nixpkgs-submodule-with-a-gen-typed-option = cell [
      release
      (
        { config, ... }:
        {
          options.p =
            mkOption {
              type = types.submodule {
                options.x = gm.mkOption {
                  type = t.int;
                  default = 1;
                };
              };
            }
            // optionalAttrs (config.v == "26.11") { default = { }; };
        }
      )
    ] (c: c.p);
    # pkgs.formats' shape: a recursive nixpkgs type
    test-a-recursive-nixpkgs-type = cell [
      {
        options.v = mkOption {
          type = types.bool;
          default = true;
        };
      }
      (
        { config, ... }:
        let
          vt = types.nullOr (
            types.oneOf [
              types.int
              (types.attrsOf vt)
              (types.listOf vt)
            ]
          );
        in
        {
          options.p = mkOption { type = vt; } // optionalAttrs config.v { default.a = 1; };
        }
      )
    ] (c: c.p);
    test-gen-mk-option-carrying-a-nixpkgs-type = cell (grav gm.mkOption types.str) (c: c.p);
    test-gen-mk-option-with-no-type = cell [
      release
      ({ config, ... }: {
        options.p = gm.mkOption { } // optionalAttrs (config.v == "26.11") { default = "grav_2"; };
      })
    ] (c: c.p);
    test-a-nixpkgs-null-or-over-a-gen-element = cell (grav mkOption (types.nullOr t.str)) (c: c.p);
    test-a-group-holding-a-non-option-member = cell [
      release
      (
        { config, ... }:
        {
          options.g = {
            a = mkOption {
              type = types.int;
              default = 1;
            };
            b = 5;
          }
          // optionalAttrs (config.v == "26.11") { };
        }
      )
    ] (c: c.g.a);
    test-a-group-holding-a-non-option-member-control = cell [
      {
        options.g = {
          a = mkOption {
            type = types.int;
            default = 1;
          };
          b = 5;
        };
      }
    ] (c: c.g.a);
    # the same reads inside a nested gen evaluation, and the declaring files of a yielded node
    test-a-nested-gen-evaluation = {
      expr = (gen (nested t.submodule)).s.p;
      expected = (lib.evalModules { modules = nested types.submodule; }).config.s.p;
    };
    test-a-nested-yielded-node-declarations = {
      expr = (gen (nested t.submodule)).s.seenP;
      expected = (lib.evalModules { modules = nested types.submodule; }).config.s.seenP;
    };
    test-a-nested-plain-node-declarations = {
      expr = (gen (nested t.submodule)).s.seenV;
      expected = (lib.evalModules { modules = nested types.submodule; }).config.s.seenV;
    };
    # gen grammar reading a module argument (D1): the key set is computed with arguments refused,
    # the leaf with arguments from strictly earlier passes
    test-gen-a-bare-mk-option-under-with-an-argument = {
      expr =
        (gen [
          { _module.args.u.x = 1; }
          (import ./_fixtures/with-argument-gen-mk-option.nix gm)
        ]).p;
      expected = 1;
    };
    test-gen-a-whnf-reading-an-argument = {
      expr =
        (gen [
          { _module.args.u.d = true; }
          ({ u, ... }: { options.p = gm.mkOption { type = t.int; } // optionalAttrs u.d { default = 7; }; })
        ]).p;
      expected = 7;
    };
    test-gen-presence-moving-with-an-argument = {
      expr =
        (gen [
          { _module.args.u.leaf = true; }
          (
            { u, ... }:
            {
              options.p =
                if u.leaf then
                  gm.mkOption {
                    type = t.int;
                    default = 5;
                  }
                else
                  { };
            }
          )
        ]).p;
      expected = 5;
    };
    # value reads of pending nodes: every presence reads config.v, every default the previous node
    test-a-value-chain-of-pending-nodes = cell (
      [
        v
        {
          options.${nm 0} = mkOption {
            type = types.int;
            default = 0;
          };
        }
      ]
      ++ map (
        i:
        { config, ... }:
        {
          options.${nm i} =
            mkOption {
              type = types.int;
              default = config.${nm (i - 1)} + 1;
            }
            // optionalAttrs (config.v >= 0) { };
        }
      ) (lib.range 1 8)
    ) (c: c.${nm 8});
    # chains of declaration-time reads, longer than 300 staged passes would reach
    test-a-chain-of-290-declaration-reads = cell (fanChain 290) (c: c.${nm 290});
    test-a-chain-of-310-declaration-reads = cell (fanChain 310) (c: c.${nm 310});
    # a chain recurses inside one resolution level, as nixpkgs' chain recurses inside its one fold
    # (gate v0 C2): 80 reads under 100 held frames each, and 400 reads under none
    test-a-chain-of-80-reads-under-100-held-frames = cell (dchain 80 100) (c: c.${nm 80});
    test-a-chain-of-400-reads = cell (dchain 400 0) (c: c.${nm 400});
    # an unread pending node in a group with no definitions is never forced, as nixpkgs' unmatched
    # check never forces it: its abort stays unread
    test-an-unread-node-in-a-definition-free-group-stays-unforced = cell [
      v
      (
        { config, ... }:
        {
          options.q.x =
            mkOption { type = types.int; }
            // (if config.v >= 0 then abort "unread declaration aborted" else { });
        }
      )
      ({ config, ... }: {
        options.z = mkOption { type = types.int; } // optionalAttrs (config.v >= 0) { default = 5; };
      })
    ] (c: c.z);
    test-a-declaration-reading-nothing = cell [
      {
        options.p = mkOption {
          type = types.str;
          default = "d";
        };
      }
    ] (c: c.p);

    # cycles nixpkgs aborts on: gen-merge refuses them by name, catchably
    test-a-nixpkgs-declaration-reading-its-own-value-is-caught = caught [
      (
        { config, ... }:
        {
          options.c =
            mkOption {
              type = types.bool;
              default = true;
            }
            // (if config.c then { } else { });
        }
      )
    ] (c: c.c);
    test-a-gen-declaration-reading-its-own-value-is-caught = caught [
      (
        { config, ... }:
        {
          options.c =
            gm.mkOption {
              type = t.bool;
              default = true;
            }
            // (if config.c then { } else { });
        }
      )
    ] (c: c.c);
    test-a-mutual-declaration-cycle-is-caught = caught [
      ({ config, ... }: {
        options.p = mkOption { type = types.bool; } // optionalAttrs config.q { default = true; };
      })
      ({ config, ... }: {
        options.q = mkOption { type = types.bool; } // optionalAttrs config.p { default = true; };
      })
    ] (c: c.p);
    test-a-read-reaching-a-gen-self-cycle-is-caught = caught [
      (
        { config, ... }:
        {
          options.y =
            gm.mkOption {
              type = t.bool;
              default = true;
            }
            // (if config.y then { } else { });
        }
      )
      ({ config, ... }: {
        options.p = mkOption { type = types.bool; } // optionalAttrs config.y { default = false; };
      })
    ] (c: c.p);
    test-a-key-set-reading-config-is-caught = caught [
      (
        { config, ... }:
        {
          options = {
            flag = mkOption {
              type = types.bool;
              default = true;
            };
          }
          // (
            if config.flag then
              {
                extra = mkOption {
                  type = types.int;
                  default = 1;
                };
              }
            else
              { }
          );
        }
      )
    ] (c: c.flag);
    # a self-cycle under d held frames, both grammars
    test-a-self-cycle-under-held-frames-is-caught = {
      expr =
        lib.concatMap
          (
            d:
            map (g: (builtins.tryEval (gen (deepcyc g.mk g.bool d)).c).success) [
              {
                mk = mkOption;
                inherit (types) bool;
              }
              {
                mk = gm.mkOption;
                inherit (t) bool;
              }
            ]
          )
          [
            10
            15
            30
            100
            300
          ];
      expected = lib.genList (_: false) 10;
    };
    # a gen self-cycle reached behind a chain of 80 reads under 100 held frames
    test-a-gen-self-cycle-behind-a-chain-is-caught = caught (
      dchain 80 100
      ++ [
        (
          { config, ... }:
          {
            options.g =
              gm.mkOption {
                type = t.bool;
                default = true;
              }
              // (if config.${nm 80} >= 0 && config.g then { } else { });
          }
        )
      ]
    ) (c: c.g);
  };
}
