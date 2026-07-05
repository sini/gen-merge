# Shared parity corpus (design spec §3) — the P-parameterized fixture set exercised by BOTH the
# evalModules-equivalence oracle (oracle.nix, run byte-for-byte on both engines) AND the
# portable-subset lint (lint.nix, asserted to accept every fixture). One source of truth so
# "the lint accepts the whole oracle corpus" is mechanically true, not a re-declared approximation.
#
# Each fixture :: P -> [ modules ], where P is the constructor pack
# `{ mkOption; types; mkMerge; mkIf; mkForce; mkDefault; }`. Path leaves resolve relative to THIS
# file's directory (`./plain-config.nix`), so both consumers reach the same ctor-free leaf.
# `_`-prefixed, so import-tree skips it (it is not a test module — mkCi's flakeModule.nix).
{
  typed-and-priority = P: [
    {
      options.a = P.mkOption {
        type = P.types.str;
        default = "da";
      };
    }
    {
      options.b = P.mkOption {
        type = P.types.int;
        default = 0;
      };
    }
    {
      a = P.mkForce "forced";
      b = 7;
    }
    { a = P.mkDefault "weak"; }
  ];
  freeform = P: [
    {
      freeformType = P.types.lazyAttrsOf P.types.str;
      options.known = P.mkOption {
        type = P.types.str;
        default = "k";
      };
    }
    {
      known = "K";
      extra1 = "e1";
    }
    { extra2 = "e2"; }
  ];
  # WIDE freeform coalescing — the same undeclared key `shared` defined across THREE modules at
  # different priorities (mkDefault < bare < mkForce), plus per-module-unique keys. Pins that the
  # per-module coalescing of unmatched defs preserves priority resolution through the freeform path
  # (mkForce wins `shared`) AND absorbs disjoint keys from every module.
  freeform-multi-priority = P: [
    { freeformType = P.types.lazyAttrsOf P.types.str; }
    {
      shared = P.mkDefault "weak";
      only1 = "a";
    }
    {
      shared = P.mkForce "forced";
      only2 = "b";
    }
    {
      shared = "plain";
      only3 = "c";
    }
  ];
  # LIST-typed freeform values across modules — the same undeclared key `xs` (a `listOf str`) defined
  # in three modules. nixpkgs concatenates freeform defs in reverse-module order (`[c b a]`); pins
  # that coalescing emits per-module defs in that same order so the concat is byte-identical (the
  # order-sensitive twin of `listof-reverse`, through the freeform absorption path).
  freeform-list-order = P: [
    { freeformType = P.types.lazyAttrsOf (P.types.listOf P.types.str); }
    { xs = [ "a" ]; }
    { xs = [ "b" ]; }
    { xs = [ "c" ]; }
  ];
  # NESTED freeform depth — undeclared keys absorbed UNDER a declared group (`grp` is declared via a
  # leaf `grp.declared`, so `grp.free*` are unmatched at depth 2). Pins that the unmatched-path
  # reshaping (`setAttrByPath` at depth > 1) survives per-module coalescing — each module's deep keys
  # fold into one nested subtree via `recursiveUpdate` WITHIN that module — and that declared wins
  # over freeform at the shared `grp` node. Two modules contribute overlapping nested freeform keys
  # (incl. an mkForce on `grp.freeA`), so per-key resolution ACROSS modules also rides the freeform
  # path.
  freeform-nested-depth = P: [
    {
      freeformType = P.types.lazyAttrsOf (P.types.lazyAttrsOf P.types.str);
      options.grp.declared = P.mkOption {
        type = P.types.str;
        default = "d";
      };
    }
    {
      grp.declared = "set";
      grp.freeA = "fa";
    }
    {
      grp.freeB = "fb";
      grp.freeA = P.mkForce "fa-forced";
    }
  ];
  submodule-name-selfref = P: [
    {
      options.entries = P.mkOption {
        default = { };
        type = P.types.attrsOf (
          P.types.submodule (
            { name, config, ... }:
            {
              config._module.args.self = config;
              options.n = P.mkOption {
                type = P.types.str;
                default = name;
              };
              options.label = P.mkOption {
                type = P.types.str;
                default = "L-" + config.n;
              };
            }
          )
        );
      };
    }
    {
      entries.foo = { };
      entries.bar = {
        n = "custom";
      };
    }
  ];
  listof-reverse = P: [
    {
      options.xs = P.mkOption {
        type = P.types.listOf P.types.str;
        default = [ ];
      };
    }
    {
      xs = [
        "a"
        "b"
      ];
    }
    { xs = [ "c" ]; }
  ];
  nested-submodule = P: [
    {
      options.outer = P.mkOption {
        default = { };
        type = P.types.submodule {
          options.inner = P.mkOption {
            default = { };
            type = P.types.submodule {
              options.v = P.mkOption {
                type = P.types.int;
                default = 1;
              };
            };
          };
        };
      };
    }
    { outer.inner.v = 42; }
  ];
  mkif-mkmerge = P: [
    {
      options.a = P.mkOption {
        type = P.types.str;
        default = "d";
      };
    }
    {
      config = P.mkMerge [
        (P.mkIf false { a = "no"; })
        (P.mkIf true { a = "yes"; })
      ];
    }
  ];
  # merge-aware combinators — byte-identical to nixpkgs `lib.types.{nullOr,either,oneOf}`.
  nullor-combinator = P: [
    {
      options.unset = P.mkOption {
        type = P.types.nullOr P.types.str;
        default = null;
      };
      options.set = P.mkOption {
        type = P.types.nullOr P.types.str;
        default = null;
      };
      options.nested = P.mkOption {
        type = P.types.nullOr (P.types.listOf P.types.int);
        default = null;
      };
    }
    {
      set = "v";
      nested = [
        1
        2
      ];
    }
  ];
  either-combinator = P: [
    {
      options.s = P.mkOption { type = P.types.either P.types.str P.types.int; };
      options.i = P.mkOption { type = P.types.either P.types.str P.types.int; };
    }
    {
      s = "left";
      i = 7;
    }
  ];
  oneof-combinator = P: [
    {
      options.v = P.mkOption {
        type = P.types.oneOf [
          P.types.str
          P.types.int
          P.types.bool
        ];
      };
    }
    { v = true; }
  ];
  # nested/structured option-declaration paths — `options.a.b.c = mkOption {…}` must build a
  # nested option TREE (nixpkgs `lib.evalModules` auto-nests), so `config.a.b.c` resolves and a
  # SECOND module's `options.a.b.d` merges by RECURSING beside the first (not `//`-clobbering `b`).
  # This is the prerequisite for composing den-shaped configs (`options.den.schema/hosts/classes`).
  nested-options = P: [
    {
      options.a.b.c = P.mkOption {
        type = P.types.int;
        default = 1;
      };
    }
    { config.a.b.c = 7; }
    {
      options.a.b.d = P.mkOption {
        type = P.types.str;
        default = "x";
      };
    }
  ];
  # path-leaf composition — a BARE path (`./plain-config.nix`) sitting directly in the module list
  # must be `import`ed and composed (nixpkgs `lib.evalModules` imports a path leaf; the enabler for a
  # consumer loading `(import-tree ./dir).files`, a bare path LIST). The path file is ctor-free
  # (engine-agnostic `{ config.value = 42; }`); an inline `P`-param module DECLARES `value` so nixpkgs'
  # undeclared-option check is satisfied. `config.value == 42` byte-identical both engines.
  path-leaf = P: [
    {
      options.value = P.mkOption {
        type = P.types.int;
        default = 0;
      };
    }
    ./plain-config.nix
  ];
  # path-INSIDE-`imports` — the same path reached through another module's `imports = [ ./p.nix ]`
  # (nixpkgs recurses into `imports`, importing each path). `collectModules` must `callM` it too.
  path-in-imports = P: [
    {
      options.value = P.mkOption {
        type = P.types.int;
        default = 0;
      };
      imports = [ ./plain-config.nix ];
    }
  ];
  # the real gen-aspects `aspectSubmodule` shape: keyed collection of submodules, each with a
  # self-referential `config._module.args.aspect = config`, structural options (name / includes as
  # listOf), AND a freeform of nested string keys — the integrated C2 surface, byte-identical.
  aspect-shaped = P: [
    {
      options.aspects = P.mkOption {
        default = { };
        type = P.types.attrsOf (
          P.types.submodule (
            {
              name,
              config,
              aspect,
              ...
            }:
            {
              config._module.args.aspect = config;
              freeformType = P.types.lazyAttrsOf P.types.str;
              options.name = P.mkOption {
                type = P.types.str;
                default = name;
              };
              options.includes = P.mkOption {
                type = P.types.listOf P.types.str;
                default = [ ];
              };
              # reads the self-ref module ARG `aspect` (= config), proving the fixpoint binding
              options.selfName = P.mkOption {
                type = P.types.str;
                default = aspect.name;
              };
            }
          )
        );
      };
    }
    {
      aspects.web = {
        includes = [ "base" ];
        extra = "x";
      };
      aspects.db.includes = [
        "base"
        "pg"
      ];
    }
  ];
}
