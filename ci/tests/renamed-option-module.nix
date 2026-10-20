# nixpkgs' RENAMED-OPTION FAMILY on the engine — `mkRenamedOptionModule`, `mkRenamedOptionModuleWith`
# and `mkAliasOptionModule`, all three `doRename`, which declares the alias leaf as
# `mkOption { … } // optionalAttrs (toType != null) { type = toType; }` with `toType` read from
# `options.<to>.type`. The leaf's WHNF reads another declaration, so the declaration guard's poisoned
# fold cannot resolve it; the guard's staged passes (`stagedDeclarations`, den-hoag-9oc7y) re-try it
# against the declarations of strictly earlier passes, where the target has resolved. Each cell runs
# one module set through the engine and through nixpkgs' `lib.evalModules`, and reads the same
# projection off both (ADR-0039's serve half: gen serves nixpkgs' value where nixpkgs serves).
#
# The defining modules carry `_file`, so the rename warning's file label is that name on both
# engines; an anonymous module's label differs between them (den-hoag-z9dby's class, not this one's).
# A genuine cycle stays refused by name: those cells are in `ci/tests-error.nix`
# (`renamed-option-module`) and `ci/tests-process.nix`.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  lib = nixpkgsLib;
  inherit (lib) mkOption types;
  R = lib.mkRenamedOptionModule;
  A = lib.mkAliasOptionModule;
  def = v: {
    _file = "def.nix";
    config = v;
  };
  # A rename that is itself the source of a definition (a chain's middle link) labels it with the
  # file of the module importing it.
  named = f: m: {
    _file = f;
    imports = [ m ];
  };

  # nixpkgs' own shape: `doRename` writes `warnings` and reads them, so they are declared.
  base = {
    options.warnings = mkOption {
      type = types.listOf types.str;
      default = [ ];
    };
    options.a = mkOption { type = types.int; };
  };

  read = extra: c: {
    inherit (c) a warnings;
    extra = extra c;
  };
  cell = extra: mods: {
    expr = read extra (genMerge.evalModuleTree { } mods).config;
    expected = read extra (lib.evalModules { modules = mods; }).config;
  };
  none = _: null;
  argTyped =
    { u, ... }:
    {
      options.v = mkOption { type = u.t; };
    };
  argDefines = {
    _file = "args.nix";
    _module.args.u.t = types.int;
  };
  sub = s: {
    options.s = mkOption {
      type = s {
        imports = [
          { options.x = mkOption { type = types.int; }; }
          (A [ "y" ] [ "x" ])
        ];
      };
    };
  };
in
{
  flake.tests.renamed-option-module = {
    test-renamed = cell none [
      base
      (R [ "b" ] [ "a" ])
      (def { b = 1; })
    ];
    test-renamed-with = cell none [
      base
      (lib.mkRenamedOptionModuleWith {
        from = [ "b" ];
        to = [ "a" ];
        sinceRelease = 2405;
      })
      (def { b = 1; })
    ];
    test-alias = cell none [
      base
      (A [ "b" ] [ "a" ])
      (def { b = 1; })
    ];
    # The rename shares a group with its target.
    test-renamed-sibling = cell (c: c.s.new) [
      base
      { options.s.new = mkOption { type = types.int; }; }
      (R [ "s" "old" ] [ "s" "new" ])
      (def {
        a = 1;
        s.old = 4;
      })
    ];
    # The alias inside gen's own `submodule`, whose nested tree is this engine, against nixpkgs'
    # `submodule` on the reference side.
    test-alias-inside-a-gen-submodule = {
      expr =
        read (c: c.s.x)
          (genMerge.evalModuleTree { } [
            base
            (sub genMerge.types.submodule)
            (def {
              a = 1;
              s.y = 9;
            })
          ]).config;
      expected =
        read (c: c.s.x)
          (lib.evalModules {
            modules = [
              base
              (sub types.submodule)
              (def {
                a = 1;
                s.y = 9;
              })
            ];
          }).config;
    };
    # c → b → a resolves in two passes, and in either presentation order: a pass is a node's rank in
    # the read relation, not a position in the module list.
    test-chain = cell none [
      base
      (named "c-to-b.nix" (R [ "c" ] [ "b" ]))
      (R [ "b" ] [ "a" ])
      (def { c = 1; })
    ];
    test-chain-permuted = cell none [
      (def { c = 1; })
      (R [ "b" ] [ "a" ])
      (named "c-to-b.nix" (R [ "c" ] [ "b" ]))
      base
    ];
    # The target is declared by a module that takes the `options` formal and reads it only in
    # `config`: a staging decided by formals would put the target in a later pass than the rename.
    test-target-declared-by-an-options-formal-module = cell (c: c.a2) [
      base
      (
        { options, ... }:
        {
          options.a2 = mkOption { type = types.int; };
          config.warnings = lib.optional (options ? zz) "never";
        }
      )
      (R [ "b" ] [ "a2" ])
      (def {
        a = 1;
        b = 5;
      })
    ];
    # The target's type reads a module argument that another module defines (nixpkgs' `systemd.nix`
    # under `with utils;`), so the alias resolves once an earlier pass's declarations carry the
    # arguments their own modules define. The chain c → b → a resolves one link per pass beside it.
    test-a-rename-onto-a-type-read-from-a-module-argument = cell (c: c.v) [
      base
      (
        { u, ... }:
        {
          options.v = mkOption { type = u.t; };
        }
      )
      {
        _file = "args.nix";
        _module.args.u.t = types.int;
      }
      (R [ "w" ] [ "v" ])
      (named "c-to-b.nix" (R [ "c" ] [ "b" ]))
      (R [ "b" ] [ "a" ])
      (def {
        c = 1;
        w = 5;
      })
    ];
    # The same alone: no other node is pending, so the alias's hops through the argument are the
    # only passes it reads.
    test-a-lone-rename-onto-a-type-read-from-a-module-argument = cell (c: c.v) [
      base
      argTyped
      argDefines
      (R [ "w" ] [ "v" ])
      (def {
        a = 1;
        w = 5;
      })
    ];
    # The target's module reads the argument under `with`, nixpkgs' `systemd.nix` shape.
    test-a-rename-onto-a-declaration-under-with-an-argument = cell (c: c.v) [
      base
      (
        { u, ... }:
        with u;
        {
          options.v = mkOption { type = t; };
        }
      )
      argDefines
      (R [ "w" ] [ "v" ])
      (def {
        a = 1;
        w = 5;
      })
    ];
    # The argument the target's type reads is itself defined from a second argument.
    test-a-rename-onto-a-type-read-through-an-argument-chain = cell (c: c.v) [
      base
      argTyped
      (
        { q, ... }:
        {
          _module.args.u = q;
        }
      )
      { _module.args.q.t = types.int; }
      (R [ "w" ] [ "v" ])
      (def {
        a = 1;
        w = 5;
      })
    ];
    # The target's type is read from a third option's declaration.
    test-a-rename-onto-a-type-read-from-another-declaration = cell (c: c.v) [
      base
      (
        { options, ... }:
        {
          options.v = mkOption { type = options.third.type; };
        }
      )
      { options.third = mkOption { type = types.int; }; }
      (R [ "w" ] [ "v" ])
      (def {
        a = 1;
        w = 5;
      })
    ];
    # The hops run through the elements of one argument: element i reads element i - 1, so the
    # passes the alias needs grow with the list, not with the tree's leaves or arguments.
    test-a-rename-onto-a-type-read-down-a-list-argument = cell (c: c.v) [
      base
      (
        { u, ... }:
        {
          options.v = mkOption { type = builtins.elemAt u 6; };
        }
      )
      (
        { u, ... }:
        {
          _module.args.u = lib.genList (i: if i == 0 then types.int else builtins.elemAt u (i - 1)) 7;
        }
      )
      (R [ "w" ] [ "v" ])
      (def {
        a = 1;
        w = 5;
      })
    ];
    # A declaration reading its own evaluation at declaration time, beside the renames: nixpkgs'
    # grammar reads `config`, `options` and module arguments there as nixpkgs' fold lets it
    # (den-hoag-2tna3), so what the staged passes refused here is served.
    test-a-presence-reading-options = cell (c: c.s.x) [
      base
      (
        { options, ... }:
        {
          options.s =
            if options ? a then
              {
                x = mkOption {
                  type = types.int;
                  default = 3;
                };
              }
            else
              { };
        }
      )
      (def { a = 1; })
    ];
    test-a-declaration-reading-config = cell (c: c.b) [
      base
      ({ config, ... }: {
        options.b = mkOption { type = types.int; } // lib.optionalAttrs (config.a == 1) { default = 2; };
      })
      (def { a = 1; })
    ];
    # The rename chain beside it resolves one link per pass.
    test-a-presence-reading-a-module-argument = cell (c: c.v) [
      base
      ({ u, ... }: { options.v = if u.leaf then mkOption { type = types.int; } else { }; })
      { _module.args.u.leaf = true; }
      (named "c-to-b.nix" (R [ "c" ] [ "b" ]))
      (R [ "b" ] [ "a" ])
      (def {
        c = 1;
        v = 5;
      })
    ];
    # A rename whose target's type is read down a list argument longer than the passes: element i
    # reads element i - 1.
    test-a-rename-deeper-than-the-passes = cell (c: c.v) [
      base
      ({ u, ... }: { options.v = mkOption { type = builtins.elemAt u 400; }; })
      ({ u, ... }: {
        _module.args.u = lib.genList (i: if i == 0 then types.int else builtins.elemAt u (i - 1)) 401;
      })
      (R [ "w" ] [ "v" ])
      (def {
        a = 1;
        w = 5;
      })
    ];
    # An evaluated field of an option record, as `misc/nixpkgs.nix` reads `isDefined`.
    test-a-declaration-reading-an-evaluated-field = cell (c: c.b) [
      base
      ({ options, ... }: {
        options.b =
          mkOption { type = types.int; } // lib.optionalAttrs options.a.isDefined { default = 2; };
      })
      (def { a = 1; })
    ];
    # A cycle's refusal is a thrown error, so `tryEval` catches it (nixpkgs reaches infinite
    # recursion); the refusal's text is pinned in `ci/tests-error.nix`.
    test-a-rename-cycle-refusal-is-catchable = {
      expr =
        (builtins.tryEval (
          builtins.deepSeq
            (genMerge.evalModuleTree { } [
              base
              (A [ "b" ] [ "c" ])
              (A [ "c" ] [ "b" ])
              (def { a = 1; })
            ]).config
            null
        )).success;
      expected = false;
    };
    # Two renames redeclare one group, and one of its members is named `type`: the group's
    # declaration trees are told apart from empty ones by their key sets, never by comparing them,
    # which would read the alias's `type` and so its target's.
    test-a-renamed-member-named-type = cell (c: c.t) [
      base
      { options.t = mkOption { type = types.int; }; }
      {
        options.h = mkOption {
          type = types.int;
          default = 0;
        };
      }
      (R [ "g" "type" ] [ "t" ])
      (R [ "g" "host" ] [ "h" ])
      (def {
        a = 1;
        g.type = 5;
      })
    ];
    # The target is a submodule's sub-option named `options`, so `doRename`'s `attrByPath` stops at
    # the declaration's own `options` field, which a stamped declaration answers as nixpkgs' does.
    test-a-rename-onto-a-sub-option-named-options = cell (c: c.s.options) [
      base
      {
        options.s = mkOption {
          type = types.submodule {
            options.options = mkOption {
              type = types.int;
              default = 0;
            };
          };
          default = { };
        };
      }
      (R [ "o" ] [ "s" "options" ])
      (def {
        a = 1;
        o = 5;
      })
    ];
  };
}
