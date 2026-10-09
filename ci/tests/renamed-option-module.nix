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
  };
}
