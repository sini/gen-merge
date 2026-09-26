# WHAT A FUNCTION MODULE IS APPLIED TO, per formal source (lib/modules.nix `callM` and `callD`).
#
# A module whose every formal is in the base arguments (`specialArgs`, `options`, `config`,
# `prefix`) is applied to the base set itself, with no per-application `extra` copy. The copy it
# elides was `extra // baseArgs`, which holds the same keys and the same slots, so these cells pin
# the values and the key set a module sees on both arms: the elided one (`options`/`config`, a
# `specialArgs` formal) and the copying one (a `_module.args` formal). The declaration stratum is
# pinned the same way, through a module whose `options` read a `specialArgs` formal.
#
# RED, evaluated: `callM`'s elided arm applying `removeAttrs baseArgs [ "prefix" ]` reds the two
# base key-set cells; applying `baseArgs // { foo = 2; }` reds the specialArgs-value cell; `callD`'s
# applying `declArgs // { foo = 2; }` reds the declaration-stratum cell.
{ genMerge, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption types;

  decl = {
    options.a = mkOption {
      type = types.int;
      default = 1;
    };
    options.seen = mkOption {
      type = types.attrsOf types.anything;
      default = { };
    };
  };
  run =
    modules:
    (evalModuleTree {
      specialArgs.foo = 7;
      modules = [ decl ] ++ modules;
    }).config;

  # every formal in the base arguments: the elided arm
  baseFormals = run [
    (
      { options, config, ... }@args:
      {
        seen.base = {
          hasA = options ? a;
          a = config.a;
          keys = builtins.attrNames args;
        };
      }
    )
  ];
  special = run [
    (
      { foo, ... }@args:
      {
        seen.special = {
          inherit foo;
          keys = builtins.attrNames args;
        };
      }
    )
  ];
  # a `_module.args` formal: the copying arm
  moduleArg = run [
    { config._module.args.bar = 3; }
    (
      { bar, foo, ... }@args:
      {
        seen.moduleArg = {
          inherit bar foo;
          keys = builtins.attrNames args;
        };
      }
    )
  ];
  # the declaration stratum, applied by `callD`: `declaredOptions` is its own publication, while
  # `.config` reads the declarations `callM` applied
  declared = gm.declaredOptions {
    specialArgs.foo = 7;
    modules = [
      (
        { foo, prefix, ... }:
        {
          options.d = mkOption {
            type = types.int;
            default = foo;
          };
          options.p = mkOption {
            type = types.anything;
            default = prefix;
          };
        }
      )
    ];
  };
in
{
  flake.tests.formal-binding = {
    test-options-and-config-formals-see-the-module-values = {
      expr = {
        inherit (baseFormals.seen.base) hasA a;
      };
      expected = {
        hasA = true;
        a = 1;
      };
    };
    test-options-and-config-formals-see-the-base-key-set = {
      expr = baseFormals.seen.base.keys;
      expected = [
        "config"
        "foo"
        "options"
        "prefix"
      ];
    };
    test-a-special-arg-formal-sees-its-value = {
      expr = special.seen.special.foo;
      expected = 7;
    };
    test-a-special-arg-formal-sees-the-base-key-set = {
      expr = special.seen.special.keys;
      expected = [
        "config"
        "foo"
        "options"
        "prefix"
      ];
    };
    test-a-module-args-formal-sees-its-value-beside-a-special-arg = {
      expr = {
        inherit (moduleArg.seen.moduleArg) bar foo;
      };
      expected = {
        bar = 3;
        foo = 7;
      };
    };
    test-a-module-args-formal-adds-its-own-key = {
      expr = moduleArg.seen.moduleArg.keys;
      expected = [
        "bar"
        "config"
        "foo"
        "options"
        "prefix"
      ];
    };
    test-the-declaration-stratum-binds-a-special-arg-and-prefix = {
      expr = {
        d = declared.d.default;
        p = declared.p.default;
      };
      expected = {
        d = 7;
        p = [ ];
      };
    };
  };
}
