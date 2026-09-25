# THE MODULE READER — the values it answers. Its refusals are `ci/tests-error.nix`'s `module-reader`
# group (a refusal's message is only assertable there); the shorthand shapes' agreement with nixpkgs
# is `differential.nix`'s `reader-*` fixtures. This file holds what neither can: the controls that
# must read the same before and after the reader became the reference's `unifyModuleSyntax`.
{ genMerge, ... }:
let
  gm = genMerge;
  t = gm.types;
  int0 = gm.mkOption {
    type = t.int;
    default = 0;
  };
  decl = {
    options.a = int0;
    options.foo = int0;
  };
  read =
    m:
    let
      c =
        (gm.evalModuleTree {
          modules = [
            decl
            m
          ];
        }).config;
    in
    {
      inherit (c) a foo;
    };

  # The typo `option.c` (for `options.c`). Its declaration-only reads are refused by name in
  # `ci/tests-error.nix`'s `module-reader` group; here, its config read and the spelled-right control.
  typo = {
    _file = "/real/T.nix";
    options.b = int0;
    option.c = int0;
  };
  selfFn = { lib, ... }: selfFn;
in
{
  flake.tests.module-reader = {
    # A CONFIG read of the typo module is refused, as its declaration-only reads are. And the
    # control: spelled `options.c`, a declaration-only read sees `c`.
    test-config-read-of-the-same-typo-module-is-refused = {
      expr = (builtins.tryEval (builtins.deepSeq (read typo) null)).success;
      expected = false;
    };
    test-declaration-only-read-control-spelled-right = {
      expr = builtins.attrNames (
        gm.declaredOptions {
          modules = [
            (
              removeAttrs typo [ "option" ]
              // {
                options.b = int0;
                options.c = int0;
              }
            )
          ];
        }
      );
      expected = [
        "b"
        "c"
      ];
    };

    # A module function whose result is not a module is refused CATCHABLY (it once aborted with
    # `expected a set but found a function`, which `tryEval` does not contain). The control: a
    # module function returning a module merges.
    test-function-module-returning-a-function-is-refused-catchably = {
      expr = (builtins.tryEval (builtins.deepSeq (read (_: selfFn)) null)).success;
      expected = false;
    };
    test-function-module-returning-a-module-control = {
      expr = read (_: {
        a = 2;
      });
      expected = {
        a = 2;
        foo = 0;
      };
    };

    # ── UNCHANGED by the reader: the controls and gen-merge's kept `_module` superset ─────────────
    test-structured-config-control = {
      expr = read { config.a = 2; };
      expected = {
        a = 2;
        foo = 0;
      };
    };
    test-shorthand-control = {
      expr = read { foo = 1; };
      expected = {
        a = 0;
        foo = 1;
      };
    };
    # `_module` beside `config` is folded into config (the reference refuses it): the kept superset.
    test-module-key-beside-config-is-folded = {
      expr = read {
        config.a = 2;
        _module.args.zz = 1;
      };
      expected = {
        a = 2;
        foo = 0;
      };
    };
    test-class-beside-config-is-stripped = {
      expr = read {
        config.a = 2;
        _class = "x";
      };
      expected = {
        a = 2;
        foo = 0;
      };
    };
    test-key-and-file-beside-config-are-admitted = {
      expr = read {
        config.a = 2;
        key = "k";
        _file = "/real/K.nix";
      };
      expected = {
        a = 2;
        foo = 0;
      };
    };
  };
}
