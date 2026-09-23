# THE MODULE READER — the values it answers. Its refusals are `ci/tests-error.nix`'s `module-reader`
# group (a refusal's message is only assertable there); the shorthand shapes' agreement with nixpkgs
# is `differential.nix`'s `reader-*` fixtures. This file holds the two things neither can: the
# controls that must read the same before and after the reader became the reference's
# `unifyModuleSyntax`, and the one boundary it leaves open, pinned at today's value.
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

  # ★ THE BOUNDARY, PINNED — README "Known byte-mode boundaries". A DECLARATION-ONLY read does not
  # reach the module-syntax refusals, which sit in the config reader: on the typo `option.c` (for
  # `options.c`) the declaration `c` vanishes from `declaredOptions` and `.options` without a word,
  # where the reference refuses the module. These cells assert that silent answer ON PURPOSE, so a
  # fix that refuses the declaration-only read turns them red and has to rewrite them.
  typo = {
    _file = "/real/T.nix";
    options.b = int0;
    option.c = int0;
  };
in
{
  flake.tests.module-reader = {
    test-declaration-only-read-of-a-typo-key-is-not-refused = {
      expr = builtins.attrNames (gm.declaredOptions { modules = [ typo ]; });
      expected = [ "b" ];
    };
    test-declaration-only-options-read-of-a-typo-key-is-not-refused = {
      expr =
        builtins.attrNames
          (gm.evalModuleTree {
            modules = [
              decl
              typo
            ];
          }).options;
      expected = [
        "a"
        "b"
        "foo"
      ];
    };
    # The same module on a CONFIG read is refused — the boundary is the declaration-only read, not
    # the module. And the control: spelled `options.c`, the same read does see `c`.
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
