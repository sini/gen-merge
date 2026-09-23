# EACH NESTING TYPE READS A DEFINITION AS ITS REFERENCE DOES — the values. One binding,
# `defsAsModules`, is nixpkgs' `submoduleWith` `allModules` flag for flag:
#   * `(evalModuleTree …).type` reads EVERY def as a module, as `(lib.evalModules …).type` does;
#   * `types.submodule` reads an ATTRSET def as config and any other def as a module, as
#     `lib.types.submodule` does.
# A module is a path, a string naming an absolute path, a function or an attrset (the reference's
# `loadModule` imports whatever is not a function or an attrset). The refusals are
# `ci/tests-error.nix`'s `def-reading` group.
{ genMerge, ... }:
let
  gm = genMerge;
  t = gm.types;
  int0 = gm.mkOption {
    type = t.int;
    default = 0;
  };
  tree = (gm.evalModuleTree { modules = [ { options.a = int0; } ]; }).type;
  sub = t.submodule { options.a = int0; };
  outer = check: type: def: {
    inherit check;
    modules = [
      { options.t = gm.mkOption { inherit type; }; }
      {
        _file = "/real/F.nix";
        config.t = def;
      }
    ];
  };
  valueAt = type: def: (gm.evalModuleTree (outer true type def)).config.t;
  undeclaredAt =
    type: def:
    map (u: { inherit (u) file path; }) (gm.evalModuleTree (outer false type def)).undeclared;
  keyOpt = {
    options.key = gm.mkOption {
      type = t.str;
      default = "k0";
    };
  };
  a5 = ./_fixtures/def-reading-a5.nix;
  topA = modules: (gm.evalModuleTree { modules = [ { options.a = int0; } ] ++ modules; }).config.a;
in
{
  flake.tests.def-reading = {
    # ── the tree type: every def is a module ──────────────────────────────────────────────────
    test-tree-attrset-def-control = {
      expr = valueAt tree { a = 1; };
      expected = {
        a = 1;
      };
    };
    # Uncatchable before the landing (the def was read as config).
    test-tree-function-def-is-a-module = {
      expr = valueAt tree ({ ... }: { a = 3; });
      expected = {
        a = 3;
      };
    };
    test-tree-path-def-is-a-module = {
      expr = valueAt tree a5;
      expected = {
        a = 5;
      };
    };
    test-tree-config-key-is-module-syntax = {
      expr = valueAt tree { config.a = 2; };
      expected = {
        a = 2;
      };
    };
    test-tree-imports-key-is-module-syntax = {
      expr = valueAt tree { imports = [ { a = 4; } ]; };
      expected = {
        a = 4;
      };
    };
    test-tree-functor-def-is-a-module = {
      expr = valueAt tree { __functor = _: { ... }: { a = 6; }; };
      expected = {
        a = 6;
      };
    };
    # `key' is module identity, as at the top level (den-hoag-470xp owns whether it is refused).
    test-tree-key-is-module-identity = {
      expr = valueAt (gm.evalModuleTree { modules = [ keyOpt ]; }).type { key = "k1"; };
      expected = {
        key = "k0";
      };
    };
    test-tree-undeclared-key-of-a-wrapped-def-names-its-file = {
      expr = undeclaredAt tree {
        _file = "/real/W.nix";
        imports = [ { bogus = 1; } ];
      };
      expected = [
        {
          file = "/real/W.nix";
          path = [
            "t"
            "bogus"
          ];
        }
      ];
    };
    test-tree-undeclared-key-of-a-function-def-names-its-file = {
      expr = undeclaredAt tree ({ ... }: { bogus = 1; });
      expected = [
        {
          file = "/real/F.nix";
          path = [
            "t"
            "bogus"
          ];
        }
      ];
    };
    test-tree-undeclared-key-control = {
      expr = undeclaredAt tree {
        a = 1;
        bogus = 1;
      };
      expected = [
        {
          file = "/real/F.nix";
          path = [
            "t"
            "bogus"
          ];
        }
      ];
    };

    # ── `types.submodule`: an attrset def is config, anything else is a module ───────────────
    # Uncatchable before the landing (`"x"` was read as an import).
    test-submodule-imports-key-is-config = {
      expr = valueAt (t.submodule {
        options.imports = gm.mkOption { type = t.listOf t.str; };
      }) { imports = [ "x" ]; };
      expected = {
        imports = [ "x" ];
      };
    };
    test-submodule-key-is-config = {
      expr = valueAt (t.submodule keyOpt) { key = "k1"; };
      expected = {
        key = "k1";
      };
    };
    test-submodule-function-def-is-a-module = {
      expr = valueAt sub ({ ... }: { a = 3; });
      expected = {
        a = 3;
      };
    };
    test-submodule-path-def-is-a-module = {
      expr = valueAt sub a5;
      expected = {
        a = 5;
      };
    };

    # ── a STRING naming an absolute path is imported, beside the path-literal control ───────
    test-absolute-path-string-import-is-a-module = {
      expr = topA [ { imports = [ "${a5}" ]; } ];
      expected = 5;
    };
    test-path-literal-import-control = {
      expr = topA [ { imports = [ a5 ]; } ];
      expected = 5;
    };
    # A union's member dispatch asks the submodule the same question: a def that is both a `str` and
    # a path string is the MODULE under `either (submodule M) str`, as in nixpkgs. Before, the union
    # answered the string. The plain string is the control that the right member still takes a string.
    test-either-submodule-str-takes-a-path-string-as-the-module = {
      expr = {
        pathString = valueAt (t.either sub t.str) "${a5}";
        plainString = valueAt (t.either sub t.str) "hello";
      };
      expected = {
        pathString = {
          a = 5;
        };
        plainString = "hello";
      };
    };
  };
}
