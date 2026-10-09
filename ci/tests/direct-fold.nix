# The direct fold (den-hoag-c7jkw.1): an `attrsOf` whose element nests directly, at an evaluation
# accessor's root, folds the key walk's own records (`evAt`'s `positions` question) rather than
# splitting its definitions a second time. Every cell here passes on the second derivation too: what
# they pin is that the records ARE the split, element for element, through every pass the walk runs
# (discharge, priority, order) and through the element's own fold. The refusals through the same
# branch are pinned on `testsError` (`../tests-error.nix`, group `direct-fold`).
#
# Beside them, two pins on `modules.nix` `ownFold`: a record stating `verify` beside a fold of its
# own spelled as `merge` keeps that fold. A leaf arm keyed on `verify` ahead of the import call
# serves these a different value (den-hoag-c7jkw.1, dropped for that reason). A foreign base stating
# `verify` keeps its own `check` as well (`interface.nix` `checksDefs`); its refusals are on
# `testsError`, group `foreign-leaf-check`.
{
  genMerge,
  nixpkgsLib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  users =
    defs:
    (gm.evalModuleTree { } (
      [
        {
          options.users = gm.mkOption {
            type = t.attrsOf (
              t.submodule {
                options.uid = gm.mkOption {
                  type = t.int;
                  default = 0;
                };
              }
            );
            default = { };
          };
        }
      ]
      ++ map (d: { config.users = d; }) defs
    )).config.users;
  leaf =
    ty: defs:
    (gm.evalModuleTree { } (
      [ { options.o = gm.mkOption { type = ty; }; } ] ++ map (v: { config.o = v; }) defs
    )).config.o;
in
{
  flake.tests.direct-fold = {
    # A sibling of an element outside the domain folds without reaching it.
    test-a-sibling-of-a-refused-element-folds = {
      expr =
        (users [
          { u0 = 5; }
          { u1.uid = 7; }
        ]).u1;
      expected = {
        uid = 7;
      };
    };
    test-names-do-not-reach-a-refused-element = {
      expr = builtins.attrNames (users [
        { u0 = 5; }
        { u1.uid = 7; }
      ]);
      expected = [
        "u0"
        "u1"
      ];
    };
    test-an-element-under-a-false-condition-is-absent = {
      expr = users [
        { u0 = gm.mkIf false { uid = 1; }; }
        {
          u1 = {
            uid = 2;
          };
        }
      ];
      expected = {
        u1.uid = 2;
      };
    };
    test-priority-selects-an-element-s-definitions = {
      expr = users [
        { u0 = gm.mkDefault { uid = 1; }; }
        { u0 = gm.mkForce { uid = 2; }; }
      ];
      expected = {
        u0.uid = 2;
      };
    };
    test-order-properties-discharge-at-the-element = {
      expr = users [
        { u0 = gm.mkOrder 2000 { uid = 1; }; }
        { u1 = gm.mkBefore { uid = 2; }; }
      ];
      expected = {
        u0.uid = 1;
        u1.uid = 2;
      };
    };
    test-a-function-definition-is-an-element-module = {
      expr = users [ { u0 = { ... }: { config.uid = 9; }; } ];
      expected = {
        u0.uid = 9;
      };
    };
    test-an-element-reads-its-name = {
      expr = users [
        { alice = { name, ... }: { config.uid = builtins.stringLength name; }; }
      ];
      expected = {
        alice.uid = 5;
      };
    };

    # `verify` is not "no fold of its own": a record stating it beside a `merge` keeps the `merge`.
    test-a-verify-beside-a-merge-keeps-the-merge = {
      expr =
        leaf
          {
            name = "hand";
            verify = _: null;
            merge = _loc: defs: builtins.length defs * 100;
          }
          [
            1
            1
          ];
      expected = 200;
    };
    test-a-foreign-leaf-with-a-verify-keeps-its-merge = {
      expr = leaf (nixpkgsLib.types.lines // { verify = _: null; }) [
        "a"
        "b"
      ];
      expected = "b\na";
    };
    # The base's own check runs beside the copy's `verify`, and a value inside both is served.
    test-a-foreign-attrs-with-a-verify-serves-a-value-its-base-admits = {
      expr = leaf (nixpkgsLib.types.attrs // { verify = _: null; }) [
        { a = 1; }
        { b = 2; }
      ];
      expected = {
        a = 1;
        b = 2;
      };
    };
  };
}
