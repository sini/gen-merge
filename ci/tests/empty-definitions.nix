# ALL DEFINITIONS FILTERED OUT BY CONDITIONS — the empty-definition value of a nesting type is its
# reference's: a submodule (and the tree type) evaluates its own module set over no definitions, and a
# STRICT container (`attrsOf`, `listOf`) drops an element whose every definition was discharged, where
# `lazyAttrsOf` keeps it at the element's empty value. nixpkgs `mergeDefinitions` (`optionalValue`,
# `emptyValue`) and `submoduleWith`'s `emptyValue.value = base.config` are the reference.
{ genMerge, ... }:
let
  gm = genMerge;
  t = gm.types;
  inherit (gm) mkOption mkIf mkDefault;
  subMod = {
    options.a = mkOption { type = t.int; };
    options.b = mkOption {
      type = t.int;
      default = 7;
    };
  };
  sub = t.submodule subMod;
  subName = t.submodule (
    { name, ... }:
    {
      options.n = mkOption {
        type = t.str;
        default = name;
      };
    }
  );
  tree = (gm.evalModuleTree { modules = [ subMod ]; }).type;
  at =
    type: defs:
    (gm.evalModuleTree {
      modules = [ { options.o = mkOption { inherit type; }; } ] ++ map (d: { config.o = d; }) defs;
    }).config.o;
in
{
  flake.tests.empty-definitions = {
    test-submodule-sole-mkIf-false-reads-defaults = {
      expr = (at sub [ (mkIf false { a = 1; }) ]).b;
      expected = 7;
    };
    test-submodule-undefined-reads-defaults = {
      expr = (at sub [ ]).b;
      expected = 7;
    };
    test-submodule-empty-value-declares-its-options = {
      expr = builtins.attrNames (at sub [ (mkIf false { a = 1; }) ]);
      expected = [
        "a"
        "b"
      ];
    };
    test-tree-sole-mkIf-false-reads-defaults = {
      expr = (at tree [ (mkIf false { a = 1; }) ]).b;
      expected = 7;
    };
    test-lazyAttrsOf-discharged-element-reads-defaults = {
      expr = (at (t.lazyAttrsOf sub) [ { k = mkIf false { a = 1; }; } ]).k.b;
      expected = 7;
    };
    test-attrsOf-drops-a-discharged-element = {
      expr = builtins.attrNames (at (t.attrsOf sub) [ { k = mkIf false { a = 1; }; } ]);
      expected = [ ];
    };
    test-attrsOf-leaf-drops-a-discharged-element = {
      expr = at (t.attrsOf t.int) [ { k = mkIf false 1; } ];
      expected = { };
    };
    test-listOf-leaf-drops-a-discharged-element = {
      expr = at (t.listOf t.int) [
        [
          (mkIf false 1)
          2
        ]
      ];
      expected = [ 2 ];
    };
    test-listOf-submodule-drops-a-discharged-element = {
      expr = builtins.length (at (t.listOf sub) [ [ (mkIf false { a = 1; }) ] ]);
      expected = 0;
    };
    # The empty value is evaluated as the reference's `base` is: with the documentation placeholder
    # as `name`, not `""` and not the option's own name.
    test-submodule-empty-value-name-placeholder = {
      expr = (at subName [ (mkIf false { }) ]).n;
      expected = "‹name›";
    };
    # A survivor keeps its SOURCE position: the index is taken before the discharged element is
    # dropped, as nixpkgs `listOf` indexes (`imap1`) inside its `filter`.
    test-listOf-survivor-keeps-its-source-index = {
      expr = map (e: e.n) (
        at (t.listOf subName) [
          [
            (mkIf false { })
            { }
          ]
        ]
      );
      expected = [ "1" ];
    };
    # ARMING CONTROLS, green at RED and GREEN: a surviving definition wins over the empty value, and
    # `lazyAttrsOf` keeps the key its strict sibling drops.
    test-control-surviving-def-wins = {
      expr = at sub [
        (mkIf false { a = 1; })
        (mkDefault { a = 2; })
      ];
      expected = {
        a = 2;
        b = 7;
      };
    };
    test-control-lazyAttrsOf-keeps-the-key = {
      expr = builtins.attrNames (at (t.lazyAttrsOf sub) [ { k = mkIf false { a = 1; }; } ]);
      expected = [ "k" ];
    };
  };
}
