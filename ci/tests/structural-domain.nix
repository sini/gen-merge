{ genMerge, ... }:
let
  gm = genMerge;
  inherit (gm) evalModuleTree mkOption;
  t = gm.types;

  sub = t.submodule {
    options.a = mkOption {
      type = t.int;
      default = 0;
    };
  };
  run =
    ty: defs:
    (evalModuleTree {
      modules = [
        { options.o = mkOption { type = ty; }; }
      ]
      ++ map (v: {
        _file = "/p/F.nix";
        o = v;
      }) defs;
    }).config.o;
  # `false` is a CATCHABLE refusal. An uncatchable abort does not return `false`: it escapes
  # `tryEval` and takes the whole cell down, which is how this cell reads on a fold that lets a
  # wrong-kind definition reach the interpreter.
  folds = v: (builtins.tryEval (builtins.deepSeq v null)).success;
in
{
  # EVERY STRUCTURAL CONTAINER REFUSES A WRONG-KIND DEFINITION CATCHABLY (`refusingOutside`,
  # lib/types.nix); the messages are pinned in tests-error's `structural-domain` group. LIVE
  # CONTROLS in the same cell: each member's right-kind twin is its value, so the refusals are not
  # a fold that refuses everything, and `attrs` over an int — refused by name before any of this —
  # reads `false` through the same instrument.
  flake.tests.structural-domain.test-every-structural-container-refuses-catchably = {
    expr = {
      refused = map folds [
        (run (t.listOf t.int) [ 5 ])
        (run (t.attrsOf t.int) [ 5 ])
        (run (t.lazyAttrsOf t.int) [ [ 1 ] ])
        (run t.deferredModule [ 5 ])
        (run sub [ 5 ])
        (run (t.listOf t.int) [
          (gm.mkForce (gm.mkIf false [ 1 ]))
          [ 2 ]
        ])
        (run (t.attrsOf (t.listOf t.int)) [ { k = 5; } ])
        (run (t.listOf (t.attrsOf t.int)) [ [ 5 ] ])
      ];
      attrsControl = folds (run t.attrs [ 5 ]);
      twins = {
        listOf = run (t.listOf t.int) [
          [
            1
            2
          ]
        ];
        attrsOf = run (t.attrsOf t.int) [
          { a = 1; }
          { b = 2; }
        ];
        lazyAttrsOf = run (t.lazyAttrsOf t.int) [ { a = 1; } ];
        deferredModule = builtins.length (run t.deferredModule [ { } ]).imports;
        submodule = run sub [ { a = 3; } ];
        nested = run (t.attrsOf (t.listOf t.int)) [ { k = [ 5 ]; } ];
      };
    };
    expected = {
      refused = [
        false
        false
        false
        false
        false
        false
        false
        false
      ];
      attrsControl = false;
      twins = {
        listOf = [
          1
          2
        ];
        attrsOf = {
          a = 1;
          b = 2;
        };
        lazyAttrsOf = {
          a = 1;
        };
        deferredModule = 1;
        submodule = {
          a = 3;
        };
        nested = {
          k = [ 5 ];
        };
      };
    };
  };
}
