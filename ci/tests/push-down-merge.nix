# `pushDownProperties`' merge arm (lib/priority.nix, den-hoag-l5iea §4.2): the fold over a merge's pushed
# contents starts at `{ }`, and `mergeConfigAttrs` joins `{ }` to its other operand as that operand itself. The
# join of `{ }` and a config is that config key for key, so this changes no value, and the first content is no
# longer rebuilt through `listToAttrs`.
#
# The value cells pin the arm's answer on every shape it meets: no contents, one, a shared key, a content that
# is not an attrset, first or later. The copy cell reads the copy itself: an attribute rebuilt through
# `listToAttrs` takes its position from the builder in lib/priority.nix, so the first content's attribute
# keeps its own position only where nothing rebuilt it.
{
  prelude,
  ...
}:
let
  priority = import ../../lib/priority.nix { inherit prelude; };
  inherit (priority) pushDownProperties mkMerge mkIf;
  push = contents: pushDownProperties (mkMerge contents);
  refused = v: (builtins.tryEval (builtins.deepSeq v v)).success == false;
in
{
  flake.tests.push-down-merge = {
    test-an-empty-merge-pushes-down-to-no-keys = {
      expr = push [ ];
      expected = { };
    };
    test-one-content-is-that-content = {
      expr = push [ { a = 1; } ];
      expected = {
        a = 1;
      };
    };
    test-a-shared-key-merges-and-the-rest-stand = {
      expr = push [
        {
          a = 1;
          b = 2;
        }
        {
          a = 3;
          c = 4;
        }
      ];
      expected = {
        a = mkMerge [
          1
          3
        ];
        b = 2;
        c = 4;
      };
    };
    test-a-nested-merge-and-condition-push-through = {
      expr = push [
        (mkMerge [ { a = 1; } ])
        (mkIf true { a = 2; })
      ];
      expected = {
        a = mkMerge [
          1
          (mkIf true 2)
        ];
      };
    };
    # A content that is not an attrset is the join's result as it stands, the first one met.
    test-a-content-that-is-not-an-attrset-is-the-result = {
      expr = {
        alone = push [ 5 ];
        first = push [
          5
          { a = 1; }
        ];
        later = push [
          { a = 1; }
          5
          6
        ];
        underCondition = push [
          (mkIf true 5)
          { a = 1; }
        ];
      };
      expected = {
        alone = 5;
        first = 5;
        later = 5;
        underCondition = 5;
      };
    };
    test-a-throwing-content-refuses-catchably = {
      expr = {
        alone = refused (push [ (throw "C1-FIRST") ]);
        later = refused (push [
          { a = 1; }
          (throw "C1-LATER")
        ]);
      };
      expected = {
        alone = true;
        later = true;
      };
    };
    test-the-first-content-is-not-rebuilt =
      let
        first = {
          a = 1;
        };
      in
      {
        expr = builtins.unsafeGetAttrPos "a" (push [
          first
          { b = 2; }
        ]);
        expected = builtins.unsafeGetAttrPos "a" first;
      };
    # The empty test is `{ } == a`, not `a == { }`: attrset equality asks its left operand whether it is a
    # derivation, so the reversed order forces a content's `type` key on every later join.
    test-a-content-type-key-is-not-forced = {
      expr = builtins.attrNames (push [
        {
          type = throw "TYPE-FORCED";
          a = 1;
        }
        { b = 2; }
        { c = 3; }
      ]);
      expected = [
        "a"
        "b"
        "c"
        "type"
      ];
    };
  };
}
