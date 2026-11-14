# THE SHARED CLOSURE DECISION FORCES NOTHING BASE DOES NOT (lib/modules.nix, the guard's `closure` record and
# `removal.closure`'s re-walk). Base decides a same-path drop by `keyedDrop`'s first arm before any key comparison,
# and never reads a first holder's `__keyEq`; the publisher and the re-walk test only keys and paths, so a
# `__keyEq` that reads `config` or throws stays unread and the evaluation serves. RED: a shareability test that
# reads `__keyEq` (`keqOf … == null`) refuses the first two by the guard's `config` refusal or the throw, and the
# third at its same-path drop. The controls state `__keyEq = null`, so every arm serves them.
{ genMerge, ... }:
let
  gm = genMerge;
  fx = ./_fixtures/closure-decision;
  plain = {
    key = "plain";
    options.a = gm.mkOption {
      type = gm.types.int;
      default = 0;
    };
  };
  serve = ms: (gm.evalModuleTree { } ms).config;
in
{
  flake.tests.closure-decision = {
    test-a-key-comparison-reading-config-is-never-forced = {
      expr = serve [
        plain
        (
          { config, ... }:
          {
            key = "A";
            __keyEq = if config.a == 0 then null else null;
          }
        )
      ];
      expected.a = 0;
    };
    test-a-throwing-key-comparison-is-never-forced = {
      expr = serve [
        plain
        (
          { ... }:
          {
            key = "A";
            __keyEq = throw "closure-decision: the key comparison was forced";
          }
        )
      ];
      expected.a = 0;
    };
    test-a-same-path-drop-reads-no-key-comparison = {
      expr = serve [
        plain
        (fx + "/kq.nix")
        (fx + "/kq.nix")
      ];
      expected.a = 0;
    };
    test-a-null-key-comparison-serves = {
      expr = serve [
        plain
        (
          { ... }:
          {
            key = "A";
            __keyEq = null;
          }
        )
      ];
      expected.a = 0;
    };
    test-a-same-path-drop-with-a-null-key-comparison-serves = {
      expr = serve [
        plain
        (fx + "/kn.nix")
        (fx + "/kn.nix")
      ];
      expected.a = 0;
    };
  };
}
