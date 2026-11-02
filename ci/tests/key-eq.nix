# THE KEY COMPARISON (`__keyEq`, den-hoag-kind-generator-collision-d4gnx) — what composes, and that
# every refusal is catchable in both import orders. The by-name texts are `ci/tests-error.nix`'s
# `key-eq` group. `l` is a list option, so one module reads one element and two read two: the cells
# tell "one module" from "both composed", not only "refused" from "not".
{ genMerge, ... }:
let
  gm = genMerge;
  decl.options.l = gm.mkOption {
    type = gm.types.listOf gm.types.str;
    default = [ ];
  };
  withEq = decide: v: {
    key = "K";
    __keyEq = {
      subject = v;
      inherit decide;
    };
    l = [ v ];
  };
  eq = withEq (a: b: a == b);
  plain = v: {
    key = "K";
    l = [ v ];
  };
  l =
    mods:
    let
      v = (gm.evalModuleTree { } ([ decl ] ++ mods)).config.l;
      r = builtins.tryEval (builtins.deepSeq v v);
    in
    if r.success then r.value else "REFUSED";
in
{
  flake.tests.key-eq = {
    # `decide` true is ONE module; false refuses, in both orders. The control is a lone occurrence.
    test-equal-is-one-module-unequal-refuses-in-both-orders = {
      expr = {
        alone = l [ (eq "x") ];
        equal = l [
          (eq "x")
          (eq "x")
        ];
        xThenY = l [
          (eq "x")
          (eq "y")
        ];
        yThenX = l [
          (eq "y")
          (eq "x")
        ];
      };
      expected = {
        alone = [ "x" ];
        equal = [ "x" ];
        xThenY = "REFUSED";
        yThenX = "REFUSED";
      };
    };
    # Only one occurrence publishing the comparison refuses in BOTH orders (ADR-0022): kept-publishes
    # and dropped-publishes are one outcome.
    test-only-one-publishing-refuses-in-both-orders = {
      expr = {
        keptPublishes = l [
          (eq "x")
          (plain "y")
        ];
        droppedPublishes = l [
          (plain "y")
          (eq "x")
        ];
      };
      expected = {
        keptPublishes = "REFUSED";
        droppedPublishes = "REFUSED";
      };
    };
    # Neither publishing keeps nixpkgs' key rule: the first occurrence is the module.
    test-neither-publishing-keeps-the-first = {
      expr = {
        xy = l [
          (plain "x")
          (plain "y")
        ];
        yx = l [
          (plain "y")
          (plain "x")
        ];
      };
      expected = {
        xy = [ "x" ];
        yx = [ "y" ];
      };
    };
    # A non-boolean `decide`, and `__keyEq` on a module with no `key`, refuse catchably.
    test-non-boolean-decide-and-keyless-publisher-refuse-catchably = {
      expr = {
        nonBool = l [
          (withEq (_: _: "yes") "x")
          (withEq (_: _: "yes") "x")
        ];
        keyless = l [
          {
            __keyEq = {
              subject = 1;
              decide = _: _: true;
            };
            l = [ "z" ];
          }
        ];
      };
      expected = {
        nonBool = "REFUSED";
        keyless = "REFUSED";
      };
    };
    # A path-keyed occurrence is the one file: it keeps nixpkgs' rule, so a fixture whose `decide` is
    # always false is still one module when its path is imported twice.
    test-path-keyed-twice-is-one-module = {
      expr = l [
        ./_fixtures/key-eq-path.nix
        ./_fixtures/key-eq-path.nix
      ];
      expected = [ "p" ];
    };
    # A path import sharing its key with a content module is not the one file: only the content
    # module publishes, so the pair refuses in both orders. The path-twice cell above is its control.
    test-path-and-content-sharing-a-key-refuse-in-both-orders =
      let
        file = ./_fixtures/key-eq-plain-path.nix;
        content = {
          key = toString file;
          __keyEq = {
            subject = 1;
            decide = _: _: true;
          };
          l = [ "content" ];
        };
      in
      {
        expr = {
          contentThenPath = l [
            content
            file
          ];
          pathThenContent = l [
            file
            content
          ];
        };
        expected = {
          contentThenPath = "REFUSED";
          pathThenContent = "REFUSED";
        };
      };
    # The content keys the closure reads, published for a consumer that decides a module meets no
    # sibling (gen-schema's layered introspection): `key` among them, so two plain modules naming
    # one key meet in the closure and one is dropped (`plain` above, every cell reading one element).
    test-closure-keys-are-published = {
      expr = {
        inherit (gm.moduleSyntax) closure;
        oneModule = l [
          (plain "a")
          (plain "b")
        ];
      };
      expected = {
        closure = [
          "disabledModules"
          "imports"
          "key"
          "require"
        ];
        oneModule = [ "a" ];
      };
    };
    # The published list is the fast path's own: the names `moduleClosure` tests inline by `?` (read off
    # the source between its binding and the closure it falls to) are exactly `moduleSyntax.closure`, so
    # neither side moves alone.
    test-closure-keys-are-the-fast-paths-tests =
      let
        src = builtins.readFile ../../lib/modules.nix;
        after = builtins.elemAt (builtins.split "\n  moduleClosure =\n" src) 2;
        body = builtins.head (builtins.split "removal[.]closure specialArgs" after);
        tested = builtins.filter builtins.isList (builtins.split "e[.]content [?] ([A-Za-z_]+)" body);
      in
      {
        expr = builtins.sort builtins.lessThan (map builtins.head tested);
        expected = builtins.sort builtins.lessThan gm.moduleSyntax.closure;
      };
    test-key-eq-is-a-module-key-in-both-lists = {
      expr = {
        structured = builtins.elem "__keyEq" gm.moduleSyntax.structured;
        shorthandMeta = builtins.elem "__keyEq" gm.moduleSyntax.shorthandMeta;
      };
      expected = {
        structured = true;
        shorthandMeta = true;
      };
    };
  };
}
