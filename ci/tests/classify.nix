# Source-class classification + `pureModule` (design spec §§0.3/3/5) — the srcClass substrate the warm
# override path (A4-T2) consumes. Nothing consumes it yet beyond these tests.
#
# The load-bearing WHY (spec §0.3): `builtins.functionArgs` cannot prove a function module clean —
# `args@{ genSchema, ... }: args.config` shows only `genSchema`, a bare lambda shows `{ }`, yet the
# engine applies every function module with the whole `specialArgs // extra` set (nixpkgs semantics),
# so any function module can reach `config`. Hence attrsets classify clean UNCONDITIONALLY, function
# modules are DIRTY BY DEFAULT, and `pureModule` is the author's explicit clean assertion. The
# adversarial pair below (formals-only + `@`-capture, both UNMARKED → dirty) pins dirty-by-default.
{ genMerge, ... }:
let
  gm = genMerge;
  inherit (gm)
    classifyModule
    pureModule
    evalModuleTree
    mkOption
    ;
  t = gm.types;

  # ── one fixture per class ─────────────────────────────────────────────────
  attrsetMod = {
    config.foo = 1;
  };
  pathToAttrset = ./_fixtures/plain-config.nix; # `{ config.value = 42; }`
  pathToFunction = ./_fixtures/fn-module.nix; # `{ config, ... }: { }`

  # function modules — dirty by default (the whole point: none of these is provably clean)
  formalsOnlyFn = { genSchema, ... }: { config.foo = genSchema; };
  captureFn =
    args@{ ... }:
    {
      config.foo = args;
    };
  bareLambda = args: { config.foo = args; };
  functorNoMarker = {
    __functor = self: (_: { config.foo = 1; });
  };

  # marked-pure — the author's clean assertion (reads only a specialArg)
  markedFn = pureModule ({ unit, ... }: { config.foo = unit; });

  # a marked wrapper WITH imports: the wrapper is marked-pure; the imported plain function classifies
  # INDEPENDENTLY (classifyModule tags the wrapper as a whole and does NOT descend its imports).
  importedPlainFn = { config, ... }: { };
  markedWithImports = pureModule (
    { ... }:
    {
      imports = [ importedPlainFn ];
      config.foo = 1;
    }
  );

  # ── end-to-end: pureModule integrates with `callM`, contributes config, leaks no marker ───────────
  # The wrapped clean function reads a specialArg (`u`) and imports a (dirty) function module that
  # contributes `b`; both defs land in config and NO `__pureModule` key survives (config equality is
  # the marker-leak tooth the spec asks for).
  e2e = evalModuleTree {
    specialArgs = {
      u = "U";
    };
    modules = [
      {
        options.a = mkOption { type = t.str; };
        options.b = mkOption { type = t.int; };
      }
      (pureModule (
        { u, ... }:
        {
          config.a = u;
          imports = [ ({ ... }: { config.b = 7; }) ];
        }
      ))
    ];
  };
in
{
  flake.tests.classify = {
    # CLEAN core — attrsets and path-to-attrset, unconditionally.
    test-attrset-is-clean = {
      expr = classifyModule attrsetMod;
      expected = "attrset";
    };
    test-path-to-attrset-is-clean = {
      expr = classifyModule pathToAttrset;
      expected = "attrset";
    };

    # DIRTY — every function shape, incl. the two statically-invisible config escapes.
    test-path-to-function-is-dirty = {
      expr = classifyModule pathToFunction;
      expected = "dirty";
    };
    test-formals-only-fn-unmarked-is-dirty = {
      expr = classifyModule formalsOnlyFn;
      expected = "dirty";
    };
    test-at-capture-fn-unmarked-is-dirty = {
      expr = classifyModule captureFn;
      expected = "dirty";
    };
    test-bare-lambda-is-dirty = {
      expr = classifyModule bareLambda;
      expected = "dirty";
    };
    test-functor-without-marker-is-dirty = {
      expr = classifyModule functorNoMarker;
      expected = "dirty";
    };

    # MARKED-PURE — the author's clean assertion.
    test-pure-module-is-marked-pure = {
      expr = classifyModule markedFn;
      expected = "marked-pure";
    };

    # IMPORTS classify INDEPENDENTLY — the wrapper is marked-pure; its imported plain fn is dirty.
    test-marked-wrapper-with-imports-is-marked-pure = {
      expr = classifyModule markedWithImports;
      expected = "marked-pure";
    };
    test-imported-plain-fn-classifies-independently = {
      expr = classifyModule importedPlainFn;
      expected = "dirty";
    };

    # END-TO-END — the wrapped clean module applies, contributes config, leaks NO marker key.
    test-pure-module-config-has-no-marker = {
      expr = e2e.config;
      expected = {
        a = "U";
        b = 7;
      };
    };
  };
}
