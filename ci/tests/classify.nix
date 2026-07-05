# Source-class classification + `pureModule` (design spec §§0.3/3/5) — the srcClass substrate the warm
# re-eval path consumes. Nothing consumes it yet beyond these tests.
#
# The load-bearing WHY (spec §0.3): `builtins.functionArgs` cannot prove a function module clean —
# `args@{ genSchema, ... }: args.config` shows only `genSchema`, a bare lambda shows `{ }`, yet the
# engine applies every function module with the whole `specialArgs // extra` set (nixpkgs semantics),
# so any function module can reach `config`. Hence attrsets classify clean UNCONDITIONALLY, function
# modules are DIRTY BY DEFAULT, and `pureModule` is the author's explicit clean assertion. The
# adversarial pair below (formals-only + `@`-capture, both UNMARKED → dirty) pins dirty-by-default.
{ genMerge, genMergeCore, ... }:
let
  gm = genMerge;
  # The shipped public API — `pureModule` is the module-author surface; `evalModuleTree` drives the
  # end-to-end teeth.
  inherit (gm)
    pureModule
    evalModuleTree
    mkOption
    ;
  # `classifyModule` is NOT on the public surface (lib/default.nix) — it rides the internal core seam
  # (lib/modules.nix), reached here through the ci flake's test-only `genMergeCore` handle.
  inherit (genMergeCore) classifyModule;
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

  # ── end-to-end: pureModule integrates with `callM`, contributes config ────────────────────────────
  # The wrapped clean function reads a specialArg (`u`) and imports a (dirty) function module that
  # contributes `b`; both defs land in config. This pins the `callM` path — the wrapper's `__functor`
  # is applied and CONSUMED before its content entry is recorded, so `__pureModule` is gone from config
  # by construction (NOT via the `configOf` strip, which the separate `stripFixture` below pins).
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

  # ── defensive `configOf` strip — the ONLY test that fails if the strip line is deleted ────────────
  # A raw config-shorthand attrset carrying `__pureModule` WITHOUT the `__functor` wrapper path: `callM`
  # never consumes it (it is a plain attrset, not a marked wrapper), so the marker would leak into config
  # as a freeform key unless `configOf` strips it. Freeform absorbs `x`; the marker must NOT survive.
  stripFixture = evalModuleTree {
    modules = [
      { freeformType = t.lazyAttrsOf t.anything; }
      {
        __pureModule = true;
        x = 1;
      }
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

    # END-TO-END — the wrapped clean module applies via `callM` and contributes config (marker consumed
    # pre-record; no `__pureModule` in config by construction).
    test-pure-module-config-via-callm = {
      expr = e2e.config;
      expected = {
        a = "U";
        b = 7;
      };
    };

    # DEFENSIVE STRIP — a raw shorthand carrying the marker key (no functor path) must not leak it.
    # The ONLY test that fails if the `configOf` `__pureModule` strip line is removed.
    test-configof-strips-marker-key = {
      expr = stripFixture.config;
      expected = {
        x = 1;
      };
    };
  };
}
