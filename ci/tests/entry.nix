# THE STANDALONE ROOT ENTRY — the plain-import path, which no other cell in this suite reaches.
#
# ★★★ WHY THIS FILE EXISTS. Every other suite here builds the library by importing `../lib` directly
# with injected values, so the ROOT `default.nix` — the entry a non-flake consumer actually uses — is
# evaluated by NOTHING. A shim can therefore name fewer arguments than the library it delegates to,
# promise lockstep with the flake in its own comment, and stay green forever. The class is not
# hypothetical: it fired five times in one day across this roster, in the same shape each time — a
# library grows a formal, the flake output is updated, the shim is not, and `import ./.` throws
# `called without required argument` while every cell passes.
#
# ★★ THE CELL IS PURE, AND THE PURITY IS A CONSEQUENCE OF HOW IT IS CALLED. This shim's defaults
# `builtins.fetchTree` the flake-locked revisions; supplying BOTH formals explicitly means those
# defaults are never forced, so this reaches the network not at all. What it tests is the shim's
# SIGNATURE and its DELEGATION — which is precisely where the defect lives.
#
# ★ IT CATCHES BOTH DIRECTIONS OF THE DRIFT, which is why it is an argument-passing cell rather than
# an `attrNames` comparison alone:
#   · a shim naming FEWER formals than `lib` refuses this application by name
#     (`called with unexpected argument 'types'`);
#   · a shim that forwards fewer than `lib` requires refuses inside it
#     (`called without required argument 'prelude'`).
# Both are uncatchable evaluator refusals, so either turns these cells ☢️ rather than ❌ — a crash is
# the loudest reading available and the right one for an entry point that does not exist.
#
# ★ `prelude` AND `genTypes` ARE THE SAME BINDINGS THE FLAKE'S `lib` OUTPUT IS BUILT FROM (ci/flake.nix
# binds each once). That is what makes the comparison below a reading of the SHIM: over two different
# substrate builds it would be comparing two libraries, and equal `attrNames` would say nothing about
# the entry point.
{
  genMerge,
  prelude,
  genTypes,
  ...
}:
let
  standalone = import ../.. {
    inherit prelude;
    types = genTypes;
  };
in
{
  # ★ The assertion is over the APPLIED surfaces, not over the entries themselves: both are functions
  # of their injected substrate, and two Nix lambdas are never equal — so `entry == entry` would read
  # `false` on a correct library and could not distinguish drift from the language. The applied form
  # is also the stronger claim: it is the surface a consumer actually receives.
  flake.tests.entry.test-standalone-entry-matches-lib = {
    expr = builtins.attrNames standalone;
    expected = builtins.attrNames genMerge;
  };

  # The surface is not merely equal but non-trivial, so the cell above cannot pass by both sides being
  # empty. Twenty is a floor with real margin under the shipped surface, not a restatement of it: a
  # count pinned exactly would fail on every deliberate addition and teach the next author to edit
  # this line rather than read it.
  flake.tests.entry.test-control-the-compared-surface-is-non-trivial = {
    expr = builtins.length (builtins.attrNames standalone) > 20;
    expected = true;
  };

  # ★ THE COMPARISON IS SHOWN ABLE TO FAIL, in the same run. Without this, an `attrNames` equality
  # between two values that happen to be the same import is a tautology nobody has checked.
  flake.tests.entry.test-control-the-comparison-discriminates = {
    expr = builtins.attrNames standalone == builtins.attrNames (removeAttrs genMerge [ "types" ]);
    expected = false;
  };

  # And the library reached THROUGH the shim actually works, rather than merely having the right keys
  # — a delegation that forwarded the wrong value would satisfy an `attrNames` check.
  #
  # ★ THE PROBE IS CHOSEN TO EXERCISE BOTH FORWARDED FORMALS AT ONCE. It runs the engine (which is
  # built over `prelude`) across an option whose type comes from the published `types` namespace
  # (which exists only if `types` was forwarded — a shim delegating `types = { }` would still
  # construct a library, and its `types.str` would not be there). One resolved config value is
  # therefore evidence about the whole delegation rather than about one half of it.
  flake.tests.entry.test-the-shims-library-is-live = {
    expr =
      (standalone.evalModuleTree {
        modules = [
          { options.x = standalone.mkOption { type = standalone.types.str; }; }
          { config.x = "through-the-shim"; }
        ];
      }).config.x;
    expected = "through-the-shim";
  };
}
