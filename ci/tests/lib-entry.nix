# THE LIBRARY ENTRY'S CALLING CONVENTION — that `lib/default.nix`'s header and its formal list say
# the same thing about what a caller must supply.
#
# ★★★ WHY THIS FILE EXISTS. `lib/default.nix` documented `types ? { }` as an OPTIONAL parameter for
# byte-mode bring-up, and that default DID NOT EVALUATE. The published `types` namespace is a
# linkset merge whose allowlist names three collisions AGAINST THE LEAF VOCABULARY (`listOf`,
# `attrsOf`, `option`), so an EMPTY vocabulary makes every entry stale and `merge.types` throws from
# inside: `linkset: allowlist entry 'attrsOf' names no actual collision between 'gen-types' and
# 'gen-merge'`. A caller following the library's own stated convention got an exception, not a
# default — and could not tell "I called it wrong" from "the library is broken" (den-hoag-qsrcp).
#
# ★★ THE DEFECT WAS INVISIBLE TO EVERY OTHER CELL IN THIS SUITE, WHICH IS THE REASON FOR A FILE
# RATHER THAN A LINE. Measured: `ci#tests` 450/450 and `ci#testsError` 61/61, exit 0 on both, with
# the broken default live. Every construction here — `genMerge`, `genMergeCompat`, `genMergeWith`,
# `genMergeWithMemo` (ci/flake.nix), the root shim (`default.nix`) and the flake output — supplies
# `types` explicitly, so the DEFAULT is the one path the suite never took. A convention nothing
# exercises is prose, and prose does not red.
#
# ★ THE INSTRUMENT IS `builtins.functionArgs`, WHICH READS THE SIGNATURE AND FORCES NOTHING —
# `builtins.functionArgs ({ a ? throw "FORCED", b }: null)` is `{ a = true; b = false; }` with no
# throw (ci/tests/entry.nix measures the same property for the root shim). `true` at a name means
# THAT NAME CARRIES A DEFAULT, so the expectation below is the claim "this entry synthesizes none
# of its four inputs" stated as data. Re-introducing `types ? { }` flips exactly one field and
# reds this cell by name.
#
# ★ THE EXPECTATION IS THE WHOLE RECORD, NOT `types` ALONE. `prelude`, `types`, `memo` and `scope`
# are four foreign VALUES this library cannot construct — it is nixpkgs-lib-free and has no fetcher
# — so "defaults nothing" is the property, and a record equality states it without a name list that
# a fifth formal could slip past.
#
# ★★ `scope` (gen-scope.lib, ADR-0006) IS THE FOURTH, AND IT IS THE ONE THE CONVENTION WAS TESTED
# ON. It is required for the same measured reason `types` and `memo` are: a defaulted evaluator
# cannot refuse, so the library's door would admit a non-evaluator and diverge inside the knot
# instead of naming what is missing at the construction call (den-hoag-0pk67).
{
  prelude,
  genTypes,
  genMemo,
  genScope,
  ...
}:
let
  documented = {
    inherit prelude;
    types = genTypes;
    memo = genMemo;
    scope = genScope;
  };
in
{
  # (i) THE HEADER AND THE FORMALS AGREE: no input is defaulted, so omitting one aborts AT THE CALL
  # SITE naming it rather than throwing from inside the namespace assembly.
  flake.tests.lib-entry.test-the-entry-defaults-nothing = {
    expr = builtins.functionArgs (import ../../lib);
    expected = {
      prelude = false;
      types = false;
      memo = false;
      scope = false;
    };
  };

  # (ii) THE DOCUMENTED CALL EVALUATES, and it is the `types` namespace that is forced — the member
  # the bad default threw on. `builtins.attrNames` is the force: it is what runs the linkset merge.
  # The assertion is MEMBERSHIP FROM BOTH SIDES rather than a count, deliberately: the vocabulary's
  # size is gen-types' to move, and a cell pinning it would red on a routine bump while saying
  # nothing about this convention.
  flake.tests.lib-entry.test-the-documented-call-publishes-the-merged-namespace = {
    expr =
      let
        t = (import ../../lib documented).types;
      in
      builtins.deepSeq (builtins.attrNames t) {
        fromLeafVocabulary = t ? str;
        fromStructuralStrategies = t ? attrsOf;
      };
    expected = {
      fromLeafVocabulary = true;
      fromStructuralStrategies = true;
    };
  };

  # (iii) CONTROL — the reader discriminates a defaulted formal from a required one, exercised at an
  # input the two cells above never use. Without it, a `functionArgs` that returned a constant
  # record would pass (i) forever; the fixture's own formals are named here and by nothing else.
  flake.tests.lib-entry.test-control-the-formals-reader-sees-a-default = {
    expr = builtins.functionArgs (
      {
        required,
        defaulted ? { },
      }:
      null
    );
    expected = {
      required = false;
      defaulted = true;
    };
  };
}
