# THE DOOR CHECKS FIRE AT APPLICATION, NOT ONLY BEHIND A LATER FIELD READ (den-hoag-7gp66 P1
# lazy-doors fix).
#
# `door-checks.nix` proves `mkCoreValue`'s and `lint`'s checkRequired violations are CATCHABLE, but
# does so with `deepSeq` (`force`) — and `evalModuleTree`'s own cells in that file already note the
# gap that leaves open for the OTHER two doors: a bare `(mkCoreValue badArgs).digest` would never
# touch a violation the return's own construction does not force. This file closes that gap with a
# narrower, harder predicate: `seq` alone, to WHNF of the door's OWN return, reading NO field at
# all — the shape of a defensive `builtins.seq (door args) rest` a caller writes to gate on
# validity before touching any output.
#
# MEASURED (den-hoag-7gp66 P1 strictness sweep, gen-memo eed0685's defect class — a check that sits
# behind a later read is a check a caller who does not make that read never runs): `mkCoreValue`
# returned `{ __coreValue = true; inherit (checked) digest values; }` — `__coreValue` is a literal,
# so the return's own WHNF forced neither `digest` nor `values`, and `isCoreValue`'s own
# `.__coreValue or false` read is exactly the consumer pattern that would never touch `checked`
# either. Fixed by threading `builtins.seq checked` through the return — the idiom gen-settings'
# door fix (0474486) already uses. `lint` was already strict (`ci/tests/door-checks.nix`'s
# `test-missing-modules-refused-catchably` already used `deepSeq`, but the door refuses at `seq`
# too — pinned below, not fixed). `evalModuleTree` is excluded (out of this population — never
# landed, perf-bench regression).
{ genMerge, ... }:
let
  gm = genMerge;

  # `seq`, not `deepSeq`: WHNF of the door's own return, no field read — the strictly narrower
  # predicate `door-checks.nix`'s `deepSeq`-based `force`/`refused` cannot discriminate, since
  # `deepSeq` forces straight through to the same guard whichever field it hangs off.
  refusesAtApplication = e: !(builtins.tryEval (builtins.seq e null)).success;
  answersAtApplication = e: (builtins.tryEval (builtins.seq e null)).success;
in
{
  flake.tests.door-application-strictness = {
    # ★ LIVE CONTROL FOR THE WHOLE SUITE, first: `tryEval`+`seq` catches an ordinary throw, and a
    # non-throwing value answers. Without this, every `refusesAtApplication` cell below is equally
    # consistent with a predicate that reads `false` no matter what it is handed.
    test-control-tryeval-seq-catches-an-ordinary-throw = {
      expr = refusesAtApplication (throw "control probe, not this suite's subject");
      expected = true;
    };
    test-control-tryeval-seq-answers-a-non-throwing-value = {
      expr = answersAtApplication 1;
      expected = true;
    };

    # mkCoreValue — FIXED: was `{ __coreValue = true; inherit (checked) digest values; }`; now
    # `builtins.seq checked { ... }`.
    test-mkcorevalue-missing-required-field-refused-at-application = {
      expr = refusesAtApplication (gm.mkCoreValue { digest = "d"; });
      expected = true;
    };
    test-mkcorevalue-non-attrset-refused-at-application = {
      expr = refusesAtApplication (gm.mkCoreValue "zzq_p1_str");
      expected = true;
    };
    # R5's stated price is unchanged: an extra field on a record door is still admitted, and is
    # admitted at application too — `checkRequired` never looks at it either way.
    test-mkcorevalue-extra-field-on-a-record-is-admitted-at-application = {
      expr = answersAtApplication (
        gm.mkCoreValue {
          digest = "d";
          values = { };
          zzq_p1_unk = 1;
        }
      );
      expected = true;
    };

    # lint — already strict. Pinned, not fixed.
    test-lint-missing-required-field-refused-at-application = {
      expr = refusesAtApplication (gm.lint { });
      expected = true;
    };
    test-lint-non-attrset-refused-at-application = {
      expr = refusesAtApplication (gm.lint "zzq_p1_str");
      expected = true;
    };
  };
}
