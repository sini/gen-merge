# gen-merge's closed record doors — lint, mkCoreValue — route through gen-prelude's shared
# `checkOptions` / `checkRequired` (den-hoag-7gp66 P1, spec
# `2026-09-25-gen-uniform-api-grammar-spec.md` §v1.2) rather than native closed formals, so a
# missing required field or an extra field is answered BY NAME and CATCHABLY instead of Nix's own
# uncatchable "called with unexpected/without required argument". `ci/tests-error.nix`'s
# `door-checks` suite pins WHICH message fires; this suite pins that a refusal is catchable
# (ADR-0025 item 1) and that a record door still admits an extra field (R5's stated price — width
# subtyping, never reported).
#
# `evalModuleTree`'s own wiring is deferred: it composes `checkOptions` over `checkRequired` too,
# but that composition regresses the hub's perf-bench (entityMatch/kindMatch/schemaHosts thunk and
# alloc ratios go over bound — CANDIDATE OVER BOUND, exit 6). The reverted hunk and its cells are
# saved as a diff for a follow-up unit rather than landed here; see
# reports/den-hoag-7gp66-p1-merge-evalmoduletree-check.diff in den-ag-design.
{ genMerge, ... }:
let
  gm = genMerge;
  force = v: builtins.deepSeq v null;
  refused = v: !(builtins.tryEval v).success;
in
{
  flake.tests.door-lint = {
    test-valid-call-unchanged = {
      expr = gm.lint { modules = [ { } ]; };
      expected = [ ];
    };
    # R5: a record door is open, so an extra field is admitted and never reported — the call must
    # not throw.
    test-extra-field-on-a-record-is-admitted = {
      expr = refused (
        force (
          gm.lint {
            modules = [ { } ];
            zzq_door_check_c = 1;
          }
        )
      );
      expected = false;
    };
    test-missing-modules-refused-catchably = {
      expr = refused (force (gm.lint { }));
      expected = true;
    };
    test-non-set-argument-refused-catchably = {
      expr = refused (force (gm.lint "zzq_door_check_d"));
      expected = true;
    };
  };

  flake.tests.door-mk-core-value = {
    test-valid-call-unchanged = {
      expr = gm.mkCoreValue {
        digest = "d";
        values = { };
      };
      expected = {
        __coreValue = true;
        digest = "d";
        values = { };
      };
    };
    test-extra-field-on-a-record-is-admitted = {
      expr = refused (
        force (
          gm.mkCoreValue {
            digest = "d";
            values = { };
            zzq_door_check_e = 1;
          }
        )
      );
      expected = false;
    };
    test-missing-required-field-refused-catchably = {
      expr = refused (force (gm.mkCoreValue { digest = "d"; }));
      expected = true;
    };
    test-non-set-argument-refused-catchably = {
      expr = refused (force (gm.mkCoreValue "zzq_door_check_f"));
      expected = true;
    };
  };
}
