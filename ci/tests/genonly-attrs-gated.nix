# A REFUSED EVALUATION SERVES NO DEFINITION VALUE THROUGH ITS GEN-ONLY ATTRIBUTES (ADR-0039 (b′)). `optionDefs`,
# `freeformConfig` and `warmDecision.uncheckedConfig` carry definition values, so they are read through the refusal
# the exported `config` carries, its identity verdict then `_orphanCheck`, as `options` is
# (`./checked-result-seam.nix`). `provenance`, `undeclared`, `deprecations`, `freeformProv` and the warm decision's
# metadata carry none and are served past the refusal, as README states.
#
# A warm evaluation runs through its prior's continuation, `warmDecision.next`, which holds the prior's record unread
# through its refusal: warm over a refused prior equals cold, an uncatchable prior check included, and the
# continuation is the published door warm-started from that prior, refusing what the door refuses
# (`./_fixtures/genonly-attrs-gated.nix`; the refusal texts are in `../tests-error.nix`). RED before the landing:
# every `gated-*` cell (served), and every `next-*`, `next-edited-*` and `door-next-*` cell (`<absent>`).
{ genMerge, ... }:
let
  fx = import ./_fixtures/genonly-attrs-gated.nix { gm = genMerge; };
  # one cell per read: `test-<table>-<group>-<read>`, expecting `expected.<group>.<read>`
  table =
    name: actual: expected:
    builtins.concatLists (
      builtins.attrValues (
        builtins.mapAttrs (
          group: reads:
          map (read: {
            name = "test-${name}-${group}-${read}";
            value = {
              expr = if builtins.isAttrs actual.${group} then actual.${group}.${read} else actual.${group};
              expected = reads.${read};
            };
          }) (builtins.attrNames reads)
        ) expected
      )
    );
  every =
    v: names:
    builtins.listToAttrs (
      map (n: {
        name = n;
        value = v;
      }) names
    );
  stated = every "served" [
    "provenance"
    "undeclared"
    "deprecations"
    "freeformProv"
    "warmDecision.mode"
    "warmDecision.strict"
    "warmDecision.options"
  ];
  warmEqualsCold = {
    mode = "warm";
    reason = null;
    config = true;
    provenance = true;
  };
in
{
  flake.tests.genonly-attrs-gated =
    builtins.listToAttrs (
      table "gated" fx.gated {
        s1 = every "refused" [
          "optionDefs.values"
          "optionDefs.topDefs"
          "optionDefs.realized.unmatched"
          "freeformConfig"
          "warmDecision.uncheckedConfig"
        ];
        s2 = every "refused" [
          "optionDefs.values"
          "freeformConfig"
          "warmDecision.uncheckedConfig"
        ];
        idm = every "refused" [
          "optionDefs.values"
          "freeformConfig"
          "warmDecision.uncheckedConfig"
        ];
      }
      ++ table "clean" fx.clean {
        s1 = {
          "optionDefs.values" = "served";
          "optionDefs.topDefs" = "served";
          "warmDecision.uncheckedConfig.a" = 5;
          "config.a" = 5;
        };
        s2 = {
          freeformConfig = {
            free = 7;
          };
          "warmDecision.uncheckedConfig.free" = 7;
          "config.free" = 7;
        };
        idm = {
          "optionDefs.values" = "served";
          "warmDecision.uncheckedConfig.name" = "igloo";
        };
      }
      ++ table "stated" fx.stated {
        s1 = stated;
        # the throwing `_module.check` definition is forced to WHNF by its own loc's provenance record (README
        # "Forcing contract"), so `provenance._module.check` alone refuses, at base as on the build
        s2 = removeAttrs stated [ "provenance" ];
        idm = stated;
      }
      ++ table "warm" fx.warm {
        w3a = warmEqualsCold;
        w3b = warmEqualsCold;
        w3c = warmEqualsCold;
        w3d = warmEqualsCold;
        w3e = warmEqualsCold;
      }
      ++ table "door" fx.doorArms {
        door = {
          root = "refused";
          misspelt = "refused";
        };
        next = {
          root = "refused";
          misspelt = "refused";
        };
      }
    )
    // {
      # the control on every gated read: each source's `config` refuses
      test-config-s1-refused = {
        expr = fx.config.s1;
        expected = "refused";
      };
      test-config-s2-refused = {
        expr = fx.config.s2;
        expected = "refused";
      };
      test-config-idm-refused = {
        expr = fx.config.idm;
        expected = "refused";
      };
      # the continuation over the refused `s1`'s own modules refuses as `s1` does
      test-next-over-its-own-modules-refuses-every-gated-leaf = {
        expr = fx.next;
        expected = {
          config = "refused";
          "optionDefs.values" = "refused";
          "optionDefs.topDefs" = "refused";
          freeformConfig = "refused";
          "warmDecision.uncheckedConfig" = "refused";
        };
      };
      # after an edit declaring the stray, the continuation is the door warm-started from `s1`, and equals cold
      test-next-edited-equals-the-door-and-cold = {
        expr = fx.nextEdited;
        expected = {
          mode = "warm";
          doorConfig = true;
          doorProvenance = true;
          coldConfig = true;
          coldProvenance = true;
        };
      };
    };
}
