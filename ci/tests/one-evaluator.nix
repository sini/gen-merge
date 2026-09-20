# ONE EVALUATOR — that gen-merge's module-tree evaluation is a USE of the injected graph evaluator
# and not a second engine standing beside it (ADR-0006; ADR-0008 §1).
#
# Three properties, and each is here because the other two pass without it:
#
#   · THE DOOR — the library refuses a construction whose `scope` is not an evaluator, BY NAME and
#     catchably, rather than admitting it and dying inside the knot. Its refusal arm is a `throw`,
#     so the message lives in `ci/tests-error.nix`; what lives here is the arm that must still
#     evaluate, without which a door that refused everything would read as a pass.
#   · THE FOLD'S REFUSAL — a declaration shape ADR-0033 rules inadmissible refuses at the fold and
#     `tryEval` CONTAINS it. The discriminating figure is containment, not the message: at
#     `3aa6dac` every one of these arms was `infinite recursion encountered`, which `tryEval` does
#     not contain, so the reading moves from an abort to a value.
#   · NO SECOND DRIVER — the published library declares no fixpoint driver of its own. This one
#     exists because the first two pass on a HALF-PORTED engine that routes the declaration plane
#     through the injected evaluator and keeps its own `fix` for the freeform or nested-submodule
#     path. That is the two-driver state the consolidation exists to end, and neither of the cells
#     above looks at whether a second driver survived.
{
  genMerge,
  genPrelude,
  lib,
  ...
}:
let
  gm = genMerge;
  t = gm.types;
  inherit (gm) mkOption;

  # Force the whole config tree and report CONTAINMENT. A shallow force would not reach the fold.
  probe =
    mods: builtins.tryEval (builtins.deepSeq (gm.evalModuleTree { modules = mods; }).config "ok");

  # ── the source scan, for the driver census ──────────────────────────────────────────────────
  # Comment-stripped, LINES unit. The same strip `ci/tests/purity.nix` runs over the same domain,
  # and the DOMAIN's own pin lives there: `test-scan-subject-is-the-library-tree` expects an exact
  # nine-path manifest, so a file leaving `lib/` reds that cell rather than silently shrinking this
  # scan. What this file adds is the live control, below — a zero over a scan that read nothing is
  # not a result, and the control is what separates the two.
  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );

  walk =
    dir:
    lib.concatLists (
      lib.mapAttrsToList (
        entry: type:
        if type == "directory" then
          walk (dir + "/${entry}")
        else if lib.hasSuffix ".nix" entry then
          [ (dir + "/${entry}") ]
        else
          [ ]
      ) (builtins.readDir dir)
    );

  code = lib.concatMapStringsSep "\n" (p: stripComments (builtins.readFile p)) (
    walk ../../lib
    ++ [
      ../../flake.nix
      ../../default.nix
    ]
  );

  # LINES, not occurrences — the unit the reading is stated in, carried in the name.
  linesMatching =
    token: lib.length (lib.filter (l: genPrelude.hasInfix token l) (lib.splitString "\n" code));
in
{
  flake.tests.one-evaluator = {

    # ── THE DOOR, its live arm ────────────────────────────────────────────────────────────────
    # A construction over the REAL evaluator evaluates and returns the ordinary value. The refusal
    # arms are in `ci/tests-error.nix`; without this one they are consistent with a door that
    # refuses unconditionally, which would be a broken library passing its own oracle.
    test-the-door-admits-a-real-evaluator = {
      expr = probe [
        {
          options.x = mkOption { type = t.str; };
          config.x = "v";
        }
      ];
      expected = {
        success = true;
        value = "ok";
      };
    };

    # ── THE FOLD'S REFUSAL, both directions, in one cell ──────────────────────────────────────
    # ★ THE ADMITTED ARMS ARE NOT DECORATION. Each is a shape the declaration stratum must NOT
    # refuse, and each was measured admitted at `3aa6dac` too — so a refusal that widened to cover
    # one of them would red here rather than passing as a stricter engine. `optionDefaultReadsConfig`
    # is the sharpest: an option DESCRIPTOR legitimately carries stratum-2 values in its own
    # fields, and an engine that produced its declarations under the poisoned arguments rather than
    # merely GUARDING them with it refuses this shape. Measured: 10 cells across four suites.
    #
    # ★ THE REFUSED ARMS REPORT CONTAINMENT, WHICH IS THE WHOLE READING. `false` here means
    # `{ success = false; }` — a refusal a caller can catch. At `3aa6dac` all three read
    # `infinite recursion encountered` and `tryEval` did not contain any of them, so this cell's
    # own `expr` was not a value at all.
    test-the-declaration-stratum-admits-value-reads-and-refuses-declaration-reads = {
      expr = {
        # ADMITTED — stratum 2 reading stratum 1's settled output, which ADR-0033 licenses.
        optionValueReadsConfig =
          (probe [
            (
              { config, ... }:
              {
                options.a = mkOption { type = t.int; };
                options.b = mkOption { type = t.int; };
                config.a = 14;
                config.b = config.a;
              }
            )
          ]).success;
        optionDefaultReadsConfig =
          (probe [
            (
              { config, ... }:
              {
                options.n = mkOption {
                  type = t.str;
                  default = "n";
                };
                options.label = mkOption {
                  type = t.str;
                  default = "L-" + config.n;
                };
              }
            )
          ]).success;
        optionsReadInADescriptorField =
          (probe [
            (
              { options, ... }:
              {
                options.x = mkOption {
                  type = t.int;
                  default = lib.length (builtins.attrNames options);
                };
              }
            )
          ]).success;

        # REFUSED — the declaration plane reading the value plane. ADR-0033's own three shapes.
        optionKeySetReadsConfig =
          (probe [
            (
              { config, ... }:
              {
                options = {
                  flag = mkOption {
                    type = t.bool;
                    default = true;
                  };
                }
                // (if config.flag then { extra = mkOption { type = t.int; }; } else { });
                config.extra = 1;
              }
            )
          ]).success;
        importsTargetsReadConfig =
          (probe [
            (
              { config, ... }:
              {
                options.which = mkOption {
                  type = t.attrsOf t.attrs;
                  default = { };
                };
                imports = [ (config.which.target or { }) ];
              }
            )
          ]).success;
        optionKeySetReadsOptions =
          (probe [
            (
              { options, ... }:
              {
                options = {
                  a = mkOption {
                    type = t.int;
                    default = 1;
                  };
                }
                // (
                  if options ? b then
                    { }
                  else
                    {
                      b = mkOption {
                        type = t.int;
                        default = 2;
                      };
                    }
                );
              }
            )
          ]).success;
      };
      expected = {
        optionValueReadsConfig = true;
        optionDefaultReadsConfig = true;
        optionsReadInADescriptorField = true;
        optionKeySetReadsConfig = false;
        importsTargetsReadConfig = false;
        optionKeySetReadsOptions = false;
      };
    };

    # ── NO SECOND DRIVER ──────────────────────────────────────────────────────────────────────
    # `prelude.fix` is gen-merge's own knot-tie and was its sole fixpoint driver; the module tree is
    # now an ordinary attribute on the injected evaluator, so the token is gone from the published
    # library. The live control is the same reader over the same text, on a `prelude.` member the
    # library does use — without it a scan that read nothing would report the same zero.
    #
    # ★ IT IS A SOURCE-TEXT PREDICATE OVER ONE TREE, and that bound is the point rather than a gap:
    # it is precision-oriented and an author could evade it by naming a driver something else. That
    # residue belongs to the hub's driver register, which is read by a person. Widening this cell
    # into a census of the ecosystem is the shape the design rejects.
    test-the-published-library-declares-no-fixpoint-driver = {
      expr = {
        fixDriverLines = linesMatching "prelude.fix";
        controlIsLive = linesMatching "prelude.genList" > 0;
      };
      expected = {
        fixDriverLines = 0;
        controlIsLive = true;
      };
    };

    # ★ CONTROL — the scanner discriminates. Without it `fixDriverLines = 0` is consistent with a
    # reader that cannot match anything at all, and `controlIsLive` above only says SOME token was
    # found. This one asks the same reader for the subject token under a spelling that IS present,
    # so the zero above is a statement about `prelude.fix` and not about the instrument.
    test-control-the-driver-scanner-finds-the-token-it-is-looking-for = {
      expr = linesMatching "driveKnot" > 0;
      expected = true;
    };
  };
}
